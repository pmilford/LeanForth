#!/usr/bin/env python3
"""Offline DWARF (.eh_frame) unwinder and symboliser for perf.data files.

The installed perf (WSL build) has no libelf, libdw or libunwind, so it can
record user stacks (--call-graph dwarf) but cannot unwind or symbolise them.
This script does both:

  perfunwind.py PERF_DATA OUT_STACKS [--max-frames N]

It reads PERF_RECORD_MMAP/MMAP2 and PERF_RECORD_SAMPLE records, unwinds each
sample's copied user stack with the CFI rules in each ELF's .eh_frame
(tracking RSP, RBP and the return address), maps every frame to the enclosing
function symbol (.symtab, else .dynsym), demangles with c++filt, and writes one
line per sample: "pid<TAB>truncated-flag<TAB>leaf;caller;...;outermost".
truncated-flag is 1 when unwinding stopped before reaching a frame with no
caller (end of copied stack, unknown code, unreadable slot), else 0.
"""
import bisect, collections, os, struct, subprocess, sys

# ---------------------------------------------------------------- ELF -----

class Elf:
    def __init__(self, path):
        self.path = path
        with open(path, 'rb') as f:
            self.data = f.read()
        d = self.data
        assert d[:4] == b'\x7fELF' and d[4] == 2, path
        (self.phoff, self.shoff) = struct.unpack_from('<QQ', d, 0x20)
        (phentsize, phnum, shentsize, shnum, shstrndx) = struct.unpack_from('<HHHHH', d, 0x36)
        self.segs = []
        for i in range(phnum):
            (ptype, pflags, off, vaddr, paddr, filesz, memsz, align) = \
                struct.unpack_from('<IIQQQQQQ', d, self.phoff + i * phentsize)
            if ptype == 1:  # PT_LOAD
                self.segs.append((off, vaddr, filesz))
        self.secs = {}
        shdrs = []
        for i in range(shnum):
            shdrs.append(struct.unpack_from('<IIQQQQIIQQ', d, self.shoff + i * shentsize))
        strtab_off = shdrs[shstrndx][4]
        for sh in shdrs:
            name = d[strtab_off + sh[0]: d.index(b'\0', strtab_off + sh[0])].decode()
            self.secs[name] = sh
        self._syms()
        self._eh_frame()
        self.rowcache = {}

    def file_off_to_vaddr(self, off):
        for (o, v, sz) in self.segs:
            if o <= off < o + max(sz, 1):
                return off - o + v
        return off

    def _syms(self):
        d = self.data
        syms = {}
        for tab, strn in (('.dynsym', '.dynstr'), ('.symtab', '.strtab')):
            if tab not in self.secs or strn not in self.secs:
                continue
            sh, st = self.secs[tab], self.secs[strn]
            off, size, ent = sh[4], sh[5], sh[9] or 24
            stroff = st[4]
            for i in range(size // ent):
                (nm, info, other, shndx, value, ssize) = struct.unpack_from('<IBBHQQ', d, off + i * ent)
                typ = info & 0xf
                if typ not in (2, 10) or value == 0 or shndx == 0:
                    continue
                name = d[stroff + nm: d.index(b'\0', stroff + nm)].decode('utf-8', 'replace')
                # prefer .symtab names (later loop overwrites)
                syms[value] = (name, ssize)
        self.sym_addrs = sorted(syms)
        self.sym_info = [syms[a] for a in self.sym_addrs]

    def symbol(self, vaddr):
        i = bisect.bisect_right(self.sym_addrs, vaddr) - 1
        if i < 0:
            return None
        a = self.sym_addrs[i]
        name, size = self.sym_info[i]
        if size and vaddr >= a + size:
            # inside a gap; still attribute to nearest preceding symbol if size unknown
            return None
        return name

    # ------------------------------------------------------- eh_frame -----
    def _read_enc(self, enc, pos, sec_vaddr, sec_off):
        d = self.data
        fmt = enc & 0x0f
        start = pos
        if enc == 0xff:
            return None, pos
        if fmt == 0x00:
            v = struct.unpack_from('<Q', d, pos)[0]; pos += 8
        elif fmt == 0x01:
            v, pos = uleb(d, pos)
        elif fmt == 0x02:
            v = struct.unpack_from('<H', d, pos)[0]; pos += 2
        elif fmt == 0x03:
            v = struct.unpack_from('<I', d, pos)[0]; pos += 4
        elif fmt == 0x04:
            v = struct.unpack_from('<Q', d, pos)[0]; pos += 8
        elif fmt == 0x09:
            v, pos = sleb(d, pos)
        elif fmt == 0x0a:
            v = struct.unpack_from('<h', d, pos)[0]; pos += 2
        elif fmt == 0x0b:
            v = struct.unpack_from('<i', d, pos)[0]; pos += 4
        elif fmt == 0x0c:
            v = struct.unpack_from('<q', d, pos)[0]; pos += 8
        else:
            raise ValueError(f'encoding {enc:#x}')
        app = enc & 0x70
        if app == 0x10:  # pcrel
            v += sec_vaddr + (start - sec_off)
        v &= 0xffffffffffffffff
        return v, pos

    def _eh_frame(self):
        self.fdes = []  # (pc_begin, pc_end, cie, instr_start, instr_end)
        if '.eh_frame' not in self.secs:
            return
        sh = self.secs['.eh_frame']
        sec_vaddr, sec_off, sec_size = sh[3], sh[4], sh[5]
        d = self.data
        pos = sec_off
        end = sec_off + sec_size
        cies = {}
        while pos + 4 <= end:
            length = struct.unpack_from('<I', d, pos)[0]
            if length == 0:
                pos += 4
                continue
            hdr = 4
            if length == 0xffffffff:
                length = struct.unpack_from('<Q', d, pos + 4)[0]
                hdr = 12
            entry_start = pos + hdr
            entry_end = entry_start + length
            cie_id = struct.unpack_from('<I', d, entry_start)[0]
            if cie_id == 0:
                cies[pos] = self._parse_cie(entry_start + 4, entry_end, sec_vaddr, sec_off)
            else:
                cie_pos = entry_start - cie_id
                cie = cies.get(cie_pos)
                if cie is None:
                    # find CIE parse lazily
                    length2 = struct.unpack_from('<I', d, cie_pos)[0]
                    cie = self._parse_cie(cie_pos + 8, cie_pos + 4 + length2, sec_vaddr, sec_off)
                    cies[cie_pos] = cie
                p = entry_start + 4
                pc_begin, p = self._read_enc(cie['fde_enc'], p, sec_vaddr, sec_off)
                pc_range, p = self._read_enc(cie['fde_enc'] & 0x0f, p, sec_vaddr, sec_off)
                if cie['aug'].startswith('z'):
                    alen, p = uleb(d, p)
                    p += alen
                self.fdes.append((pc_begin, pc_begin + pc_range, cie, p, entry_end))
            pos = entry_end
        self.fdes.sort(key=lambda t: t[0])
        self.fde_starts = [t[0] for t in self.fdes]

    def _parse_cie(self, p, end, sec_vaddr, sec_off):
        d = self.data
        version = d[p]; p += 1
        z = d.index(b'\0', p)
        aug = d[p:z].decode(); p = z + 1
        if 'eh' in aug:
            p += 8
        code_align, p = uleb(d, p)
        data_align, p = sleb(d, p)
        if version == 1:
            ra = d[p]; p += 1
        else:
            ra, p = uleb(d, p)
        fde_enc = 0
        if aug.startswith('z'):
            alen, p = uleb(d, p)
            q = p
            for ch in aug[1:]:
                if ch == 'R':
                    fde_enc = d[q]; q += 1
                elif ch == 'P':
                    penc = d[q]; q += 1
                    _, q = self._read_enc(penc, q, sec_vaddr, sec_off)
                elif ch == 'L':
                    q += 1
                elif ch in 'SB':
                    pass
                else:
                    break
            p += alen
        return {'aug': aug, 'code_align': code_align, 'data_align': data_align,
                'ra': ra, 'fde_enc': fde_enc, 'instr': (p, end)}

    def find_fde(self, vaddr):
        i = bisect.bisect_right(self.fde_starts, vaddr) - 1
        if i < 0:
            return None
        f = self.fdes[i]
        if f[0] <= vaddr < f[1]:
            return f
        return None

    def row(self, vaddr):
        """CFA rule (reg, off) or None, rbp rule offset or None, ra offset."""
        r = self.rowcache.get(vaddr)
        if r is not None:
            return r
        f = self.find_fde(vaddr)
        if f is None:
            r = False
        else:
            r = self._exec(f, vaddr)
        self.rowcache[vaddr] = r
        return r

    def _exec(self, fde, target):
        cie = fde[2]
        ca, da = cie['code_align'], cie['data_align']
        state = {'cfa': (7, 8), 'regs': {}}
        init = None

        def run(p, end, loc, state, stop_at):
            d = self.data
            stack = []
            while p < end:
                op = d[p]; p += 1
                hi = op & 0xc0
                if hi == 0x40:
                    loc += (op & 0x3f) * ca
                    if stop_at is not None and loc > stop_at:
                        return state
                elif hi == 0x80:
                    off, p = uleb(d, p)
                    state['regs'][op & 0x3f] = ('off', off * da)
                elif hi == 0xc0:
                    reg = op & 0x3f
                    if init and reg in init['regs']:
                        state['regs'][reg] = init['regs'][reg]
                    else:
                        state['regs'].pop(reg, None)
                elif op == 0x00:
                    pass
                elif op == 0x01:
                    loc, p = self._read_enc(cie['fde_enc'], p, 0, 0)
                elif op in (0x02, 0x03, 0x04):
                    n = {0x02: 1, 0x03: 2, 0x04: 4}[op]
                    delta = int.from_bytes(d[p:p + n], 'little'); p += n
                    loc += delta * ca
                    if stop_at is not None and loc > stop_at:
                        return state
                elif op == 0x05:
                    reg, p = uleb(d, p); off, p = uleb(d, p)
                    state['regs'][reg] = ('off', off * da)
                elif op == 0x06:
                    reg, p = uleb(d, p)
                    if init and reg in init['regs']:
                        state['regs'][reg] = init['regs'][reg]
                    else:
                        state['regs'].pop(reg, None)
                elif op in (0x07, 0x08):
                    reg, p = uleb(d, p)
                    state['regs'].pop(reg, None)
                    if op == 0x07:
                        state['regs'][reg] = ('undef', 0)
                elif op == 0x09:
                    reg, p = uleb(d, p); reg2, p = uleb(d, p)
                    state['regs'][reg] = ('reg', reg2)
                elif op == 0x0a:
                    stack.append((state['cfa'], dict(state['regs'])))
                elif op == 0x0b:
                    if stack:
                        cfa, regs = stack.pop()
                        state['cfa'] = cfa
                        state['regs'] = regs
                elif op == 0x0c:
                    reg, p = uleb(d, p); off, p = uleb(d, p)
                    state['cfa'] = (reg, off)
                elif op == 0x0d:
                    reg, p = uleb(d, p)
                    state['cfa'] = (reg, state['cfa'][1] if state['cfa'] else 0)
                elif op == 0x0e:
                    off, p = uleb(d, p)
                    state['cfa'] = (state['cfa'][0] if state['cfa'] else 7, off)
                elif op == 0x0f:
                    n, p = uleb(d, p); p += n
                    state['cfa'] = ('expr', 0)
                elif op in (0x10, 0x16):
                    reg, p = uleb(d, p); n, p = uleb(d, p); p += n
                    state['regs'][reg] = ('expr', 0)
                elif op == 0x11:
                    reg, p = uleb(d, p); off, p = sleb(d, p)
                    state['regs'][reg] = ('off', off * da)
                elif op == 0x12:
                    reg, p = uleb(d, p); off, p = sleb(d, p)
                    state['cfa'] = (reg, off * da)
                elif op == 0x13:
                    off, p = sleb(d, p)
                    state['cfa'] = (state['cfa'][0], off * da)
                elif op in (0x14, 0x15):
                    reg, p = uleb(d, p)
                    if op == 0x14:
                        off, p = uleb(d, p)
                    else:
                        off, p = sleb(d, p)
                    state['regs'][reg] = ('val', off * da)
                elif op == 0x2e:
                    _, p = uleb(d, p)
                elif op == 0x2f:
                    reg, p = uleb(d, p); off, p = uleb(d, p)
                    state['regs'][reg] = ('off', -off * da)
                else:
                    raise ValueError(f'CFA op {op:#x} in {self.path}')
            return state

        s0 = run(cie['instr'][0], cie['instr'][1], fde[0], {'cfa': (7, 8), 'regs': {}}, None)
        init = {'cfa': s0['cfa'], 'regs': dict(s0['regs'])}
        s = run(fde[3], fde[4], fde[0], {'cfa': s0['cfa'], 'regs': dict(s0['regs'])}, target)
        return (s['cfa'], s['regs'].get(6), s['regs'].get(cie['ra'], ('off', -8)))


def uleb(d, p):
    r = s = 0
    while True:
        b = d[p]; p += 1
        r |= (b & 0x7f) << s; s += 7
        if b < 0x80:
            return r, p


def sleb(d, p):
    r = s = 0
    while True:
        b = d[p]; p += 1
        r |= (b & 0x7f) << s; s += 7
        if b < 0x80:
            if b & 0x40:
                r -= 1 << s
            return r, p

# ------------------------------------------------------------ perf.data ---

S_IP, S_TID, S_TIME, S_ADDR, S_READ, S_CALLCHAIN, S_ID, S_CPU, S_PERIOD, S_STREAM_ID, \
    S_RAW, S_BRANCH, S_REGS_USER, S_STACK_USER = [1 << i for i in range(14)]
S_IDENTIFIER = 1 << 16


def read_perf(path):
    with open(path, 'rb') as f:
        data = f.read()
    assert data[:8] == b'PERFILE2', 'not a perf.data file'
    (hsize, attr_size, a_off, a_size, d_off, d_size) = struct.unpack_from('<QQQQQQ', data, 8)
    attr = data[a_off: a_off + attr_size]
    sample_type = struct.unpack_from('<Q', attr, 24)[0]
    regs_mask = struct.unpack_from('<Q', attr, 80)[0]
    nregs = bin(regs_mask).count('1')
    reg_bits = [i for i in range(64) if regs_mask >> i & 1]
    unsupported = sample_type & (S_READ | S_RAW | S_BRANCH)
    assert not unsupported, f'sample_type {sample_type:#x} has unsupported fields'
    pos, end = d_off, d_off + d_size
    while pos + 8 <= end:
        (typ, misc, size) = struct.unpack_from('<IHH', data, pos)
        if size == 0:
            break
        body = pos + 8
        if typ in (1, 10):  # MMAP, MMAP2
            (pid, tid, addr, length, pgoff) = struct.unpack_from('<IIQQQ', data, body)
            q = body + 32
            if typ == 10:
                q += 24 + 8
            fname = data[q: data.index(b'\0', q)].decode('utf-8', 'replace')
            yield ('mmap', pid, addr, length, pgoff, fname)
        elif typ == 9:
            q = body
            if sample_type & S_IDENTIFIER:
                q += 8
            ip = None
            if sample_type & S_IP:
                ip = struct.unpack_from('<Q', data, q)[0]; q += 8
            pid = tid = 0
            if sample_type & S_TID:
                pid, tid = struct.unpack_from('<II', data, q); q += 8
            if sample_type & S_TIME:
                q += 8
            if sample_type & S_ADDR:
                q += 8
            if sample_type & S_ID:
                q += 8
            if sample_type & S_STREAM_ID:
                q += 8
            if sample_type & S_CPU:
                q += 8
            if sample_type & S_PERIOD:
                q += 8
            if sample_type & S_CALLCHAIN:
                nr = struct.unpack_from('<Q', data, q)[0]; q += 8 + 8 * nr
            regs = {}
            if sample_type & S_REGS_USER:
                abi = struct.unpack_from('<Q', data, q)[0]; q += 8
                if abi:
                    vals = struct.unpack_from(f'<{nregs}Q', data, q); q += 8 * nregs
                    regs = dict(zip(reg_bits, vals))
            stack, sp = b'', 0
            if sample_type & S_STACK_USER:
                ssize = struct.unpack_from('<Q', data, q)[0]; q += 8
                if ssize:
                    raw = data[q: q + ssize]; q += ssize
                    dyn = struct.unpack_from('<Q', data, q)[0]; q += 8
                    stack = raw[:dyn]
            yield ('sample', pid, tid, ip, regs, stack)
        pos += size

# ------------------------------------------------------------- unwind -----

PERF_BP, PERF_SP, PERF_IP = 6, 7, 8


class Maps:
    def __init__(self):
        self.by_pid = collections.defaultdict(list)
        self.elfs = {}

    def add(self, pid, addr, length, pgoff, fname):
        if not fname.startswith('/') or fname.startswith('/dev') or fname.startswith('/memfd'):
            return
        self.by_pid[pid].append((addr, addr + length, pgoff, fname))

    def lookup(self, pid, a):
        for (s, e, pgoff, fname) in reversed(self.by_pid.get(pid, ())):
            if s <= a < e:
                elf = self.elfs.get(fname)
                if elf is None:
                    try:
                        elf = Elf(fname)
                    except Exception as ex:  # not an ELF or unreadable
                        sys.stderr.write(f'cannot read {fname}: {ex}\n')
                        elf = False
                    self.elfs[fname] = elf
                if not elf:
                    return None, None
                return elf, elf.file_off_to_vaddr(a - s + pgoff)
        return None, None


def unwind(maps, pid, regs, stack, max_frames):
    sp0 = regs.get(PERF_SP, 0)
    rsp, rbp, rip = sp0, regs.get(PERF_BP, 0), regs.get(PERF_IP, 0)

    def rd(a):
        o = a - sp0
        if 0 <= o and o + 8 <= len(stack):
            return struct.unpack_from('<Q', stack, o)[0]
        return None

    frames = []
    first = True
    while len(frames) < max_frames:
        elf, va = maps.lookup(pid, rip if first else rip - 1)
        if elf is None:
            frames.append(f'[unknown {rip:#x}]')
            return frames, True
        name = elf.symbol(va) or f'[{os.path.basename(elf.path)}+{va:#x}]'
        frames.append(name)
        r = elf.row(va)
        if not r:
            return frames, True
        (cfa_reg, cfa_off), rbp_rule, ra_rule = r
        if cfa_reg == 7:
            cfa = rsp + cfa_off
        elif cfa_reg == 6:
            cfa = rbp + cfa_off
        else:
            return frames, True
        if ra_rule[0] == 'undef':
            return frames, False
        if ra_rule[0] != 'off':
            return frames, True
        ra = rd(cfa + ra_rule[1])
        if ra is None:
            return frames, True
        if rbp_rule and rbp_rule[0] == 'off':
            v = rd(cfa + rbp_rule[1])
            if v is None:
                return frames, True
            rbp = v
        rsp, rip = cfa, ra
        first = False
        if ra == 0:
            return frames, False
    return frames, True


def main():
    path, out = sys.argv[1], sys.argv[2]
    max_frames = 2000
    if '--max-frames' in sys.argv:
        max_frames = int(sys.argv[sys.argv.index('--max-frames') + 1])
    maps = Maps()
    raw = []
    nsamp = 0
    for rec in read_perf(path):
        if rec[0] == 'mmap':
            maps.add(*rec[1:])
        else:
            _, pid, tid, ip, regs, stack = rec
            nsamp += 1
            if not regs:
                raw.append((pid, 1, [f'[no-user-regs {ip:#x}]']))
                continue
            frames, trunc = unwind(maps, pid, regs, stack, max_frames)
            raw.append((pid, 1 if trunc else 0, frames))
    # demangle all distinct names in one c++filt call
    names = sorted({n for _, _, fr in raw for n in fr})
    dem = subprocess.run(['c++filt'], input='\n'.join(names) + '\n', capture_output=True,
                         text=True).stdout.split('\n')
    m = dict(zip(names, dem))
    with open(out, 'w') as f:
        for pid, trunc, fr in raw:
            f.write(f'{pid}\t{trunc}\t' + ';'.join(m.get(n, n).replace(';', ',') for n in fr) + '\n')
    sys.stderr.write(f'{nsamp} samples written to {out}\n')


main()
