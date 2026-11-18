#!/usr/bin/env python3
"""PERF1 sampling profiler for gforth-fast (no perf on this machine).

Runs a command as a child, seizes it with ptrace, and every INTERVAL seconds
interrupts it, reads its registers and its Forth return stack, and maps each
return address (a threaded-code address whose preceding cell is a colon
definition's start: a `call`) to the colon definition holding it, using the
symbol table that symdump.fs writes from inside the same process.

usage: sample.py OUT.prof INTERVAL -- CMD ARGS...
  env PROF_SYMS must be set (the child writes it after loading).
Writes OUT.prof: one line per sample, words innermost first, ';'-separated.
"""
import ctypes, os, sys, time, bisect, signal

libc = ctypes.CDLL(None, use_errno=True)
libc.ptrace.restype = ctypes.c_long
libc.ptrace.argtypes = [ctypes.c_long, ctypes.c_long, ctypes.c_void_p, ctypes.c_void_p]
PTRACE_CONT, PTRACE_GETREGS, PTRACE_DETACH = 7, 12, 17
PTRACE_SEIZE, PTRACE_INTERRUPT = 0x4206, 0x4207
REGS = ("r15 r14 r13 r12 rbp rbx r11 r10 r9 r8 rax rcx rdx rsi rdi orig_rax rip cs "
        "eflags rsp ss fs_base gs_base ds es fs gs").split()

class Regs(ctypes.Structure):
    _fields_ = [(n, ctypes.c_ulong) for n in REGS]

def main():
    out, interval = sys.argv[1], float(sys.argv[2])
    cmd = sys.argv[sys.argv.index('--') + 1:]
    symf = os.environ['PROF_SYMS']
    if os.path.exists(symf):
        os.unlink(symf)
    pid = os.fork()
    if pid == 0:
        fd = os.open('/dev/null', os.O_RDONLY); os.dup2(fd, 0)
        os.execvp(cmd[0], cmd)
    if libc.ptrace(PTRACE_SEIZE, pid, None, None) != 0:
        print('seize failed', ctypes.get_errno(), file=sys.stderr); return 1
    # wait for the symbol table (written after loading main.fs)
    starts, names, rp0 = None, None, None
    mem = None
    samples = {}
    rpreg = None
    libc_rng = None
    status = 0
    t_start = time.time()
    nsamp = 0
    while True:
        time.sleep(interval)
        try:
            wp, st = os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            break
        if wp == pid:
            if os.WIFEXITED(st) or os.WIFSIGNALED(st):
                status = st; break
            if os.WIFSTOPPED(st):  # a signal stop: pass it on
                sig = os.WSTOPSIG(st)
                libc.ptrace(PTRACE_CONT, pid, None, ctypes.c_void_p(sig if (st >> 16) == 0 else 0))
                continue
        if starts is None:
            if not os.path.exists(symf):
                continue
            txt = open(symf).read()
            if 'SP0 ' not in txt:
                continue
            ents = []
            for line in txt.splitlines():
                p = line.split(' ', 2)
                if p[0] == 'RP0': rp0 = int(p[1], 16); continue
                if p[0] == 'SP0': continue
                if len(p) == 3 and p[1] == 'c':
                    ents.append((int(p[0], 16), p[2]))
            ents.sort()
            starts = [e[0] for e in ents]; names = [e[1] for e in ents]
            startset = set(starts)
            lo, hi = starts[0], starts[-1] + 65536
            hi2 = hi + (64 << 20)
            mem = os.open('/proc/%d/mem' % pid, os.O_RDONLY)
            print('symbols', len(starts), 'rp0 %x' % rp0, file=sys.stderr)
        if libc.ptrace(PTRACE_INTERRUPT, pid, None, None) != 0:
            continue
        wp, st = os.waitpid(pid, 0)
        if os.WIFEXITED(st) or os.WIFSIGNALED(st):
            status = st; break
        regs = Regs()
        libc.ptrace(PTRACE_GETREGS, pid, None, ctypes.byref(regs))
        if libc_rng is None:
            libc_rng = []
            tok = int.from_bytes(os.pread(mem, 8, starts[len(starts) // 2]), 'little')
            code_rng = (0, 0)
            for ml in open('/proc/%d/maps' % pid):
                f = ml.split()
                if len(f) >= 6 and ('libc.so' in f[5] or 'ld-linux' in f[5] or 'libm' in f[5]):
                    x, y = f[0].split('-'); libc_rng.append((int(x, 16), int(y, 16)))
                x, y = [int(v, 16) for v in f[0].split('-')]
                if x <= tok < y: code_rng = (x, y)
            print('native code region %x-%x' % code_rng, file=sys.stderr)
        ip, rp, rip = regs.rbx, regs.r14, regs.rip
        line = []
        if any(x <= rip < y for x, y in libc_rng):
            line.append('<libc>')
        if lo <= ip < hi:
            line.append(names[bisect.bisect_right(starts, ip) - 1])
        else:
            line.append('<ip?>')
        if rp0 - (1 << 16) < rp <= rp0:
            try:
                buf = os.pread(mem, rp0 - rp, rp)
            except OSError:
                buf = b''
            for i in range(0, len(buf) - 7, 8):
                a = int.from_bytes(buf[i:i + 8], 'little')
                if lo <= a < hi:
                    try:
                        prev = int.from_bytes(os.pread(mem, 8, a - 8), 'little')
                    except OSError:
                        continue
                    if prev in startset or code_rng[0] <= prev < code_rng[1]:
                        line.append(names[bisect.bisect_right(starts, a) - 1])
        else:
            line.append('<other-stack>')
        key = ';'.join(line); samples[key] = samples.get(key, 0) + 1
        nsamp += 1
        libc.ptrace(PTRACE_CONT, pid, None, None)
    with open(out, 'w') as f:
        f.write('# samples %d wall %.1f s interval %g\n' % (nsamp, time.time() - t_start, interval))
        for s, c in sorted(samples.items(), key=lambda x: -x[1]):
            f.write('%d\t%s\n' % (c, s))
    print('exit', os.WEXITSTATUS(status) if os.WIFEXITED(status) else -1, 'samples', nsamp, file=sys.stderr)

main()
