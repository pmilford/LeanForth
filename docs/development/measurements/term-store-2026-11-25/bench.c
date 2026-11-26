/* Term-store micro-benchmarks in C (docs/design/TERM_STORE.md, 2026-11-25):
   the same layout and operations as bench.fs (chase, cons, inst), as a
   reference point. Build: cc -O2 -o bench bench.c */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct { uint32_t tag, a, b, data; } node_t;
static node_t *nodes; static uint32_t ncount, nmask;
static uint32_t *tbl; static uint32_t tmask;   /* slot i: tbl[2i] hash, tbl[2i+1] index + 1 */
static uint64_t acc;

static double now_ms(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e3 + t.tv_nsec / 1e6; }
static uint64_t lcg(uint64_t x) { return (x * 1103515245u + 12345u) & 0xFFFFFFFFu; }
static void store_new(uint32_t n) { nodes = malloc(sizeof(node_t) * n); ncount = 0; }
static uint32_t put(uint32_t t, uint32_t a, uint32_t b, uint32_t d) {
  node_t *p = &nodes[ncount]; p->tag = t; p->a = a; p->b = b; p->data = d; return ncount++; }
static void table_new(int lg) { tmask = (1u << lg) - 1; tbl = calloc(2u << lg, 4); }
static uint32_t fmix(uint32_t h) { h ^= h >> 16; h *= 0x85EBCA6Bu; h ^= h >> 13; h *= 0xC2B2AE35u; h ^= h >> 16; return h; }
static uint32_t hash3(uint32_t t, uint32_t a, uint32_t b) { return fmix(((t * 0x9E3779B1u) ^ a) * 0x85EBCA6Bu ^ b); }
static uint32_t loose(uint32_t d) { return d & 0xFFFFF; }
static uint32_t cons(uint32_t t, uint32_t a, uint32_t b) {
  uint32_t h = hash3(t, a, b), i = h & tmask, v;
  while ((v = tbl[2 * i + 1])) {
    if (tbl[2 * i] == h) { node_t *p = &nodes[v - 1]; if (p->tag == t && p->a == a && p->b == b) return v - 1; }
    i = (i + 1) & tmask; }
  uint32_t d = t == 3 ? (loose(nodes[a].data) > loose(nodes[b].data) ? loose(nodes[a].data) : loose(nodes[b].data))
             : t == 2 ? a + 1 : 0;
  uint32_t r = put(t, a, b, d); tbl[2 * i] = h; tbl[2 * i + 1] = r + 1; return r; }

static void dag(uint32_t n) {
  store_new(2 * n); nmask = n - 1; uint64_t x = 1;
  for (uint32_t i = 0; i < n; i++) { x = lcg(x);
    if (i < 8 || (x & 7) == 0) put(2, i & 3, 0, (i & 3) + 1);
    else put(3, (x >> 8) % i, (x >> 3) % i, 0); } }
static void chase(int lg) {
  dag(1u << lg); uint64_t x = 1; uint32_t r = 0; double t0 = now_ms();
  for (uint32_t s = 0; s < (1u << 24); s++) {
    node_t *p = &nodes[r];
    if (p->tag == 3) { acc += p->data; x = lcg(x); r = (x & 1) ? p->a : p->b; }
    else { x = lcg(x); r = (x >> 4) & nmask; } }
  printf("  C %.3f ms  sum %llu\n", now_ms() - t0, (unsigned long long)acc); free(nodes); acc = 0; }
static void cons_bench(void) {
  store_new((1u << 23) + 2048); table_new(23);
  for (uint32_t i = 0; i < 2048; i++) cons(2, i, 0);
  uint64_t x = 1; double t0 = now_ms();
  for (uint32_t s = 0; s < (1u << 22); s++) { x = lcg(x); cons(3, (x >> 8) % 2048, (x >> 19) % 2048); }
  printf("  C %.3f ms  made %u\n", now_ms() - t0, ncount); free(nodes); free(tbl); }
static uint32_t csub, visits;
static uint32_t inst(uint32_t r) {
  visits++; node_t *p = &nodes[r];
  if (loose(p->data) == 0) return r;
  if (p->tag == 2) return csub;
  uint32_t a = inst(p->a); uint32_t b = inst(nodes[r].b); return cons(3, a, b); }
static uint32_t tree(uint64_t *x, int d) {
  if (d == 0) { *x = lcg(*x); return ((*x >> 24) & 3) ? cons(1, 0, 0) : cons(2, 0, 0); }
  uint32_t a = tree(x, d - 1); uint32_t b = tree(x, d - 1); return cons(3, a, b); }
static void inst_bench(void) {
  store_new(1u << 23); table_new(23); csub = cons(1, 0, 0); uint64_t x = 1;
  uint32_t root = tree(&x, 18); visits = 0; double t0 = now_ms(); inst(root);
  printf("  C recursive %.3f ms  visits %u  nodes %u\n", now_ms() - t0, visits, ncount); }
int main(void) {
  printf("chase 2^12 nodes, 2^24 steps:\n"); chase(12);
  printf("chase 2^22 nodes, 2^24 steps:\n"); chase(22);
  printf("cons 2^22 app(a,b), a,b < 2048:\n"); cons_bench();
  printf("inst depth-18 tree:\n"); inst_bench(); return 0; }
