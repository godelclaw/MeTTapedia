// Exact checks of the split/merge width-change rule on word sets.
//
// Colours 1,2,3 (xor = third colour).  A_k: nonzero words of length k with
// xor-sum 0 (parity-admissible).  I_k = A_k for odd k, A_k minus the three
// constant words for even k.
//   merge at (0,1): x with x0 != x1  ->  (x0^x1, x2, ..., x_{k-1})
//   split at 0:     x -> (a, b, x1, ..., x_{k-1}), {a,b} = colours != x0
//   ring:           zigzag ring relation (as in ring_sectors.cpp)
// For each k: merge(I_k) == A_{k-1}?; from S = I_k, split then r rings:
// the least r with the result containing I_{k+1}, whether it stays so for
// the next 12 rings, and whether the result then equals I_{k+1}.
// Usage: split_merge_check KMIN KMAX

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static int64_t P3[20];

static void decode(int K, int64_t c, int* w) { for (int i = 0; i < K; ++i) { w[i] = int(c % 3) + 1; c /= 3; } }
static int64_t encode(int K, const int* w) { int64_t c = 0; for (int i = K - 1; i >= 0; --i) c = c * 3 + (w[i] - 1); return c; }

struct Set {
  int K; std::vector<uint64_t> b;
  explicit Set(int K_) : K(K_), b((P3[K_] + 63) / 64, 0) {}
  void add(int64_t c) { b[c >> 6] |= 1ULL << (c & 63); }
  bool has(int64_t c) const { return (b[c >> 6] >> (c & 63)) & 1; }
  long long count() const { long long n = 0; for (auto x : b) n += __builtin_popcountll(x); return n; }
  bool contains(const Set& o) const { for (size_t i = 0; i < b.size(); ++i) if (o.b[i] & ~b[i]) return false; return true; }
  bool equals(const Set& o) const { return b == o.b; }
};

static Set admissible(int K, bool dropConstant) {
  Set s(K); int w[20];
  for (int64_t c = 0; c < P3[K]; ++c) {
    decode(K, c, w);
    int x = 0; for (int i = 0; i < K; ++i) x ^= w[i];
    if (x) continue;
    if (dropConstant) { bool cst = true; for (int i = 1; i < K; ++i) if (w[i] != w[0]) cst = false; if (cst) continue; }
    s.add(c);
  }
  return s;
}

static void ringSuccessors(int K, const int* x, Set& out) {
  int a[20], y[20], choice[20];
  int depth = 0; choice[0] = 0;
  while (depth >= 0) {
    if (choice[depth] >= 3) { --depth; if (depth >= 0) ++choice[depth]; continue; }
    int cand = choice[depth] + 1;
    if (cand == x[depth]) { ++choice[depth]; continue; }
    a[depth] = cand;
    if (depth > 0) { int yy = a[depth - 1] ^ x[depth] ^ a[depth]; if (!yy) { ++choice[depth]; continue; } y[depth - 1] = yy; }
    if (depth == K - 1) {
      int yy = a[K - 1] ^ x[0] ^ a[0];
      if (yy) { y[K - 1] = yy; out.add(encode(K, y)); }
      ++choice[depth]; continue;
    }
    ++depth; choice[depth] = 0;
  }
}

static Set ring(const Set& s) {
  Set out(s.K); int w[20];
  for (int64_t c = 0; c < P3[s.K]; ++c) if (s.has(c)) { decode(s.K, c, w); ringSuccessors(s.K, w, out); }
  return out;
}

static Set split0(const Set& s) {
  Set out(s.K + 1); int w[20], v[20];
  for (int64_t c = 0; c < P3[s.K]; ++c) if (s.has(c)) {
    decode(s.K, c, w);
    for (int a = 1; a <= 3; ++a) {
      if (a == w[0]) continue;
      int b = a ^ w[0];
      v[0] = a; v[1] = b;
      for (int i = 1; i < s.K; ++i) v[i + 1] = w[i];
      out.add(encode(s.K + 1, v));
    }
  }
  return out;
}

static Set merge01(const Set& s) {
  Set out(s.K - 1); int w[20], v[20];
  for (int64_t c = 0; c < P3[s.K]; ++c) if (s.has(c)) {
    decode(s.K, c, w);
    if (w[0] == w[1]) continue;
    v[0] = w[0] ^ w[1];
    for (int i = 2; i < s.K; ++i) v[i - 1] = w[i];
    out.add(encode(s.K - 1, v));
  }
  return out;
}

int main(int argc, char** argv) {
  int kmin = argc > 1 ? atoi(argv[1]) : 3, kmax = argc > 2 ? atoi(argv[2]) : 10;
  P3[0] = 1; for (int i = 1; i < 20; ++i) P3[i] = 3 * P3[i - 1];
  for (int k = kmin; k <= kmax; ++k) {
    Set I = admissible(k, k % 2 == 0), A = admissible(k, false);
    std::printf("k=%d |A_k|=%lld |I_k|=%lld", k, A.count(), I.count());
    if (k - 1 >= 3) {
      Set m = merge01(I), Am = admissible(k - 1, false);
      std::printf("  merge(I_k)==A_{k-1}: %s", m.equals(Am) ? "yes" : "NO");
    }
    Set In = admissible(k + 1, (k + 1) % 2 == 0);
    Set T = split0(I);
    int first = -1; bool stays = true; bool exact = false;
    for (int r = 0; r <= 60; ++r) {
      if (r > 0) T = ring(T);
      bool ok = T.contains(In);
      if (first < 0 && ok) { first = r; exact = T.equals(In); }
      else if (first >= 0) { if (!ok) stays = false; if (r >= first + 12) break; }
    }
    std::printf("  split then rings: first r with >= I_{k+1}: %d, stays for 12 more: %s, equals I_{k+1} there: %s\n",
                first, first >= 0 ? (stays ? "yes" : "NO") : "-", exact ? "yes" : "no");
    std::fflush(stdout);
  }
  return 0;
}
