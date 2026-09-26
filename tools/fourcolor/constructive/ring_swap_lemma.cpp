// Exhaustive checks of the two-ring lemmas for the zigzag tube ring.
//
// For every admissible word x:
//  * pure shift: shift(x) is reachable in exactly two rings, where
//    shift(z)_i = z_{i+1} (a ring followed by its complementary ring);
//  * swap: for every cyclic position j with x_j != x_{j+1}, shift(swap_j(x))
//    is reachable in exactly two rings.  The swap lemma is proved for words
//    using all three colours; words using two colours are reported
//    separately (the swap fails for all of them).
// Ring relation as in ring_sectors.cpp.
//
// Usage: ring_swap_lemma KMIN KMAX

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static int K;

static void decode(int64_t code, int* w) {
  for (int i = 0; i < K; ++i) { w[i] = int(code % 3) + 1; code /= 3; }
}
static int64_t encode(const int* w) {
  int64_t c = 0;
  for (int i = K - 1; i >= 0; --i) c = c * 3 + (w[i] - 1);
  return c;
}

static void successors(const int* x, std::vector<int64_t>& out) {
  out.clear();
  int a[32], y[32], choice[32];
  int depth = 0;
  choice[0] = 0;
  while (depth >= 0) {
    if (choice[depth] >= 3) { --depth; if (depth >= 0) ++choice[depth]; continue; }
    int cand = choice[depth] + 1;
    if (cand == x[depth]) { ++choice[depth]; continue; }
    a[depth] = cand;
    if (depth > 0) {
      int yy = a[depth - 1] ^ x[depth] ^ a[depth];
      if (yy == 0) { ++choice[depth]; continue; }
      y[depth - 1] = yy;
    }
    if (depth == K - 1) {
      int yy = a[K - 1] ^ x[0] ^ a[0];
      if (yy != 0) { y[K - 1] = yy; out.push_back(encode(y)); }
      ++choice[depth];
      continue;
    }
    ++depth;
    choice[depth] = 0;
  }
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
}

int main(int argc, char** argv) {
  int kmin = argc > 1 ? atoi(argv[1]) : 5, kmax = argc > 2 ? atoi(argv[2]) : 12;
  for (K = kmin; K <= kmax; ++K) {
    int64_t total = 1;
    for (int i = 0; i < K; ++i) total *= 3;
    std::vector<int> index(total, -1);
    std::vector<int64_t> words;
    int w[32];
    for (int64_t c = 0; c < total; ++c) {
      decode(c, w);
      int cnt[4] = {0, 0, 0, 0};
      for (int i = 0; i < K; ++i) cnt[w[i]]++;
      if (cnt[1] % 2 == K % 2 && cnt[2] % 2 == K % 2 && cnt[3] % 2 == K % 2) {
        index[c] = (int)words.size(); words.push_back(c);
      }
    }
    const int n = (int)words.size();
    std::vector<std::vector<int>> succ(n);
    std::vector<int64_t> tmp;
    for (int u = 0; u < n; ++u) {
      decode(words[u], w);
      successors(w, tmp);
      for (int64_t s : tmp) succ[u].push_back(index[s]);
    }
    long long tests3 = 0, fails3 = 0, tests2 = 0, fails2 = 0, shiftFails = 0;
    std::vector<int> mark(n, -1);
    int stamp = 0;
    int firstFail = -1, firstJ = -1;
    for (int u = 0; u < n; ++u) {
      ++stamp;
      for (int v : succ[u]) for (int z : succ[v]) mark[z] = stamp;
      decode(words[u], w);
      int cnt[4] = {0, 0, 0, 0};
      for (int i = 0; i < K; ++i) cnt[w[i]]++;
      bool three = cnt[1] && cnt[2] && cnt[3];
      {
        int t[32];
        for (int i = 0; i < K; ++i) t[i] = w[(i + 1) % K];
        if (mark[index[encode(t)]] != stamp) ++shiftFails;
      }
      for (int j = 0; j < K; ++j) {
        int j1 = (j + 1) % K;
        if (w[j] == w[j1]) continue;
        int z[32];
        for (int i = 0; i < K; ++i) z[i] = w[i];
        std::swap(z[j], z[j1]);
        int t[32];
        for (int i = 0; i < K; ++i) t[i] = z[(i + 1) % K];
        bool ok = mark[index[encode(t)]] == stamp;
        if (three) { ++tests3; if (!ok) { ++fails3; if (firstFail < 0) { firstFail = u; firstJ = j; } } }
        else { ++tests2; if (!ok) ++fails2; }
      }
    }
    std::printf("k=%d words=%d pure-shift failures: %lld; three-colour swaps: %lld failures / %lld; two-colour swaps: %lld / %lld",
                K, n, shiftFails, fails3, tests3, fails2, tests2);
    if (firstFail >= 0) {
      decode(words[firstFail], w);
      std::printf("; first failure x=");
      for (int i = 0; i < K; ++i) std::printf("%d", w[i]);
      std::printf(" j=%d", firstJ);
    }
    std::printf("\n");
    std::fflush(stdout);
  }
  return 0;
}
