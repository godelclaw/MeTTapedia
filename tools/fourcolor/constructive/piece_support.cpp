// Boundary support of a cubic piece.
//
// Input (stdin), one piece per file:
//   n m k
//   m lines "u v"            internal edges (0-based vertices, may repeat for
//                            parallel edges)
//   k integers              port vertices in cyclic boundary order
//   k integers (optional)   port signs +1/-1 for the flux sector
// Every vertex has internal degree + number of ports = 3.
//
// A boundary word gives each port a colour in {1,2,3}.  It is admissible when
// every colour count has the parity of k.  The program decides, for one
// representative of every colour-permutation orbit of admissible words,
// whether the word extends to a proper 3-edge-colouring of the piece, and
// reports the support size, the density against the admissible words, and
// the distribution of the flux vector f_c = sum_p sign(p) [word_p = c] over
// admissible words and over the support.  With --sector F1,F2,F3 only words
// whose flux is a permutation of (F1,F2,F3) are examined (bipartite pieces
// are confined to one sector, so this is exact for them).  With --dump FILE
// the supported orbit representatives are written one per line (digits 0-2).
//
// Usage: piece_support [--sector F1,F2,F3] [--dump FILE] < piece.txt

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <string>
#include <vector>

struct Piece {
  int n = 0, m = 0, k = 0;
  std::vector<int> eu, ev;             // internal edges
  std::vector<int> port;               // port vertex, in order
  std::vector<int> sign;               // port sign
  std::vector<std::vector<int>> incE;  // vertex -> internal edges
  std::vector<std::vector<int>> incP;  // vertex -> ports
};

static Piece P;
static std::vector<int> col;    // internal edge colours, 0 = unassigned
static std::vector<int> pcol;   // port colours
static std::vector<int> trail;

static int knownMask(int v) {
  int mask = 0;
  for (int e : P.incE[v]) if (col[e]) {
    if (mask & (1 << col[e])) return -1;
    mask |= 1 << col[e];
  }
  for (int p : P.incP[v]) {
    if (mask & (1 << pcol[p])) return -1;
    mask |= 1 << pcol[p];
  }
  return mask;
}

// propagate forced colours; returns false on conflict
static bool propagate(std::vector<int>& queue) {
  while (!queue.empty()) {
    int v = queue.back(); queue.pop_back();
    int mask = knownMask(v);
    if (mask < 0) return false;
    int known = __builtin_popcount(mask);
    if (known == 2) {
      int missing = 0;
      for (int c = 1; c <= 3; ++c) if (!(mask & (1 << c))) missing = c;
      for (int e : P.incE[v]) if (!col[e]) {
        col[e] = missing; trail.push_back(e);
        int w = P.eu[e] == v ? P.ev[e] : P.eu[e];
        queue.push_back(w);
        queue.push_back(v);
        break;
      }
    }
  }
  return true;
}

static bool dfs() {
  // choose an unassigned edge with the most constrained endpoint
  int best = -1, bestScore = -1;
  for (int e = 0; e < P.m; ++e) if (!col[e]) {
    int a = knownMask(P.eu[e]), b = knownMask(P.ev[e]);
    if (a < 0 || b < 0) return false;
    int score = __builtin_popcount(a) + __builtin_popcount(b);
    if (score > bestScore) { bestScore = score; best = e; }
  }
  if (best < 0) return true;
  int a = knownMask(P.eu[best]), b = knownMask(P.ev[best]);
  for (int c = 1; c <= 3; ++c) {
    if ((a | b) & (1 << c)) continue;
    size_t mark = trail.size();
    col[best] = c; trail.push_back(best);
    std::vector<int> q{P.eu[best], P.ev[best]};
    if (propagate(q) && dfs()) return true;
    while (trail.size() > mark) { col[trail.back()] = 0; trail.pop_back(); }
  }
  return false;
}

static bool extends(const std::vector<int>& word) {
  pcol = word;
  std::fill(col.begin(), col.end(), 0);
  trail.clear();
  std::vector<int> q;
  for (int v = 0; v < P.n; ++v) {
    if (knownMask(v) < 0) return false;
    q.push_back(v);
  }
  if (!propagate(q)) return false;
  return dfs();
}

int main(int argc, char** argv) {
  const char* dumpPath = nullptr;
  std::vector<int> sector;  // optional flux multiset filter
  for (int a = 1; a < argc; ++a) {
    if (!std::strcmp(argv[a], "--dump") && a + 1 < argc) dumpPath = argv[++a];
    else if (!std::strcmp(argv[a], "--sector") && a + 1 < argc) {
      int x, y, z;
      if (std::sscanf(argv[++a], "%d,%d,%d", &x, &y, &z) == 3) sector = {x, y, z};
      std::sort(sector.begin(), sector.end());
    }
  }
  if (std::scanf("%d %d %d", &P.n, &P.m, &P.k) != 3) return 2;
  P.eu.resize(P.m); P.ev.resize(P.m);
  P.incE.assign(P.n, {}); P.incP.assign(P.n, {});
  for (int e = 0; e < P.m; ++e) {
    if (std::scanf("%d %d", &P.eu[e], &P.ev[e]) != 2) return 2;
    P.incE[P.eu[e]].push_back(e);
    if (P.ev[e] != P.eu[e]) P.incE[P.ev[e]].push_back(e);
  }
  P.port.resize(P.k);
  for (int i = 0; i < P.k; ++i) {
    if (std::scanf("%d", &P.port[i]) != 1) return 2;
    P.incP[P.port[i]].push_back(i);
  }
  P.sign.assign(P.k, 1);
  for (int i = 0; i < P.k; ++i) { int s; if (std::scanf("%d", &s) == 1) P.sign[i] = s; else break; }
  for (int v = 0; v < P.n; ++v)
    if (P.incE[v].size() + P.incP[v].size() != 3) {
      std::fprintf(stderr, "vertex %d has degree %zu\n", v, P.incE[v].size() + P.incP[v].size());
      return 2;
    }
  col.assign(P.m, 0);
  const int k = P.k;
  // restricted-growth representatives of colour-permutation orbits
  std::vector<int> w(k, 1);
  long long adm = 0, supp = 0, reps = 0;
  std::map<std::vector<int>, std::pair<long long, long long>> flux;  // flux -> (adm, supp)
  FILE* dump = dumpPath ? std::fopen(dumpPath, "w") : nullptr;
  const int perms[6][3] = {{1, 2, 3}, {1, 3, 2}, {2, 1, 3}, {2, 3, 1}, {3, 1, 2}, {3, 2, 1}};
  // enumerate RGS: w[0] = 1, w[i] <= 1 + max(w[0..i-1]), values <= 3
  std::vector<int> mx(k, 1);
  while (true) {
    int cnt[4] = {0, 0, 0, 0};
    for (int i = 0; i < k; ++i) cnt[w[i]]++;
    bool inSector = true;
    if (!sector.empty()) {
      std::vector<int> f(3, 0);
      for (int i = 0; i < k; ++i) f[w[i] - 1] += P.sign[i];
      std::sort(f.begin(), f.end());
      inSector = (f == sector);
    }
    if (inSector && cnt[1] % 2 == k % 2 && cnt[2] % 2 == k % 2 && cnt[3] % 2 == k % 2) {
      ++reps;
      bool ok = extends(w);
      int used = (cnt[1] > 0) + (cnt[2] > 0) + (cnt[3] > 0);
      int orbit = used == 1 ? 3 : 6;
      adm += orbit;
      if (ok) supp += orbit;
      // flux over the orbit (distinct images)
      std::map<std::vector<int>, int> seen;
      for (auto& p : perms) {
        std::vector<int> img(k);
        for (int i = 0; i < k; ++i) img[i] = p[w[i] - 1];
        if (seen.count(img)) continue;
        seen[img] = 1;
        std::vector<int> f(3, 0);
        for (int i = 0; i < k; ++i) f[img[i] - 1] += P.sign[i];
        auto& fl = flux[f];
        fl.first++;
        if (ok) fl.second++;
      }
      if (dump && ok) {
        for (int i = 0; i < k; ++i) std::fputc('0' + w[i] - 1, dump);
        std::fputc('\n', dump);
      }
    }
    // next RGS
    int i = k - 1;
    while (i >= 1) {
      int limit = std::min(3, mx[i - 1] + 1);
      if (w[i] < limit) break;
      --i;
    }
    if (i < 1) break;
    w[i]++;
    mx[i] = std::max(mx[i - 1], w[i]);
    for (int j = i + 1; j < k; ++j) { w[j] = 1; mx[j] = mx[j - 1]; }
  }
  if (dump) std::fclose(dump);
  std::printf("n=%d m=%d k=%d admissible=%lld support=%lld density=%.4f reps=%lld\n",
              P.n, P.m, k, adm, supp, adm ? double(supp) / adm : 0.0, reps);
  std::printf("flux sectors (f1,f2,f3): support/admissible\n");
  for (auto& kv : flux) {
    std::printf("  (%d,%d,%d): %lld/%lld%s\n", kv.first[0], kv.first[1], kv.first[2],
                kv.second.second, kv.second.first,
                kv.second.second == kv.second.first ? " full" : (kv.second.second ? "" : " empty"));
  }
  return 0;
}
