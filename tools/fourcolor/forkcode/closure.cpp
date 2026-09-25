// Closure of the finite fork code of the physical fork fold.
//
// This program mirrors the Lean definitions of
// Mettapedia/GraphTheory/FourColor/PhysicalForkCode.lean:
//   Code n    : two flags, colour support, face return, cut records;
//   Glue      : pairing of child positions and kept marks in parent order;
//   Legal     : the physical legality constraints;
//   Euler     : sharedCount + cyc retL + cyc retR = 2 + cyc (merged * pair);
//   fork      : the abstract fork;
//   leafCode  : the code of a single edge.
// States are stored as canonical representatives under renaming of
// positions (PhysicalForkCode.reach_relabel).  The fork is symmetric in its
// two children up to renaming of the parent, so each unordered pair of
// states is glued once, with every matching of their positions.
//
// Encoding.  A colour presentation on n positions is a base-3 word: at a
// position with one shore edge the digit is its colour, at a position with
// two shore edges it is the missing colour.  A cut record is
// bits + inside<<n + outside<<(n+1) + cost<<(n+2).
//
// Usage: closure BOUND [--prune-dead-bridge] [--time-limit SECONDS]
//                      [--progress SECONDS] [--dump FILE]
// Output: one JSON object on stdout; progress lines on stderr.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <unordered_map>
#include <vector>
#include <thread>
#include <mutex>
#include <atomic>

static constexpr int MAXN = 6;
static constexpr int COLW = 12;  // 729 colour presentations need 12 words
static constexpr int CUTW = 8;   // 512 cut records need 8 words

static int POW3[MAXN + 2];

struct Code {
  uint8_t n = 0;
  uint8_t two = 0;
  uint8_t ret[MAXN] = {0};
  uint64_t col[COLW] = {0};
  uint64_t cut[CUTW] = {0};
};

static inline bool bget(const uint64_t* b, int i) { return (b[i >> 6] >> (i & 63)) & 1ULL; }
static inline void bset(uint64_t* b, int i) { b[i >> 6] |= 1ULL << (i & 63); }
static inline int colDigit(int idx, int i) { return (idx / POW3[i]) % 3; }

static bool codeEq(const Code& a, const Code& b) { return std::memcmp(&a, &b, sizeof(Code)) == 0; }
static bool codeLess(const Code& a, const Code& b) { return std::memcmp(&a, &b, sizeof(Code)) < 0; }

static uint64_t codeHash(const Code& c) {
  const unsigned char* p = reinterpret_cast<const unsigned char*>(&c);
  uint64_t h = 1469598103934665603ULL;
  for (size_t i = 0; i < sizeof(Code); ++i) { h ^= p[i]; h *= 1099511628211ULL; }
  return h ^ (h >> 29);
}

// ---------------------------------------------------------------- renaming

struct PermTable {
  std::vector<std::array<uint8_t, MAXN>> perms;  // perms[s][i] = sigma(i)
  std::vector<std::vector<uint16_t>> colMap;     // old presentation -> new
  std::vector<std::vector<uint16_t>> bitMap;     // old bits -> new bits
};
static PermTable PT[MAXN + 1];

static void buildPermTables() {
  for (int n = 0; n <= MAXN; ++n) {
    std::array<uint8_t, MAXN> p{};
    for (int i = 0; i < n; ++i) p[i] = (uint8_t)i;
    do {
      PT[n].perms.push_back(p);
      std::vector<uint16_t> cm(POW3[n]);
      for (int idx = 0; idx < POW3[n]; ++idx) {
        int ni = 0;
        for (int i = 0; i < n; ++i) ni += colDigit(idx, p[i]) * POW3[i];
        cm[idx] = (uint16_t)ni;
      }
      PT[n].colMap.push_back(std::move(cm));
      std::vector<uint16_t> bm(1 << n);
      for (int b = 0; b < (1 << n); ++b) {
        int nb = 0;
        for (int i = 0; i < n; ++i) if ((b >> p[i]) & 1) nb |= 1 << i;
        bm[b] = (uint16_t)nb;
      }
      PT[n].bitMap.push_back(std::move(bm));
    } while (std::next_permutation(p.begin(), p.begin() + n));
  }
}

// Code.relabel sigma: position i of the result reads position sigma(i).
static Code relabel(const Code& c, int s) {
  const int n = c.n;
  const auto& p = PT[n].perms[s];
  Code r;
  r.n = c.n;
  uint8_t inv[MAXN] = {0};
  for (int i = 0; i < n; ++i) inv[p[i]] = (uint8_t)i;
  for (int i = 0; i < n; ++i) {
    if ((c.two >> p[i]) & 1) r.two |= (uint8_t)(1 << i);
    r.ret[i] = inv[c.ret[p[i]]];
  }
  const auto& cm = PT[n].colMap[s];
  for (int w = 0; w < COLW; ++w) {
    uint64_t x = c.col[w];
    while (x) { int b = __builtin_ctzll(x); x &= x - 1; bset(r.col, cm[w * 64 + b]); }
  }
  const auto& bm = PT[n].bitMap[s];
  const int mask = (1 << n) - 1;
  for (int w = 0; w < CUTW; ++w) {
    uint64_t x = c.cut[w];
    while (x) {
      int b = __builtin_ctzll(x); x &= x - 1;
      int idx = w * 64 + b;
      bset(r.cut, bm[idx & mask] | ((idx >> n) << n));
    }
  }
  return r;
}

// Minimal encoding over the renamings that sort a renaming-invariant
// signature of the positions.  Isomorphic codes get equal canonical forms.
static Code canonical(const Code& c) {
  const int n = c.n;
  if (n == 0) return c;
  std::array<std::array<int, 8>, MAXN> sig{};
  for (int i = 0; i < n; ++i) {
    int len = 1, y = c.ret[i];
    while (y != i) { y = c.ret[y]; ++len; }
    sig[i][0] = ((c.two >> i) & 1) * 16 + len;
  }
  for (int w = 0; w < COLW; ++w) {
    uint64_t x = c.col[w];
    while (x) {
      int b = __builtin_ctzll(x); x &= x - 1;
      int idx = w * 64 + b;
      for (int i = 0; i < n; ++i) sig[i][1 + colDigit(idx, i)]++;
    }
  }
  const int mask = (1 << n) - 1;
  for (int w = 0; w < CUTW; ++w) {
    uint64_t x = c.cut[w];
    while (x) {
      int b = __builtin_ctzll(x); x &= x - 1;
      int idx = w * 64 + b;
      int bits = idx & mask, flags = idx >> n;
      for (int i = 0; i < n; ++i) if ((bits >> i) & 1) sig[i][4 + (flags & 3)]++;
    }
  }
  bool have = false;
  Code best;
  const int np = (int)PT[n].perms.size();
  for (int s = 0; s < np; ++s) {
    const auto& p = PT[n].perms[s];
    bool ok = true;
    for (int i = 0; i + 1 < n && ok; ++i) if (sig[p[i]] > sig[p[i + 1]]) ok = false;
    if (!ok) continue;
    Code r = relabel(c, s);
    if (!have || codeLess(r, best)) { best = r; have = true; }
  }
  return best;
}

// ---------------------------------------------------------------- the fork

struct Stats {
  uint64_t pairs = 0, matchings = 0, widthRejected = 0, eulerRejected = 0, forks = 0,
           deadBridgePruned = 0;
};

static int cycCount(const int* p, int m) {
  bool seen[2 * MAXN] = {false};
  int c = 0;
  for (int i = 0; i < m; ++i) {
    if (seen[i]) continue;
    ++c;
    int y = i;
    while (!seen[y]) { seen[y] = true; y = p[y]; }
  }
  return c;
}

// OR the first `len` bits of src into dst at bit offset `off`.
static void orBits(uint64_t* dst, int dstWords, const uint64_t* src, int len, int off) {
  for (int s = 0; s < len; s += 64) {
    uint64_t chunk = src[s >> 6];
    int rem = len - s;
    if (rem < 64) chunk &= (1ULL << rem) - 1;
    if (!chunk) continue;
    int pos = off + s;
    int w = pos >> 6, sh = pos & 63;
    dst[w] |= chunk << sh;
    if (sh && w + 1 < dstWords) dst[w + 1] |= chunk >> (64 - sh);
  }
}

struct Matching {
  int k = 0;
  int li[MAXN], rj[MAXN];
};

// All parent codes of one matching (one per orientation of the open pairs).
template <class Emit>
static void emitMatching(const Code& L, const Code& R, const Matching& M, int bound,
                         int cycL, int cycR, Stats& st, Emit&& emit) {
  const int nL = L.n, nR = R.n, k = M.k;
  bool shL[MAXN] = {false}, shR[MAXN] = {false};
  int openIdx[MAXN];
  int nOpen = 0;
  for (int t = 0; t < k; ++t) {
    shL[M.li[t]] = true; shR[M.rj[t]] = true;
    bool open = !((L.two >> M.li[t]) & 1) && !((R.two >> M.rj[t]) & 1);
    openIdx[t] = open ? nOpen++ : -1;
  }
  const int uL = nL - k, uR = nR - k, nP = uL + uR + nOpen;
  st.matchings++;
  if (nP > bound) { st.widthRejected++; return; }
  int leftU[MAXN], rightU[MAXN];
  { int a = 0; for (int i = 0; i < nL; ++i) if (!shL[i]) leftU[a++] = i; }
  { int a = 0; for (int j = 0; j < nR; ++j) if (!shR[j]) rightU[a++] = j; }

  // Euler guard (independent of the orientation choice)
  const int m = nL + nR;
  int pairPerm[2 * MAXN], merged[2 * MAXN], p[2 * MAXN];
  for (int x = 0; x < m; ++x) pairPerm[x] = x;
  for (int t = 0; t < k; ++t) { pairPerm[M.li[t]] = nL + M.rj[t]; pairPerm[nL + M.rj[t]] = M.li[t]; }
  for (int i = 0; i < nL; ++i) merged[i] = L.ret[i];
  for (int j = 0; j < nR; ++j) merged[nL + j] = nL + R.ret[j];
  for (int x = 0; x < m; ++x) p[x] = merged[pairPerm[x]];
  if (k + cycL + cycR != 2 + cycCount(p, m)) { st.eulerRejected++; return; }

  Code P;
  P.n = (uint8_t)nP;
  // two
  for (int u = 0; u < uL; ++u) if ((L.two >> leftU[u]) & 1) P.two |= (uint8_t)(1 << u);
  for (int u = 0; u < uR; ++u) if ((R.two >> rightU[u]) & 1) P.two |= (uint8_t)(1 << (uL + u));
  for (int o = 0; o < nOpen; ++o) P.two |= (uint8_t)(1 << (uL + uR + o));

  // colour: group left presentations by their shared digits
  const int nKeys = POW3[k];
  thread_local std::vector<std::array<uint64_t, COLW>> gL;
  thread_local std::vector<char> hasL;
  thread_local std::vector<std::vector<int>> gR;
  if ((int)gL.size() < nKeys) { gL.resize(nKeys); hasL.resize(nKeys); gR.resize(nKeys); }
  for (int q = 0; q < nKeys; ++q) { gL[q].fill(0); hasL[q] = 0; gR[q].clear(); }
  for (int w = 0; w < COLW; ++w) {
    uint64_t x = L.col[w];
    while (x) {
      int b = __builtin_ctzll(x); x &= x - 1;
      int idx = w * 64 + b;
      int key = 0, part = 0;
      for (int t = 0; t < k; ++t) key += colDigit(idx, M.li[t]) * POW3[t];
      for (int u = 0; u < uL; ++u) part += colDigit(idx, leftU[u]) * POW3[u];
      bset(gL[key].data(), part);
      hasL[key] = 1;
    }
  }
  for (int w = 0; w < COLW; ++w) {
    uint64_t x = R.col[w];
    while (x) {
      int b = __builtin_ctzll(x); x &= x - 1;
      int idx = w * 64 + b;
      int key = 0, part = 0;
      for (int t = 0; t < k; ++t) key += colDigit(idx, M.rj[t]) * POW3[t];
      for (int u = 0; u < uR; ++u) part += colDigit(idx, rightU[u]) * POW3[u];
      gR[key].push_back(part);
    }
  }
  for (int kl = 0; kl < nKeys; ++kl) {
    if (!hasL[kl]) continue;
    for (int kr = 0; kr < nKeys; ++kr) {
      if (gR[kr].empty()) continue;
      bool ok = true;
      int openPart = 0;
      for (int t = 0; t < k && ok; ++t) {
        int xl = (kl / POW3[t]) % 3, xr = (kr / POW3[t]) % 3;
        bool tl = (L.two >> M.li[t]) & 1, tr = (R.two >> M.rj[t]) & 1;
        if (tl && !tr) ok = (xr == xl);            // {0,1,2}\{xl} and {xr} disjoint
        else if (!tl && tr) ok = (xl == xr);       // {xl} and {0,1,2}\{xr} disjoint
        else {                                     // two single colours
          ok = (xl != xr);
          if (ok) openPart += (3 - xl - xr) * POW3[openIdx[t]];
        }
      }
      if (!ok) continue;
      for (int part : gR[kr]) {
        int off = POW3[uL] * (part + POW3[uR] * openPart);
        orBits(P.col, COLW, gL[kl].data(), POW3[uL], off);
      }
    }
  }

  // cut records: group by shared bits and cost
  const int nb = 1 << k;
  thread_local std::vector<std::vector<int>> cL, cR;
  if ((int)cL.size() < 2 * nb) { cL.resize(2 * nb); cR.resize(2 * nb); }
  for (int q = 0; q < 2 * nb; ++q) { cL[q].clear(); cR[q].clear(); }
  const int maskL = (1 << nL) - 1, maskR = (1 << nR) - 1;
  for (int w = 0; w < CUTW; ++w) {
    uint64_t x = L.cut[w];
    while (x) {
      int b = __builtin_ctzll(x); x &= x - 1;
      int idx = w * 64 + b;
      int bits = idx & maskL, fl = idx >> nL;
      int key = 0, ub = 0;
      for (int t = 0; t < k; ++t) key |= ((bits >> M.li[t]) & 1) << t;
      for (int u = 0; u < uL; ++u) ub |= ((bits >> leftU[u]) & 1) << u;
      cL[key * 2 + ((fl >> 2) & 1)].push_back(ub | ((fl & 3) << 8));
    }
  }
  for (int w = 0; w < CUTW; ++w) {
    uint64_t x = R.cut[w];
    while (x) {
      int b = __builtin_ctzll(x); x &= x - 1;
      int idx = w * 64 + b;
      int bits = idx & maskR, fl = idx >> nR;
      int key = 0, ub = 0;
      for (int t = 0; t < k; ++t) key |= ((bits >> M.rj[t]) & 1) << t;
      for (int u = 0; u < uR; ++u) ub |= ((bits >> rightU[u]) & 1) << u;
      cR[key * 2 + ((fl >> 2) & 1)].push_back(ub | ((fl & 3) << 8));
    }
  }
  for (int key = 0; key < nb; ++key) {
    int openBits = 0;
    for (int t = 0; t < k; ++t) if (openIdx[t] >= 0 && ((key >> t) & 1)) openBits |= 1 << openIdx[t];
    for (int cl = 0; cl < 2; ++cl) for (int cr = 0; cr < 2; ++cr) {
      if (cl && cr) continue;
      for (int a : cL[key * 2 + cl]) for (int bb : cR[key * 2 + cr]) {
        int bits = (a & 0xff) | ((bb & 0xff) << uL) | (openBits << (uL + uR));
        int fl = ((a >> 8) | (bb >> 8)) | ((cl | cr) << 2);
        bset(P.cut, bits | (fl << nP));
      }
    }
  }

  // face return, one parent per orientation of the open pairs
  for (int mask = 0; mask < (1 << nOpen); ++mask) {
    int kept[2 * MAXN];
    for (int x = 0; x < m; ++x) kept[x] = -1;
    int markOf[MAXN];
    for (int u = 0; u < uL; ++u) { kept[leftU[u]] = u; markOf[u] = leftU[u]; }
    for (int u = 0; u < uR; ++u) { kept[nL + rightU[u]] = uL + u; markOf[uL + u] = nL + rightU[u]; }
    for (int t = 0; t < k; ++t) {
      if (openIdx[t] < 0) continue;
      int pos = uL + uR + openIdx[t];
      int mark = ((mask >> openIdx[t]) & 1) ? nL + M.rj[t] : M.li[t];
      kept[mark] = pos; markOf[pos] = mark;
    }
    Code Q = P;
    for (int pos = 0; pos < nP; ++pos) {
      int y = p[markOf[pos]];
      while (kept[y] < 0) y = p[y];
      Q.ret[pos] = (uint8_t)kept[y];
    }
    st.forks++;
    emit(Q);
  }
}

template <class Emit>
static void forkAll(const Code& L, const Code& R, int bound, Stats& st, Emit&& emit) {
  const int nL = L.n, nR = R.n;
  int pl[MAXN], pr[MAXN];
  for (int i = 0; i < nL; ++i) pl[i] = L.ret[i];
  for (int j = 0; j < nR; ++j) pr[j] = R.ret[j];
  const int cycL = cycCount(pl, nL), cycR = cycCount(pr, nR);
  Matching M;
  bool usedR[MAXN] = {false};
  // matchings with increasing left positions, each mapped to an unused right position
  // nP = nL + nR - 2k + open <= bound with open <= k forces k >= kmin.
  const int kmin = std::max(1, (nL + nR - bound + 1) / 2);
  auto rec = [&](auto&& self, int start) -> void {
    if (M.k >= kmin) emitMatching(L, R, M, bound, cycL, cycR, st, emit);
    if (M.k + std::min(nL - start, nR - M.k) < kmin) return;
    for (int i = start; i < nL; ++i) {
      for (int j = 0; j < nR; ++j) {
        if (usedR[j]) continue;
        if (((L.two >> i) & 1) && ((R.two >> j) & 1)) continue;  // at most three edges
        usedR[j] = true;
        M.li[M.k] = i; M.rj[M.k] = j; M.k++;
        self(self, i + 1);
        M.k--;
        usedR[j] = false;
      }
    }
  };
  rec(rec, 0);
}

// A record crossed by one edge whose side meets no position: its bridge can
// never be repaired, so every descendant keeps a cut of size one.
static bool hasDeadBridge(const Code& c) {
  const int n = c.n;
  if (n == 0) return false;
  const int all = (1 << n) - 1;
  const int fl = 1 | 2 | 4;  // inside, outside, cost
  return bget(c.cut, 0 | (fl << n)) || bget(c.cut, all | (fl << n));
}

static long peakRssKiB() {
  FILE* f = std::fopen("/proc/self/status", "r");
  if (!f) return -1;
  char line[256];
  long v = -1;
  while (std::fgets(line, sizeof line, f)) {
    if (std::strncmp(line, "VmHWM:", 6) == 0) { v = std::atol(line + 6); break; }
  }
  std::fclose(f);
  return v;
}

int main(int argc, char** argv) {
  if (argc < 2) { std::fprintf(stderr, "usage: closure BOUND [options]\n"); return 2; }
  POW3[0] = 1;
  for (int i = 1; i < MAXN + 2; ++i) POW3[i] = POW3[i - 1] * 3;
  const int bound = std::atoi(argv[1]);
  bool pruneDead = false, bothOrders = false;
  int threads = 1;
  double timeLimit = 1e18, progressEvery = 60;
  std::string dumpFile;
  for (int a = 2; a < argc; ++a) {
    std::string s = argv[a];
    if (s == "--prune-dead-bridge") pruneDead = true;
    else if (s == "--both-orders") bothOrders = true;
    else if (s == "--threads" && a + 1 < argc) threads = std::max(1, std::atoi(argv[++a]));
    else if (s == "--time-limit" && a + 1 < argc) timeLimit = std::atof(argv[++a]);
    else if (s == "--progress" && a + 1 < argc) progressEvery = std::atof(argv[++a]);
    else if (s == "--dump" && a + 1 < argc) dumpFile = argv[++a];
  }
  if (bound < 2 || bound > MAXN) { std::fprintf(stderr, "bound must be in 2..%d\n", MAXN); return 2; }
  buildPermTables();
  const auto t0 = std::chrono::steady_clock::now();
  auto elapsed = [&] {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  };

  std::vector<Code> states;
  std::unordered_map<uint64_t, std::vector<uint32_t>> index;
  auto insert = [&](const Code& c) -> bool {
    uint64_t h = codeHash(c);
    auto& bucket = index[h];
    for (uint32_t i : bucket) if (codeEq(states[i], c)) return false;
    bucket.push_back((uint32_t)states.size());
    states.push_back(c);
    return true;
  };
  // leafCode
  Code leaf;
  leaf.n = 2; leaf.two = 0; leaf.ret[0] = 1; leaf.ret[1] = 0;
  for (int c = 0; c < 3; ++c) bset(leaf.col, c + 3 * c);
  bset(leaf.cut, 0 | (0 << 2) | (1 << 3) | (0 << 4));   // U empty
  bset(leaf.cut, 1 | (1 << 2) | (1 << 3) | (1 << 4));   // U = end 0
  bset(leaf.cut, 2 | (1 << 2) | (1 << 3) | (1 << 4));   // U = end 1
  bset(leaf.cut, 3 | (1 << 2) | (0 << 3) | (0 << 4));   // U = both ends
  insert(canonical(leaf));

  bool rootColourable[2][2] = {{false, false}, {false, false}};  // [colourable][smallCut]
  Stats st;
  size_t i = 0;
  bool complete = true;
  double lastProgress = 0;
  // Batch-parallel worklist: every state i is glued once with every j <= i.
  // New states found in a batch are appended after it; they are processed in
  // later batches against all earlier states, so no pair is missed.
  struct Local {
    std::vector<Code> found;
    bool roots[2][2] = {{false, false}, {false, false}};
    Stats st;
  };
  while (i < states.size()) {
    if (elapsed() > timeLimit) { complete = false; break; }
    if (elapsed() - lastProgress > progressEvery) {
      lastProgress = elapsed();
      std::fprintf(stderr, "[%.0fs] processed %zu / %zu states, forks %llu\n", elapsed(), i,
                   states.size(), (unsigned long long)st.forks);
    }
    const size_t batchEnd = std::min(states.size(), i + (size_t)std::max(64, 16 * threads));
    std::vector<Local> locals(threads);
    std::atomic<size_t> next(i);
    auto worker = [&](int tid) {
      Local& loc = locals[tid];
      for (;;) {
        size_t a = next.fetch_add(1);
        if (a >= batchEnd) break;
        const Code L = states[a];
        auto emitLocal = [&](const Code& q) {
          if (q.n == 0) {
            bool colourable = bget(q.col, 0);
            bool small = false;
            for (int f = 0; f < 8; ++f) if (bget(q.cut, f) && (f & 1) && (f & 2)) small = true;
            loc.roots[colourable][small] = true;
            return;
          }
          if (pruneDead && hasDeadBridge(q)) { loc.st.deadBridgePruned++; return; }
          loc.found.push_back(canonical(q));
        };
        for (size_t j = 0; j <= a; ++j) {
          loc.st.pairs++;
          const Code R = states[j];
          forkAll(L, R, bound, loc.st, emitLocal);
          if (bothOrders && j != a) forkAll(R, L, bound, loc.st, emitLocal);
        }
      }
    };
    std::vector<std::thread> pool;
    for (int t = 1; t < threads; ++t) pool.emplace_back(worker, t);
    worker(0);
    for (auto& th : pool) th.join();
    for (auto& loc : locals) {
      for (auto& c : loc.found) insert(c);
      for (int c = 0; c < 2; ++c) for (int x = 0; x < 2; ++x) if (loc.roots[c][x]) rootColourable[c][x] = true;
      st.pairs += loc.st.pairs; st.matchings += loc.st.matchings;
      st.widthRejected += loc.st.widthRejected; st.eulerRejected += loc.st.eulerRejected;
      st.forks += loc.st.forks; st.deadBridgePruned += loc.st.deadBridgePruned;
    }
    i = batchEnd;
  }
  int byWidth[MAXN + 1] = {0};
  for (auto& c : states) byWidth[c.n]++;
  size_t processed = i;
  std::printf("{\"bound\": %d, \"prune_dead_bridge\": %s, \"threads\": %d, \"complete\": %s, "
              "\"states\": %zu, \"processed\": %zu, \"by_width\": {",
              bound, pruneDead ? "true" : "false", threads, complete ? "true" : "false",
              states.size(), processed);
  bool first = true;
  for (int n = 1; n <= MAXN; ++n) {
    if (!byWidth[n]) continue;
    std::printf("%s\"%d\": %d", first ? "" : ", ", n, byWidth[n]);
    first = false;
  }
  std::printf("}, \"root_codes\": [");
  first = true;
  for (int c = 0; c < 2; ++c) for (int s = 0; s < 2; ++s) if (rootColourable[c][s]) {
    std::printf("%s{\"colourable\": %s, \"small_cut\": %s}", first ? "" : ", ",
                c ? "true" : "false", s ? "true" : "false");
    first = false;
  }
  bool rejecting = rootColourable[0][0];
  std::printf("], \"rejecting_root\": %s, \"pairs\": %llu, \"matchings\": %llu, "
              "\"width_rejected\": %llu, \"euler_rejected\": %llu, \"forks\": %llu, "
              "\"dead_bridge_pruned\": %llu, \"seconds\": %.1f, \"peak_rss_kib\": %ld}\n",
              rejecting ? "true" : "false", (unsigned long long)st.pairs,
              (unsigned long long)st.matchings, (unsigned long long)st.widthRejected,
              (unsigned long long)st.eulerRejected, (unsigned long long)st.forks,
              (unsigned long long)st.deadBridgePruned, elapsed(), peakRssKiB());
  if (!dumpFile.empty()) {
    FILE* f = std::fopen(dumpFile.c_str(), "w");
    if (f) {
      for (auto& c : states) {
        std::fprintf(f, "%d %d", c.n, c.two);
        for (int q = 0; q < c.n; ++q) std::fprintf(f, " %d", c.ret[q]);
        for (int w = 0; w < COLW; ++w) std::fprintf(f, " %llx", (unsigned long long)c.col[w]);
        for (int w = 0; w < CUTW; ++w) std::fprintf(f, " %llx", (unsigned long long)c.cut[w]);
        std::fprintf(f, "\n");
      }
      std::fclose(f);
    }
  }
  return 0;
}
