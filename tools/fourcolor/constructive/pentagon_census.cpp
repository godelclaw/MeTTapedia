// Face-complement census for plane cubic maps.
//
// Input (stdin): plantri ASCII code, one map per line, "n adj,adj,...", with
// vertices named by consecutive characters starting at 'a' and every
// adjacency list in cyclic order.  Normal-form maps are the duals of
// 5-connected triangulations:  plantri -c5m5 -d -a N | pentagon_census
// Fullerenes from fullgen can be converted with planar_code_to_ascii.py.
//
// For every face of length L <= MAXL (default 5) whose vertices are distinct
// and whose spokes leave the face, the complement of the face is a piece whose
// ports are the L spokes, in face order.  The program decides which
// parity-admissible spoke words extend to a proper 3-edge-colouring of the
// complement (one representative per colour-permutation orbit), and reports
// per face length: the number of faces, the number whose complement support
// is not all admissible words, and the minimum support density.
//
// With --log FILE, every non-full complement is written as one JSON line:
//   {"map": index (1-based, in input order), "n": vertices,
//    "rotation": adjacency lists as read, "face": face vertices in order,
//    "support": words realized, "admissible": admissible words,
//    "missing": missing orbit representatives (restricted growth strings)}
//
// Usage: pentagon_census [--max-face L] [--log FILE] < maps.txt

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <string>
#include <vector>

struct Piece {
  int n = 0, m = 0, k = 0;
  std::vector<int> eu, ev, port;
  std::vector<std::vector<int>> incE, incP;
};

static Piece P;
static std::vector<int> col, pcol, trail;

static int knownMask(int v) {
  int mask = 0;
  for (int e : P.incE[v]) if (col[e]) { if (mask & (1 << col[e])) return -1; mask |= 1 << col[e]; }
  for (int p : P.incP[v]) { if (mask & (1 << pcol[p])) return -1; mask |= 1 << pcol[p]; }
  return mask;
}

static bool propagate(std::vector<int>& q) {
  while (!q.empty()) {
    int v = q.back(); q.pop_back();
    int mask = knownMask(v);
    if (mask < 0) return false;
    if (__builtin_popcount(mask) == 2) {
      int miss = 0;
      for (int c = 1; c <= 3; ++c) if (!(mask & (1 << c))) miss = c;
      for (int e : P.incE[v]) if (!col[e]) {
        col[e] = miss; trail.push_back(e);
        q.push_back(P.eu[e] == v ? P.ev[e] : P.eu[e]);
        q.push_back(v);
        break;
      }
    }
  }
  return true;
}

static bool dfs() {
  int best = -1, bestScore = -1;
  for (int e = 0; e < P.m; ++e) if (!col[e]) {
    int a = knownMask(P.eu[e]), b = knownMask(P.ev[e]);
    if (a < 0 || b < 0) return false;
    int s = __builtin_popcount(a) + __builtin_popcount(b);
    if (s > bestScore) { bestScore = s; best = e; }
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
  col.assign(P.m, 0);
  trail.clear();
  std::vector<int> q;
  for (int v = 0; v < P.n; ++v) {
    if (knownMask(v) < 0) return false;
    q.push_back(v);
  }
  if (!propagate(q)) return false;
  return dfs();
}

// admissible restricted-growth representatives of length k, with orbit sizes
static std::vector<std::pair<std::vector<int>, int>> representatives(int k) {
  std::vector<std::pair<std::vector<int>, int>> out;
  std::vector<int> w(k, 1), mx(k, 1);
  while (true) {
    int cnt[4] = {0, 0, 0, 0};
    for (int i = 0; i < k; ++i) cnt[w[i]]++;
    if (cnt[1] % 2 == k % 2 && cnt[2] % 2 == k % 2 && cnt[3] % 2 == k % 2) {
      int used = (cnt[1] > 0) + (cnt[2] > 0) + (cnt[3] > 0);
      out.push_back({w, used == 1 ? 3 : 6});
    }
    int i = k - 1;
    while (i >= 1 && w[i] >= std::min(3, mx[i - 1] + 1)) --i;
    if (i < 1) break;
    w[i]++;
    mx[i] = std::max(mx[i - 1], w[i]);
    for (int j = i + 1; j < k; ++j) { w[j] = 1; mx[j] = mx[j - 1]; }
  }
  return out;
}

int main(int argc, char** argv) {
  int maxL = 5;
  const char* logPath = nullptr;
  for (int a = 1; a < argc; ++a) {
    if (!std::strcmp(argv[a], "--max-face") && a + 1 < argc) maxL = std::atoi(argv[++a]);
    else if (!std::strcmp(argv[a], "--log") && a + 1 < argc) logPath = argv[++a];
  }
  FILE* logFile = logPath ? std::fopen(logPath, "w") : nullptr;
  std::map<int, std::vector<std::pair<std::vector<int>, int>>> repCache;
  std::map<int, long long> faces, nonfull, admissible;
  std::map<int, double> minDensity;
  static char buf[1 << 20];
  long long mapIndex = 0;
  while (std::fgets(buf, sizeof buf, stdin)) {
    int n = 0;
    char* p = buf;
    if (std::sscanf(p, "%d", &n) != 1) continue;
    while (*p && *p != ' ') ++p;
    while (*p == ' ') ++p;
    std::vector<std::vector<int>> adj(n);
    int v = 0;
    for (; *p && *p != '\n'; ++p) {
      if (*p == ',') { ++v; continue; }
      adj[v].push_back((int)(unsigned char)*p - 'a');
    }
    ++mapIndex;
    std::map<std::pair<int, int>, int> used;
    for (int u = 0; u < n; ++u) for (int w : adj[u]) {
      if (used.count({u, w})) continue;
      std::vector<int> face;
      int a = u, b = w;
      while (!used.count({a, b})) {
        used[{a, b}] = 1;
        face.push_back(a);
        auto& nb = adj[b];
        int pos = int(std::find(nb.begin(), nb.end(), a) - nb.begin());
        int c = nb[(pos + 1) % nb.size()];
        a = b; b = c;
      }
      const int L = (int)face.size();
      if (L > maxL) continue;
      std::vector<int> inFace(n, 0), idx(n, -1);
      for (int x : face) inFace[x] = 1;
      P = Piece();
      for (int x = 0; x < n; ++x) if (!inFace[x]) idx[x] = P.n++;
      P.incE.assign(P.n, {});
      P.incP.assign(P.n, {});
      for (int x = 0; x < n; ++x) for (int y : adj[x]) {
        if (x < y && !inFace[x] && !inFace[y]) {
          P.eu.push_back(idx[x]); P.ev.push_back(idx[y]);
          P.incE[idx[x]].push_back(P.m); P.incE[idx[y]].push_back(P.m);
          P.m++;
        }
      }
      bool ok = true;
      for (int x : face) {
        int outside = -1, count = 0;
        for (int y : adj[x]) if (!inFace[y]) { outside = y; ++count; }
        if (count != 1) { ok = false; break; }
        P.incP[idx[outside]].push_back(P.k);
        P.port.push_back(idx[outside]);
        P.k++;
      }
      if (!ok) continue;
      bool degreesOk = true;
      for (int x = 0; x < P.n; ++x)
        if (P.incE[x].size() + P.incP[x].size() != 3) degreesOk = false;
      if (!degreesOk) continue;
      if (!repCache.count(L)) repCache[L] = representatives(L);
      long long adm = 0, sup = 0;
      std::vector<std::string> missing;
      for (auto& r : repCache[L]) {
        adm += r.second;
        if (extends(r.first)) sup += r.second;
        else {
          std::string s;
          for (int c : r.first) s.push_back(char('0' + c - 1));
          missing.push_back(s);
        }
      }
      faces[L]++;
      admissible[L] = adm;
      double d = double(sup) / adm;
      if (!minDensity.count(L) || d < minDensity[L]) minDensity[L] = d;
      if (sup < adm) {
        nonfull[L]++;
        if (logFile) {
          std::fprintf(logFile, "{\"map\": %lld, \"n\": %d, \"rotation\": [", mapIndex, n);
          for (int x = 0; x < n; ++x) {
            std::fprintf(logFile, "%s[", x ? ", " : "");
            for (size_t t = 0; t < adj[x].size(); ++t) std::fprintf(logFile, "%s%d", t ? ", " : "", adj[x][t]);
            std::fprintf(logFile, "]");
          }
          std::fprintf(logFile, "], \"face\": [");
          for (int t = 0; t < L; ++t) std::fprintf(logFile, "%s%d", t ? ", " : "", face[t]);
          std::fprintf(logFile, "], \"support\": %lld, \"admissible\": %lld, \"missing\": [", sup, adm);
          for (size_t t = 0; t < missing.size(); ++t) std::fprintf(logFile, "%s\"%s\"", t ? ", " : "", missing[t].c_str());
          std::fprintf(logFile, "]}\n");
        }
      }
    }
  }
  if (logFile) std::fclose(logFile);
  std::printf("maps=%lld\n", mapIndex);
  for (auto& kv : faces) {
    int L = kv.first;
    std::printf("  face length %d: faces=%lld non-full complements=%lld min density=%.4f (admissible %lld)\n",
                L, kv.second, nonfull[L], minDensity[L], admissible[L]);
  }
  return 0;
}
