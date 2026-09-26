// Sectors of the zigzag tube ring transfer.
//
// Colours are the nonzero Klein-group elements 1,2,3 (third colour = xor).
// A zigzag ring with k inputs x and k outputs y: choose a_j in {1,2,3} \ {x_j}
// (the colour of the zigzag edge from input vertex j to output vertex j); the
// output at position i is y_i = a_i ^ x_{i+1} ^ a_{i+1}, which must be nonzero
// (properness at output vertex i).
//
// For each k: the parity-admissible words, the strongly connected classes of
// the word graph, whether every edge stays inside its class (closed classes,
// no transient words), conservation of colour counts along every edge, the
// period of every class, and whether each three-colour count class is a
// single class.
//
// Usage: ring_sectors KMIN KMAX

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <numeric>
#include <vector>

static int K;
static std::vector<int> pow3;

static void decode(int64_t code, int* w) {
  for (int i = 0; i < K; ++i) { w[i] = int(code % 3) + 1; code /= 3; }
}
static int64_t encode(const int* w) {
  int64_t c = 0;
  for (int i = K - 1; i >= 0; --i) c = c * 3 + (w[i] - 1);
  return c;
}

// all outputs of one ring from input x
static void successors(const int* x, std::vector<int64_t>& out) {
  out.clear();
  int a[32], y[32];
  // depth-first over a_0..a_{K-1}; check y_{i-1} once a_i is chosen,
  // and y_{K-1} (which needs a_0) at the end
  std::vector<int> stack;
  int choice[32];
  int depth = 0;
  choice[0] = 0;
  while (depth >= 0) {
    if (choice[depth] >= 3) { --depth; if (depth >= 0) ++choice[depth]; continue; }
    int cand = choice[depth] + 1;  // 1..3
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
  int kmin = argc > 1 ? atoi(argv[1]) : 5, kmax = argc > 2 ? atoi(argv[2]) : 9;
  for (K = kmin; K <= kmax; ++K) {
    int64_t total = 1;
    for (int i = 0; i < K; ++i) total *= 3;
    // admissible words: every colour count has the parity of K
    std::vector<int64_t> words;
    std::vector<int> index(total, -1);
    int w[32];
    for (int64_t c = 0; c < total; ++c) {
      decode(c, w);
      int cnt[4] = {0, 0, 0, 0};
      for (int i = 0; i < K; ++i) cnt[w[i]]++;
      if (cnt[1] % 2 == K % 2 && cnt[2] % 2 == K % 2 && cnt[3] % 2 == K % 2) {
        index[c] = (int)words.size();
        words.push_back(c);
      }
    }
    const int n = (int)words.size();
    // CSR adjacency
    std::vector<int64_t> offset(n + 1, 0);
    std::vector<int> adj;
    std::vector<int64_t> succ;
    bool conserve = true;
    int64_t edges = 0;
    for (int u = 0; u < n; ++u) {
      decode(words[u], w);
      int cu[4] = {0, 0, 0, 0};
      for (int i = 0; i < K; ++i) cu[w[i]]++;
      successors(w, succ);
      for (int64_t s : succ) {
        int v = index[s];
        if (v < 0) { std::printf("nonadmissible successor!\n"); return 1; }
        int wy[32]; decode(s, wy);
        int cv[4] = {0, 0, 0, 0};
        for (int i = 0; i < K; ++i) cv[wy[i]]++;
        if (cv[1] != cu[1] || cv[2] != cu[2] || cv[3] != cu[3]) conserve = false;
        adj.push_back(v);
      }
      offset[u + 1] = (int64_t)adj.size();
    }
    edges = (int64_t)adj.size();
    // iterative Tarjan
    std::vector<int> idx(n, -1), low(n, 0), comp(n, -1), st;
    std::vector<char> on(n, 0);
    std::vector<std::pair<int, int64_t>> call;
    int counter = 0, ncomp = 0;
    for (int s = 0; s < n; ++s) {
      if (idx[s] >= 0) continue;
      call.push_back({s, offset[s]});
      idx[s] = low[s] = counter++; st.push_back(s); on[s] = 1;
      while (!call.empty()) {
        int u = call.back().first;
        int64_t& e = call.back().second;
        if (e < offset[u + 1]) {
          int v = adj[e++];
          if (idx[v] < 0) {
            idx[v] = low[v] = counter++; st.push_back(v); on[v] = 1;
            call.push_back({v, offset[v]});
          } else if (on[v]) {
            low[u] = std::min(low[u], idx[v]);
          }
        } else {
          if (low[u] == idx[u]) {
            while (true) {
              int x = st.back(); st.pop_back(); on[x] = 0; comp[x] = ncomp;
              if (x == u) break;
            }
            ++ncomp;
          }
          call.pop_back();
          if (!call.empty()) {
            int p = call.back().first;
            low[p] = std::min(low[p], low[u]);
          }
        }
      }
    }
    // closedness
    bool closed = true;
    for (int u = 0; u < n && closed; ++u)
      for (int64_t e = offset[u]; e < offset[u + 1]; ++e)
        if (comp[adj[e]] != comp[u]) { closed = false; break; }
    // sizes
    std::vector<int> csize(ncomp, 0);
    for (int u = 0; u < n; ++u) csize[comp[u]]++;
    std::map<int, int> hist;
    for (int c = 0; c < ncomp; ++c) hist[csize[c]]++;
    // periods by BFS levels inside each class
    std::vector<int> level(n, -1), period(ncomp, 0);
    for (int u = 0; u < n; ++u) {
      if (level[u] >= 0) continue;
      int c = comp[u];
      std::vector<int> q{u};
      level[u] = 0;
      for (size_t h = 0; h < q.size(); ++h) {
        int x = q[h];
        for (int64_t e = offset[x]; e < offset[x + 1]; ++e) {
          int v = adj[e];
          if (comp[v] != c) continue;
          if (level[v] < 0) { level[v] = level[x] + 1; q.push_back(v); }
          else period[c] = std::gcd(period[c], std::abs(level[x] + 1 - level[v]));
        }
      }
    }
    std::map<int, int> phist;
    for (int c = 0; c < ncomp; ++c) phist[period[c]]++;
    // count classes: map count vector -> set of comps
    std::map<std::vector<int>, std::vector<int>> byCount;
    for (int u = 0; u < n; ++u) {
      decode(words[u], w);
      std::vector<int> cnt(3, 0);
      for (int i = 0; i < K; ++i) cnt[w[i] - 1]++;
      byCount[cnt].push_back(comp[u]);
    }
    int threeColourClasses = 0, threeColourSingle = 0, twoColourClasses = 0;
    std::map<int, int> twoSplit;
    for (auto& kv : byCount) {
      auto& v = kv.second;
      std::sort(v.begin(), v.end());
      v.erase(std::unique(v.begin(), v.end()), v.end());
      bool three = kv.first[0] > 0 && kv.first[1] > 0 && kv.first[2] > 0;
      if (three) { threeColourClasses++; if (v.size() == 1) threeColourSingle++; }
      else { twoColourClasses++; twoSplit[(int)v.size()]++; }
    }
    std::printf("k=%d |Adm|=%d edges=%lld classes=%d closed=%s countsConserved=%s\n",
                K, n, (long long)edges, ncomp, closed ? "yes" : "NO", conserve ? "yes" : "NO");
    std::printf("   class sizes:");
    for (auto& kv : hist) std::printf(" %dx%d", kv.first, kv.second);
    std::printf("\n   periods:");
    for (auto& kv : phist) std::printf(" p%d:%d", kv.first, kv.second);
    std::printf("\n   three-colour count classes: %d, single class: %d; two-colour count classes: %d, split into:",
                threeColourClasses, threeColourSingle, twoColourClasses);
    for (auto& kv : twoSplit) std::printf(" %d-way:%d", kv.first, kv.second);
    std::printf("\n");
    std::fflush(stdout);
  }
  return 0;
}
