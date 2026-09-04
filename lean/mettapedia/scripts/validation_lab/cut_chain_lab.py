"""D1b small-case gate: nested exact saturated transversal chains.

A transversal of a planar cubic map is a simple cycle in the dual graph, i.e.
a closed curve crossing a set X of primal edges (its width |X|).  It is
  * separating  if the two designated holes A, B lie on different sides;
  * exact       if G - X has exactly two connected components (so X is
                 exactly the edge set between them);
  * saturated   if the 2|X| endpoints of X are pairwise distinct (each side's
                 new boundary is a simple cycle through |X| vertices).
Its geometric seam type is the cyclic sequence of sizes of the faces it
passes through, canonical up to rotation and reflection.

A chain is a family of pairwise nested separating transversals (A-sides
strictly increasing, so every slab contains at least one vertex).  We
compute, for each instance and width bound b, the longest chain m(b) over
ALL exact saturated separating transversals of width <= b (exhaustive dual
cycle enumeration; feasible on small instances), whether a longest chain
has one common seam type, and the BFS-frontier chain (levels of primal
distance from hole A) as a cheap lower bound on large instances.

Pre-registered outcomes.  T = on (5,0)-tube annuli of length L the ring
frontiers give m(10) = L, all exact and saturated, one seam type (the
corridor mechanism of prop:target-forced-cut-chain holds on the source's
own family).  W = on GP(k,0) with antipodal pentagon holes, m(b) is bounded
by a constant depending on b only, not on k (the wall branch: no bounded
width cut chain exists on sphere-like maps, so D1b needs the wall
exclusion D1d there).

Generators: Codex's v24_goldberg.make_goldberg_graph and
v24_tube_seed_census.make_tube_annulus (tools/fourcolor on PYTHONPATH).
"""
import sys, os, json, time
from collections import defaultdict, deque, Counter
sys.path.insert(0, os.environ.get('V24_TOOLS', '/home/oruzi/repos/MeTTapedia-4cp/tools/fourcolor'))
from v24_goldberg import make_goldberg_graph
from v24_tube_seed_census import make_tube_annulus


class Map:
    def __init__(self, n, edges, triangles, A_vertices, B_vertices, hole_faces):
        self.n = n; self.edges = [tuple(e) for e in edges]; self.tri = [tuple(t) for t in triangles]
        self.A = set(A_vertices); self.B = set(B_vertices); self.holes = set(hole_faces)
        self.adj = defaultdict(list)
        for ei, (u, v) in enumerate(self.edges):
            self.adj[u].append((v, ei)); self.adj[v].append((u, ei))
        # dual: faces = ids in triangles; dual edge per primal edge = the two faces common to its endpoints
        self.dual_edge = {}
        self.dadj = defaultdict(list)
        self.face_size = Counter()
        for v in range(n):
            for f in self.tri[v]: self.face_size[f] += 1
        for ei, (u, v) in enumerate(self.edges):
            common = set(self.tri[u]) & set(self.tri[v])
            if len(common) != 2:
                raise ValueError(f"edge {ei} borders {len(common)} common faces")
            f, g = sorted(common)
            self.dual_edge[ei] = (f, g)
            self.dadj[f].append((g, ei)); self.dadj[g].append((f, ei))
        self.faces = sorted(self.face_size)

    # ---- sides of a crossed-edge set
    def sides(self, X):
        Xs = set(X); seen = [-1] * self.n; comp = 0
        for s in range(self.n):
            if seen[s] >= 0: continue
            stack = [s]; seen[s] = comp
            while stack:
                x = stack.pop()
                for (y, ei) in self.adj[x]:
                    if ei in Xs or seen[y] >= 0: continue
                    seen[y] = comp; stack.append(y)
            comp += 1
        return seen, comp

    def classify(self, X):
        """Return (exact, saturated, separating, A_side_bitmask) for crossed set X."""
        seen, comp = self.sides(X)
        exact = comp == 2 and all(seen[u] != seen[v] for (u, v) in (self.edges[e] for e in X))
        ends = [w for e in X for w in self.edges[e]]
        saturated = len(set(ends)) == len(ends)
        a_comp = {seen[v] for v in self.A}; b_comp = {seen[v] for v in self.B}
        separating = len(a_comp) == 1 and len(b_comp) == 1 and a_comp != b_comp
        mask = 0
        if separating:
            ac = next(iter(a_comp))
            for v in range(self.n):
                if seen[v] == ac: mask |= 1 << v
        return exact, saturated, separating, mask

    def seam_type(self, cycle_faces):
        seq = [self.face_size[f] for f in cycle_faces]
        k = len(seq); cands = []
        for s in range(k):
            r = seq[s:] + seq[:s]; cands.append(tuple(r)); cands.append(tuple(r[::-1]))
        return min(cands)

    # ---- exhaustive simple dual cycles of length <= b avoiding hole faces
    def dual_cycles(self, b):
        out = []
        faces = [f for f in self.faces if f not in self.holes]
        for f0 in faces:
            # paths from f0 using faces > f0 only (dedupe by minimum face), edges distinct
            stack = [(f0, [f0], [], set())]
            while stack:
                cur, path, eds, used = stack.pop()
                for (g, ei) in self.dadj[cur]:
                    if ei in used or g in self.holes: continue
                    if g == f0 and len(eds) + 1 >= 2:
                        out.append((path[:], eds + [ei]))
                        continue
                    if g <= f0 or g in path: continue
                    if len(eds) + 1 >= b: continue
                    stack.append((g, path + [g], eds + [ei], used | {ei}))
        # dedupe (each cycle found twice, once per direction)
        seen = set(); uniq = []
        for (fs, es) in out:
            key = frozenset(es)
            if key in seen: continue
            seen.add(key); uniq.append((fs, es))
        return uniq

    def frontier_chain(self):
        dist = [-1] * self.n; q = deque()
        for v in self.A: dist[v] = 0; q.append(v)
        while q:
            x = q.popleft()
            for (y, _) in self.adj[x]:
                if dist[y] < 0: dist[y] = dist[x] + 1; q.append(y)
        levels = []
        for lv in range(max(dist)):
            X = [ei for ei, (u, v) in enumerate(self.edges) if (dist[u] <= lv) != (dist[v] <= lv)]
            levels.append(X)
        return levels


def longest_chain(items):
    """items: list of (mask, key). Longest chain under strict subset of masks."""
    items = sorted(items, key=lambda t: bin(t[0]).count('1'))
    best = [1] * len(items); prev = [-1] * len(items)
    for i in range(len(items)):
        mi = items[i][0]
        for j in range(i):
            mj = items[j][0]
            if mj != mi and (mj & mi) == mj and best[j] + 1 > best[i]:
                best[i] = best[j] + 1; prev[i] = j
    if not items: return 0, []
    i = max(range(len(items)), key=lambda t: best[t]); chain = []
    while i >= 0: chain.append(items[i]); i = prev[i]
    return len(chain), chain[::-1]


def analyze(M, name, b_list, exhaustive):
    res = {'name': name, 'V': M.n, 'E': len(M.edges), 'F': len(M.faces)}
    fr = M.frontier_chain()
    fr_rows = []
    for X in fr:
        exact, sat, sep, mask = M.classify(X)
        fr_rows.append((len(X), exact, sat, sep))
    res['frontier'] = dict(levels=len(fr), widths=[r[0] for r in fr_rows],
                           all_exact=all(r[1] for r in fr_rows), all_saturated=all(r[2] for r in fr_rows),
                           all_separating=all(r[3] for r in fr_rows))
    if exhaustive:
        t0 = time.time()
        bmax = max(b_list)
        cyc = M.dual_cycles(bmax)
        cls = []
        for (fs, es) in cyc:
            exact, sat, sep, mask = M.classify(es)
            if exact and sat and sep:
                cls.append((len(es), mask, M.seam_type(fs)))
        res['exhaustive'] = {}
        for b in b_list:
            items = [(mask, (w, st)) for (w, mask, st) in cls if w <= b]
            m, chain = longest_chain(items)
            seams = Counter(k[1] for (_, k) in chain)
            res['exhaustive'][b] = dict(candidates=len(items), m=m,
                                        chain_widths=[k[0] for (_, k) in chain],
                                        common_seam=(len(seams) == 1), seam_types=len(seams))
        res['exhaustive_seconds'] = round(time.time() - t0, 1)
    return res


def tube_map(L):
    inst = make_tube_annulus(L)
    n = len(inst['dual_triangles'])
    hole_faces = set()
    inner = set(inst['inner_face_vertices']); outer = set(inst['outer_face_vertices'])
    # hole faces (if kept as ids): faces common to every boundary vertex's triangle
    for grp in (inner, outer):
        common = None
        for v in grp:
            s = set(inst['dual_triangles'][v]); common = s if common is None else common & s
        if common: hole_faces |= common
    return Map(n, inst['tangle_edges'], inst['dual_triangles'], inner, outer, hole_faces)


def goldberg_map(k):
    g = make_goldberg_graph(k)
    n = g['primal_vertex_count']; tri = g['dual_triangles']
    pents = g['pentagon_face_ids']
    # faces incident to each vertex: tri[v]; pick two pentagons at maximal dual distance
    dadj = defaultdict(set)
    for (u, v) in g['primal_edges']:
        c = set(tri[u]) & set(tri[v])
        if len(c) == 2:
            f, h = c; dadj[f].add(h); dadj[h].add(f)
    def bfs(s):
        d = {s: 0}; q = deque([s])
        while q:
            x = q.popleft()
            for y in dadj[x]:
                if y not in d: d[y] = d[x] + 1; q.append(y)
        return d
    best = None
    for p in pents:
        d = bfs(p)
        for q_ in pents:
            if best is None or d[q_] > best[0]: best = (d[q_], p, q_)
    _, A, B = best
    Av = [v for v in range(n) if A in tri[v]]; Bv = [v for v in range(n) if B in tri[v]]
    return Map(n, g['primal_edges'], tri, Av, Bv, {A, B})


if __name__ == '__main__':
    out = []
    Ls = [1, 2, 3, 4, 5, 6]; ks = [1, 2, 3]
    for L in Ls:
        M = tube_map(L)
        r = analyze(M, f"tube(5,0) L={L}", [6, 8, 10, 12], exhaustive=(L <= 4))
        print(json.dumps(r), flush=True); out.append(r)
    for L in [8, 12, 16, 20]:
        M = tube_map(L); r = analyze(M, f"tube(5,0) L={L}", [10], exhaustive=False)
        print(json.dumps(r), flush=True); out.append(r)
    for k in ks:
        M = goldberg_map(k)
        r = analyze(M, f"GP({k},0)", [6, 8, 10, 12], exhaustive=(k <= 2))
        print(json.dumps(r), flush=True); out.append(r)
    for k in [4, 6, 8]:
        M = goldberg_map(k); r = analyze(M, f"GP({k},0)", [12], exhaustive=False)
        print(json.dumps(r), flush=True); out.append(r)
    json.dump(out, open('cut_chain_results.json', 'w'), indent=1)
