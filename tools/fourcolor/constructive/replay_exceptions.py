"""Independent replay of the exceptional pentagon complements.

Reads exceptional_pentagons.json (a JSON array of the records written by
pentagon_census --log; a file of JSON lines is also accepted) and, for
each record, rechecks everything with code paths independent of the census:

 * the map is a simple cubic graph whose rotation traces a sphere
   (V - E + F = 2), networkx agrees it is planar, and every face has length
   at least 5;
 * cyclic edge-connectivity at least 5, by brute force over every set of at
   most four edges (a cut is cyclic when two components of the remainder
   contain cycles);
 * nontrivial cyclic five-edge cuts (both sides with more than five vertices),
   enumerated through five-cycles of the dual graph;
 * the support of the pentagon's complement on its five spokes, deciding each
   of the 3^5 spoke words with a SAT solver (CaDiCaL by default); the words are
   ordered by the face order of the record;
 * the missing words: whether they form exactly one colour-permutation orbit,
   and whether they are "good" words (some three cyclically consecutive
   spokes of equal colour), which are exactly the spoke words of the pentagon
   itself.

Usage: python3 replay_exceptions.py [--solver PATH] [exceptional_pentagons.json]
"""
import itertools
import json
import os
import subprocess
import sys
import tempfile

import networkx as nx


def faces_from_rotation(rot):
    used, faces = set(), []
    for u in range(len(rot)):
        for w in rot[u]:
            if (u, w) in used:
                continue
            face, a, b = [], u, w
            while (a, b) not in used:
                used.add((a, b))
                face.append(a)
                nb = rot[b]
                c = nb[(nb.index(a) + 1) % len(nb)]
                a, b = b, c
            faces.append(face)
    return faces


def find(parent, x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def cyclic_cut(n, edges, removed):
    """True if removing `removed` leaves two components that contain cycles."""
    parent = list(range(n))
    size_e = [0] * n
    for i, (u, v) in enumerate(edges):
        if i in removed:
            continue
        ru, rv = find(parent, u), find(parent, v)
        if ru != rv:
            parent[ru] = rv
    comp_v, comp_e = {}, {}
    for x in range(n):
        r = find(parent, x)
        comp_v[r] = comp_v.get(r, 0) + 1
    for i, (u, v) in enumerate(edges):
        if i in removed:
            continue
        r = find(parent, u)
        comp_e[r] = comp_e.get(r, 0) + 1
    cyclic = sum(1 for r in comp_v if comp_e.get(r, 0) >= comp_v[r])
    return cyclic >= 2


def small_cyclic_cuts(n, edges, max_size):
    count = 0
    for s in range(1, max_size + 1):
        for removed in itertools.combinations(range(len(edges)), s):
            if cyclic_cut(n, edges, set(removed)):
                count += 1
    return count


def nontrivial_five_cuts(G, faces):
    edge_faces = {}
    for i, f in enumerate(faces):
        for t in range(len(f)):
            edge_faces.setdefault(frozenset((f[t], f[(t + 1) % len(f)])), []).append(i)
    D = nx.Graph()
    for e, fl in edge_faces.items():
        D.add_edge(fl[0], fl[1], edge=e)
    cycles = {}
    for s in sorted(D.nodes()):
        stack = [(s, [s])]
        while stack:
            v, path = stack.pop()
            if len(path) == 5:
                if s in D[v]:
                    cycles[frozenset(path)] = path
                continue
            for w in D[v]:
                if w > s and w not in path:
                    stack.append((w, path + [w]))
    count = 0
    for cyc in cycles.values():
        cut = [tuple(D[cyc[i]][cyc[(i + 1) % 5]]["edge"]) for i in range(5)]
        H = G.copy()
        H.remove_edges_from(cut)
        comps = list(nx.connected_components(H))
        if len(comps) == 2 and min(len(c) for c in comps) > 5:
            count += 1
    return count


def spoke_word_extends(solver, rot, face, word):
    inface = set(face)
    rest = [v for v in range(len(rot)) if v not in inface]
    internal = [(u, v) for u in rest for v in rot[u] if v not in inface and u < v]
    var = {}
    for i, e in enumerate(internal):
        for c in range(3):
            var[(i, c)] = 3 * i + c + 1
    clauses = []
    for i in range(len(internal)):
        clauses.append([var[(i, c)] for c in range(3)])
        for c in range(3):
            for d in range(c + 1, 3):
                clauses.append([-var[(i, c)], -var[(i, d)]])
    fixed = {}
    for t, x in enumerate(face):
        outside = [y for y in rot[x] if y not in inface]
        assert len(outside) == 1
        fixed.setdefault(outside[0], []).append(word[t])
    for v in rest:
        inc = [i for i, (a, b) in enumerate(internal) if v in (a, b)]
        ports = fixed.get(v, [])
        if len(set(ports)) < len(ports):
            return False
        for c in range(3):
            for i, j in itertools.combinations(inc, 2):
                clauses.append([-var[(i, c)], -var[(j, c)]])
            if c in ports:
                for i in inc:
                    clauses.append([-var[(i, c)]])
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {3 * len(internal)} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
        path = f.name
    res = subprocess.run([solver, "-q", path], capture_output=True, text=True)
    os.unlink(path)
    if res.returncode not in (10, 20):
        raise RuntimeError(f"solver failed: {res.returncode} {res.stderr[:200]}")
    return res.returncode == 10


def rgs(word):
    seen = {}
    return "".join(str(seen.setdefault(c, len(seen))) for c in word)


def is_good(word):
    return any(word[i] == word[(i + 1) % 5] == word[(i + 2) % 5] for i in range(5))


def pentagon_words():
    words = set()
    for c in itertools.product(range(3), repeat=5):
        if all(c[i] != c[(i + 1) % 5] for i in range(5)):
            # spoke at vertex i sees cycle edges c[i-1] and c[i]
            words.add(tuple(3 - c[i - 1] - c[i] for i in range(5)))
    return words


def main():
    args = sys.argv[1:]
    solver = "cadical"
    if "--solver" in args:
        solver = args[args.index("--solver") + 1]
        del args[args.index("--solver"):args.index("--solver") + 2]
    path = args[0] if args else os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                             "exceptional_pentagons.json")
    own = pentagon_words()
    assert len(own) == 30 and all(is_good(w) for w in own)
    text = open(path).read()
    records = json.loads(text) if text.lstrip().startswith("[") else [json.loads(l) for l in text.splitlines() if l.strip()]
    for r in records:
        rot, face, n = r["rotation"], r["face"], r["n"]
        G = nx.Graph()
        for u in range(n):
            for v in rot[u]:
                G.add_edge(u, v)
        edges = sorted(tuple(sorted(e)) for e in G.edges())
        simple = all(len(set(nb)) == 3 and u not in nb for u, nb in enumerate(rot))
        faces = faces_from_rotation(rot)
        euler = n - len(edges) + len(faces)
        planar = nx.check_planarity(G)[0]
        lengths = sorted(len(f) for f in faces)
        face_ok = sorted(face) in [sorted(f) for f in faces]
        cuts4 = small_cyclic_cuts(n, edges, 4)
        cuts5 = nontrivial_five_cuts(G, faces)
        admissible = [w for w in itertools.product(range(3), repeat=5)
                      if all(w.count(c) % 2 == 1 for c in range(3))]
        supported = {w for w in admissible if spoke_word_extends(solver, rot, face, w)}
        inadmissible_sat = sum(1 for w in itertools.product(range(3), repeat=5)
                               if w not in set(admissible) and spoke_word_extends(solver, rot, face, w))
        missing = sorted(set(admissible) - supported)
        orbits = sorted({rgs(w) for w in missing})
        counts = {L: lengths.count(L) for L in sorted(set(lengths))}
        print(f"map {r['map']} (n={n}): simple cubic {simple}; Euler V-E+F={euler}; planar {planar}; "
              f"faces {counts}; face is a face {face_ok}")
        print(f"   cyclic cuts of size <=4: {cuts4}; nontrivial cyclic 5-cuts: {cuts5}")
        print(f"   support {len(supported)} of {len(admissible)} admissible words "
              f"(inadmissible words extending: {inadmissible_sat}); missing {len(missing)} words, "
              f"orbits {orbits}; all missing good: {all(is_good(w) for w in missing)}; "
              f"good words supported: {sum(1 for w in supported if is_good(w))} of 30")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
