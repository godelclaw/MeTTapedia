"""Extract the V=14 good-word same-sector-nest certificate as an explicit
tangle: replicate the width-two enumerator's construction (same vertex ids,
rotation rule, face tracing, Tait colouring), re-verify every validity
condition with the enumerator's own functions, and emit JSON with integer
vertex ids suitable for a Lean finite witness.

Usage: CLOSED_WEB_ENUM_DIR=<dir> python3 extract_goodword_certificate.py
"""
import os, sys, json
from collections import defaultdict
sys.path.insert(0, os.environ.get('CLOSED_WEB_ENUM_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-numerics'))
import closed_web_enum as E

ex = json.load(open('goodword_widthtwo_results.json'))['14']['example']
p, q, kin, kout = ex['p'], ex['q'], ex['kin'], ex['kout']
chordsS = [tuple(c) for c in ex['prsS']]; chordsT = [tuple(c) for c in ex['prsT']]
x1, x2 = ex['colouring'][0], ex['colouring'][1]

r = E.build_and_check(p, q, kin, kout, chordsS, chordsT)
assert r is not None, "enumerator rejects the certificate"
goods = [c for c in r['colourings'] if c[3] and c[0] == x1 and c[1] == x2]
assert goods, "colouring not good/closed per enumerator"

# ---- replicate construction (verbatim logic) ----
IB1, IB2, OB1, OB2 = 'IB1', 'IB2', 'OB1', 'OB2'
Ia = ['Ia%d' % i for i in range(3)]; Oa = ['Oa%d' % i for i in range(3)]
adj = defaultdict(dict); edges = []
def add_edge(u, v):
    eid = len(edges); edges.append((u, v)); adj[u][v] = eid; adj[v][u] = eid
add_edge(IB1, 0)
for i in range(p - 1): add_edge(i, i + 1)
add_edge(p - 1, OB1)
add_edge(IB2, p)
for j in range(q - 1): add_edge(p + j, p + j + 1)
add_edge(p + q - 1, OB2)
chord_of = {}
for (x, y) in chordsS + chordsT:
    add_edge(x, y); chord_of[x] = y; chord_of[y] = x
sectorS = set()
for (x, y) in chordsS: sectorS.add(x); sectorS.add(y)
rot = {}
for i in range(p):
    down = IB1 if i == 0 else i - 1
    up = OB1 if i == p - 1 else i + 1
    c = chord_of[i]
    rot[i] = [down, c, up] if i in sectorS else [down, up, c]
for j in range(q):
    v = p + j
    down = IB2 if j == 0 else v - 1
    up = OB2 if j == q - 1 else v + 1
    c = chord_of[v]
    rot[v] = [down, up, c] if v in sectorS else [down, c, up]
stubs = [IB1, IB2, OB1, OB2] + Ia + Oa
for s in stubs: rot[s] = list(adj[s].keys())
inner_stubs = {IB1, IB2} | set(Ia); outer_stubs = {OB1, OB2} | set(Oa)
# face tracing
darts = [(u, v) for u in rot for v in rot[u]]
seen = set(); faces = []
for d in darts:
    if d in seen: continue
    f = []; cur = d
    while cur not in seen:
        seen.add(cur); f.append(cur)
        u, v = cur; rr = rot[v]; k = rr.index(u)
        cur = (v, rr[(k + 1) % len(rr)])
    faces.append(f)
hole_faces = []; interior = []
for f in faces:
    si = {u for (u, v) in f if u in inner_stubs}; so = {u for (u, v) in f if u in outer_stubs}
    (hole_faces if (si or so) else interior).append(f)
assert len(hole_faces) == 2 and min(len(f) for f in interior) >= 5
# colouring
col = {eid: 0 for eid in range(len(edges))}
def path_colours(start, length): return [start if k % 2 == 0 else 3 - start for k in range(length)]
b1 = [adj[IB1][0]] + [adj[i][i + 1] for i in range(p - 1)] + [adj[p - 1][OB1]]
b2 = [adj[IB2][p]] + [adj[p + j][p + j + 1] for j in range(q - 1)] + [adj[p + q - 1][OB2]]
for eid, c in zip(b1, path_colours(x1, p + 1)): col[eid] = c
for eid, c in zip(b2, path_colours(x2, q + 1)): col[eid] = c
assert E.strands_all_radial(edges, col, adj, inner_stubs, outer_stubs)
inner_order = [u for (u, v) in [hf for hf in hole_faces if any(u in inner_stubs for (u, _) in hf)][0] if u in inner_stubs]
word = tuple(col[adj[s][next(iter(adj[s]))]] for s in inner_order)
assert E.is_good_word(word), word

# ---- integer ids: internal 0..V-1, then stubs ----
V = p + q
vid = {v: v for v in range(V)}
for k, s in enumerate(stubs): vid[s] = V + k
int_edges = [(vid[u], vid[v]) for (u, v) in edges]
faces_eids = [[adj[u][v] for (u, v) in f] for f in faces]
# sectors: faces reachable without crossing rail edges (rail = non-alpha edges)
rail_eids = {eid for eid in range(len(edges)) if col[eid] != 0}
face_of_dart = {}
for fi, f in enumerate(faces):
    for d in f: face_of_dart[d] = fi
parent = list(range(len(faces)))
def find(x):
    while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
    return x
for eid, (u, v) in enumerate(edges):
    if eid in rail_eids: continue
    a, b = face_of_dart[(u, v)], face_of_dart[(v, u)]
    parent[find(a)] = find(b)
label = {}
for fi in range(len(faces)):
    label[fi] = find(fi)
classes = sorted(set(label.values()))
sector_of_face = [classes.index(label[fi]) for fi in range(len(faces))]
chords = [(min(x, y), max(x, y), 'S') for (x, y) in chordsS if isinstance(x, int) and isinstance(y, int) and (x < p) == (y < p)]
chords += [(min(x, y), max(x, y), 'T') for (x, y) in chordsT if isinstance(x, int) and isinstance(y, int) and (x < p) == (y < p)]
out = dict(V=V, p=p, q=q, kin=kin, kout=kout, x1=x1, x2=x2, inner_word=list(word),
           vertex_names={str(vid[s]): s for s in stubs},
           edges=int_edges, colouring=[col[e] for e in range(len(edges))],
           rotation={str(vid[u]): [vid[w] for w in rot[u]] for u in rot},
           faces=faces_eids, hole_faces=[faces.index(f) for f in hole_faces],
           interior_face_lengths=sorted(len(f) for f in interior),
           inner_stubs=sorted(vid[s] for s in inner_stubs), outer_stubs=sorted(vid[s] for s in outer_stubs),
           rail_B1=[vid[IB1]] + list(range(p)) + [vid[OB1]], rail_B2=[vid[IB2]] + list(range(p, p + q)) + [vid[OB2]],
           sector_of_face=sector_of_face, n_sectors=len(classes),
           same_path_chords=[(lo, hi, s, adj[lo][hi]) for (lo, hi, s) in chords])
json.dump(out, open('goodword_nest_certificate_V14.json', 'w'), indent=1)
print("V", V, "edges", len(edges), "faces", len(faces), "interior lengths", out['interior_face_lengths'], "sectors", len(classes))
print("chords:", out['same_path_chords'])
print("inner word", word, "colouring alpha count", sum(1 for e in col.values() if e == 0))
nest = [(c1, c2) for c1 in chords for c2 in chords if c1[0] < c2[0] and c2[1] < c1[1]]
print("nested pairs (outer, inner):", nest, "same sector:", [c1[2] == c2[2] for c1, c2 in nest])
