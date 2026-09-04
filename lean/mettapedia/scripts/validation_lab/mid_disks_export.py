"""Phase A: enumerate intermediate pentaheptite disk types (4..MAXF faces,
ring in [RMIN,RMAX]) from a few central seeds, dedupe by WL hash, export."""
import sys, json, math
import networkx as nx
import pentaheptite_disks_lab as P
RMIN, RMAX, MAXF = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
faces, fadj, interior = P.faces, P.fadj, P.interior
def cd(f): return sum(math.hypot(*P.vpos[u]) for (u, v) in faces[f]) / len(faces[f])
seeds = sorted(interior, key=cd)[:6]
subsets = set()
for f in seeds:
    subsets.add(frozenset([f])); P.grow(frozenset([f]), subsets, MAXF)
def wl_key(fs):
    G = nx.Graph()
    for fi in fs:
        for (u, v) in faces[fi]: G.add_edge(u, v)
    for v in G.nodes: G.nodes[v]['d'] = str(G.degree(v))
    return (tuple(sorted(len(faces[fi]) for fi in fs)), nx.weisfeiler_lehman_graph_hash(G, node_attr='d', iterations=4))
types = {}
for fs in subsets:
    if len(fs) < 4: continue
    t = P.disk_tangle(fs)
    if t is None or not (RMIN <= t[0] <= RMAX): continue
    key = wl_key(fs)
    if key not in types: types[key] = (fs, t)
out = []
for key, (fs, (n, nv, E)) in types.items():
    out.append(dict(wl=key[1], faces=sorted(len(faces[f]) for f in fs), nfaces=len(fs), n=n, nv=nv,
                    edges=[[list(z) if isinstance(z, tuple) else z for z in e] for e in E]))
out.sort(key=lambda r: (-r['nfaces'], r['n']))
json.dump(out, open(f'mid_types_r{RMIN}_{RMAX}_f{MAXF}.json', 'w'))
from collections import Counter
print(f"subsets {len(subsets)}, types {len(out)}; by (nfaces, ring): {sorted(Counter((r['nfaces'], r['n']) for r in out).items())}")
