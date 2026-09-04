"""All bounded disks of the pentaheptite wall up to the certifiable scale.

Disks = connected unions of 1..3 interior faces of the pentaheptite tiling
(k0, 2x2 diamond sublattice), as port tangles (boundary vertices get a port,
in the cyclic order of the disk boundary), deduplicated by WL graph hash,
ring <= RING_MAX.  Each is run through the reducibility menu.

Pre-registered: PD1 = some disk is reducible (the wall is excluded at this
scale); PD2 = none is -> outcome-B specimen at ring <= RING_MAX.
"""
import sys, json, time
from collections import Counter, defaultdict
import networkx as nx
import wall_flower_lab as W
from patch_reducibility_lab import analyze_tangle

R = 10
vpos, rot, hexes, centres = W.hex_lattice(R)
(a1, b1), (a2, b2) = (0, -2), (-2, 0)
chosen = {(i * a1 + j * a2, i * b1 + j * b2) for i in range(-3 * R, 3 * R + 1) for j in range(-3 * R, 3 * R + 1)}
for c in sorted(chosen & set(centres)):
    a, b = hexes[c][0], hexes[c][1]
    if all(len(rot[w]) == 3 for w in [a, b] + rot[a] + rot[b]): W.sw_rotate(rot, a, b)
faces = W.faces_of(rot)
fverts = [[u for (u, v) in f] for f in faces]
import math
interior = [fi for fi in range(len(faces)) if all(math.hypot(*vpos[v]) < (R - 3) * W.S3 for v in fverts[fi])]
assert all(len(faces[fi]) in (5, 7) for fi in interior), Counter(len(faces[fi]) for fi in interior)
fadj = defaultdict(set)
face_of_dart = {}
for fi, f in enumerate(faces):
    for d in f: face_of_dart[d] = fi
for fi in interior:
    for (u, v) in faces[fi]:
        g = face_of_dart[(v, u)]
        if g in interior: fadj[fi].add(g)

def disk_tangle(fset):
    edges = set(); everts = set()
    cnt = Counter()
    for fi in fset:
        for (u, v) in faces[fi]:
            e = (min(u, v), max(u, v)); edges.add(e); cnt[e] += 1; everts |= {u, v}
    bnd_edges = [e for e in edges if cnt[e] == 1]
    deg = Counter()
    for (u, v) in edges: deg[u] += 1; deg[v] += 1
    bverts = [v for v in everts if deg[v] == 2]
    # walk the boundary cycle
    badj = defaultdict(list)
    for (u, v) in bnd_edges: badj[u].append(v); badj[v].append(u)
    start = bverts[0]; order = [start]; prev = None; cur = start
    while True:
        nxt = [w for w in badj[cur] if w != prev]
        if not nxt: break
        prev, cur = cur, nxt[0]
        if cur == start: break
        order.append(cur)
    if len(order) != len(set(order)) or set(order) != set(v for e in bnd_edges for v in e):
        return None   # boundary not a single simple cycle (not a disk)
    ports = [v for v in order if deg[v] == 2]
    vid = {v: i for i, v in enumerate(sorted(everts))}
    E = [(vid[u], vid[v]) for (u, v) in edges] + [(('p', i), vid[v]) for i, v in enumerate(ports)]
    return len(ports), len(everts), E

def wl_key(fset):
    G = nx.Graph()
    for fi in fset:
        for (u, v) in faces[fi]: G.add_edge(u, v)
    for v in G.nodes: G.nodes[v]['d'] = str(G.degree(v))
    return (tuple(sorted(len(faces[fi]) for fi in fset)), nx.weisfeiler_lehman_graph_hash(G, node_attr='d', iterations=4))

def grow(fset, subsets, maxf):
    if len(fset) >= maxf: return
    for fi in fset:
        for g in fadj[fi]:
            if g not in fset:
                ns = frozenset(fset | {g})
                if ns not in subsets:
                    subsets.add(ns); grow(ns, subsets, maxf)


if __name__ == '__main__':
    RING_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    MAXF = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    subsets = set()
    for fi in interior:
        subsets.add(frozenset([fi])); grow(frozenset([fi]), subsets, MAXF)
    types = {}
    for fs in subsets:
        key = wl_key(fs)
        if key in types: continue
        t = disk_tangle(fs)
        if t is None: continue
        types[key] = (fs, t)
    print(f"interior faces {len(interior)}, connected subsets {len(subsets)}, distinct disk types {len(types)}", flush=True)
    out = []
    for key, (fs, (n, nv, E)) in sorted(types.items(), key=lambda kv: kv[1][1][0]):
        sizes = [len(faces[fi]) for fi in fs]
        if n > RING_MAX:
            print(json.dumps(dict(faces=sizes, ring=n, vertices=nv, skipped='ring > RING_MAX')), flush=True)
            out.append(dict(faces=sizes, ring=n, vertices=nv, reducible=None)); continue
        r = analyze_tangle(n, nv, E, del_max=3)
        r['faces'] = sizes; r['wl'] = key[1]
        print(json.dumps(r), flush=True); out.append(r)
    json.dump(out, open(f'pentaheptite_disks_ring{RING_MAX}.json', 'w'), indent=1)
    red = [r for r in out if r.get('reducible')]
    unk = [r for r in out if r.get('reducible') is None]
    print(f"SUMMARY: disk types {len(out)}, reducible {len(red)}, irreducible {len(out) - len(red) - len(unk)}, beyond scale {len(unk)}")
    print("OUTCOME:", ("PD1 reducible disks: " + str([(r['faces'], r['ring']) for r in red])) if red else "PD2 (no reducible bounded disk at this scale)")
