"""Intermediate pentaheptite disks (4..MAXF faces, ring in [RMIN, RMAX]):
enumerate connected face unions of the pentaheptite tiling, dedupe by WL
hash, export tangles, and rank by cheap metrics: support fraction of
admissible words, best sampled cap coverage, depth-1 Kempe growth.
Pre-registered: candidates with high cap coverage AND positive growth go
to the full closure engine (closure + caps + deletions)."""
import sys, json, random, time, math
from collections import Counter, defaultdict
import networkx as nx
sys.path.insert(0, '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp')
from kempe import noncrossing
import pentaheptite_disks_lab as P
from cap_zero_kempe_test import Extender, word_of
from kempe_goal_directed import Closure
RMIN, RMAX, MAXF = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
faces, fadj, interior = P.faces, P.fadj, P.interior
subsets = set()
def grow(fs):
    if len(fs) >= MAXF: return
    for fi in fs:
        for g in fadj[fi]:
            if g not in fs:
                ns = frozenset(fs | {g})
                if ns not in subsets:
                    subsets.add(ns); grow(ns)
# seed from a few central faces only (types repeat by periodicity)
def cd(f): return sum(math.hypot(*P.vpos[u]) for (u, v) in faces[f]) / len(faces[f])
seeds = sorted(interior, key=cd)[:6]
for f in seeds:
    subsets.add(frozenset([f])); grow(frozenset([f]))
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
print(f"subsets {len(subsets)}, disk types with ring in [{RMIN},{RMAX}]: {len(types)}", flush=True)
rng = random.Random(9)
def admissible(w):
    c = [w.count(t) for t in range(3)]
    return c[0] % 2 == c[1] % 2 == c[2] % 2
rows = []
for key, (fs, (n, nv, E)) in sorted(types.items(), key=lambda kv: kv[1][1][0]):
    X = Extender(n, nv, E); C = Closure(X, n)
    # support fraction
    tot = ext = 0
    while tot < 600:
        w = tuple(rng.randrange(3) for _ in range(n))
        if not admissible(w): continue
        tot += 1; ext += C.in_supp(w)
    # best sampled cap coverage
    caps = noncrossing(list(range(n))) if n % 2 == 0 else []
    best = 0.0; bestmu = None
    for mu in caps:
        k = sum(X.extends(word_of(mu, [rng.randrange(3) for _ in range(n // 2)], n)) for _ in range(30))
        if k / 30 > best: best, bestmu = k / 30, mu
    # depth-1 growth
    tested = good = 0; deadline = time.time() + 60
    while tested < 150 and time.time() < deadline:
        w = tuple(rng.randrange(3) for _ in range(n))
        if not admissible(w) or C.in_supp(w): continue
        tested += 1; good += bool(C.good(w, 1, deadline))
    row = dict(faces=sorted(len(faces[f]) for f in fs), ring=n, vertices=nv, supp_frac=round(ext / tot, 3),
               best_cap=best, best_cap_mu=bestmu, growth1=round(good / max(1, tested), 3), wl=key[1])
    rows.append(row)
    json.dump(dict(n=n, nv=nv, edges=[[list(z) if isinstance(z, tuple) else z for z in e] for e in E], faces=row['faces']),
              open(f"pentaheptite_mid_{key[1][:10]}.json", 'w'))
    print(json.dumps({k: v for k, v in row.items() if k != 'best_cap_mu'}), flush=True)
json.dump(rows, open(f'pentaheptite_mid_disks_r{RMIN}_{RMAX}.json', 'w'), indent=1)
rows.sort(key=lambda r: -(r['best_cap'] + r['growth1']))
print("TOP candidates:", [(r['faces'], r['ring'], r['best_cap'], r['growth1'], r['wl'][:10]) for r in rows[:6]])
