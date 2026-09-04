"""Growth check for the D1b gate: does the longest exact saturated separating
chain grow with size on tubes (corridor) and stay flat on Goldberg spheres
(wall branch)?  Tube instances are built with the cap pendants removed
(the generator's tangle omits the cap cycles), holes = the two boundary
rings.  Pre-registered: m_tube(L) grows linearly in L at width 6..8;
m_GP(k) at width <= 8 does not grow with k.
"""
import sys, json, time
from cut_chain_lab import Map, analyze, goldberg_map, make_tube_annulus


def tube_map_nopendant(L):
    inst = make_tube_annulus(L)
    tri = inst['dual_triangles']; n = len(tri)
    inner = set(inst['inner_face_vertices']); outer = set(inst['outer_face_vertices'])
    edges = [tuple(e) for e in inst['tangle_edges']]
    deg = {}
    for u, v in edges:
        deg[u] = deg.get(u, 0) + 1; deg[v] = deg.get(v, 0) + 1
    pend = {v for v in range(n) if deg.get(v, 0) == 1}
    keep = [v for v in range(n) if v not in pend]
    idx = {v: i for i, v in enumerate(keep)}
    E = [(idx[u], idx[v]) for (u, v) in edges if u not in pend and v not in pend]
    T = [tri[v] for v in keep]
    A = {idx[w] for (u, v) in edges for w in (u, v) if (u in pend and u in inner and w == v) or (v in pend and v in inner and w == u)}
    B = {idx[w] for (u, v) in edges for w in (u, v) if (u in pend and u in outer and w == v) or (v in pend and v in outer and w == u)}
    holes = set()
    for grp in (inner, outer):
        common = None
        for v in grp:
            s = set(tri[v]); common = s if common is None else common & s
        if common: holes |= common
    return Map(len(keep), E, T, A, B, holes)


if __name__ == '__main__':
    which = sys.argv[1]
    out = []
    if which == 'tubes':
        for L in [2, 4, 6, 8, 10]:
            r = analyze(tube_map_nopendant(L), f"tube(5,0) L={L} (no pendants)", [6, 8], exhaustive=True)
            print(json.dumps({k: r[k] for k in ('name', 'V', 'frontier', 'exhaustive', 'exhaustive_seconds')}), flush=True); out.append(r)
    else:
        for k in [2, 3, 4]:
            bl = [6, 8, 10] if k <= 3 else [6, 8]
            r = analyze(goldberg_map(k), f"GP({k},0)", bl, exhaustive=True)
            print(json.dumps({k_: r[k_] for k_ in ('name', 'V', 'exhaustive', 'exhaustive_seconds')}), flush=True); out.append(r)
    json.dump(out, open(f'cut_chain_growth_{which}.json', 'w'), indent=1)
