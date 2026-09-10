#!/usr/bin/env python3
"""Falsifier harness for the two-deletion minimum-disagreement route, in the route's own
model: delete two separated adjacent pairs, colour each deletion graph properly (ports have
degree two), compare on the common core.

Statements about a *least counterexample* are vacuous (4CT holds), so they cannot be
refuted by example.  What is refutable is any lemma whose hypotheses are satisfiable in a
real planar cubic graph.  The satisfiable analogue of the absolute minimum is a
Kempe-orbit-restricted minimum: the route's own `AbsoluteMinimum.orbit_minima` says an
absolute minimum is in particular an orbit minimum, so every consequence of orbit
minimality holds at both.  Orbit minima with positive disagreement exist in colourable
graphs; they are the adversarial suite.

At each orbit minimiser with positive disagreement this checks:
  L0  every core vertex carries 0, 2 or 3 disagreeing edges;
  L1  every component of the disagreement subgraph that avoids the ports carries at least
      two jump types (equivalently contains a triple point);
  L2  every region (component of the dual cut along the disagreement) that avoids the port
      faces carries at least two jump types on its boundary;
and it measures the smallest such region and whether port-free walls occur at all.

L1 and L2 are the proposed lemmas; a violation refutes them.

Usage: blocked_minimum_lab.py PLANTRI N [--pairs k] [--cap c] [--out file.json]
"""
import sys, subprocess, json
from collections import deque

plantri, N = sys.argv[1], int(sys.argv[2])
PAIRS = int(sys.argv[sys.argv.index('--pairs') + 1]) if '--pairs' in sys.argv else 6
CAP = int(sys.argv[sys.argv.index('--cap') + 1]) if '--cap' in sys.argv else 3000
OUT = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None


def load(plantri, N):
    out = subprocess.run([plantri, '-a', '-d', '-c3', str(N)], capture_output=True)
    graphs = []
    for line in out.stdout.decode('utf-8', errors='ignore').strip().split('\n'):
        if not line.strip():
            continue
        head, body = line.split(' ', 1)
        graphs.append([[ord(ch) - ord('a') for ch in adj.strip()] for adj in body.split(',')])
    return graphs


def edge_list(rot):
    edges, eid = [], {}
    for u, nb in enumerate(rot):
        for v in nb:
            if u < v:
                eid[(u, v)] = eid[(v, u)] = len(edges)
                edges.append((u, v))
    return edges, eid


def faces(rot, eid):
    nxt = {}
    for v, nb in enumerate(rot):
        for i, u in enumerate(nb):
            nxt[(u, v)] = (v, nb[(i + 1) % len(nb)])
    seen, out = set(), []
    for d in nxt:
        if d in seen:
            continue
        cyc, x = [], d
        while x not in seen:
            seen.add(x)
            cyc.append(eid[x])
            x = nxt[x]
        out.append(cyc)
    return out


def deletion_colourings(edges, nv, dele, cap):
    """proper 3-edge-colourings of G - dele (dele = two adjacent vertices)"""
    live = [k for k, (u, v) in enumerate(edges) if u not in dele and v not in dele]
    inc = [[] for _ in range(nv)]
    for k in live:
        for z in edges[k]:
            inc[z].append(k)
    out, col = [], [-1] * len(edges)

    def rec(i):
        if len(out) >= cap:
            return
        if i == len(live):
            out.append(tuple(col))
            return
        k = live[i]
        for c in range(3):
            good = True
            for z in edges[k]:
                if any(col[j] == c for j in inc[z] if j != k and col[j] >= 0):
                    good = False
                    break
            if good:
                col[k] = c
                rec(i + 1)
        col[k] = -1

    rec(0)
    return out, live, inc


def chains(col, edges, live, inc, a, b):
    """components of the (a,b)-subgraph (paths at the degree-two ports, cycles elsewhere)"""
    sub = [k for k in live if col[k] in (a, b)]
    seen, out = set(), []
    for k0 in sub:
        if k0 in seen:
            continue
        comp, stack = set(), [k0]
        while stack:
            k = stack.pop()
            if k in comp:
                continue
            comp.add(k)
            for z in edges[k]:
                for j in inc[z]:
                    if j in comp or col[j] not in (a, b):
                        continue
                    stack.append(j)
        seen |= comp
        out.append(frozenset(comp))
    return out


def orbits(cols, edges, live, inc):
    idx = set(cols)
    seen, out = set(), []
    for c0 in cols:
        if c0 in seen:
            continue
        comp, q = set(), deque([c0])
        while q:
            c = q.popleft()
            if c in comp:
                continue
            comp.add(c)
            for a, b in ((0, 1), (0, 2), (1, 2)):
                for ch in chains(c, edges, live, inc, a, b):
                    d = list(c)
                    for k in ch:
                        d[k] = b if c[k] == a else a
                    d = tuple(d)
                    if d in idx and d not in comp:
                        q.append(d)
        seen |= comp
        out.append(sorted(comp))
    return out


def analyse(rot, edges, fs, core, ports, dele, c, d, portsA=frozenset(), portsB=frozenset()):
    wall = [k for k in core if c[k] != d[k]]
    typ = {k: frozenset((c[k], d[k])) for k in wall}
    deg = {}
    for k in wall:
        for z in edges[k]:
            deg[z] = deg.get(z, 0) + 1
    corev = [z for z in range(len(rot)) if z not in ports and z not in dele]
    l0 = all(deg.get(z, 0) in (0, 2, 3) for z in corev)
    inc = {}
    for k in wall:
        for z in edges[k]:
            inc.setdefault(z, []).append(k)
    seen, comps = set(), []
    for k0 in wall:
        if k0 in seen:
            continue
        comp, stack = set(), [k0]
        while stack:
            k = stack.pop()
            if k in comp:
                continue
            comp.add(k)
            for z in edges[k]:
                for j in inc[z]:
                    if j not in comp:
                        stack.append(j)
        seen |= comp
        comps.append(comp)
    free = [w for w in comps if not any(z in ports or z in dele for k in w for z in edges[k])]
    l1 = all(len({typ[k] for k in w}) >= 2 for w in free)
    side = {}
    for i, f in enumerate(fs):
        for k in f:
            side.setdefault(k, []).append(i)
    dadj = {i: [] for i in range(len(fs))}
    for k, ff in side.items():
        if len(ff) == 2 and k not in wall:
            dadj[ff[0]].append(ff[1])
            dadj[ff[1]].append(ff[0])
    seenf, regions = set(), []
    for i in range(len(fs)):
        if i in seenf:
            continue
        r, stack = set(), [i]
        while stack:
            x = stack.pop()
            if x in r:
                continue
            r.add(x)
            stack.extend(dadj[x])
        seenf |= r
        regions.append(r)
    bad = {i for i, f in enumerate(fs)
           if any(z in ports or z in dele for k in f for z in edges[k])}
    l2, small, freereg = True, None, 0
    for r in regions:
        if r & bad:
            continue
        bnd = [k for k in wall if len(side[k]) == 2 and (side[k][0] in r) != (side[k][1] in r)]
        if not bnd:
            continue
        freereg += 1
        if len({typ[k] for k in bnd}) < 2:
            l2 = False
        small = len(r) if small is None else min(small, len(r))
    # which sites each wall component is anchored to
    spans = 0
    for w in comps:
        vs = {z for k in w for z in edges[k]}
        hitA = bool(vs & portsA)
        hitB = bool(vs & portsB)
        if hitA and hitB:
            spans += 1
    return {"delta": len(wall), "L0": l0, "L1": l1, "L2": l2, "free_walls": len(free),
            "walls": len(comps), "spanning_walls": spans,
            "free_regions": freereg, "min_free_region": small,
            "triple_points": sum(1 for z, g in deg.items() if g == 3)}


graphs = load(plantri, N)
tot = {"graphs": len(graphs), "sites": 0, "orbit_pairs": 0, "positive": 0,
       "L0_fail": 0, "L1_fail": 0, "L2_fail": 0, "free_wall_cases": 0, "free_region_cases": 0,
       "walls_total": 0, "spanning_cases": 0}
sizes, deltas, specimens, dd = [], [], [], []
for gi, rot in enumerate(graphs):
    nv = len(rot)
    edges, eid = edge_list(rot)
    fs = faces(rot, eid)
    nbr = {v: set(rot[v]) for v in range(nv)}
    sites = []
    for k, (u, v) in enumerate(edges):
        for k2, (x, y) in list(enumerate(edges))[k + 1:]:
            A, B = {u, v}, {x, y}
            if A & B:
                continue
            # separated: no edge between the two closed neighbourhoods
            NA = A | nbr[u] | nbr[v]
            NB = B | nbr[x] | nbr[y]
            if NA & NB:
                continue
            sites.append((A, B))
    for A, B in sites[:PAIRS]:
        tot["sites"] += 1
        # distance between the two sites in G
        dist, seenv, frontier = 0, set(A), set(A)
        while frontier and not (frontier & B):
            frontier = {w for z in frontier for w in rot[z]} - seenv
            seenv |= frontier
            dist += 1
        cs, liveA, incA = deletion_colourings(edges, nv, A, CAP)
        ds, liveB, incB = deletion_colourings(edges, nv, B, CAP)
        if not cs or not ds:
            continue
        core = [k for k in range(len(edges))
                if not (set(edges[k]) & (A | B))]
        pA = set().union(*[nbr[z] for z in A]) - A
        pB = set().union(*[nbr[z] for z in B]) - B
        ports = (pA | pB) - A - B
        for C in orbits(cs, edges, liveA, incA):
            for D in orbits(ds, edges, liveB, incB):
                tot["orbit_pairs"] += 1
                best, arg = None, None
                for c in C:
                    for d in D:
                        delta = sum(1 for k in core if c[k] != d[k])
                        if best is None or delta < best:
                            best, arg = delta, (c, d)
                if best == 0:
                    continue
                tot["positive"] += 1
                deltas.append(best); dd.append((dist, best))
                r = analyse(rot, edges, fs, core, ports, A | B, *arg, portsA=pA, portsB=pB)
                for key in ("L0", "L1", "L2"):
                    if not r[key]:
                        tot[key + "_fail"] += 1
                tot["walls_total"] += r["walls"]
                if r["spanning_walls"]:
                    tot["spanning_cases"] += 1
                if r["free_walls"]:
                    tot["free_wall_cases"] += 1
                if r["free_regions"]:
                    tot["free_region_cases"] += 1
                if r["min_free_region"] is not None:
                    sizes.append(r["min_free_region"])
                if len(specimens) < 60:
                    specimens.append({"graph": gi, "rot": rot, "A": sorted(A), "B": sorted(B),
                                      "c": list(arg[0]), "d": list(arg[1]), **r})
print(f"cubic order {2*N-4}: graphs {tot['graphs']} separated sites {tot['sites']} "
      f"orbit pairs {tot['orbit_pairs']} positive minima {tot['positive']}")
print(f"  L0 failures {tot['L0_fail']}  L1 failures {tot['L1_fail']}  L2 failures {tot['L2_fail']}")
print(f"  minima with a port-free wall: {tot['free_wall_cases']}   with a port-free region: "
      f"{tot['free_region_cases']}")
if deltas:
    print(f"  disagreement at the minima: min {min(deltas)} median "
          f"{sorted(deltas)[len(deltas)//2]} max {max(deltas)}")
spanning = [sp for sp in tot.get("spanning", [])]
if tot["positive"]:
    print(f"  walls per minimum: {tot['walls_total']/tot['positive']:.1f}; "
          f"minima with a wall joining the two sites: {tot['spanning_cases']}")
if sizes:
    print(f"  smallest port-free region (faces): min {min(sizes)} median "
          f"{sorted(sizes)[len(sizes)//2]} max {max(sizes)}")
if dd:
    from collections import defaultdict
    by = defaultdict(list)
    for a, b in dd:
        by[a].append(b)
    print("  disagreement by site distance: " +
          "  ".join(f"d={k}: n={len(v)} min={min(v)} max={max(v)}" for k, v in sorted(by.items())))
if OUT:
    json.dump({"summary": tot, "region_sizes": sizes, "deltas": deltas, "dist_delta": dd,
               "specimens": specimens}, open(OUT, "w"), indent=1)
    print("wrote", OUT)
