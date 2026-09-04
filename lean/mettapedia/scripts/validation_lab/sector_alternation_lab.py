#!/usr/bin/env python3
"""Sector-Alternation small-case lab (Knuth gate for the 4CP closed-web layer).

PRE-REGISTERED QUESTION (fixed before running).  Addendum XXVII(i) of the
v24 working notes claims: in the closed-web graph B1 u B2 u alpha, every
same-path chord's disk drains -- each interior vertex of the chord's
B-sub-arc sends its alpha-edge OUT of the disk, to the opposite sector;
hence same-sector nesting is impossible and nests alternate sectors.
The Lean rainbow fence proved noncrossing+laminarity alone bound nothing;
this lab tests the STRONGER drainage invariant on the actual census.

PRE-REGISTERED CALIBRATION (must all hit or the lab is void):
  (K0) C30 two-hole census size = 5412 colorings;
  (K1) totally-closed webs (Addendum VIII test) = 360;
  (K2) same-path chord count across the 360 webs = 460.
PRE-REGISTERED VERDICTS:
  (V1) Sector-Alternation holds on all webs (zero same-sector nested
       chord pairs, every interior vertex drains out) -> invariant
       CONFIRMED on the census; formalization is justified; report the
       measured alternation depth and interface widths (keystone data).
  (V2) any violation -> the violating (web, chord, vertex) is THE
       deliverable: a concrete counterexample to the repaired invariant.

Closure test implemented from Addendum VIII verbatim:
  strand = 2-color Kempe component; inner-touching = contains an inner
  spoke edge; web W = union of inner-touching strands' edges; totally
  closed = every edge of W has BOTH its containing components
  inner-touching.

B-structure per closed web: the distinguished color a is the one whose
complementary two colors' edge union forms exactly two disjoint paths
(the rails B1, B2) spanning all internal vertices, each running from an
inner pendant to an outer pendant.  Sectors: components of the face
adjacency after cutting along rail edges and pendant (spoke) edges.
Same-path chord: an a-edge with both endpoints internal on one rail.
Its sector is the sector of its incident faces.  Violation: two
same-path chords on one rail, nested along the rail order, in the SAME
sector; or an interior vertex whose alpha-edge is a same-sector chord
landing inside.  (A radial a-edge or an opposite-sector chord drains.)

Run: nice -n 19 python3 sector_alternation_lab.py
"""

import json
import sys
from collections import defaultdict, deque

from smallful import build_small
from lift_lab import two_hole_tangle, components_of
from census import enumerate_colorings


def find_polar_pentagons(faces, pent_face_ids, nbrs):
    """Return the pair of vertex-disjoint pentagon faces (the tube poles)."""
    pairs = []
    for i in pent_face_ids:
        for j in pent_face_ids:
            if i < j and not (set(faces[i][1]) & set(faces[j][1])):
                pairs.append((i, j))
    return pairs


def closure_test(col, tedges, v2e, spokes):
    m = len(tedges)
    comps = components_of(col, tedges, v2e, m)
    inner_set = set(spokes['inner'])
    inner_touching = []
    for (pair, ce, cv) in comps:
        if ce & inner_set:
            inner_touching.append((pair, ce))
    web_edges = set()
    for (_pair, ce) in inner_touching:
        web_edges |= ce
    if not web_edges:
        return False, web_edges
    # each edge lies in exactly two components (its color with each other色)
    touching_pairs = {}
    for (pair, ce, _cv) in comps:
        for e in ce:
            touching_pairs.setdefault(e, []).append(
                (pair, bool(ce & inner_set)))
    for e in web_edges:
        entries = touching_pairs.get(e, [])
        if len(entries) != 2 or not all(t for (_p, t) in entries):
            return False, web_edges
    return True, web_edges


def rails_of(col, tedges, v2e, spokes, n_vertices, pendant):
    """For each candidate color a, test whether the other two colors form
    exactly two disjoint internal paths from inner to outer pendants."""
    for a in (0, 1, 2):
        rail_edges = [ei for ei in range(len(tedges)) if col[ei] != a]
        deg = defaultdict(int)
        adj = defaultdict(list)
        for ei in rail_edges:
            u, v = tedges[ei]
            deg[u] += 1
            deg[v] += 1
            adj[u].append((v, ei))
            adj[v].append((u, ei))
        # trace components of the rail graph
        seen = set()
        paths = []
        ok = True
        for start in list(adj.keys()):
            if start in seen or deg[start] != 1:
                continue
            path = [start]
            seen.add(start)
            prev = None
            cur = start
            while True:
                nxts = [w for (w, _e) in adj[cur] if w != prev]
                if not nxts:
                    break
                if len([w for (w, _e) in adj[cur] if w != prev]) > 1 and cur != start:
                    ok = False
                    break
                nxt = nxts[0]
                prev, cur = cur, nxt
                path.append(cur)
                seen.add(cur)
                if deg[cur] == 1:
                    break
            paths.append(path)
        if not ok:
            continue
        if len(seen) != len(adj):
            continue  # a cycle component exists
        # want exactly two paths, each with pendant endpoints on both holes
        real = [p for p in paths if len(p) >= 2]
        if len(real) not in (1, 2):
            continue
        good = True
        for p in real:
            ends = [p[0], p[-1]]
            if not all(v in pendant for v in ends):
                good = False
        if not good:
            continue
        internal = set(v for v in range(n_vertices)
                       if v not in pendant) & set(
            v for p in real for v in p)
        allint = set(v for v in range(n_vertices) if v not in pendant
                     and any(True for _ in v2e[v]))
        if internal != allint:
            continue
        return a, real
    return None, None


def face_sectors(tedges, faces_t, rail_eids, spoke_eids):
    """Components of face adjacency not crossing rail or spoke edges."""
    e2f = defaultdict(list)
    for fi, fedges in enumerate(faces_t):
        for e in fedges:
            e2f[e].append(fi)
    barrier = set(rail_eids)  # only rails bound sectors; a-spokes lie inside
    parent = list(range(len(faces_t)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for e, fs in e2f.items():
        if e in barrier or len(fs) != 2:
            continue
        ra, rb = find(fs[0]), find(fs[1])
        if ra != rb:
            parent[ra] = rb
    sector = {}
    for fi in range(len(faces_t)):
        sector[fi] = find(fi)
    return sector, e2f


def tangle_faces(nbrs, tedges, dropped_faces, faces):
    """Faces of the tangle = fullerene faces minus the two caps, with each
    face as the set of its tangle edge ids."""
    eidx = {e: i for i, e in enumerate(tedges)}
    out = []
    for fi, (flen, cyc) in enumerate(faces):
        if fi in dropped_faces:
            continue
        es = []
        k = len(cyc)
        for i in range(k):
            a, b = cyc[i], cyc[(i + 1) % k]
            key = (min(a, b), max(a, b))
            if key in eidx:
                es.append(eidx[key])
        out.append(es)
    return out


def analyze_web(col, tedges, v2e, spokes, caps, n, faces, cap_faces):
    pendant = set(caps['outer']) | set(caps['inner'])
    a, rails = rails_of(col, tedges, v2e, spokes, n, pendant)
    if a is None:
        return {'rails': False}
    rail_vids = [set(p) for p in rails]
    rail_order = [{v: i for i, v in enumerate(p)} for p in rails]
    nrails = len(rails)
    rail_eids = set()
    for ei in range(len(tedges)):
        if col[ei] != a:
            rail_eids.add(ei)
    spoke_eids = set(spokes['outer']) | set(spokes['inner'])
    ftang = tangle_faces(None, tedges, cap_faces, faces)
    sector, e2f = face_sectors(tedges, ftang, rail_eids, spoke_eids)
    n_sectors = len(set(sector.values()))
    chords = []  # (rail_index, lo, hi, sector_id, eid)
    radial = 0
    feet = 0
    for ei in range(len(tedges)):
        if col[ei] != a or ei in spoke_eids:
            continue
        u, v = tedges[ei]
        if u in pendant or v in pendant:
            feet += 1
            continue
        ru = 0 if u in rail_vids[0] else 1
        rv = 0 if v in rail_vids[0] else 1
        if nrails == 1:
            ru = rv = 0
        if ru != rv:
            radial += 1
            continue
        o = rail_order[ru]
        lo, hi = sorted((o[u], o[v]))
        fs = e2f.get(ei, [])
        sec = sector[fs[0]] if fs else -1
        sec2 = sector[fs[1]] if len(fs) > 1 else sec
        chords.append((ru, lo, hi, sec, sec2, ei))
    # violations: same-rail nested pair with a COMMON sector on the nested side
    violations = []
    for i in range(len(chords)):
        for j in range(len(chords)):
            if i == j:
                continue
            r1, lo1, hi1, s1a, s1b, e1 = chords[i]
            r2, lo2, hi2, s2a, s2b, e2 = chords[j]
            if r1 != r2:
                continue
            if lo1 < lo2 and hi2 < hi1:  # j strictly nested in i
                if {s1a, s1b} & {s2a, s2b}:
                    violations.append((chords[i], chords[j]))
    # interior drainage: every interior vertex of each chord's sub-arc
    drain_bad = []
    for (r, lo, hi, sa, sb, ei) in chords:
        for pos in range(lo + 1, hi):
            w = rails[r][pos]
            aedges = [e for e in v2e[w] if col[e] == a]
            for e in aedges:
                u2, v2_ = tedges[e]
                other = v2_ if u2 == w else u2
                if other in rail_vids[r] and e != ei:
                    o = rail_order[r]
                    if lo < o[other] < hi:
                        fs = e2f.get(e, [])
                        osec = {sector[f] for f in fs}
                        if {sa, sb} & osec:
                            drain_bad.append((ei, e, w))
    # alternation depth: longest nested chain of same-rail chords
    depth = 0
    for r in range(nrails):
        cs = sorted([c for c in chords if c[0] == r], key=lambda c: (c[1], -c[2]))
        best = {}
        for idx, c in enumerate(cs):
            best[idx] = 1
            for jdx in range(idx):
                cj = cs[jdx]
                if cj[1] < c[1] and c[2] < cj[2]:
                    best[idx] = max(best[idx], best[jdx] + 1)
            depth = max(depth, best[idx])
    return {'rails': True, 'a': a, 'nrails': nrails,
            'n_sectors': n_sectors,
            'chords': len(chords), 'radial': radial, 'feet': feet,
            'violations': violations, 'drain_bad': drain_bad,
            'nest_depth': depth}


def main() -> int:
    nbrs, edges, faces, pent_face_ids = build_small('C30')
    pairs = find_polar_pentagons(faces, pent_face_ids, nbrs)
    result = None
    for (p1, p2) in pairs:
        tedges, v2e, spokes, caps = two_hole_tangle(nbrs, edges, faces, p1, p2)
        sols = enumerate_colorings(tedges, v2e, len(nbrs))
        if len(sols) == 5412:
            result = (p1, p2, tedges, v2e, spokes, caps, sols)
            break
    if result is None:
        print("CALIBRATION K0 FAILED: no polar pair gives 5412 colorings")
        for (p1, p2) in pairs[:6]:
            tedges, v2e, spokes, caps = two_hole_tangle(nbrs, edges, faces, p1, p2)
            sols = enumerate_colorings(tedges, v2e, len(nbrs))
            print(f"  pair ({p1},{p2}): {len(sols)}")
        return 1
    p1, p2, tedges, v2e, spokes, caps, sols = result
    print(f"K0 OK: caps ({p1},{p2}), census {len(sols)}")
    closed = []
    for s in sols:
        ok, web = closure_test(list(s), tedges, v2e, spokes)
        if ok:
            closed.append(s)
    print(f"K1: totally closed webs = {len(closed)} (expect 360)")
    stats = {'chords': 0, 'violations': 0, 'drain_bad': 0,
             'max_depth': 0, 'rails_fail': 0, 'sector_counts': defaultdict(int)}
    examples = []
    for s in closed:
        r = analyze_web(list(s), tedges, v2e, spokes, caps, len(nbrs),
                        faces, {p1, p2})
        if not r['rails']:
            stats['rails_fail'] += 1
            continue
        stats.setdefault('by_nrails', defaultdict(lambda: {'webs':0,'chords':0,'viol':0,'drain':0,'depth':0}))
        b = stats['by_nrails'][r['nrails']]
        b['webs'] += 1; b['chords'] += r['chords']; b['viol'] += len(r['violations'])
        b['drain'] += len(r['drain_bad']); b['depth'] = max(b['depth'], r['nest_depth'])
        stats['chords'] += r['chords']
        stats['violations'] += len(r['violations'])
        stats['drain_bad'] += len(r['drain_bad'])
        stats['max_depth'] = max(stats['max_depth'], r['nest_depth'])
        stats['sector_counts'][r['n_sectors']] += 1
        if r['violations'] or r['drain_bad']:
            examples.append({'coloring': list(s),
                             'violations': [str(v) for v in r['violations']],
                             'drain_bad': [str(d) for d in r['drain_bad']]})
    print(f"rails identified: {len(closed) - stats['rails_fail']}/{len(closed)}"
          f" (fail {stats['rails_fail']})")
    print(f"K2: same-path chords total = {stats['chords']} (expect 460)")
    print(f"sector-count histogram: {dict(stats['sector_counts'])}")
    for k, b in sorted(stats['by_nrails'].items()):
        print(f"  rails={k}: webs={b['webs']} chords={b['chords']} same-sector-nests={b['viol']} drain-violations={b['drain']} max-depth={b['depth']}")
    print(f"VERDICT: same-sector nested pairs = {stats['violations']}, "
          f"interior drainage violations = {stats['drain_bad']}, "
          f"max nest depth = {stats['max_depth']}")
    with open('sector_alternation_results.json', 'w') as fh:
        json.dump({'census': len(sols), 'closed': len(closed),
                   'chords': stats['chords'],
                   'violations': stats['violations'],
                   'drain_bad': stats['drain_bad'],
                   'max_depth': stats['max_depth'],
                   'rails_fail': stats['rails_fail'],
                   'examples': examples[:10]}, fh, indent=1)
    print("wrote sector_alternation_results.json")
    return 0


if __name__ == '__main__':
    sys.exit(main())
