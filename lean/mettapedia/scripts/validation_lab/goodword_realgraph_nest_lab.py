"""Real-graph nesting lab: on Ben's small graphs (C24/C30/C40), for EVERY
vertex-disjoint pentagon cap pair, take the totally closed webs at a good
inner word (three consecutive majority spokes in the cyclic order of the
inner hole, one each of the other two colours) and run the full
sector/chord analysis: same-path chords, same-sector nested pairs, interior
drainage failures, nest depth.

Pre-registered outcomes: N1 = some real-graph good-word closed web has a
same-sector nested pair / drainage failure -> Addendum XXVII(i) refuted on a
real graph at a good word (specimen saved).  N2 = chords occur but never
nest on any real good-word closed web in range -> nesting is not yet seen
on real graphs (the abstract V=14 family remains the only witness).

Run with the v24 toolchain directory on PYTHONPATH.
"""
import sys, json, time
from collections import Counter
import sector_alternation_lab as L


def cyclic_good(col, inner_spokes):
    """Three consecutive majority spokes (cyclically), one each of the others."""
    w = [col[e] for e in inner_spokes]
    if sorted(Counter(w).values(), reverse=True) != [3, 1, 1]:
        return False
    m = Counter(w).most_common(1)[0][0]
    n = len(w)
    return any(all(w[(s + t) % n] == m for t in range(3)) for s in range(n))


def sweep(name):
    t0 = time.time()
    nbrs, edges, faces, pent_face_ids = L.build_small(name)
    pents = list(pent_face_ids)
    fv = {f: set(faces[f][1]) for f in pents}
    tot = Counter(); depth_hist = Counter(); cert = None
    for i in range(len(pents)):
        for j in range(i + 1, len(pents)):
            p1, p2 = pents[i], pents[j]
            if fv[p1] & fv[p2]:
                continue
            tedges, v2e, spokes, caps = L.two_hole_tangle(nbrs, edges, faces, p1, p2)
            sols = L.enumerate_colorings(tedges, v2e, len(nbrs))
            tot['pairs'] += 1; tot['colourings'] += len(sols)
            for s in sols:
                col = list(s)
                ok, _ = L.closure_test(col, tedges, v2e, spokes)
                if not ok:
                    continue
                tot['closed'] += 1
                mult = tuple(sorted(Counter(col[e] for e in spokes['inner']).values(), reverse=True))
                if mult != (3, 1, 1):
                    continue
                tot['closed_311'] += 1
                good = cyclic_good(col, spokes['inner'])
                if not good:
                    continue
                tot['good_closed'] += 1
                r = L.analyze_web(col, tedges, v2e, spokes, caps, len(nbrs), faces, {p1, p2})
                if not r['rails']:
                    tot['rails_fail'] += 1; continue
                tot[f"rails{r['nrails']}"] += 1
                tot['chords'] += r['chords']
                if r['chords']: tot['good_with_chords'] += 1
                tot['nested_pairs'] += len(r['violations'])
                tot['drain_bad'] += len(r['drain_bad'])
                depth_hist[r['nest_depth']] += 1
                if r['violations']:
                    tot['webs_with_nest'] += 1
                    if cert is None or r['nest_depth'] > cert['depth']:
                        cert = dict(graph=name, caps=[p1, p2], coloring=col, depth=r['nest_depth'],
                                    n_sectors=r['n_sectors'], chords=r['chords'],
                                    violations=[str(v) for v in r['violations']],
                                    drain_bad=[str(d) for d in r['drain_bad']])
    dt = time.time() - t0
    print(f"{name}: pairs={tot['pairs']} colourings={tot['colourings']} closed={tot['closed']} "
          f"(3,1,1)={tot['closed_311']} cyclic-good={tot['good_closed']} rails-fail={tot['rails_fail']} "
          f"two-rail={tot['rails2']} one-rail={tot['rails1']} chords={tot['chords']} "
          f"webs-with-chords={tot['good_with_chords']} same-sector-nested-pairs={tot['nested_pairs']} "
          f"webs-with-nest={tot['webs_with_nest']} drain-bad={tot['drain_bad']} depth={dict(depth_hist)} [{dt:.0f}s]", flush=True)
    print("OUTCOME", name + ":", "N1 (same-sector nest on a real good-word closed web)" if tot['nested_pairs'] else "N2 (no nests)", flush=True)
    return dict(tot), dict(depth_hist), cert


if __name__ == '__main__':
    names = sys.argv[1:] or ['C24']
    out = {}
    for nm in names:
        t, h, c = sweep(nm)
        out[nm] = dict(stats=t, depth=h, certificate=c)
        json.dump(out, open(f'goodword_realgraph_nest_{"_".join(names)}.json', 'w'), indent=1)
