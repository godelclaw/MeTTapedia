"""Real-graph sweep: are good-word totally closed webs always chord-free?

For each of Ben's small graphs (C24, C30, C40) and EVERY vertex-disjoint pair
of pentagon caps (proper annulus), enumerate all proper tangle colourings,
keep the totally closed webs (Addendum VIII), keep those whose inner word has
multiplicities (3,1,1), and count same-path alpha chords (an alpha edge with
both endpoints internal on one rail).

Pre-registered outcomes: R1 = some real-graph good-word closed web has a
chord -> the "ladder" claim is false; that specimen is the deliverable.
R2 = no chord on any such web across all cap pairs -> strong evidence for
"good-word total closure => every internal alpha edge radial"; a proof
attempt is warranted.

Run with the v24 toolchain directory on PYTHONPATH.
"""
import sys, json, time
from collections import Counter, defaultdict
import sector_alternation_lab as L


def word(col, spoke_eids):
    c = Counter(col[e] for e in spoke_eids)
    return tuple(sorted((c[0], c[1], c[2]), reverse=True))


def chord_count(col, tedges, v2e, spokes, n, pend):
    a, rails = L.rails_of(col, tedges, v2e, spokes, n, pend)
    if a is None:
        return None, None
    rv = [set(p) for p in rails]
    spoke_eids = set(spokes['inner']) | set(spokes['outer'])
    chords = 0
    for ei, (u, v) in enumerate(tedges):
        if col[ei] != a or ei in spoke_eids or u in pend or v in pend:
            continue
        ru = [i for i, s in enumerate(rv) if u in s]
        rvv = [i for i, s in enumerate(rv) if v in s]
        if ru and rvv and ru[0] == rvv[0]:
            chords += 1
    return chords, len(rails)


def sweep(name):
    t0 = time.time()
    nbrs, edges, faces, pent_face_ids = L.build_small(name)
    pents = list(pent_face_ids)
    fv = {f: set(faces[f][1]) for f in pents}
    tot = Counter(); specimens = []
    pairs_done = 0
    for i in range(len(pents)):
        for j in range(i + 1, len(pents)):
            p1, p2 = pents[i], pents[j]
            if fv[p1] & fv[p2]:
                continue  # caps must be vertex-disjoint
            try:
                tedges, v2e, spokes, caps = L.two_hole_tangle(nbrs, edges, faces, p1, p2)
            except Exception as ex:
                tot['pair_build_fail'] += 1
                continue
            pend = set(caps['outer']) | set(caps['inner'])
            sols = L.enumerate_colorings(tedges, v2e, len(nbrs))
            pairs_done += 1
            tot['colourings'] += len(sols)
            for s in sols:
                col = list(s)
                ok, _ = L.closure_test(col, tedges, v2e, spokes)
                if not ok:
                    continue
                tot['closed'] += 1
                wi = word(col, spokes['inner']); wo = word(col, spokes['outer'])
                if wi != (3, 1, 1):
                    continue
                tot['good_closed'] += 1
                ch, nr = chord_count(col, tedges, v2e, spokes, len(nbrs), pend)
                if ch is None:
                    tot['rails_fail'] += 1
                    continue
                tot[f'rails{nr}'] += 1
                if ch:
                    tot['good_with_chords'] += 1
                    tot['max_chords'] = max(tot['max_chords'], ch)
                    if len(specimens) < 5:
                        specimens.append(dict(graph=name, caps=[p1, p2], coloring=col, chords=ch,
                                              inner=wi, outer=wo))
    dt = time.time() - t0
    print(f"{name}: pairs={pairs_done} colourings={tot['colourings']} closed={tot['closed']} "
          f"good-word closed={tot['good_closed']} with chords={tot['good_with_chords']} "
          f"max chords={tot['max_chords']} rails-fail={tot['rails_fail']} "
          f"two-rail={tot['rails2']} one-rail={tot['rails1']} [{dt:.0f}s]", flush=True)
    return dict(tot), specimens


if __name__ == '__main__':
    names = sys.argv[1:] or ['C24', 'C30']
    out = {}
    for nm in names:
        t, sp = sweep(nm)
        out[nm] = dict(stats=t, specimens=sp)
        print("OUTCOME", nm + ":", "R1 (chords on a real good-word closed web)" if t.get('good_with_chords') else "R2 (chord-free)", flush=True)
        json.dump(out, open('goodword_realgraph_chord_sweep.json', 'w'), indent=1)
