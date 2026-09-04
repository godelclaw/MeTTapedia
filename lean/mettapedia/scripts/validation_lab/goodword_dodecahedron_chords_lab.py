"""Chord census on the dodecahedral good-word closed webs (the smallest
real-graph GWCO witnesses: dodecahedron minus two non-adjacent pentagon caps,
10 internal vertices, 12 totally closed webs at a good inner word).

Question: does any of these closed webs carry a same-path alpha chord (an
alpha edge with both endpoints on one B-rail)?  Without chords the
Sector-Alternation / drainage layer has nothing to act on.

Input: the GWCO witness JSON (graph, tangle edges, spokes, caps, colourings).
Uses the census pipeline's closure test and rail extraction only (no faces
needed for a chord count).

Run with the v24 toolchain directory (smallful.py, lift_lab.py, census.py) on
PYTHONPATH, e.g. PYTHONPATH=<4ct_toolchain dir> nice -n 19 python3 <this file>
"""
import sys
import json
from collections import Counter, defaultdict
import sector_alternation_lab as L

J = sys.argv[1] if len(sys.argv) > 1 else 'gwco_counterexample_dodecahedron_caps_0_3.json'
d = json.load(open(J))
tedges = [tuple(e) for e in d['tedges']]
n = len(d['nbrs'])
v2e = defaultdict(list)
for i, (u, v) in enumerate(tedges):
    v2e[u].append(i); v2e[v].append(i)
spokes = {'inner': d['inner_spokes'], 'outer': d['outer_spokes']}
spoke_eids = set(spokes['inner']) | set(spokes['outer'])
pend = set(d['inner_cap']) | set(d['outer_cap'])
webs = d['closed_webs_at_good_inner_word']
print(f"{d['graph']} caps {d['caps']}: tangle edges {len(tedges)}, good-inner-word closed webs {len(webs)}")
total_chords = 0
for k, col in enumerate(webs):
    col = list(col)
    ok, _ = L.closure_test(col, tedges, v2e, spokes)
    a, rails = L.rails_of(col, tedges, v2e, spokes, n, pend)
    wi = tuple(sorted(Counter(col[e] for e in spokes['inner']).values(), reverse=True))
    wo = tuple(sorted(Counter(col[e] for e in spokes['outer']).values(), reverse=True))
    if a is None:
        print(f" web {k}: closed={ok} rails=FAIL"); continue
    rv = [set(p) for p in rails]
    chords = radial = 0
    for ei, (u, v) in enumerate(tedges):
        if col[ei] != a or ei in spoke_eids or u in pend or v in pend:
            continue
        ru = [i for i, s in enumerate(rv) if u in s]
        rvv = [i for i, s in enumerate(rv) if v in s]
        if ru and rvv and ru[0] == rvv[0]:
            chords += 1
        else:
            radial += 1
    total_chords += chords
    print(f" web {k}: closed={ok} inner={wi} outer={wo} a={a} rails={len(rails)} "
          f"lens={[len(p) for p in rails]} chords={chords} radial={radial}")
print("OUTCOME:", "chords present" if total_chords else "chord-free (all internal alpha edges radial)")
