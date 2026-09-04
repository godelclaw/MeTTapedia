"""Knuth gate on the lemma's actual objects: good-word closed webs.

Population: the six totally closed webs at a good inner word on C30 with
non-polar caps (4,12) (the clean annular GWCO witness), colourings from
gwco_candidate_c30_caps_4_12.json, re-analysed with the census pipeline.

Pre-registered outcomes: G1 = some good-word closed web has a same-sector
nested chord pair / drainage failure -> the Sector-Alternation Lemma fails
on its own target population.  G2 = none -> universal drainage holds on
every known real-graph good-word closed web (deep branch alive there).

Run with the v24 toolchain directory (smallful.py, lift_lab.py, census.py) on
PYTHONPATH, e.g. PYTHONPATH=<4ct_toolchain dir> nice -n 19 python3 <this file>
"""
import json
from collections import Counter
import sector_alternation_lab as L

J = '/home/oruzi/repos/ai-agents/lean/private/4cp-numerics/gwco_candidate_c30_caps_4_12.json'
d = json.load(open(J))
p1, p2 = d['caps']
nbrs, edges, faces, pent_face_ids = L.build_small('C30')
tedges, v2e, spokes, caps = L.two_hole_tangle(nbrs, edges, faces, p1, p2)
mine = {tuple(sorted(e)): i for i, e in enumerate(tedges)}
theirs = [tuple(sorted(e)) for e in d['tedges']]
assert set(mine) == set(theirs), "tangle edge sets differ"
perm = [mine[e] for e in theirs]  # their index -> my index


def word(col, spoke_eids):
    c = Counter(col[e] for e in spoke_eids)
    return tuple(sorted((c[0], c[1], c[2]), reverse=True))


webs = d['closed_webs_at_good_inner_word']
print(f"C30 caps {p1},{p2}: {len(webs)} good-inner-word closed webs from json; tangle edges {len(tedges)}")
g1 = 0
for k, wcol in enumerate(webs):
    col = [None] * len(tedges)
    for j, cval in enumerate(wcol):
        col[perm[j]] = cval
    ok, web = L.closure_test(col, tedges, v2e, spokes)
    r = L.analyze_web(col, tedges, v2e, spokes, caps, len(nbrs), faces, {p1, p2})
    wi, wo = word(col, spokes['inner']), word(col, spokes['outer'])
    print(f" web {k}: closed={ok} inner={wi} outer={wo} rails={r.get('nrails')} sectors={r.get('n_sectors')} "
          f"chords={r.get('chords')} radial={r.get('radial')} feet={r.get('feet')} "
          f"nested-same-sector={len(r.get('violations', []))} drain-bad={len(r.get('drain_bad', []))} depth={r.get('nest_depth')}")
    if r.get('violations') or r.get('drain_bad'):
        g1 += 1
print("OUTCOME:", "G1 (drainage fails on a good-word closed web)" if g1 else "G2 (universal drainage holds on all six)")
