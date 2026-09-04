"""Boundary-word classification of the closed-web census.

Pre-registered question: does same-sector chord nesting (the drainage
failure) occur on closed webs whose hole boundary words are of the good
type (3,1,1), or only on (3,2,0)-type words?

Outcomes: B1 = nesting occurs on some (3,1,1)/(3,1,1) web -> the
good-word restriction does not rescue universal drainage.
B2 = nesting occurs only on webs with a (3,2,0) boundary -> the
good-word restriction is a genuine scope (deep branch alive there).
"""
import sys
import json
from collections import defaultdict, Counter
import sector_alternation_lab as L


def word(col, spoke_eids):
    c = Counter(col[e] for e in spoke_eids)
    return tuple(sorted((c[0], c[1], c[2]), reverse=True))


def run(name, expect_census, expect_closed):
    nbrs, edges, faces, pent_face_ids = L.build_small(name)
    pairs = L.find_polar_pentagons(faces, pent_face_ids, nbrs)
    result = None
    for (p1, p2) in pairs:
        tedges, v2e, spokes, caps = L.two_hole_tangle(nbrs, edges, faces, p1, p2)
        sols = L.enumerate_colorings(tedges, v2e, len(nbrs))
        if len(sols) == expect_census:
            result = (p1, p2, tedges, v2e, spokes, caps, sols)
            break
    assert result is not None, "calibration failed"
    p1, p2, tedges, v2e, spokes, caps, sols = result
    closed = [s for s in sols if L.closure_test(list(s), tedges, v2e, spokes)[0]]
    assert len(closed) == expect_closed, len(closed)
    table = defaultdict(lambda: {'webs': 0, 'nrails': Counter(), 'nested_webs': 0,
                                 'nested_pairs': 0, 'drain_bad': 0, 'max_depth': 0,
                                 'chords': 0})
    for s in closed:
        col = list(s)
        r = L.analyze_web(col, tedges, v2e, spokes, caps, len(nbrs), faces, {p1, p2})
        wi = word(col, spokes['inner'])
        wo = word(col, spokes['outer'])
        key = (wi, wo)
        t = table[key]
        t['webs'] += 1
        if not r['rails']:
            t['nrails']['fail'] += 1
            continue
        t['nrails'][r['nrails']] += 1
        t['chords'] += r['chords']
        if r['violations']:
            t['nested_webs'] += 1
        t['nested_pairs'] += len(r['violations'])
        t['drain_bad'] += len(r['drain_bad'])
        t['max_depth'] = max(t['max_depth'], r['nest_depth'])
    print(f"== {name}: census {len(sols)}, closed {len(closed)} ==")
    print("inner-word  outer-word  webs  rails{1,2,fail}  chords  nested-webs  nested-pairs  drain-bad  max-depth")
    out = {}
    for key in sorted(table):
        t = table[key]
        print(f"{key[0]}  {key[1]}  {t['webs']:4d}  {dict(t['nrails'])}  {t['chords']:5d}  "
              f"{t['nested_webs']:5d}  {t['nested_pairs']:5d}  {t['drain_bad']:5d}  {t['max_depth']}")
        out[str(key)] = {k: (dict(v) if isinstance(v, Counter) else v) for k, v in t.items()}
    good = [k for k in table if k[0] == (3, 1, 1) and k[1] == (3, 1, 1)]
    good_nested = sum(table[k]['nested_pairs'] for k in good)
    print(f"good-word (3,1,1)/(3,1,1) webs: {sum(table[k]['webs'] for k in good)}, "
          f"same-sector nested pairs on them: {good_nested}")
    print("OUTCOME:", "B1 (nesting on good words)" if good_nested else "B2 (nesting only off good words)")
    return out


if __name__ == '__main__':
    which = sys.argv[1:] or ['C30']
    res = {}
    if 'C30' in which:
        res['C30'] = run('C30', 5412, 360)
    if 'C40' in which:
        res['C40'] = run('C40', 31704, 720)
    with open('boundary_word_results.json', 'w') as fh:
        json.dump(res, fh, indent=1)
