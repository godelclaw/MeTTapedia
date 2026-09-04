"""Sector-Alternation Lemma (Addendum XXVII(i)) on GOOD-WORD closed webs of the
width-two annular family (the GWCO counterexample family, 5 inner + 5 outer
stubs, two B-paths, alpha chords given as explicit noncrossing matchings on the
two sector boundaries S and T).

For every valid (graph, colouring) at a GOOD inner word with all strands
radial (= totally closed web), test each same-path chord c=(lo,hi) drawn in
sector X in {S,T}:
  * a nested same-path chord (lo<lo'<hi'<hi) drawn in the SAME sector X is a
    same-sector nest = drainage failure (the lemma says impossible);
  * a nested chord drawn in the OTHER sector is the alternation the lemma
    predicts.
Pre-registered outcomes: W1 = some good-word closed web has a same-sector
nest -> lemma fails on its target population.  W2 = none, but opposite-sector
nests occur -> alternation structure confirmed on this family.  W3 = no nests
at all -> lemma vacuous on this family (chords never nest).
"""
import sys, time, json
from collections import Counter, defaultdict
sys.path.insert(0, __import__("os").environ.get("CLOSED_WEB_ENUM_DIR", "."))
import closed_web_enum as E


def chords_of(prs, p):
    out = []
    for (x, y) in prs:
        if isinstance(x, int) and isinstance(y, int) and ((x < p) == (y < p)):
            out.append((min(x, y), max(x, y)))
    return out


def run(V):
    t0 = time.time()
    stats = Counter()
    depth_hist = Counter()
    example = None
    n_struct = 0
    for p in range(1, V):
        q = V - p
        B1 = list(range(p)); B2 = list(range(p, p + q))
        same_path = lambda x, y: (x < p) == (y < p)
        for kin in range(4):
            for kout in range(4):
                IaS = ['Ia%d' % i for i in range(kin)]; IaT = ['Ia%d' % i for i in range(kin, 3)]
                OaS = ['Oa%d' % i for i in range(kout)]; OaT = ['Oa%d' % i for i in range(kout, 3)]
                ptsS = B1 + OaS + B2[::-1] + IaS[::-1]
                ptsT = B2 + OaT + B1[::-1] + IaT[::-1]
                optS = set(B1 + B2); optT = set(B1 + B2)
                byT = defaultdict(list)
                for usedT, prsT in E.noncrossing_matchings(ptsT, optT, same_path):
                    byT[frozenset(v for v in usedT if isinstance(v, int))].append(prsT)
                allV = frozenset(B1 + B2)
                for usedS, prsS in E.noncrossing_matchings(ptsS, optS, same_path):
                    intS = frozenset(v for v in usedS if isinstance(v, int))
                    need = allV - intS
                    if need not in byT: continue
                    for prsT in byT[need]:
                        n_struct += 1
                        r = E.build_and_check(p, q, kin, kout, list(prsS), list(prsT))
                        if r is None: continue
                        goods = [c for c in r['colourings'] if c[3]]
                        if not goods: continue
                        cS = chords_of(prsS, p); cT = chords_of(prsT, p)
                        same_nest = 0; opp_nest = 0; depth = 0
                        allc = [(c, 'S') for c in cS] + [(c, 'T') for c in cT]
                        for (c1, s1) in allc:
                            for (c2, s2) in allc:
                                if c1 == c2: continue
                                if c1[0] < c2[0] and c2[1] < c1[1]:
                                    if s1 == s2: same_nest += 1
                                    else: opp_nest += 1
                        # nest depth (longest chain, any sector)
                        cs = sorted([c for c, _ in allc], key=lambda c: (c[0], -c[1]))
                        best = [1] * len(cs)
                        for i in range(len(cs)):
                            for j in range(i):
                                if cs[j][0] < cs[i][0] and cs[i][1] < cs[j][1]:
                                    best[i] = max(best[i], best[j] + 1)
                        depth = max(best) if best else 0
                        ng = len(goods)
                        stats['good_webs'] += ng
                        stats['chords'] += ng * len(allc)
                        stats['same_sector_nests'] += ng * same_nest
                        stats['opposite_sector_nests'] += ng * opp_nest
                        if same_nest: stats['webs_with_same_sector_nest'] += ng
                        if opp_nest: stats['webs_with_opposite_nest'] += ng
                        depth_hist[depth] += ng
                        if same_nest and example is None:
                            example = dict(V=V, p=p, q=q, kin=kin, kout=kout, prsS=[list(x) for x in prsS],
                                           prsT=[list(x) for x in prsT], colouring=list(goods[0][:3]))
    dt = time.time() - t0
    print(f"V={V}: structures={n_struct} good closed webs={stats['good_webs']} chords={stats['chords']} "
          f"same-sector nests={stats['same_sector_nests']} (webs {stats['webs_with_same_sector_nest']}) "
          f"opposite-sector nests={stats['opposite_sector_nests']} (webs {stats['webs_with_opposite_nest']}) "
          f"depth hist={dict(depth_hist)} [{dt:.0f}s]", flush=True)
    if example: print("  example same-sector nest:", json.dumps(example))
    return dict(stats), dict(depth_hist), example


if __name__ == '__main__':
    Vs = [int(a) for a in sys.argv[1:]] or [10, 12]
    out = {}
    for V in Vs:
        s, h, ex = run(V)
        out[V] = dict(stats=s, depth=h, example=ex)
        if s.get('same_sector_nests'):
            print("OUTCOME: W1 (same-sector nest on a good-word closed web)")
        elif s.get('opposite_sector_nests'):
            print("OUTCOME: W2 (only opposite-sector nests: alternation confirmed)")
        else:
            print("OUTCOME: W3 (no nests at all on good-word closed webs)")
    json.dump(out, open('goodword_widthtwo_results.json', 'w'), indent=1)
