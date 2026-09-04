"""Depth-1 Kempe growth at large ring: sample random admissible words NOT in
supp(K); fraction good at depth 1 (switch lands in supp) estimates
|layer1| / |admissible \\ supp|.  Coronene: large; rigid 5/7 disks: ~0.
Pre-registered: G1 = growth fraction >= 0.10 -> a full closure at this
ring can plausibly reach a cap (invest in the engine); G2 = < 0.02 ->
rigid, outcome B stands at radius 2."""
import sys, json, random, time
from cap_zero_kempe_test import load, Extender
from kempe_goal_directed import Closure
path = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 400; budget = float(sys.argv[3]) if len(sys.argv) > 3 else 2400
n, nv, E = load(path); X = Extender(n, nv, E); C = Closure(X, n)
rng = random.Random(5)
def admissible(w):
    c = [w.count(t) for t in range(3)]
    return c[0] % 2 == c[1] % 2 == c[2] % 2
t0 = time.time(); deadline = t0 + budget
tested = good = insupp = 0; per = []
while tested < N and time.time() < deadline:
    w = tuple(rng.randrange(3) for _ in range(n))
    if not admissible(w): continue
    if C.in_supp(w): insupp += 1; continue
    t1 = time.time(); g = C.good(w, 1, deadline); per.append(time.time() - t1)
    tested += 1; good += bool(g)
    if tested % 50 == 0: print(f"  {tested}: good {good} ({good/tested:.3f}), mean {sum(per)/len(per):.2f}s/word, supp hits {insupp}", flush=True)
frac = good / max(1, tested)
print(f"RESULT {path}: depth-1 good {good}/{tested} = {frac:.3f} of non-support admissible words (supp hits {insupp}); {time.time()-t0:.0f}s")
print("OUTCOME:", "G1 (closure grows; engine investment plausible)" if frac >= 0.10 else ("G2 (rigid at radius 2)" if frac < 0.02 else "G-mid"))
json.dump(dict(tangle=path, tested=tested, good=good, frac=frac, insupp=insupp), open(path.replace('.json', '_depth1.json'), 'w'))
