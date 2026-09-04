"""Phase B worker: cheap metrics for a shard of exported disk types:
support fraction (200 words), best sampled cap coverage (up to 300 caps x
20 words), depth-1 growth (40 words, 20 s cap). Writes one JSON line per type."""
import sys, json, random, time
sys.path.insert(0, '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp')
from kempe import noncrossing
from cap_zero_kempe_test import Extender, word_of
from kempe_goal_directed import Closure
path, shard, nshards, minfaces = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
types = [r for r in json.load(open(path)) if r['nfaces'] >= minfaces]
mine = types[shard::nshards]
rng = random.Random(100 + shard)
def admissible(w):
    c = [w.count(t) for t in range(3)]
    return c[0] % 2 == c[1] % 2 == c[2] % 2
out = open(path.replace('.json', f'_metrics_{shard}.jsonl'), 'w')
for r in mine:
    n, nv = r['n'], r['nv']
    E = [tuple((('p', z[1]) if isinstance(z, list) else z) for z in e) for e in r['edges']]
    X = Extender(n, nv, E); C = Closure(X, n); t0 = time.time()
    tot = ext = 0
    while tot < 200:
        w = tuple(rng.randrange(3) for _ in range(n))
        if not admissible(w): continue
        tot += 1; ext += C.in_supp(w)
    caps = noncrossing(list(range(n))) if n % 2 == 0 else []
    rng.shuffle(caps); best = 0.0; bestmu = None
    for mu in caps[:300]:
        k = sum(X.extends(word_of(mu, [rng.randrange(3) for _ in range(n // 2)], n)) for _ in range(20))
        if k / 20 > best: best, bestmu = k / 20, mu
    tested = good = 0; deadline = time.time() + 20
    while tested < 40 and time.time() < deadline:
        w = tuple(rng.randrange(3) for _ in range(n))
        if not admissible(w) or C.in_supp(w): continue
        tested += 1; good += bool(C.good(w, 1, deadline))
    row = dict(wl=r['wl'], faces=r['faces'], nfaces=r['nfaces'], ring=n, vertices=nv, supp_frac=round(ext / tot, 3),
               best_cap=best, best_cap_mu=bestmu, growth1=round(good / max(1, tested), 3), growth_tested=tested,
               seconds=round(time.time() - t0, 1))
    out.write(json.dumps(row) + '\n'); out.flush()
print("done shard", shard, len(mine))
