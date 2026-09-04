"""Rank every noncrossing cap of a disk by sampled coverage (fraction of its
pair-colourings that extend into the disk), then exact coverage of the top
caps modulo colour permutation. Sizes the gap a Kempe closure must close."""
import sys, json, random, time
sys.path.insert(0, '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp')
from kempe import noncrossing
from cap_zero_kempe_test import load, Extender, word_of, cap_words
path = sys.argv[1]; SAMPLE = int(sys.argv[2]) if len(sys.argv) > 2 else 60; TOP = int(sys.argv[3]) if len(sys.argv) > 3 else 5
n, nv, E = load(path); X = Extender(n, nv, E)
caps = noncrossing(list(range(n))); rng = random.Random(3); m = n // 2
t0 = time.time(); ranked = []
for mu in caps:
    k = sum(X.extends(word_of(mu, [rng.randrange(3) for _ in range(m)], n)) for _ in range(SAMPLE))
    ranked.append((k / SAMPLE, mu))
ranked.sort(key=lambda t: -t[0])
print(f"{path}: {len(caps)} caps ranked in {time.time()-t0:.0f}s; sampled coverage top: {[round(r[0],2) for r in ranked[:10]]}, median {ranked[len(ranked)//2][0]:.2f}")
out = []
for cov, mu in ranked[:TOP]:
    tot = ok = 0; missing = []
    for cols in cap_words(mu):
        tot += 1
        if X.extends(word_of(mu, cols, n)): ok += 1
        else: missing.append(cols)
    print(f"  cap {mu}: exact coverage {ok}/{tot} = {ok/tot:.3f} (canonical words); missing {len(missing)}")
    out.append(dict(cap=mu, sampled=cov, exact=ok / tot, total=tot, missing=len(missing), missing_words=missing[:2000]))
json.dump(out, open(path.replace('.json', '_bestcaps.json'), 'w'))
