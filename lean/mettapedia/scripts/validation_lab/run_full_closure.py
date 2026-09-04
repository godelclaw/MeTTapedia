"""Full reducibility run (Kempe closure fixpoint + cap menu + deletion menu)
on an exported tangle JSON, for rings the vectorized engine can hold.

Usage: python3 run_full_closure.py tangle.json [del_max]
Writes tangle_full.json with support/closure sizes, per-round growth,
the best cap (fewest closure-outside words), and the certificate if any.
"""
import sys, os, json, time
sys.path.insert(0, os.environ.get('KEMPE_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp'))
import numpy as np
from kempe import support, closure, noncrossing, cap_support, admissible_mask, all_words
from cap_zero_kempe_test import load
from patch_reducibility_lab import reduce_tangle, bridgeless_with_ring
import itertools

path = sys.argv[1]; del_max = int(sys.argv[2]) if len(sys.argv) > 2 else 2
n, nv, E = load(path)
t0 = time.time()
S0 = support(n, nv, E, None)
adm = admissible_mask(all_words(n))
print(f"{path}: ring {n} vertices {nv} |supp| {int(S0.sum())} admissible {int(adm.sum())} ({time.time()-t0:.0f}s)", flush=True)
C = closure(n, S0, verbose=True)
res = dict(tangle=path, ring=n, vertices=nv, supp=int(S0.sum()), admissible=int(adm.sum()), closure=int(C.sum()),
           D_reducible=bool((C & adm).sum() == adm.sum()), closure_seconds=round(time.time() - t0))
print(f"  closure {res['closure']} / {res['admissible']} ({res['closure']/res['admissible']:.3f}); D-reducible {res['D_reducible']} [{res['closure_seconds']}s]", flush=True)
if not res['D_reducible']:
    caps = noncrossing(list(range(n))) if n % 2 == 0 else []
    best = None
    for mu in caps:
        miss = int((cap_support(n, mu) & ~C).sum())
        if best is None or miss < best[0]: best = (miss, mu)
        if miss == 0: break
    res['best_cap'] = best
    print(f"  caps {len(caps)}: best cap misses {best[0] if best else None} closure-outside words", flush=True)
    if best and best[0] == 0:
        res['reducible'] = True; res['certificate'] = ('cap', best[1])
    else:
        internal = [k for k, (u, v) in enumerate(E) if not isinstance(u, tuple) and not isinstance(v, tuple)]
        bestd = None; tried = 0; found = None
        for size in range(1, del_max + 1):
            for S in itertools.combinations(internal, size):
                T = reduce_tangle(nv, E, set(S))
                if T is None: continue
                nv2, E2 = T
                if nv2 >= nv or not bridgeless_with_ring(n, nv2, E2): continue
                tried += 1
                miss = int((support(n, nv2, E2, None) & ~C).sum())
                if bestd is None or miss < bestd[0]: bestd = (miss, list(S), nv2)
                if miss == 0: found = (list(S), nv2); break
            print(f"  deletions size {size}: tried {tried}, best miss {bestd}", flush=True)
            if found: break
        res['best_deletion'] = bestd; res['reducible'] = found is not None
        if found: res['certificate'] = ('delete', found[0], found[1])
else:
    res['reducible'] = True; res['certificate'] = 'D'
res['seconds'] = round(time.time() - t0)
print("RESULT:", json.dumps({k: v for k, v in res.items() if k != 'best_cap'}), flush=True)
json.dump(res, open(path.replace('.json', '_full.json'), 'w'))
