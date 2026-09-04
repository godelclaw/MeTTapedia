"""Stone-Wales rotated coronene (2 pentagons, 2 heptagons, ring 12): known not
cap-reducible (best cap leaves 51 closure-outside words).  Test the extended
replacement menu: delete an internal edge set (|S| <= DEL), prune, suppress.
Pre-registered: SW1 = some deletion replacement reduces it; SW2 = none up to DEL."""
import sys, os, json, time, itertools
sys.path.insert(0, os.environ.get('KEMPE_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp'))
import numpy as np
from kempe import hex_patch, support, closure, admissible_mask, all_words
from swpatch import sw_rotate
from patch_reducibility_lab import reduce_tangle, bridgeless_with_ring
DEL = int(sys.argv[1]) if len(sys.argv) > 1 else 3
n, nv, E = hex_patch(1)
E2 = sw_rotate(n, nv, E)
t0 = time.time()
S0 = support(n, nv, E2, None); C = closure(n, S0, verbose=False)
print(f"SW: ring {n} vertices {nv} |supp|={int(S0.sum())} |closure|={int(C.sum())} ({time.time()-t0:.0f}s)", flush=True)
internal = [k for k, (u, v) in enumerate(E2) if not isinstance(u, tuple) and not isinstance(v, tuple)]
best = None; tried = 0; found = None
for size in range(1, DEL + 1):
    for S in itertools.combinations(internal, size):
        T = reduce_tangle(nv, E2, set(S))
        if T is None: continue
        nv2, E3 = T
        if nv2 >= nv or not bridgeless_with_ring(n, nv2, E3): continue
        tried += 1
        miss = int((support(n, nv2, E3, None) & ~C).sum())
        if best is None or miss < best[0]: best = (miss, list(S), nv2)
        if miss == 0:
            found = (list(S), nv2); break
    print(f"  size {size}: tried so far {tried}, best miss {best}", flush=True)
    if found: break
print("OUTCOME:", f"SW1 reducible by deleting {found}" if found else f"SW2 irreducible up to {DEL} deletions; best {best}")
json.dump(dict(supp=int(S0.sum()), closure=int(C.sum()), tried=tried, best=best, found=found), open('sw_deletion_test.json', 'w'))
