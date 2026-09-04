"""Disk minimality on radius-1 patches (flowers) with faces in [5, B].

A flower F(s; s_1..s_s): a central face of size s, whose i-th edge is
shared with an outer face of size s_i; consecutive outer faces share a
"notch" edge.  Each outer face has s_i - 4 own boundary vertices, each with
a port.  Ring size n = sum(s_i - 4).  This is the general radius-1 patch of
a cubic map with bounded faces.

Reducibility (disk minimality in Tait language, the engine of the 2026-08-29
hexagonal-flower work): supp(K) = boundary words extendable inside K;
closure(K) = Kempe closure of supp(K).  K is REDUCIBLE if some strictly
smaller planar disk T on the same ports has supp(T) within closure(K):
   T ranges over caps (noncrossing port pairings, 0 vertices) and over
   K minus an internal edge set S (delete, prune degree-1, suppress
   degree-2 = the cubic form of contraction), |S| <= DEL_MAX, T loopless
   and bridgeless together with the ring.
Then a least counterexample cannot contain K (swap K for T: E u T is a
smaller uncolourable graph).

Pre-registered outcomes: P1 = every flower with faces in [5,B] and ring
<= RING_MAX is reducible under this menu -> walls with such patches are
excluded by a finite list.  P2 = some flowers are irreducible under the
menu -> they are the candidate bricks of an obstruction wall (step 3).

Calibration: F(6; 6^6) = coronene must give |supp| 16533, |closure| 48495,
exactly one reducing cap.  Engine dir on PYTHONPATH (kempe.py).
"""
import sys, os, json, time, itertools
from collections import defaultdict
sys.path.insert(0, os.environ.get('KEMPE_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp'))
import numpy as np
from kempe import support, closure, noncrossing, cap_support, admissible_mask, all_words


def flower(s, outs):
    """Return (n, nverts, edges) in engine format. Central vertices c_0..c_{s-1};
    notch vertex t_i adjacent to c_i (between outer faces i-1 and i); outer
    face i has own vertices o_{i,1..k_i} (k_i = s_i - 4) between t_i and t_{i+1}.
    Face i boundary: c_i, c_{i+1}, t_{i+1}, o_{i,k}..o_{i,1}, t_i."""
    assert len(outs) == s and all(x >= 5 for x in outs)
    vid = 0
    c = list(range(s)); vid = s
    t = list(range(vid, vid + s)); vid += s
    edges = []
    for i in range(s):
        edges.append((c[i], c[(i + 1) % s]))
        edges.append((c[i], t[i]))
    ports = []
    for i in range(s):
        k = outs[i] - 4
        own = list(range(vid, vid + k)); vid += k
        chain = [t[i]] + own + [t[(i + 1) % s]]
        for a, b in zip(chain, chain[1:]):
            edges.append((a, b))
        ports.extend(own)
    n = len(ports)
    for p, v in enumerate(ports):
        edges.append((('p', p), v))
    return n, vid, edges


def canon_outs(s, outs):
    best = None
    for r in range(s):
        for seq in (outs[r:] + outs[:r], (outs[r:] + outs[:r])[::-1]):
            if best is None or tuple(seq) < best: best = tuple(seq)
    return best


def reduce_tangle(nverts, edges, delete):
    """Delete the internal edges with the given indices; prune degree-1 and
    suppress degree-2 internal vertices.  Returns (nverts', edges') relabelled,
    or None if a loop appears or a port loses its edge."""
    E = [list(e) for k, e in enumerate(edges) if k not in delete]
    changed = True
    while changed:
        changed = False
        deg = defaultdict(int)
        for (u, v) in E:
            for z in (u, v):
                if not isinstance(z, tuple): deg[z] += 1
        for (u, v) in E:
            if u == v: return None                      # loop
        verts = {z for e in E for z in e if not isinstance(z, tuple)}
        for v in sorted(verts):
            if deg[v] == 0:
                changed = True; break
            if deg[v] == 1:
                E = [e for e in E if v not in e]; changed = True; break
            if deg[v] == 2:
                inc = [e for e in E if v in e]
                a = inc[0][0] if inc[0][1] == v else inc[0][1]
                b = inc[1][0] if inc[1][1] == v else inc[1][1]
                if a == b and not isinstance(a, tuple): return None   # would create a loop
                E = [e for e in E if v not in e] + [[a, b]]; changed = True; break
    # a port must keep exactly one edge
    pdeg = defaultdict(int)
    for (u, v) in E:
        for z in (u, v):
            if isinstance(z, tuple): pdeg[z] += 1
    nports = sum(1 for e in edges for z in e if isinstance(z, tuple))
    if len(pdeg) != nports or any(d != 1 for d in pdeg.values()): return None
    verts = sorted({z for e in E for z in e if not isinstance(z, tuple)})
    relabel = {v: i for i, v in enumerate(verts)}
    E2 = [tuple(relabel[z] if not isinstance(z, tuple) else z for z in e) for e in E]
    return len(verts), E2


def bridgeless_with_ring(n, nverts, edges):
    """T together with the ring cycle through the ports is 2-edge-connected."""
    nodes = list(range(nverts)) + [('p', i) for i in range(n)]
    E = [tuple(e) for e in edges] + [(('p', i), ('p', (i + 1) % n)) for i in range(n)]
    adj = defaultdict(list)
    for k, (u, v) in enumerate(E):
        adj[u].append((v, k)); adj[v].append((u, k))
    if not nodes: return True
    def connected(skip):
        seen = {nodes[0]}; st = [nodes[0]]
        while st:
            x = st.pop()
            for (y, k) in adj[x]:
                if k == skip or y in seen: continue
                seen.add(y); st.append(y)
        return len(seen) == len(nodes)
    if not connected(-1): return False
    return all(connected(k) for k in range(len(E)))


def analyze_flower(s, outs, del_max=3, verbose=False):
    n, nv, E = flower(s, outs)
    r = analyze_tangle(n, nv, E, del_max)
    r.update(dict(s=s, outs=list(outs)))
    return r


def analyze_tangle(n, nv, E, del_max=3):
    t0 = time.time()
    S0 = support(n, nv, E, None)
    adm = admissible_mask(all_words(n))
    C = closure(n, S0, verbose=False)
    res = dict(ring=n, vertices=nv, supp=int(S0.sum()), admissible=int(adm.sum()),
               closure=int(C.sum()), D_reducible=bool((C & adm).sum() == adm.sum()))
    if res['D_reducible']:
        res['reducible'] = True; res['certificate'] = 'D'; res['seconds'] = round(time.time() - t0, 1)
        return res
    # caps
    caps = noncrossing(list(range(n))) if n % 2 == 0 else []
    for mu in caps:
        if int((cap_support(n, mu) & ~C).sum()) == 0:
            res['reducible'] = True; res['certificate'] = ('cap', mu); res['seconds'] = round(time.time() - t0, 1)
            return res
    # deletions
    internal = [k for k, (u, v) in enumerate(E) if not isinstance(u, tuple) and not isinstance(v, tuple)]
    best = None
    tried = 0
    for size in range(1, del_max + 1):
        for S in itertools.combinations(internal, size):
            T = reduce_tangle(nv, E, set(S))
            if T is None: continue
            nv2, E2 = T
            if nv2 >= nv: continue
            if not bridgeless_with_ring(n, nv2, E2): continue
            tried += 1
            ST = support(n, nv2, E2, None)
            miss = int((ST & ~C).sum())
            if best is None or miss < best[0]: best = (miss, list(S), nv2)
            if miss == 0:
                res['reducible'] = True; res['certificate'] = ('delete', list(S), nv2)
                res['candidates_tried'] = tried; res['seconds'] = round(time.time() - t0, 1)
                return res
    res['reducible'] = False; res['best_miss'] = best; res['candidates_tried'] = tried
    res['seconds'] = round(time.time() - t0, 1)
    return res


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'calib'
    if mode == 'calib':
        r = analyze_flower(6, [6] * 6, del_max=0)
        print(json.dumps(r))
        assert r['supp'] == 16533 and r['closure'] == 48495, "coronene calibration failed"
        print("CALIBRATION OK (coronene)")
        r = analyze_flower(5, [5] * 5, del_max=2)      # half-dodecahedron cap region
        print(json.dumps(r))
    else:
        B = int(sys.argv[2]) if len(sys.argv) > 2 else 7
        RING_MAX = int(sys.argv[3]) if len(sys.argv) > 3 else 12
        DEL = int(sys.argv[4]) if len(sys.argv) > 4 else 3
        out = []
        done = {}
        logp = f'patch_sweep_B{B}_r{RING_MAX}.log'
        if os.path.exists(logp):            # resume: skip flower types already recorded
            for line in open(logp):
                if line.startswith('{'):
                    r = json.loads(line); done[(r['s'], tuple(r['outs']))] = r
            out.extend(done.values())
        for s in (5, 6, 7):
            seen = set(done_key for done_key in done if done_key[0] == s)
            for outs in itertools.product(range(5, B + 1), repeat=s):
                key = canon_outs(s, list(outs))
                if (s, key) in seen or key in seen: continue
                seen.add(key)
                n = sum(x - 4 for x in key)
                if n > RING_MAX: continue
                r = analyze_flower(s, list(key), del_max=DEL)
                print(json.dumps(r), flush=True); out.append(r)
        irr = [r for r in out if not r['reducible']]
        print(f"SUMMARY: flowers={len(out)} reducible={len(out) - len(irr)} irreducible={len(irr)}")
        print("OUTCOME:", "P1 (all reducible)" if not irr else f"P2 (irreducible: {[(r['s'], r['outs']) for r in irr]})")
        json.dump(out, open(f'patch_reducibility_B{B}_ring{RING_MAX}_del{DEL}.json', 'w'), indent=1)
