"""Goal-directed, depth-limited Kempe closure membership for large rings.

Bottom-up closure over all 3^n words is out of reach at ring 20; but to
decide C-reducibility with a given cap we only need the cap's MISSING words
(those not extendable directly) to lie in the closure.  A word w is good at
depth d (d >= 1) if for some colour pair (x,y), for EVERY noncrossing
perfect matching mu of the x,y-ports of w, some subset of the chains of mu
can be switched so that the switched word is in supp or good at depth d-1.
Depth-0 membership is the extension test, memoized; switched words are
memoized by word, and small subsets are tried first with early exit.

Output: for a sample (or all) of the missing words, the fraction good at
depth 1 and depth 2, timing, and the certificates (pair + per-matching
subset) for the good ones.  Pre-registered reading: a high depth-1/2
success rate means the full closure is likely to reach the cap (build the
ring-20 closure engine); a near-zero rate means the disk is rigid at
radius 2 as it was at radius 1 (outcome B stands at radius 2).

Usage: python3 kempe_goal_directed.py tangle.json bestcaps.json [cap_index] [n_words] [depth] [time_budget_s]
"""
import sys, os, json, time, itertools, random
sys.path.insert(0, '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp')
from kempe import noncrossing as _noncrossing
_nc_memo = {}
def noncrossing(P):
    k = tuple(P)
    r = _nc_memo.get(k)
    if r is None:
        r = [[tuple(pr) for pr in mu] for mu in _noncrossing(list(P))]; _nc_memo[k] = r
    return r
from cap_zero_kempe_test import load, Extender, word_of


class Closure:
    def __init__(self, X, n):
        self.X, self.n = X, n
        self.supp_memo = {}
        self.good_memo = {}      # (word, depth) -> certificate or False
        self.tests = 0

    def in_supp(self, w):
        c = 0
        for t in reversed(w): c = c * 3 + t
        r = self.supp_memo.get(c)
        if r is None:
            r = self.X.extends(list(w)); self.supp_memo[c] = r; self.tests += 1
        return r

    def switched(self, w, x, y, chains):
        w = list(w)
        for (i, j) in chains:
            for p in (i, j):
                w[p] = y if w[p] == x else x
        return tuple(w)

    def good(self, w, depth, deadline):
        """certificate (x, y, [(mu, subset)]) if w in closure at this depth, else False."""
        if self.in_supp(w): return 'supp'
        if depth == 0: return False
        key = (w, depth)
        if key in self.good_memo: return self.good_memo[key]
        for (x, y) in ((0, 1), (0, 2), (1, 2)):
            P = [i for i in range(self.n) if w[i] in (x, y)]
            if len(P) % 2 or not P: continue
            entries = []; ok = True
            for mu in noncrossing(P):
                found = None
                for r in range(len(mu) + 1):
                    for sub in itertools.combinations(range(len(mu)), r):
                        if time.time() > deadline: self.good_memo[key] = False; return False
                        sw = self.switched(w, x, y, [mu[t] for t in sub])
                        if self.good(sw, depth - 1, deadline):
                            found = list(sub); break
                    if found is not None: break
                if found is None: ok = False; break
                entries.append((mu, found))
            if ok:
                self.good_memo[key] = (x, y, entries); return self.good_memo[key]
        self.good_memo[key] = False
        return False


def main():
    tpath, bpath = sys.argv[1], sys.argv[2]
    ci = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    nw = int(sys.argv[4]) if len(sys.argv) > 4 else 100
    depth = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    budget = float(sys.argv[6]) if len(sys.argv) > 6 else 1800
    n, nv, E = load(tpath); X = Extender(n, nv, E)
    best = json.load(open(bpath))[ci]
    mu = [tuple(p) for p in best['cap']]
    missing = [tuple(word_of(mu, cols, n)) for cols in best['missing_words']]
    rng = random.Random(11); rng.shuffle(missing)
    sample = missing[:nw]
    if os.environ.get('KGD_WORDS'):
        sample = [tuple(w) for w in json.load(open(os.environ['KGD_WORDS']))]
    C = Closure(X, n)
    print(f"{tpath} cap#{ci} exact coverage {best['exact']:.3f}; testing {len(sample)} of {best['missing']} missing words at depth {depth}", flush=True)
    t0 = time.time(); deadline = t0 + budget
    good = 0; results = []
    for k, w in enumerate(sample):
        if time.time() > deadline: break
        t1 = time.time()
        c = C.good(w, depth, deadline)
        results.append(dict(word=list(w), good=bool(c), seconds=round(time.time() - t1, 1)))
        good += bool(c)
        if k % 10 == 0:
            print(f"  {k+1} words: good {good}, ext tests {C.tests}, {time.time()-t0:.0f}s", flush=True)
    done = len(results)
    print(f"RESULT depth {depth}: {good}/{done} missing words good ({good/max(1,done):.2f}); extension tests {C.tests}; {time.time()-t0:.0f}s")
    # derivation DAG restricted to ancestors of the certified targets, streamed shallow-first as JSON lines
    suffix = os.environ.get("KGD_SUFFIX", "")
    outp = tpath.replace('.json', f'_kgd_d{depth}{suffix}_derivations.jsonl')
    need = {}
    def collect(w, d):
        if d == 0 or (w, d) in need: return
        c = C.good_memo.get((w, d))
        if not c or c == 'supp': return
        need[(w, d)] = True
        x, y, entries = c
        for mu, sub in entries:
            sw = C.switched(w, x, y, [mu[t] for t in sub])
            if not C.in_supp(sw):
                collect(sw, d - 1)
    for r in results:
        if r['good']: collect(tuple(r['word']), depth)
    written = 0; seen = set()
    with open(outp, 'w') as fh:
        for dd in range(1, depth + 1):
            for (w, d) in list(need.keys()):
                if d != dd or w in seen: continue
                seen.add(w)
                x, y, entries = C.good_memo[(w, d)]
                fh.write(json.dumps(dict(word=list(w), depth=d, x=x, y=y,
                                         entries=[[[list(p) for p in mu], sub] for mu, sub in entries])) + '\n')
                written += 1
    for r in results:
        w = tuple(r['word']); r['cert'] = 'supp' if C.in_supp(w) else ('derived' if w in seen else None)
    json.dump(dict(tangle=tpath, cap=mu, depth=depth, tested=done, good=good, results=results, derivations_file=outp),
              open(tpath.replace('.json', f'_kgd_d{depth}{suffix}.json'), 'w'))
    print(f"derivations saved: {written} (ancestor DAG of {sum(1 for r in results if r['good'])} certified targets) -> {outp}")


if __name__ == '__main__':
    main()
