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
import sys, json, time, itertools, random
sys.path.insert(0, '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp')
from kempe import noncrossing
from cap_zero_kempe_test import load, Extender, word_of


class Closure:
    def __init__(self, X, n):
        self.X, self.n = X, n
        self.supp_memo = {}
        self.good_memo = {}      # (word, depth) -> certificate or False
        self.tests = 0

    def in_supp(self, w):
        r = self.supp_memo.get(w)
        if r is None:
            r = self.X.extends(list(w)); self.supp_memo[w] = r; self.tests += 1
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
    json.dump(dict(tangle=tpath, cap=mu, depth=depth, tested=done, good=good, results=results),
              open(tpath.replace('.json', f'_kgd_d{depth}.json'), 'w'))


if __name__ == '__main__':
    main()
