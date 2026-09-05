#!/usr/bin/env python3
"""Perimeter pumping of a long face with a thin annulus: rung stabilisation.

A long face F of length l with a thin annulus of L zigzag rings around it,
bounded by an outer long face O, is the (l,0) zigzag tube of length L between
two l-gon faces.  Its rungs are the cross-sections: c (on F), d1, e1, ..., dL,
eL, c' (on O).  The cross-cut between consecutive rungs crosses the F-edge, the
L b-edges and the O-edge: width L+2.  A rung is a two-sided tangle of width
L+2; deleting a rung shortens F and O by one, and is valid in a least
counterexample once the rung relation R satisfies R^m = R^{m+1}: then a
segment of m+1 rungs has the same transfer relation as m rungs.

Pre-registered outcomes:
  P1  index <= L+1, period 1  (the tube law k-1 transfers to rungs)
  P2  index larger but finite, period 1
  P3  eventually periodic with period 2 (delete two rungs)
Any outcome gives a finite perimeter-pumping constant for thin annuli.

Usage: longface_rung_lab.py [Lmax]
"""
import itertools, sys


def rung_relation(L):
    """R[x] = set of out-words y for in-word x; words are tuples of length L+2:
    (F-edge, b_1..b_L, O-edge)."""
    width = L + 2
    words = list(itertools.product(range(3), repeat=width))
    R = {}
    for x in words:
        xF, xs, xO = x[0], x[1:L + 1], x[L + 1]
        outs = set()
        # internal colours: s_0 (c-d1), a_t (d_t-e_t), s_t (e_t-d_{t+1} or e_L-c')
        for s in itertools.product(range(3), repeat=L + 1):
            for a in itertools.product(range(3), repeat=L):
                ok = True
                # vertex d_t: {s_{t-1}, a_t, x_t} distinct
                for t in range(L):
                    if len({s[t], a[t], xs[t]}) != 3:
                        ok = False; break
                if not ok: continue
                # vertex e_t: {a_t, y_t, s_t} distinct -> y_t forced = third colour
                ys = []
                for t in range(L):
                    if a[t] == s[t + 1]:
                        ok = False; break
                    ys.append(3 - a[t] - s[t + 1])
                if not ok: continue
                # vertex c: {xF, yF, s_0} distinct -> yF forced; vertex c': {s_L, xO, yO}
                if xF == s[0] or xO == s[L]:
                    continue
                yF = 3 - xF - s[0]
                yO = 3 - s[L] - xO
                outs.add((yF,) + tuple(ys) + (yO,))
        R[x] = frozenset(outs)
    return words, R


def compose(R1, R2, words):
    return {x: frozenset(z for y in R1[x] for z in R2[y]) for x in words}


def stabilisation(L):
    words, R = rung_relation(L)
    key = lambda Rel: tuple(Rel[x] for x in words)
    seen = {key(R): 1}
    P = R
    m = 1
    while True:
        P = compose(P, R, words)
        m += 1
        k = key(P)
        if k in seen:
            return seen[k], m - seen[k], words, R
        seen[k] = m


if __name__ == '__main__':
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for L in range(1, Lmax + 1):
        idx, per, words, R = stabilisation(L)
        nonempty = sum(1 for x in words if R[x])
        verdict = 'P1' if (idx <= L + 1 and per == 1) else ('P2' if per == 1 else 'P3')
        print(f"L={L}: width {L + 2}, words {len(words)}, words with a transition {nonempty}; "
              f"R^m stabilises at index {idx}, period {per} -> {verdict}", flush=True)
