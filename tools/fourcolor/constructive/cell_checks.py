"""Exact checks of the cell rule and of unstructured excursions on word sets.

Colours 1, 2, 3 (xor = third colour).  A_w: nonzero words of length w with
xor-sum 0.  I_w = A_w for odd w, A_w minus the constant words for even w.
  split at p: x_p is replaced by an ordered pair (a, b) with a != b, a ^ b = x_p
  merge at p: positions p, p+1 (cyclically) with different colours are
              replaced by their xor
  cell at p:  split at p, then merge the second fresh port with its outer
              neighbour (the "left cell" merges the first fresh port with its
              outer neighbour instead)

Checks:
 1. cell(A_w) = A_w and cell(I_w) = A_w, for both sides (w = 3..8);
 2. two splits then two merges at arbitrary positions: how often the result
    misses part of I_w (w = 3..6);
 3. cells from a single word, applied at positions 0, 1, 2, ... cyclically:
    whether the support ever reaches A_w (w = 4..8).

Usage: python3 cell_checks.py
"""
from itertools import product


def adm(w):
    return {x for x in product((1, 2, 3), repeat=w)
            if x.count(1) % 2 == x.count(2) % 2 == x.count(3) % 2 == w % 2}


def inv(w):
    A = adm(w)
    return A if w % 2 else {x for x in A if len(set(x)) > 1}


def split(S, p):
    out = set()
    for x in S:
        for a in (1, 2, 3):
            if a == x[p]:
                continue
            out.add(x[:p] + (a, a ^ x[p]) + x[p + 1:])
    return out


def merge(S, p):
    out = set()
    for x in S:
        w = len(x)
        q = (p + 1) % w
        if x[p] == x[q]:
            continue
        c = x[p] ^ x[q]
        out.add((c,) + x[1:p] if q == 0 else x[:p] + (c,) + x[q + 1:])
    return out


def cell(S, p, side="right"):
    w = len(next(iter(S)))
    T = split(S, p)
    return merge(T, p + 1) if side == "right" else merge(T, (p - 1) % (w + 1))


def main():
    for w in range(3, 9):
        A, I = adm(w), inv(w)
        print(f"w={w}: cell(A)==A {cell(A, 0) == A}; cell(I)==A {cell(I, 0) == A}; "
              f"left cell(A)==A {cell(A, 0, 'left') == A}; left cell(I)==A {cell(I, 0, 'left') == A}")
    for w in range(3, 7):
        I = inv(w)
        bad = tot = 0
        for p1 in range(w):
            S1 = split(I, p1)
            for p2 in range(w + 1):
                S2 = split(S1, p2)
                for q1 in range(w + 2):
                    S3 = merge(S2, q1)
                    for q2 in range(w + 1):
                        S4 = merge(S3, q2)
                        tot += 1
                        if not I <= S4:
                            bad += 1
        print(f"w={w}: two splits then two merges at all positions: {bad} of {tot} miss part of I_w")
    for w in range(4, 9):
        A = adm(w)
        outcomes = {}
        for x in sorted(A):
            S, steps = {x}, 0
            while S != A and steps < 60:
                S = cell(S, steps % w)
                steps += 1
            key = "reaches A_w" if S == A else f"stuck at size {len(S)}"
            outcomes[key] = outcomes.get(key, 0) + 1
        print(f"w={w}: single-word starts, 60 cyclic cells: {outcomes}")


if __name__ == "__main__":
    main()
