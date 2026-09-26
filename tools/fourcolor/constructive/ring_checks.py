"""Brute-force cross-checks of the zigzag ring relation.

Colours are the nonzero Klein-group elements 1, 2, 3 (the third colour of two
distinct colours is their xor).  One ring with input word x and output word y
is a choice of a_i != 0, x_i with y_i = a_i ^ x_{i+1} ^ a_{i+1} != 0.

Checked for every parity-admissible word of each length k in the range:
 * cursor lemma: the relation equals the cursor process in which the carried
   colour a stays fixed unless it equals the next input letter, and then
   switches to either colour other than that letter;
 * two-colour rigidity: if some colour is absent from x, every output of one
   ring is x itself or its one-step rotation.

Usage: python3 ring_checks.py [KMIN KMAX]   (default 5 8)
"""
import sys
from itertools import product


def ring_brute(x):
    k = len(x)
    out = set()
    for a in product((1, 2, 3), repeat=k):
        if any(a[i] == x[i] for i in range(k)):
            continue
        y = tuple(a[i] ^ x[(i + 1) % k] ^ a[(i + 1) % k] for i in range(k))
        if all(v != 0 for v in y):
            out.add(y)
    return out


def ring_cursor(x):
    k = len(x)
    out = set()
    for a0 in (1, 2, 3):
        if a0 == x[0]:
            continue
        stack = [(a0,)]
        while stack:
            a = stack.pop()
            i = len(a) - 1
            nxt_letter = x[(i + 1) % k]
            options = [c for c in (1, 2, 3) if c != nxt_letter] if a[-1] == nxt_letter else [a[-1]]
            if i == k - 1:
                if a0 in options:
                    full = a + (a0,)
                    out.add(tuple(full[t] ^ x[(t + 1) % k] ^ full[t + 1] for t in range(k)))
                continue
            for c in options:
                stack.append(a + (c,))
    return out


def main(kmin, kmax):
    for k in range(kmin, kmax + 1):
        words = [x for x in product((1, 2, 3), repeat=k)
                 if all(x.count(c) % 2 == k % 2 for c in (1, 2, 3))]
        cursor_bad = rigid_bad = two_colour = 0
        for x in words:
            brute = ring_brute(x)
            if brute != ring_cursor(x):
                cursor_bad += 1
            if len(set(x)) < 3:
                two_colour += 1
                rot = tuple(x[(i + 1) % k] for i in range(k))
                if not brute <= {x, rot}:
                    rigid_bad += 1
        print(f"k={k}: admissible words {len(words)}; cursor mismatches {cursor_bad}; "
              f"words with an absent colour {two_colour}, rigidity violations {rigid_bad}")


if __name__ == "__main__":
    args = [int(a) for a in sys.argv[1:3]]
    main(*(args if len(args) == 2 else (5, 8)))
