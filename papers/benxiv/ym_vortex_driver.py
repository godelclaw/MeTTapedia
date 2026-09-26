"""Twist free energy by thermodynamic integration over the stack coupling (see ym_vortex_free_energy.c).

    F = -log Z(-beta)/Z(beta) = int_{-beta}^{beta} <E_stack>_b db,

evaluated by Gauss-Legendre quadrature, one run of ym_vortex_free_energy per node, several runs in
parallel at the lowest scheduling priority.  Standard library only.

In ordered phases (the Coulomb phase of U(1), weakly coupled SU(2) in small volumes or in five
dimensions) <E_stack>_b changes sign across a window near b = 0 whose width shrinks like L^-(d-2),
and the position of that window carries most of F.  --inner W then puts --inner-nodes Gauss-Legendre
nodes on [-W, W] and --nodes on each of [-beta, -W] and [W, beta].  Since <E_stack>_b is
nondecreasing in b (log Z is convex), left and right Riemann sums over the sorted nodes bound the
integral; both bounds are printed as a check on the quadrature.

usage: python3 ym_vortex_driver.py su2|u1 d L beta [--nodes 20] [--inner W --inner-nodes 16]
                                   [--therm 400] [--meas 2000] [--nor 3] [--jobs 4] [--hot]
                                   [--out results.jsonl]
Output: one line per node, then F with its standard error and the two Riemann bounds; with --out,
one JSON line per run.
"""
import argparse
import json
import math
import os
import subprocess
import sys
import zlib


def gauss_legendre(n):
    """Nodes and weights on [-1, 1] by Newton's method on the Legendre polynomial P_n."""
    xs, ws = [], []
    for i in range(1, n + 1):
        x = math.cos(math.pi * (i - 0.25) / (n + 0.5))
        for _ in range(100):
            p0, p1 = 1.0, x
            for k in range(2, n + 1):
                p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
            dp = n * (x * p1 - p0) / (x * x - 1)
            dx = p1 / dp
            x -= dx
            if abs(dx) < 1e-15:
                break
        p0, p1 = 1.0, x
        for k in range(2, n + 1):
            p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
        dp = n * (x * p1 - p0) / (x * x - 1)
        xs.append(x)
        ws.append(2 / ((1 - x * x) * dp * dp))
    return xs, ws


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("group", choices=["su2", "u1"])
    ap.add_argument("d", type=int)
    ap.add_argument("L", type=int)
    ap.add_argument("beta", type=float)
    ap.add_argument("--nodes", type=int, default=20)
    ap.add_argument("--inner", type=float, default=0.0)
    ap.add_argument("--inner-nodes", type=int, default=16)
    ap.add_argument("--therm", type=int, default=400)
    ap.add_argument("--meas", type=int, default=2000)
    ap.add_argument("--nor", type=int, default=3)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--hot", action="store_true")
    ap.add_argument("--out")
    a = ap.parse_args()

    exe = os.path.join(os.path.dirname(os.path.abspath(__file__)), "ym_vortex_free_energy")
    # quadrature nodes bs and weights wb on [-beta, beta]
    if a.inner > 0:
        pieces = [(-a.beta, -a.inner, a.nodes), (-a.inner, a.inner, a.inner_nodes), (a.inner, a.beta, a.nodes)]
    else:
        pieces = [(-a.beta, a.beta, a.nodes)]
    bs, wb = [], []
    for lo, hi, n in pieces:
        xs, ws = gauss_legendre(n)
        bs += [(lo + hi) / 2 + (hi - lo) / 2 * x for x in xs]
        wb += [(hi - lo) / 2 * w for w in ws]
    tag = f"{a.group} {a.d} {a.L} {a.beta}"
    runs = []
    for b in bs:
        seed = zlib.crc32(f"{tag} {b!r}".encode())
        cmd = ["nice", "-n", "19", exe, a.group, str(a.d), str(a.L), repr(a.beta), repr(b),
               str(a.therm), str(a.meas), str(a.nor), str(seed)] + (["hot"] if a.hot else [])
        runs.append(cmd)

    results = [None] * len(runs)
    active = {}
    queue = list(range(len(runs)))
    while queue or active:
        while queue and len(active) < a.jobs:
            i = queue.pop(0)
            active[i] = subprocess.Popen(runs[i], stdout=subprocess.PIPE, text=True)
        done = None
        while done is None:
            for i, p in active.items():
                if p.poll() is not None:
                    done = i
                    break
            else:
                os.wait()   # blocks until some child exits; the loop then finds it
        out = active.pop(done).stdout.read().split()
        results[done] = (float(out[0]), float(out[1]), float(out[2]), float(out[3]))

    F = sum(w * r[1] for w, r in zip(wb, results))
    err = math.sqrt(sum((w * r[2]) ** 2 for w, r in zip(wb, results)))
    stack = a.L ** (a.d - 2)
    srt = sorted(results)
    lower = (srt[0][0] + a.beta) * (-stack) + (a.beta - srt[-1][0]) * srt[-1][1]
    upper = (srt[0][0] + a.beta) * srt[0][1] + (a.beta - srt[-1][0]) * stack
    for (b0, m0, _, _), (b1, m1, _, _) in zip(srt, srt[1:]):
        lower += (b1 - b0) * m0
        upper += (b1 - b0) * m1
    print(f"{tag}: stack of {stack} plaquettes, {len(bs)} nodes, {a.meas} measurements each")
    for (b, m, se, pl) in srt:
        print(f"   b = {b:+.5f}   <E_stack>/stack = {m / stack:+.5f} +- {se / stack:.5f}   plaquette {pl:.5f}")
    print(f"   F = {F:.4f} +- {err:.4f}   Riemann bounds [{lower:.3f}, {upper:.3f}]")
    if a.out:
        with open(a.out, "a") as f:
            f.write(json.dumps({"group": a.group, "d": a.d, "L": a.L, "beta": a.beta, "nodes": a.nodes,
                                "inner": a.inner, "inner_nodes": a.inner_nodes, "weights": wb,
                                "therm": a.therm, "meas": a.meas, "nor": a.nor, "hot": a.hot,
                                "F": F, "err": err, "lower": lower, "upper": upper,
                                "runs": results}) + "\n")


if __name__ == "__main__":
    sys.exit(main())
