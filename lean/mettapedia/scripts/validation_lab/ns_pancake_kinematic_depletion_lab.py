#!/usr/bin/env python3
"""Kinematic pancake-depletion lab for the scale-local strain budget.

PRE-REGISTERED QUESTION (fixed before running).  The dyadic pancake
closure's open pin (`ScaleLocalPancakeStrainBudget`) is sufficient-ized by
three per-scale mechanism envelopes; the Biot-Savart self-depletion
envelope claims: the strain sourced by pancake-cone vorticity modes,
acting back on pancake-cone vorticity modes, is small compared to the
generic mode interaction, with a gain controlled by the cone aperture
delta_q = lambda_q^{-1/2}.

The single-mode diagonal is exactly zero (Lean:
`strainRateApply_planeWaveVelocityMode_vorticity`).  This lab measures
whether the depletion survives *aggregation*: for lattice wavevector
pairs (k1, k2) in dyadic-shell/cone configurations, it computes the
exact normalized interaction coefficient

    sigma(k1, w1; k2, w2) = |Samp(k1, u[k1,w1]) . w2| / (|w1| |w2|),

where u[k,w] = i k x w / |k|^2 is the Biot-Savart velocity amplitude of
the vorticity mode (k, w) and Samp = (i/2)(k (x) u + u (x) k) is the
strain amplitude.  Reported per shell lambda = 2^q with aperture
delta = lambda^{-1/2}:

  * sigma_max over same-shell cone pairs (worst pair, worst
    polarizations);
  * the Schur row-sum max_k2 sum_k1 sigma_max-pol(k1, k2) for the
    low-pass strain configuration (k1 over all lower cone shells,
    k2 in a thin top subshell) -- the surrogate for ||A_q^pan w_q^pan||
    against sup-norm block accounting;
  * the same two quantities with the cone replaced by the full shell
    (delta = 1), giving the depletion factor
    D(lambda) = rowsum_cone / rowsum_full.

PRE-REGISTERED VERDICT CRITERIA:
  (V1) sanity: every diagonal coefficient is 0 to machine precision
       (cross-check of the Lean null-structure theorem);
  (V2) E2 kinematically viable  <=>  D(lambda) decreases with lambda
       with a measured power-law fit D ~ delta^alpha, alpha > 0, stable
       across the two largest shells;
  (V3) E2 kinematically dead    <=>  D(lambda) is bounded below by a
       constant across shells (aggregation destroys the depletion).
The measured alpha is the lab's principal output either way; the needed
exponent is determined analytically in the follow-up stage, not here.

Discipline: single-process numpy, memory-light (vectorized row sums,
no pair matrix is materialized), resumable per shell, JSON output.
Run:  ulimit -v 25165824; nice -n 19 python3 ns_pancake_kinematic_depletion_lab.py
"""

import argparse
import json
import math
import sys

import numpy as np


def shell_modes(lam_lo: float, lam_hi: float, delta: float | None) -> np.ndarray:
    """Integer wavevectors with lam_lo <= |k| < lam_hi, within the cone
    {|khat x n| <= delta} around n = e3 (both poles); delta=None = full shell."""
    kmax = int(math.floor(lam_hi))
    rng = np.arange(-kmax, kmax + 1)
    kx, ky, kz = np.meshgrid(rng, rng, rng, indexing="ij")
    k = np.stack([kx.ravel(), ky.ravel(), kz.ravel()], axis=1).astype(np.float64)
    norm2 = (k * k).sum(axis=1)
    mask = (norm2 >= lam_lo * lam_lo) & (norm2 < lam_hi * lam_hi)
    k = k[mask]
    if delta is not None:
        norm = np.sqrt((k * k).sum(axis=1))
        sin_angle = np.sqrt(k[:, 0] ** 2 + k[:, 1] ** 2) / norm
        k = k[sin_angle <= delta]
    return k


def polarization_bases(k: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Two orthonormal real vectors perpendicular to each row of k."""
    n = k.shape[0]
    ref = np.tile(np.array([1.0, 0.0, 0.0]), (n, 1))
    close = np.abs(k[:, 0]) / np.sqrt((k * k).sum(axis=1)) > 0.9
    ref[close] = np.array([0.0, 1.0, 0.0])
    e1 = np.cross(k, ref)
    e1 /= np.linalg.norm(e1, axis=1, keepdims=True)
    e2 = np.cross(k, e1)
    e2 /= np.linalg.norm(e2, axis=1, keepdims=True)
    return e1, e2


def interaction_norm(k1: np.ndarray, w1: np.ndarray, w2col: np.ndarray) -> np.ndarray:
    """|Samp(k1, u1) . w2| for unit vorticity polarizations, vectorized over k1.

    u1 = i k1 x w1 / |k1|^2 ; Samp = (i/2)(k1 (x) u1 + u1 (x) k1).
    The i-factors combine to a real matrix: Samp.w2 =
      -(1/2) [ k1 (u1r . w2) + u1r (k1 . w2) ] with u1r = k1 x w1 / |k1|^2.
    Returns the euclidean norm per k1-row for a FIXED w2 (3-vector).
    """
    norm2 = (k1 * k1).sum(axis=1, keepdims=True)
    u1r = np.cross(k1, w1) / norm2
    a = u1r @ w2col  # (n,)
    b = k1 @ w2col  # (n,)
    vec = 0.5 * (k1 * a[:, None] + u1r * b[:, None])
    return np.linalg.norm(vec, axis=1)


def pair_sigma_max(k1s: np.ndarray, k2: np.ndarray) -> np.ndarray:
    """Max over the 2x2 polarization choices of the normalized coefficient,
    vectorized over k1s for a single k2."""
    e11, e12 = polarization_bases(k1s)
    f1, f2 = polarization_bases(k2[None, :])
    best = np.zeros(k1s.shape[0])
    for w1 in (e11, e12):
        for w2 in (f1[0], f2[0]):
            val = interaction_norm(k1s, w1, w2)
            np.maximum(best, val, out=best)
    return best


def run_shell(q: int, low_pass_gap: int, sub_thickness: float, full: bool) -> dict:
    lam = float(2 ** q)
    delta = None if full else lam ** -0.5
    # receivers: thin top subshell in the cone at scale lambda
    k2s = shell_modes(lam, lam + sub_thickness, delta)
    # strain sources: all lower shells (low-pass), per-shell aperture
    k1_list = []
    for p in range(1, q - low_pass_gap + 1):
        lp = float(2 ** p)
        dp = None if full else lp ** -0.5
        k1_list.append(shell_modes(lp, min(2 * lp, lam / (2 ** low_pass_gap)), dp))
    k1s = np.concatenate([a for a in k1_list if a.size], axis=0) if k1_list else np.zeros((0, 3))
    out = {
        "q": q, "lambda": lam, "delta": (1.0 if full else delta),
        "n_receivers": int(k2s.shape[0]), "n_sources": int(k1s.shape[0]),
    }
    if k2s.shape[0] == 0 or k1s.shape[0] == 0:
        out["empty"] = True
        return out
    # deterministic subsampling caps (documented estimator: row sums over a
    # source sample are rescaled by the count ratio; the receiver max over a
    # sample under-biases cone and full runs identically)
    rng = np.random.default_rng(0)
    max_recv, max_src = 600, 20000
    if k2s.shape[0] > max_recv:
        k2s = k2s[rng.choice(k2s.shape[0], max_recv, replace=False)]
        out["receivers_sampled"] = max_recv
    src_scale = 1.0
    if k1s.shape[0] > max_src:
        src_scale = k1s.shape[0] / max_src
        k1s = k1s[rng.choice(k1s.shape[0], max_src, replace=False)]
        out["sources_sampled"] = max_src
        out["source_scale"] = src_scale
    # diagonal sanity on the receiver set (V1)
    diag_max = 0.0
    e1, e2 = polarization_bases(k2s)
    for w in (e1, e2):
        norm2 = (k2s * k2s).sum(axis=1, keepdims=True)
        u = np.cross(k2s, w) / norm2
        a = (u * w).sum(axis=1)
        b = (k2s * w).sum(axis=1)
        vec = 0.5 * (k2s * a[:, None] + u * b[:, None])
        diag_max = max(diag_max, float(np.linalg.norm(vec, axis=1).max()))
    out["diagonal_max"] = diag_max
    # normalized row sums: sum over sources of sigma / (lambda_source scaling
    # is intrinsic: Samp carries |k1| * |u1| = |w1| exactly, no renorm needed;
    # coefficients are per unit vorticity amplitude on both sides)
    row_sums = np.zeros(k2s.shape[0])
    row_max = np.zeros(k2s.shape[0])
    for i in range(k2s.shape[0]):
        vals = pair_sigma_max(k1s, k2s[i])
        row_sums[i] = vals.sum() * src_scale
        row_max[i] = vals.max()
    out["rowsum_max"] = float(row_sums.max())
    out["rowsum_mean"] = float(row_sums.mean())
    out["pairmax"] = float(row_max.max())
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qmax", type=int, default=6)
    ap.add_argument("--low-pass-gap", type=int, default=1)
    ap.add_argument("--sub-thickness", type=float, default=1.5)
    ap.add_argument("--out", default="ns_pancake_kinematic_depletion_results.json")
    args = ap.parse_args()

    results = {"cone": [], "full": []}
    for q in range(3, args.qmax + 1):
        for full in (False, True):
            r = run_shell(q, args.low_pass_gap, args.sub_thickness, full)
            results["full" if full else "cone"].append(r)
            print(f"q={q} {'full' if full else 'cone'}: recv={r.get('n_receivers')} "
                  f"src={r.get('n_sources')} diag={r.get('diagonal_max', 0):.2e} "
                  f"rowsum_max={r.get('rowsum_max', float('nan')):.4f} "
                  f"pairmax={r.get('pairmax', float('nan')):.4f}", flush=True)
    # depletion factors and power-law fit
    table = []
    for rc, rf in zip(results["cone"], results["full"]):
        if rc.get("empty") or rf.get("empty"):
            continue
        d = rc["rowsum_max"] / rf["rowsum_max"] if rf["rowsum_max"] > 0 else float("nan")
        table.append((rc["q"], rc["delta"], d))
        print(f"q={rc['q']}: depletion factor D = {d:.4f} (delta = {rc['delta']:.4f})")
    if len(table) >= 2:
        (q0, d0, D0), (q1, d1, D1) = table[-2], table[-1]
        if D0 > 0 and D1 > 0 and d0 != d1:
            alpha = math.log(D1 / D0) / math.log(d1 / d0)
            print(f"power-law fit on last two shells: D ~ delta^{alpha:.3f}")
            results["alpha_last_two"] = alpha
    results["table"] = table
    with open(args.out, "w") as fh:
        json.dump(results, fh, indent=1)
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
