#!/usr/bin/env python3
"""Direction-coherent pancake aggregate lab (S1, second experiment).

PRE-REGISTERED QUESTION.  The kinematic dichotomy
(`PancakeConeDirectionDichotomy`, commit 4714b804b) showed pairwise
depletion is governed by vorticity-direction alignment, not the
wavevector cone.  This lab measures the *aggregate* consequence: give
every cone mode the direction-coherent polarization (the projection of
one fixed in-plane reference direction e_x off the wavevector), and
compute the same low-pass Schur row sums as the first lab, with the
output split into in-plane and axial (pancake-tilting) components.

Quantities per shell lambda = 2^q, aperture delta = lambda^{-1/2}:
  * rowsum_coh        : coherent-source, coherent-receiver row sum of
                        |Samp . w2| (full vector norm);
  * rowsum_coh_axial  : same with only the e_z output component;
  * rowsum_coh_plane  : same with only the in-plane output component;
  * baselines from the first lab: worst-polarization cone rowsum and
    full-shell rowsum (recomputed here for the same samples).

PRE-REGISTERED CRITERIA:
  (W1) coherent gain: G_coh(lambda) = rowsum_coh / rowsum_worst_cone;
       E2-with-coherence viable iff G_coh -> 0 with a stable power fit.
  (W2) channel split: if the axial (tilting) output dominates
       rowsum_coh, the surviving obstruction is pancake tilting, which
       is the pressure-Hessian envelope's channel; record the split.

Run: ulimit -v 25165824; nice -n 19 python3 ns_pancake_coherent_aggregate_lab.py
"""

import argparse
import json
import math
import sys

import numpy as np

from ns_pancake_kinematic_depletion_lab import (
    shell_modes, polarization_bases, pair_sigma_max)


def coherent_polarization(k: np.ndarray) -> np.ndarray:
    """Unit polarization: reference e_x projected off each wavevector."""
    ref = np.tile(np.array([1.0, 0.0, 0.0]), (k.shape[0], 1))
    kk = (k * k).sum(axis=1, keepdims=True)
    proj = ref - k * ((k * ref).sum(axis=1, keepdims=True) / kk)
    norms = np.linalg.norm(proj, axis=1, keepdims=True)
    good = norms[:, 0] > 1e-12
    proj[good] /= norms[good]
    return proj, good


def stretch_vectors(k1: np.ndarray, w1: np.ndarray, w2col: np.ndarray) -> np.ndarray:
    """Samp(k1,u1).w2 as vectors, vectorized over sources."""
    norm2 = (k1 * k1).sum(axis=1, keepdims=True)
    u1r = np.cross(k1, w1) / norm2
    a = u1r @ w2col
    b = k1 @ w2col
    return 0.5 * (k1 * a[:, None] + u1r * b[:, None])


def run_shell(q: int, low_pass_gap: int, sub_thickness: float) -> dict:
    lam = float(2 ** q)
    delta = lam ** -0.5
    k2s = shell_modes(lam, lam + sub_thickness, delta)
    k1_list = []
    for p in range(1, q - low_pass_gap + 1):
        lp = float(2 ** p)
        k1_list.append(shell_modes(lp, min(2 * lp, lam / (2 ** low_pass_gap)), lp ** -0.5))
    k1s = np.concatenate([a for a in k1_list if a.size], axis=0) if k1_list else np.zeros((0, 3))
    out = {"q": q, "lambda": lam, "delta": delta,
           "n_receivers": int(k2s.shape[0]), "n_sources": int(k1s.shape[0])}
    if k2s.shape[0] == 0 or k1s.shape[0] == 0:
        out["empty"] = True
        return out
    rng = np.random.default_rng(0)
    max_recv, max_src = 400, 20000
    if k2s.shape[0] > max_recv:
        k2s = k2s[rng.choice(k2s.shape[0], max_recv, replace=False)]
    src_scale = 1.0
    if k1s.shape[0] > max_src:
        src_scale = k1s.shape[0] / max_src
        k1s = k1s[rng.choice(k1s.shape[0], max_src, replace=False)]
    w1coh, good1 = coherent_polarization(k1s)
    k1s, w1coh = k1s[good1], w1coh[good1]
    w2coh, good2 = coherent_polarization(k2s)
    k2s, w2coh = k2s[good2], w2coh[good2]
    rs_coh = np.zeros(k2s.shape[0])
    rs_ax = np.zeros(k2s.shape[0])
    rs_pl = np.zeros(k2s.shape[0])
    rs_worst = np.zeros(k2s.shape[0])
    for i in range(k2s.shape[0]):
        vec = stretch_vectors(k1s, w1coh, w2coh[i])
        norms = np.linalg.norm(vec, axis=1)
        rs_coh[i] = norms.sum() * src_scale
        rs_ax[i] = np.abs(vec[:, 2]).sum() * src_scale
        rs_pl[i] = np.linalg.norm(vec[:, :2], axis=1).sum() * src_scale
        rs_worst[i] = pair_sigma_max(k1s, k2s[i]).sum() * src_scale
    out["rowsum_coherent"] = float(rs_coh.max())
    out["rowsum_coherent_axial"] = float(rs_ax.max())
    out["rowsum_coherent_plane"] = float(rs_pl.max())
    out["rowsum_worst_cone"] = float(rs_worst.max())
    out["coherent_gain"] = out["rowsum_coherent"] / out["rowsum_worst_cone"]
    out["axial_fraction"] = out["rowsum_coherent_axial"] / max(out["rowsum_coherent"], 1e-300)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qmax", type=int, default=6)
    ap.add_argument("--low-pass-gap", type=int, default=1)
    ap.add_argument("--sub-thickness", type=float, default=1.5)
    ap.add_argument("--out", default="ns_pancake_coherent_aggregate_results.json")
    args = ap.parse_args()
    rows = []
    for q in range(3, args.qmax + 1):
        r = run_shell(q, args.low_pass_gap, args.sub_thickness)
        rows.append(r)
        if r.get("empty"):
            continue
        print(f"q={q}: coh={r['rowsum_coherent']:.4f} worst={r['rowsum_worst_cone']:.4f} "
              f"gain={r['coherent_gain']:.4f} axial_frac={r['axial_fraction']:.4f}", flush=True)
    fits = {}
    usable = [r for r in rows if not r.get("empty")]
    if len(usable) >= 2:
        r0, r1 = usable[-2], usable[-1]
        for key in ("coherent_gain",):
            if r0[key] > 0 and r1[key] > 0:
                alpha = math.log(r1[key] / r0[key]) / math.log(r1["delta"] / r0["delta"])
                fits[key] = alpha
                print(f"{key} ~ delta^{alpha:.3f} (last two shells)")
    with open(args.out, "w") as fh:
        json.dump({"rows": rows, "fits": fits}, fh, indent=1)
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
