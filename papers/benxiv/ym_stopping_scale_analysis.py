"""Analysis for ym_stopping_scale_mc.c: the stopping-scale test of the Yang-Mills companion.

Runs used in the companion (group L beta ntherm nmeas nor seed start); each writes
<group>-L<L>-b<beta>.bin:
    u1  8 150 500 4000 3 101 cold     u1 12 150 500 4000 3 102 cold     u1 16 150 500 3000 3 103 cold
    u1  8 2.0 500 4000 3 104 cold     u1 12 2.0 500 4000 3 105 cold     u1 16 2.0 500 3000 3 106 cold
    u1  8 0.8 500 4000 3 107 hot      u1 12 0.8 500 4000 3 108 hot      u1 16 0.8 500 3000 3 109 hot
    su2 8 150 500 4000 3 201 cold     su2 12 150 500 4000 3 202 cold    su2 16 150 500 3000 3 203 cold
    su2 12 2.5 500 4000 3 204 hot     su2 16 2.5 500 3000 3 205 hot

usage: python3 ym_stopping_scale_analysis.py *.bin   (table of the companion; numpy only)
       python3 ym_stopping_scale_analysis.py --scales   (scale bookkeeping and v14's constants)

Per run: plaquette energy, the correlation coefficient rho_block(R) of 2^4-block energies at block
distance R along an axis, the normalised time-slice correlator of spatial-plaquette sums, and for
U(1) the transverse-photon correlator (sin theta_bc at momentum 2 pi/L along b, polarisation c,
time a) with its cosh effective mass. Errors: jackknife over 40 bins.
"""
import sys
import numpy as np


def load(path):
    with open(path, "rb") as f:
        L, group = np.frombuffer(f.read(8), dtype=np.int32)
        beta = np.frombuffer(f.read(8), dtype=np.float64)[0]
        (nmeas,) = np.frombuffer(f.read(4), dtype=np.int32)
        Lb = L // 2
        NB = Lb ** 4
        rec = 1 + NB + 4 * L + (48 * L if group == 1 else 0)
        data = np.frombuffer(f.read(), dtype=np.float64)
    n = data.size // rec
    data = data[: n * rec].reshape(n, rec)
    out = {"L": int(L), "group": int(group), "beta": float(beta), "n": n,
           "plaq": data[:, 0],
           "E": data[:, 1:1 + NB].reshape(n, Lb, Lb, Lb, Lb),
           "O": data[:, 1 + NB:1 + NB + 4 * L].reshape(n, 4, L)}
    if group == 1:
        ph = data[:, 1 + NB + 4 * L:].reshape(n, 24, L, 2)
        out["Ph"] = ph[..., 0] + 1j * ph[..., 1]
    return out


def per_config(d):
    """Per-configuration translation- and axis-averaged products (the jackknife inputs)."""
    L = d["L"]; Lb = L // 2
    E = d["E"]; O = d["O"]
    Ebar = E.mean(axis=(1, 2, 3, 4))
    cB = np.stack([np.mean([(E * np.roll(E, -R, axis=ax)).mean(axis=(1, 2, 3, 4)) for ax in (1, 2, 3, 4)], axis=0)
                   for R in range(Lb // 2 + 1)], axis=1)
    Obar = O.mean(axis=(1, 2))
    cT = np.stack([(O * np.roll(O, -t, axis=2)).mean(axis=(1, 2)) for t in range(L // 2 + 1)], axis=1)
    cols = {"plaq": d["plaq"], "Ebar": Ebar, "cB": cB, "Obar": Obar, "cT": cT}
    if "Ph" in d:
        P = d["Ph"]
        cols["cP"] = np.stack([np.real(np.roll(P, -t, axis=2) * np.conj(P)).mean(axis=(1, 2)) for t in range(L // 2 + 1)], axis=1)
    return cols


def cosh_mass(c, L):
    """m with c(t)/c(t+1) = cosh(m(L/2-t))/cosh(m(L/2-t-1)), by bisection; nan if not monotone."""
    m = np.full(len(c) - 1, np.nan)
    for t in range(len(c) - 1):
        if not (c[t] > 0 and c[t + 1] > 0 and c[t] > c[t + 1]):
            continue
        r = c[t] / c[t + 1]
        f = lambda x: np.cosh(x * (L / 2 - t)) / np.cosh(x * (L / 2 - t - 1)) - r
        lo, hi = 1e-9, 20.0
        if f(hi) < 0:
            continue
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if f(mid) > 0: hi = mid
            else: lo = mid
        m[t] = 0.5 * (lo + hi)
    return m


def estimates(cols, L):
    rB = (cols["cB"].mean(0) - cols["Ebar"].mean() ** 2)
    rT = (cols["cT"].mean(0) - cols["Obar"].mean() ** 2)
    res = {"plaq": cols["plaq"].mean(), "rho_block": rB / rB[0], "rho_time": rT / rT[0]}
    if "cP" in cols:
        cP = cols["cP"].mean(0)
        res["photon"] = cP / cP[0]
        res["m_photon"] = cosh_mass(cP, L)
    return res


def jackknife(cols, L, nbins=40):
    n = len(cols["plaq"])
    nb = min(nbins, n)
    edges = np.linspace(0, n, nb + 1).astype(int)
    full = estimates(cols, L)
    reps = []
    for b in range(nb):
        keep = np.r_[0:edges[b], edges[b + 1]:n]
        reps.append(estimates({k: v[keep] for k, v in cols.items()}, L))
    err = {}
    for k in full:
        arr = np.array([r[k] for r in reps])
        err[k] = np.sqrt((nb - 1) * np.nanmean((arr - np.nanmean(arr, axis=0)) ** 2, axis=0))
    return full, err


def fmt(v, e):
    return " ".join(f"{a:10.3e}({b:.1e})" for a, b in zip(np.atleast_1d(v), np.atleast_1d(e)))


def scales():
    """SU(2) scale bookkeeping along v14's trajectory, and v14's constants."""
    import math
    N = 2
    b0 = 11 * N / (48 * math.pi ** 2)
    b1 = (34 / 3) * N ** 2 / (16 * math.pi ** 2) ** 2
    def ln_a_lambda(beta):                      # two-loop asymptotic scaling, a Lambda_L
        g2 = 2 * N / beta
        return -(b1 / (2 * b0 ** 2)) * math.log(b0 * g2) - 1 / (2 * b0 * g2)
    b0v14 = 11 / (3 * 16 * math.pi ** 2)
    print(f"one-loop drift of beta per b=2 step: 4N^2 b0 log 2 = {4*N*N*b0v14*math.log(2):.4f}; "
          f"v14's 4N b0 log 2 = {4*N*b0v14*math.log(2):.4f}")
    steps = (ln_a_lambda(2.5) - ln_a_lambda(150.0)) / math.log(2)
    print(f"b=2 steps from beta=150 to beta=2.5 (two loop): {steps:.0f}; "
          f"length ratio 10^{(ln_a_lambda(2.5) - ln_a_lambda(150.0)) / math.log(10):.1f}")
    m_over_lambda = 3.8 * 0.18 / math.exp(ln_a_lambda(2.5))   # m_0++/sqrt(sigma) ~ 3.8, a sqrt(sigma) ~ 0.18 at 2.5
    print(f"a m_0++ at beta=150 ~ 10^{(math.log(m_over_lambda) + ln_a_lambda(150.0)) / math.log(10):.1f}")
    print("v14 App. F.5 factor product at b=2:", 7.4 * 10 * 16 * 14 * 2, "; App. O.6:", round(1.65 * 3 * 16 * 14 * 2, 1))
    print("v14 projector bound 1 + 16 (1/2)^-16 =", 1 + 16 * 2 ** 16)


if __name__ == "__main__":
    if sys.argv[1:] == ["--scales"]:
        scales()
        sys.exit()
    from ym_stopping_scale_free_field import correlations
    free = {}
    for path in sys.argv[1:]:
        d = load(path)
        L = d["L"]
        if L not in free:
            free[L] = correlations(L)[0]
        full, err = jackknife(per_config(d), L)
        g = "SU(2)" if d["group"] == 2 else "U(1)"
        line = (f"{g:5s} beta={d['beta']:6.1f} L={L:2d}  plaq {full['plaq']:.6f}  "
                f"rho_block(1) {full['rho_block'][1]:.4f}({err['rho_block'][1] * 1e4:.0f})  [free {free[L][1]:.4f}]")
        if "m_photon" in full:
            m, e = full["m_photon"], err["m_photon"]
            line += f"  photon m_eff(0) {m[0]:.3f}({e[0] * 1e3:.0f})"
            if np.isfinite(m[1]) and e[1] < 0.1:
                line += f" m_eff(1) {m[1]:.3f}({e[1] * 1e3:.0f})"
            line += f"  [massless {2 * np.arcsinh(np.sin(np.pi / L)):.3f}]"
        print(line)
