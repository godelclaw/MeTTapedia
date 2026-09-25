"""Exact beta -> infinity limit of the Wilson measure on an L^4 torus (free lattice Maxwell field).

At weak coupling U_p = exp(i theta_p) with theta_p the lattice curl of the link field, and the
plaquette energy 1 - Re tr U_p / N is theta_p^2 / 2 per colour component. Wick's theorem then gives

    Cov(P_p(x+z), P_q(x)) = (colours / 2) * G_pq(z)^2 / beta^2,

with G the unit-coupling covariance of the plaquette field, computed exactly in momentum space
(the gauge-invariant part of the propagator; the zero mode does not enter). Correlation
coefficients are independent of beta and of the number of colour components, so the same numbers
describe SU(2) and U(1) as beta -> infinity.

Outputs, for block size 2 (the b = 2 blocks of the RG step):
    rho_block(R)  correlation coefficient of block energies at block distance R along an axis,
    rho_time(t)   normalised zero-momentum correlator of spatial-plaquette time-slice sums.
"""
import sys
import numpy as np

PLANES = [(m, n) for m in range(4) for n in range(m + 1, 4)]


def plaquette_covariances(L):
    """Yields ((i, j), G_pq) for i <= j, G_pq(z) = <theta_p(x+z) theta_q(x)>, one pair at a time."""
    k = 2 * np.pi * np.fft.fftfreq(L, d=1.0 / L) / L          # momenta 2 pi n / L
    E1 = np.exp(1j * k) - 1                                    # e^{i k_mu} - 1, one axis
    shape = lambda mu: [L if a == mu else 1 for a in range(4)]
    E = [E1.reshape(shape(mu)) for mu in range(4)]
    khat2 = sum(np.abs(E[mu]) ** 2 for mu in range(4))
    khat2 = np.broadcast_to(khat2, (L,) * 4).copy()
    khat2[0, 0, 0, 0] = np.inf                                 # zero mode drops out of F
    d = lambda a, b: 1.0 if a == b else 0.0
    for i, (m, n) in enumerate(PLANES):
        for j, (r, s) in enumerate(PLANES):
            if j < i:
                continue
            num = (E[m] * np.conj(E[r]) * d(n, s) - E[m] * np.conj(E[s]) * d(n, r)
                   - E[n] * np.conj(E[r]) * d(m, s) + E[n] * np.conj(E[s]) * d(m, r))
            yield (i, j), np.fft.ifftn(np.broadcast_to(num, (L,) * 4) / khat2).real


def reflect(a):
    """a(-z) on the torus."""
    return np.roll(np.flip(a, axis=(0, 1, 2, 3)), shift=1, axis=(0, 1, 2, 3))


def correlations(L, b=2):
    H = np.zeros((L,) * 4)          # sum over all ordered plane pairs of G_pq(z)^2
    Hs = np.zeros((L,) * 4)         # same, restricted to planes not containing axis 0
    spatial = [i for i, (m, n) in enumerate(PLANES) if m != 0 and n != 0]
    for (i, j), g in plaquette_covariances(L):
        g2 = g ** 2
        pair = g2 if i == j else g2 + reflect(g2)
        H += pair
        if i in spatial and j in spatial:
            Hs += pair
    # block-block covariance: sum_{x in B(R), y in B(0)} H(x-y) = (H * w)(bR), w = autocorrelation of 1_B
    ind = np.zeros((L,) * 4)
    ind[:b, :b, :b, :b] = 1.0
    w = np.fft.ifftn(np.abs(np.fft.fftn(ind)) ** 2).real
    HW = np.fft.ifftn(np.fft.fftn(H) * np.fft.fftn(w)).real
    Lb = L // b
    covB = np.array([HW[b * R, 0, 0, 0] for R in range(Lb // 2 + 1)])
    covT = np.array([Hs[t].sum() for t in range(L // 2 + 1)])
    plaq_var = H[0, 0, 0, 0] / 6.0      # average single-plaquette G_pp(0)^2 (diagnostic)
    return covB / covB[0], covT / covT[0], plaq_var


if __name__ == "__main__":
    for L in [int(a) for a in sys.argv[1:]] or [8, 12, 16, 64]:
        rB, rT, _ = correlations(L)
        print(f"L={L}")
        print("  rho_block R=0..:", " ".join(f"{x:.4e}" for x in rB))
        print("  rho_time  t=0..:", " ".join(f"{x:.4e}" for x in rT))
