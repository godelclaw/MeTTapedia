"""Migdal-Kadanoff flows on the diamond hierarchical lattice, where the recursion is exact.

Block factor b = 2 in dimension d.  One step acts on the plaquette weight f:
    bond moving   f -> f^(b^(d-2))                   (pointwise power, i.e. products of characters)
    decimation    c_r -> c_r^(b^2)                   (normalized character coefficients)
All arithmetic is on character coefficients in 110-digit decimal arithmetic, so the exponentially
small abelian drift in d = 4 is resolved.  Standard library only.

U(1):  f = sum_k c_k e^{ik theta};  start from the Villain weight c_k = exp(-k^2 / (2 beta));
       effective coupling beta_eff = -1 / (2 log c_1).
SU(2): f = sum_j (2j+1) c_j chi_j;  start from the heat kernel c_j = exp(-t j (j+1));
       effective time t_eff = -(4/3) log c_{1/2}; the Wilson coupling is beta ~ 2 / t at weak coupling.

Output:
  1. d = 4, U(1): the drift of beta_eff per step once the weight has relaxed, for beta = 1 ... 5,
     and the local exponent a in drift = -C beta^2 exp(-a beta).
  2. d = 4, SU(2): the change of 1/t_eff per step (weak coupling: -1/8, i.e. -0.25 in beta).
  3. d = 5: both groups flow to weak coupling.
  4. The twist free energy of one coarse plaquette, F_n = -log f_n(-1) / f_n(1), with f_n the plaquette
     weight after n steps and -1 the centre element of SU(2), or the flux pi for U(1).  In d = 4 it flows
     to 0 for both groups, in d = 5 it grows for both.
"""
from decimal import Decimal, getcontext
import math

getcontext().prec = 110
D = Decimal


def u1_mul(a, b, K):
    return {k: sum((a[j] * b[k - j] for j in range(max(-K, k - K), min(K, k + K) + 1)), D(0))
            for k in range(-K, K + 1)}


def u1_step(c, d, K):
    p = c
    for _ in range(2 ** (d - 2) - 1):
        p = u1_mul(p, c, K)
    return {k: (p[k] / p[0]) ** 4 for k in p}


def u1_villain(beta, K):
    return {k: (-D(k * k) / (2 * beta)).exp() for k in range(-K, K + 1)}


def u1_beta(c):
    return -1 / (2 * c[1].ln())


def su2_mul(a, b, N):
    out = [D(0)] * (N + 1)
    for n1 in range(N + 1):
        for n2 in range(N + 1):
            prod = a[n1] * b[n2]
            for n3 in range(abs(n1 - n2), min(n1 + n2, N) + 1, 2):
                out[n3] += prod
    return out


def su2_step(c, d, N):
    a = [D(n + 1) * c[n] for n in range(N + 1)]
    p = a
    for _ in range(2 ** (d - 2) - 1):
        p = su2_mul(p, a, N)
    return [(p[n] / (D(n + 1) * p[0])) ** 4 for n in range(N + 1)]


def su2_heat(t, N):
    return [(-t * D(n) * D(n + 2) / 4).exp() for n in range(N + 1)]


def su2_inv_t(c):
    return -3 / (4 * c[1].ln())


def u1_twist(c):
    """-log f(pi) / f(0) for f = sum_k c_k e^{ik theta}."""
    return -(sum(((-1) ** abs(k)) * v for k, v in c.items()) / sum(c.values())).ln()


def su2_twist(c):
    """-log f(-1) / f(1) for f = sum_n (n+1) c_n chi_{n/2}, chi_{n/2}(+-1) = (+-1)^n (n+1)."""
    N = len(c) - 1
    num = sum(((-1) ** n) * D(n + 1) ** 2 * c[n] for n in range(N + 1))
    den = sum(D(n + 1) ** 2 * c[n] for n in range(N + 1))
    return -(num / den).ln()


def main():
    K, N = 40, 40
    print("1. d = 4, U(1), Villain start: drift of beta_eff per step after 9 steps")
    rows = []
    for s in ("1", "1.5", "2", "2.5", "3", "3.5", "4", "5"):
        c = u1_villain(D(s), K)
        traj = []
        for _ in range(10):
            traj.append(u1_beta(c))
            c = u1_step(c, 4, K)
        drift = traj[-1] - traj[-2]
        rows.append((float(traj[-2]), float(drift)))
        print(f"   beta = {s:>3}:  drift {float(drift):+.4e}")
    for (b1, d1), (b2, d2) in zip(rows, rows[1:]):
        a = (math.log(-d1 / b1 ** 2) - math.log(-d2 / b2 ** 2)) / (b2 - b1)
        print(f"   local exponent a on [{b1:.3g}, {b2:.3g}]: {a:.4f}")
    print(f"   (8 pi^2 / 5 = {1.6 * math.pi ** 2:.4f})")

    print("2. d = 4, SU(2), heat-kernel start: change of 1/t_eff per step")
    for s in ("0.5", "0.2", "0.1", "0.05"):
        c = su2_heat(D(s), N)
        inv = []
        for _ in range(6):
            inv.append(float(su2_inv_t(c)))
            c = su2_step(c, 4, N)
        print(f"   t = {s:>4}:  " + " ".join(f"{inv[i + 1] - inv[i]:+.4f}" for i in range(len(inv) - 1)))

    print("3. d = 5: the first three steps")
    for s in ("1", "2"):
        c = u1_villain(D(s), K)
        traj = [float(u1_beta(c))]
        for _ in range(3):
            c = u1_step(c, 5, K)
            traj.append(float(u1_beta(c)))
        print(f"   U(1),  beta = {s}:  beta_eff " + " -> ".join(f"{x:.4g}" for x in traj))
    for s in ("0.5", "0.2"):
        c = su2_heat(D(s), N)
        traj = [float(su2_inv_t(c))]
        for _ in range(3):
            c = su2_step(c, 5, N)
            traj.append(float(su2_inv_t(c)))
        print(f"   SU(2), t = {s}:  1/t_eff " + " -> ".join(f"{x:.4g}" for x in traj))

    print("4. The twist free energy of one coarse plaquette along the flow")
    for s, n in (("1.5", 12), ("3", 12)):
        c = u1_villain(D(s), K)
        traj = [float(u1_twist(c))]
        for _ in range(n):
            c = u1_step(c, 4, K)
            traj.append(float(u1_twist(c)))
        print(f"   d = 4, U(1),  beta = {s:>3}:  F " + " -> ".join(f"{x:.4g}" for x in traj))
    for s, n in (("0.5", 16), ("0.2", 12)):
        c = su2_heat(D(s), N)
        traj = [float(su2_twist(c))]
        for _ in range(n):
            c = su2_step(c, 4, N)
            traj.append(float(su2_twist(c)))
        print(f"   d = 4, SU(2), t = {s:>3}:  F " + " -> ".join(f"{x:.3g}" for x in traj))
    K5 = N5 = 100   # weak coupling grows in d = 5: more characters keep the ratio resolved
    c = u1_villain(D("1.5"), K5)
    traj = [float(u1_twist(c))]
    for _ in range(3):
        c = u1_step(c, 5, K5)
        traj.append(float(u1_twist(c)))
    print("   d = 5, U(1),  beta = 1.5:  F " + " -> ".join(f"{x:.4g}" for x in traj))
    c = su2_heat(D("0.5"), N5)
    traj = [float(su2_twist(c))]
    for _ in range(2):
        c = su2_step(c, 5, N5)
        traj.append(float(su2_twist(c)))
    print("   d = 5, SU(2), t = 0.5:  F " + " -> ".join(f"{x:.4g}" for x in traj))

if __name__ == "__main__":
    main()
