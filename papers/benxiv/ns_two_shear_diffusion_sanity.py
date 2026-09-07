"""Numerical diagnostic, NOT a proof or interval-certified quadrature.

Periodic divergence-free velocity:
  u = (2 eps/N sin(N y), -2 sin(x), 0).
Write f=eps*cos(N*y), g=cos(x).  Then the actual top spectral
defect is D=4*abs(f-g)*(f+g)**2. Under the physical heat evolution,
f_t=-nu*N**2*f and g_t=-nu*g.

The f phase is sampled over one period: every integer N repeats that
period exactly, so the normalized spatial integral is unchanged by
replacing N*y with an independent phase theta.
"""

import numpy as np

EPS = 1 / 16
N = 64
NU = 1.0


def evaluate(n):
    x = 2 * np.pi * (np.arange(n) + 0.173) / n
    theta = 2 * np.pi * (np.arange(n) + 0.319) / n
    g = np.cos(x)[:, None]
    f = EPS * np.cos(theta)[None, :]
    defect = 4 * np.abs(f - g) * (f + g) ** 2
    f_rate = -NU * N**2 * f
    g_rate = -NU * g
    rate = 4 * np.sign(f - g) * (f_rate - g_rate) * (f + g) ** 2
    rate += 8 * np.abs(f - g) * (f + g) * (f_rate + g_rate)
    dt = 1e-7
    f_next = f * np.exp(-NU * N**2 * dt)
    g_next = g * np.exp(-NU * dt)
    defect_next = 4 * np.abs(f_next - g_next) * (f_next + g_next) ** 2
    print(
        f"grid={n:4d} mean_D={defect.mean():.12f} "
        f"mean_heat_rate={rate.mean():.12f} "
        f"forward_difference={(defect_next.mean()-defect.mean())/dt:.12f} "
        f"min_abs_gap={np.abs(f-g).min():.3e}"
    )


if __name__ == "__main__":
    print(f"eps={EPS}, N={N}, nu={NU}; numerical evidence only")
    for grid in (256, 512, 1024, 2048):
        evaluate(grid)
