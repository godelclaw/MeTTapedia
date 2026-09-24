#!/usr/bin/env python3
"""Exact finite-Fourier background for a weighted-adjoint stress test.

On the angle torus, u=(sin(y)(2-cos(z)), sin(x)(3-2cos(z)), 0)
has omega(0)=D omega(0)=0 but nonzero strain and projected cubic flux.
The pointwise quadratic flux response to v=(sin(z),0,0) has a nonzero
signed contraction with the background projected flux.

This fixture tests a proposed local payer for a nonlocal adjoint. It is
not a norm counterexample, an NS blowup example, or a Lean certificate.
All operations use complete finite Fourier supports and rational arithmetic.
"""

from fractions import Fraction as Q

from projected_flux_viscosity import add, curl, flux, gradient_projection, mul, scale, sine_over_i


def check() -> None:
    p = {(0, 0, 0): Q(2), (0, 0, 1): Q(-1, 2), (0, 0, -1): Q(-1, 2)}
    q = {(0, 0, 0): Q(3), (0, 0, 1): Q(-1), (0, 0, -1): Q(-1)}
    u = (mul(sine_over_i(1), p), mul(sine_over_i(0), q), {})
    omega = curl(u)
    omega_zero = [sum(a.values(), Q(0)) for a in omega]
    omega_jet = [[sum((k[j] * value for k, value in a.items()), Q(0))
                  for j in range(3)] for a in omega]
    gradient = [[-sum((k[j] * value for k, value in a.items()), Q(0))
                 for j in range(3)] for a in u]
    projected = [[sum(a.values(), Q(0)) for a in row]
                 for row in gradient_projection(flux(u))]
    assert omega_zero == [0, 0, 0]
    assert omega_jet == [[0, 0, 0]] * 3
    assert gradient == [[0, 1, 0], [1, 0, 0], [0, 0, 0]]
    assert projected == [[0, Q(404, 315), 0], [Q(59, 45), 0, 0], [0, 0, 0]]

    v = (sine_over_i(2), {}, {})
    plus = flux(tuple(add(u[i], v[i]) for i in range(3)))
    minus = flux(tuple(add(u[i], scale(Q(-1), v[i])) for i in range(3)))
    base = flux(u)
    quadratic = [[sum(add(scale(Q(1, 2), plus[j][i]),
                         scale(Q(1, 2), minus[j][i]),
                         scale(Q(-1), base[j][i])).values(), Q(0))
                  for i in range(3)] for j in range(3)]
    assert quadratic == [[0, 0, 0], [-1, 0, 0], [0, 0, 0]]
    contraction = sum((projected[j][i] * quadratic[j][i]
                       for j in range(3) for i in range(3)), Q(0))
    assert contraction == Q(-59, 45)
    print("omega(0) = D omega(0) = 0; strain_xy(0) = strain_yx(0) = 1")
    print("F_12(0) = 404/315; F_21(0) = 59/45")
    print("<F(0), quadratic flux response(0)> =", contraction)
    print("Exact rational fixture passed; no norm counterexample asserted.")


if __name__ == "__main__":
    check()
