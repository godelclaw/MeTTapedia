"""Exact rational Fourier diagnostic for the octic correction, not a Lean proof.

The torus has period 2*pi and normalized measure. The limiting Riesz tensor
has multiplier k_i*k_j/|k|^2 (zero at k=0), not a finite-cutoff kernel.
For u=(0,0,theta(x,y)), nonlinear advection vanishes. Heat evolution is
therefore an exact unforced NS family with pressure zero. This program
evaluates its initial correlation and heat derivative in rational arithmetic.
The tested correction is H=E8/8+C/576. Its initial derivative can be positive
although E8 decreases. This tests this coefficient and this correction, not
all possible smaller coefficients or all signed time-integrated estimates.

The potential has purely imaginary Fourier coefficients i*p_k, p_k rational.
Its vorticity has real Fourier coefficients (-k_y*p_k, k_x*p_k, 0).
No sampled quadrature, floating-point sign test, or time discretization is used.
"""

from fractions import Fraction as F

ZERO = (0, 0)
ONE = {ZERO: F(1)}


def add(*polys):
    result = {}
    for poly in polys:
        for k, c in poly.items():
            result[k] = result.get(k, F(0)) + c
    return {k: c for k, c in result.items() if c}


def scale(poly, scalar):
    return {k: scalar * c for k, c in poly.items() if scalar * c}


def mul(a, b):
    result = {}
    for k, c in a.items():
        for l, d in b.items():
            q = (k[0] + l[0], k[1] + l[1])
            result[q] = result.get(q, F(0)) + c * d
    return {k: c for k, c in result.items() if c}


def power(poly, exponent):
    result = ONE
    for _ in range(exponent):
        result = mul(result, poly)
    return result


def symbol_derivative(poly, axis):
    """The real symbol k_j; the physical derivative has an extra factor i."""
    return {k: k[axis] * c for k, c in poly.items() if k[axis] * c}


def laplacian(poly):
    return {k: -(k[0] ** 2 + k[1] ** 2) * c for k, c in poly.items() if k != ZERO}


def riesz(poly, i, j):
    return {k: F(k[i] * k[j], k[0] ** 2 + k[1] ** 2) * c
            for k, c in poly.items() if k != ZERO and k[i] * k[j]}


def pairing(a, b):
    return sum((c * b.get((-k[0], -k[1]), F(0)) for k, c in a.items()), F(0))


def sine_imaginary(k):
    assert k != ZERO
    return {k: -F(1, 2), (-k[0], -k[1]): F(1, 2)}


def diagnostics(potential):
    assert potential.get(ZERO, 0) == 0
    assert all(potential.get((-k[0], -k[1]), 0) == -c for k, c in potential.items())
    omega = [scale(symbol_derivative(potential, 1), -1), symbol_derivative(potential, 0)]
    assert not add(symbol_derivative(omega[0], 0), symbol_derivative(omega[1], 1))
    dot = [laplacian(w) for w in omega]
    w2 = add(*(power(w, 2) for w in omega))
    w2dot = scale(add(*(mul(w, d) for w, d in zip(omega, dot))), 2)
    r, rdot = power(w2, 2), scale(mul(w2, w2dot), 2)
    correlation = diffusion = mixed = pure = F(0)
    for i in range(2):
        for j in range(2):
            q = mul(w2, mul(omega[i], omega[j]))
            qdot = add(mul(w2dot, mul(omega[i], omega[j])),
                       mul(w2, add(mul(dot[i], omega[j]), mul(omega[i], dot[j]))))
            correlation += pairing(q, riesz(r, i, j))
            diffusion += pairing(qdot, riesz(r, i, j)) + pairing(q, riesz(rdot, i, j))
            for axis in range(2):
                mixed -= 2 * pairing(symbol_derivative(q, axis),
                                     riesz(symbol_derivative(r, axis), i, j))
                d = [symbol_derivative(w, axis) for w in omega]
                d2 = add(*(power(v, 2) for v in d))
                wd = add(*(mul(w, v) for w, v in zip(omega, d)))
                # Each physical gradient has an i, so gradient pairs have a minus sign.
                qcurv = add(scale(mul(d2, mul(omega[i], omega[j])), -2),
                            scale(mul(wd, add(mul(d[i], omega[j]), mul(omega[i], d[j]))), -4),
                            scale(mul(w2, mul(d[i], d[j])), -2))
                rcurv = add(scale(power(wd, 2), -8), scale(mul(w2, d2), -4))
                pure += pairing(qcurv, riesz(r, i, j)) + pairing(q, riesz(rcurv, i, j))
    gradient_sq = scale(add(*(power(symbol_derivative(w, a), 2)
                              for w in omega for a in range(2))), -1)
    g8 = pairing(power(w2, 3), gradient_sq)
    radial = -sum((pairing(power(w2, 2), power(add(*(mul(w, symbol_derivative(w, a))
                                                    for w in omega)), 2)) for a in range(2)), F(0))
    e8 = pairing(r, r)
    e8dot = 2 * pairing(r, rdot)
    assert e8dot == -8 * g8 - 48 * radial
    assert diffusion + pure + mixed == 0
    assert g8 >= 0 and radial >= 0
    return {"C": correlation, "D": diffusion, "P": pure,
            "M": mixed, "G8": g8, "radial": radial, "E8": e8, "E8dot": e8dot}


def localized_profile(m, k, delta):
    """theta=sin(y)+(delta/k)*sin(y)^(2m)*sin(k*x)."""
    sin_sq_y = {ZERO: F(1, 2), (0, 2): -F(1, 4), (0, -2): -F(1, 4)}
    return add(sine_imaginary((0, 1)),
               scale(mul(power(sin_sq_y, m), sine_imaginary((k, 0))), delta / k))


def complementary_profile(m, k, delta):
    """theta=primitive(cos(y)^(2m+1))+(delta/k)*sin(y)^(2m)*sin(k*x).

    At m=3 the mean-zero primitive is
    (35*sin(y)+7*sin(3y)+(7/5)*sin(5y)+(1/7)*sin(7y))/64.
    """
    assert m >= 1 and k >= 1
    cos_y = {(0, 1): F(1, 2), (0, -1): F(1, 2)}
    sin_sq_y = {ZERO: F(1, 2), (0, 2): -F(1, 4), (0, -2): -F(1, 4)}
    derivative = power(cos_y, 2*m + 1)
    assert ZERO not in derivative
    primitive = {q: -c / q[1] for q, c in derivative.items()}
    return add(primitive,
               scale(mul(power(sin_sq_y, m), sine_imaginary((k, 0))), delta/k))


def corrected_growth_witness():
    k, delta = 65536, F(1, 8)
    potential = complementary_profile(3, k, delta)
    # Independent trigonometric expansion; these eleven sine modes are also
    # instantiated by ParallelHeatWitness.lean (whose derivative sign is open).
    modes = [((0, 1), F(35, 64)), ((0, 3), F(7, 64)),
             ((0, 5), F(7, 320)), ((0, 7), F(1, 448)),
             ((k, 0), delta/k * F(10, 32))]
    for j, c in [(2, -F(15, 64)), (4, F(6, 64)), (6, -F(1, 64))]:
        modes.extend([((k, j), delta/k*c), ((k, -j), delta/k*c)])
    assert potential == add(*(scale(sine_imaginary(q), c) for q, c in modes))
    values = diagnostics(potential)
    slope = values["E8dot"]/8 + values["D"]/576
    # These comparisons use rational arithmetic, not the rounded display below.
    assert values["E8dot"] < 0
    assert 12 * values["G8"] < slope < 13 * values["G8"]
    assert len(potential) == 22
    print("complementary witness: m=3, k=65536, delta=1/8, potential terms=22")
    print("exact checks: E8dot < 0; 12*G8 < Hdot < 13*G8; D+P+M = 0")
    print(f"rounded Hdot/G8={float(slope/values['G8']):.15g}")
    print("Scope: limiting Riesz multiplier; the finite-cutoff spatial certificate is not formalized.")


def main():
    one = diagnostics(sine_imaginary((1, 0)))
    assert one["C"] == one["D"] == one["M"] == 0
    print("single shear:", one)
    two = diagnostics(add(sine_imaginary((1, 0)), sine_imaginary((0, 1))))
    assert two == {"C": F(9, 32), "D": -F(9, 4), "P": -F(1, 4),
                   "M": F(5, 2), "G8": F(55, 64), "radial": F(19, 64),
                   "E8": F(169, 64), "E8dot": -F(169, 8)}
    print("equal-frequency two shears:", two)
    for m, k, delta in [(1, 16, F(1, 2)), (2, 64, F(1, 2)), (4, 256, F(1, 2)), (8, 1024, F(1, 2))]:
        values = diagnostics(localized_profile(m, k, delta))
        print(f"m={m}, k={k}, delta={delta}: "
              f"sign(D)={(values['D'] > 0)-(values['D'] < 0)}, "
              f"D/G8≈{float(values['D']/values['G8']):.8g}, "
              f"M/G8≈{float(values['M']/values['G8']):.8g}")
    corrected_growth_witness()


if __name__ == "__main__":
    main()
