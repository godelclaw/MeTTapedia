"""Exact rational Fourier diagnostic; not a Lean proof.

On the 2*pi periodic torus, let
    u = (a sin(y), 0, b sin(x) + c sin(x+y)).
This is a smooth, mean-zero, divergence-free three-dimensional field,
independent of z. It is used as initial data, not asserted to be an NS
trajectory. Its vorticity and signed eighth-moment stretching density are
    omega = (c C, -b X-c C, -a Y),
    |omega|^6 omega.S.omega = q^3 s,
    q = c^2 C^2 + (b X+c C)^2 + a^2 Y^2,
    s = -a c Y C (b X+c C),
where X=cos(x), Y=cos(y), C=cos(x+y).

The heat tangent at viscosity one has a'=-a, b'=-b, c'=-2c.
Constant Fourier coefficients are normalized spatial integrals. All
calculations below use rational arithmetic, with no grid or quadrature.
Sign reversal tests a universal sign for the isolated signed channel,
not a global NS regularity claim or monotonicity of its absolute value.
"""

from fractions import Fraction


def add(*polys):
    out = {}
    for poly in polys:
        for k, value in poly.items():
            out[k] = out.get(k, Fraction(0)) + value
    return {k: value for k, value in out.items() if value}


def scale(c, poly):
    return {k: Fraction(c) * value for k, value in poly.items() if c * value}


def mul(*polys):
    out = {(0, 0): Fraction(1)}
    for poly in polys:
        nxt = {}
        for k, value in out.items():
            for j, coeff in poly.items():
                index = (k[0] + j[0], k[1] + j[1])
                nxt[index] = nxt.get(index, Fraction(0)) + value * coeff
        out = {k: value for k, value in nxt.items() if value}
    return out


def cosine(k):
    return {k: Fraction(1, 2), (-k[0], -k[1]): Fraction(1, 2)}


def mean(poly):
    return poly.get((0, 0), Fraction(0))


def evaluate(a, b, c):
    x, y, z = cosine((1, 0)), cosine((0, 1)), cosine((1, 1))
    da, db, dc = -a, -b, -2 * c
    r = add(scale(b, x), scale(c, z))
    dr = add(scale(db, x), scale(dc, z))
    q = add(scale(c * c, mul(z, z)), mul(r, r), scale(a * a, mul(y, y)))
    dq = add(scale(2 * c * dc, mul(z, z)), scale(2, mul(r, dr)),
             scale(2 * a * da, mul(y, y)))
    s = scale(-a * c, mul(y, z, r))
    ds = add(scale(-(da * c + a * dc), mul(y, z, r)),
             scale(-a * c, mul(y, z, dr)))
    source = mean(mul(q, q, q, s))
    heat_rate = mean(add(scale(3, mul(q, q, dq, s)), mul(q, q, q, ds)))
    return source, heat_rate


if __name__ == "__main__":
    pos = evaluate(1, 1, 1)
    neg = evaluate(-1, -1, -1)
    assert pos == (Fraction(-3289, 128), Fraction(22289, 64))
    assert neg == tuple(-value for value in pos)
    assert pos[0] < 0 < pos[1]
    assert evaluate(2, 2, 2) == tuple(2**9 * value for value in pos)
    for amplitudes in ((0, 1, 1), (1, 0, 1), (1, 1, 0)):
        assert evaluate(*amplitudes) == (0, 0)
    step = Fraction(1, 10**6)
    difference = (evaluate(1-step, 1-step, 1-2*step)[0]
                  - evaluate(1+step, 1+step, 1+2*step)[0]) / (2 * step)
    assert abs(difference - pos[1]) < Fraction(1, 10**6)
    for label, result in (("u", pos), ("-u", neg)):
        print(f"{label}: normalized stretching={result[0]}; heat tangent={result[1]}")
    print("Exact rational Fourier calculation; Lean integration bridge not yet proved.")
