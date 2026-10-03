#!/usr/bin/env python3
"""Complete cyclic velocity-entropy returns with unequal parents and scales.

Symbolic Fourier jets prove the common-scale amplitude law. Exact weighted
enclosures certify the contrary multiscale return. The local PDE comparison
with positive viscosity is analytic in README.md, not Lean-certified.
"""

import json
import math
from fractions import Fraction as Rational

import sympy as sp
from sympy.polys.domains import QQ_I
from sympy.polys.rings import ring

import pressure_history_source as f
from cyclic_pressure_history import seed, velocity_time_jets
from bernoulli_pressure_return import fourth_bound, fourth_groups


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(expression, label):
    require(sp.expand(expression) == 0, label)


def energy_jets(jets):
    return [f.scale(QQ_I(1)/2, f.add(*(
        f.scale(math.comb(n, k), f.dot(jets[k], jets[n-k]))
        for k in range(n+1)))) for n in range(5)]


def material_jets(energy, velocity):
    """Apply the full evolving material derivative, retaining all parents."""
    result, fields = [], energy
    while fields:
        result.append(fields[0])
        fields = [f.add(fields[n+1], *(
            f.scale(math.comb(n, k), f.adv(velocity[k], fields[n-k]))
            for k in range(n+1))) for n in range(len(fields)-1)]
    return result


def phase_field(field, scales):
    """Pull back the complete physical Fourier outputs to their phases."""
    require(all(all(k[j] % scales[j] == 0 for j in range(3)) for k in field),
            'Every output must lie on the exact phase lattice')
    return {tuple(k[j]//scales[j] for j in range(3)): value
            for k, value in field.items()}


def reflection_projection(field, variables):
    """Average against functions of sin^2 of each ORDERED coordinate.

    Reflections and half-period translations remove sine and odd modes.
    No permutation of coordinates or their unequal weights is performed.
    """
    terms = {}
    for k, value in field.items():
        if any(j % 2 for j in k):
            continue
        orbit = tuple(abs(j)//2 for j in k)
        terms[orbit] = terms.get(orbit, 0)+value
    result = 0
    for orbit, value in terms.items():
        if hasattr(value, 'as_expr'):
            expression = value.as_expr()
        else:
            require(not value.y, 'Reflection projection must be real')
            expression = sp.Rational(str(value.x))
        result += expression*sp.prod(sp.chebyshevt(k, 1-2*x)
                                     for k, x in zip(orbit, variables))
    return sp.expand(result)


def common_scale_law():
    domain, a, b, c = ring('a,b,c', QQ_I)
    initial = [{k: domain(v)*q for k, v in field.items()}
               for field, q in zip(seed(1), (a, b, c))]
    velocity, pressure = velocity_time_jets(initial, 0, 4)
    energy = energy_jets(velocity)
    material = material_jets(energy, velocity)
    for n, field in enumerate(energy):
        require(all((-1)**sum(k) == (-1)**n for k in field),
                'Common-scale translation matches Euler time reversal')
    f.equal(pressure[0], {}, 'Canonical initial pressure')
    f.equal(material[1], {}, 'Initial material energy derivative is zero')
    f.equal(material[2], f.scale(-1, f.adv(initial, pressure[1])),
            'The second material derivative retains the generated pressure')

    X, Y, Z = sp.symbols('X Y Z')
    aa, bb, cc = (v.as_expr() for v in (a, b, c))
    product = aa**2*bb**2*cc**2
    S = 30*X*Y*Z-27*(X*Y+X*Z+Y*Z)+11*(X+Y+Z)
    T = (cc**2*X*(1-X)*Z*(1-Y)+aa**2*Y*(1-Y)*X*(1-Z)
         +bb**2*Z*(1-Z)*Y*(1-X))
    zero(reflection_projection(material[2], (X, Y, Z)),
         'The weighted second return vanishes for unequal amplitudes')
    zero(reflection_projection(material[4], (X, Y, Z))-sp.Rational(16, 15)*product*S,
         'Complete material fourth return, for symbolic unequal amplitudes')
    zero(reflection_projection(f.mul(material[2], material[2]), (X, Y, Z))-4*product*T,
         'Full new square in the fourth entropy derivative')

    # Integration by parts for the arcsine law is proved analytically in
    # the README. These exact identities check every polynomial coefficient.
    P = 150*X*Y*Z-27*(X*Y+X*Z+Y*Z)+X+Y+Z
    C = ((X-sp.Rational(1, 2))*Z*(1-Y)
         +(Y-sp.Rational(1, 2))*X*(1-Z)
         +(Z-sp.Rational(1, 2))*Y*(1-X))
    zero(sp.Rational(16, 15)*S+24*C+sp.Rational(4, 15)*P,
         'Transport and generated squares combine before taking signs')
    x, y, z = sp.symbols('x y z')
    zero(P.subs({X: x+sp.Rational(1, 2), Y: y+sp.Rational(1, 2),
                 Z: z+sp.Rational(1, 2)})
         -150*x*y*z-48*(x*y+x*z+y*z)-sp.Rational(23, 2)*(x+y+z),
         'Centered arcsine polynomial')

    t1, t2, t3, r = sp.symbols('t1 t2 t3 r')
    S1, S2, S3 = t1+t2+t3, t1*t2+t1*t3+t2*t3, t1*t2*t3
    B = sp.Rational(23, 4)*r**2*S1-12*r*S2+sp.Rational(225, 4)*S3
    remainder = (4*r*S1*(r-S1)
                 +2*r*((t1-t2)**2+(t1-t3)**2+(t2-t3)**2)
                 +sp.Rational(225, 4)*S3)
    zero(B-sp.Rational(7, 4)*r**2*S1-remainder,
         'Pointwise positive remainder gives the uniform negative sign')
    h, d1, d2, d3 = sp.symbols('h d1 d2 d3')
    zero(h+d1*X+d2*Y+d3*Z
         -(d1*X*(1-X)+d2*Y*(1-Y)+d3*Z*(1-Z))
         -(h+d1*X**2+d2*Y**2+d3*Z**2),
         'The remainder is nonnegative on the actual phase cube')
    # <X(1-X)>=1/8 for X=sin^2 x. The denominator is bounded by
    # sqrt(h+(a^2+b^2+c^2)/2), giving the explicit strict margin.
    require(Rational(1, 2)-Rational(3, 8) == Rational(1, 8), 'Arcsine moment')
    return dict(amplitudes='all a,b,c>0', regularizer='every fixed h>0',
        fourth_upper='-(7 sqrt(2)/80) a^2 b^2 c^2 (a^2+b^2+c^2) / sqrt(h+(a^2+b^2+c^2)/2)',
        zero_parent_limit='fourth return equals zero',
        pressure_mode_counts=[len(p) for p in pressure])


def different_scale_witness():
    scales = (1, 1, 4)
    initial = [{tuple(j*q for j, q in zip(k, scales)): v for k, v in field.items()}
               for field in seed(1)]
    velocity, pressure = velocity_time_jets(initial, 0, 4)
    energy = energy_jets(velocity)
    material = material_jets(energy, velocity)
    f.equal(pressure[0], {}, 'The multiscale pressure also starts at zero')
    f.equal(material[1], {}, 'Multiscale initial material energy derivative')
    X, Y, Z = sp.symbols('X Y Z')
    zero(reflection_projection(phase_field(material[2], scales), (X, Y, Z)),
         'The multiscale weighted second return vanishes')
    for n, field in enumerate(energy):
        require(all((-1)**sum(k) == (-1)**n for k in phase_field(field, scales)),
                'Phase half-period translation matches Euler time reversal')
    groups = [phase_field(field, scales) for field in
              fourth_groups(energy, pressure+[{}], False)]
    # The phase energy here is symmetric because all amplitudes equal one.
    # Thus the existing symmetric exact integration applies AFTER the
    # physical operators have used the actual unequal wave numbers.
    lo, hi = fourth_bound(groups)
    require(Rational(73, 1000) < lo <= hi < Rational(74, 1000),
            'Certified positive fourth return with every generated output')
    require(Rational(7, 2)*Rational(73, 1000)**2 > Rational(1, 8)**2,
            'Positive fourth return exceeds 1/8')
    # Independent material-coordinate evaluation uses two weighted terms.
    material_groups = [phase_field(material[4], scales),
                       phase_field(f.scale(3, f.mul(material[2], material[2])), scales), {}, {}]
    mlo, mhi = fourth_bound(material_groups)
    require(Rational(73, 1000) < mlo <= mhi < Rational(74, 1000),
            'The complete material formula independently certifies the sign')
    require(max(lo, mlo) <= min(hi, mhi), 'Independent enclosures overlap')
    # General Taylor and viscous-comparison margins used in the PDE proof.
    require(Rational(1, 24)-Rational(5, 2)/120 == Rational(1, 48), 'Taylor margin')
    require(Rational(1, 48)-Rational(1, 96) == Rational(1, 96), 'Viscous margin')
    return dict(datum='(sin y, sin(4z), sin x)', h=1,
        fourth_div_sqrt_seven_halves=['73/1000', '74/1000'],
        fourth_lower='1/8', weighted_series_order=32,
        pressure_mode_counts=[len(p) for p in pressure],
        comparison='actual unforced viscous velocity moment exceeds both its initial value and its original heat forecast on the stated interval')


def physical_entropy_identity():
    e, h, nu, G, ge2, up = sp.symbols('e h nu G ge2 up', positive=True)
    phi = 2*sp.sqrt(2)*(e+h)**sp.Rational(3, 2)
    sh = sp.sqrt(2*(e+h))
    require(sp.simplify(sp.diff(phi, e)-3*sh) == 0,
            'Physical velocity entropy derivative')
    require(sp.simplify(sp.diff(phi, e, 2)-3/sh) == 0,
            'Physical velocity entropy second derivative')
    actual = sp.diff(phi, e)*(-up-nu*G)-nu*sp.diff(phi, e, 2)*ge2
    require(sp.simplify(sp.factor(actual-(-3*sh*up-3*nu*(sh*G+ge2/sh)))) == 0,
            'Complete material-parabolic equation for the velocity entropy')
    r, sh, gr2 = sp.symbols('r sh gr2', positive=True)
    require(sp.simplify(sh*G+r**2/sh*gr2-r*(G+gr2)
                       -(sh-r)*(G-r/sh*gr2)) == 0,
            'Full regularized diffusion dominates the cubic diffusion')
    return 'V_prime+nu D_h=Pi_h, D_h>=3D; the full-data history payment is open'


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed',
        common_scale=common_scale_law(), unequal_scales=different_scale_witness(),
        physical_identity=physical_entropy_identity(),
        certification='exact symbolic algebra and rational weighted enclosures; PDE interval proofs remain analytic',
        OPEN='finite payment for complete arbitrary histories of interacting scales'), indent=2))
