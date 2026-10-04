#!/usr/bin/env python3
"""Exact Gaussian covariance work in a nonlinear heat-history reserve.

Every Fourier output is retained. The identities and rational bounds here
support the analytic heat-history and actual-flow arguments in README.md;
they are neither a closed Fourier evolution nor Lean certificates.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import heat_work_reserve as h
import joint_heat_cancellation as cyclic
from generated_fourth_moment import pressure, pair, vector_pair
from heat_remainder_pressure import plus, times, solenoidal, projection, require, same
from heat_work_parent_payment import heat as rational_heat


def zero(expression, label):
    require(s.expand(expression) == 0, label)


def tensor_divergence(tensor):
    return [f.add(*(f.diff(tensor[i][j], j) for j in range(3))) for i in range(3)]


def cotangent(z):
    square = f.dot(z, z)
    gradient = f.grad(pressure(z))
    radial = f.dot(z, gradient)
    projected = projection([f.mul(square, row) for row in z])
    return [f.add(f.scale(-1, f.mul(square, gradient[j])),
                  f.scale(-2, f.mul(radial, z[j])),
                  f.scale(2, f.add(*(f.mul(f.diff(z[i], j), projected[i])
                                     for i in range(3))))) for j in range(3)]


def covariance_identities(w):
    z = h.heat(w)
    product = f.tensor(w, w)
    zz = f.tensor(z, z)
    tau = [[f.add(h.heat([product[i][j]])[0], f.scale(-1, zz[i][j]))
            for j in range(3)] for i in range(3)]
    source = [[f.add(*(f.mul(f.diff(z[i], j), f.diff(z[k], j)) for j in range(3)))
               for k in range(3)] for i in range(3)]
    for i in range(3):
        for j in range(3):
            derivative = {k: -h.HEAT*value.diff(h.HEAT) for k, value in tau[i][j].items()}
            f.equal(f.add(derivative, f.scale(-1, f.lap(tau[i][j]))),
                    f.scale(2, source[i][j]), 'Complete covariance heat equation')
            at_zero = {k: f.QQ_I.from_sympy(h.RING.to_sympy(value).subs(h.q, 1))
                       for k, value in tau[i][j].items()}
            f.equal(at_zero, {}, 'Covariance starts at zero')
    commutator = plus(h.heat(h.nonlinear(w)), times(-1, h.nonlinear(z)))
    same(commutator, times(-1, solenoidal(tensor_divergence(tau))),
         'Heat and nonlinearity differ by the full projected covariance divergence')

    rows = []
    for q in (Q(1, 2), Q(3, 4)):
        rz = rational_heat(w, q)
        rt = [[f.add(rational_heat([product[i][j]], q)[0],
                    f.scale(-1, f.mul(rz[i], rz[j]))) for j in range(3)] for i in range(3)]
        c = plus(rational_heat(h.nonlinear(w), q), times(-1, h.nonlinear(rz)))
        projected = solenoidal(cotangent(rz))
        jacobian = f.jac(projected)
        M = [[f.scale(Q(1, 2), f.add(jacobian[i][j], jacobian[j][i]))
              for j in range(3)] for i in range(3)]
        f.equal(f.trace(M), {}, 'The projected response tensor is pointwise trace free')
        trace = f.trace(rt)
        dev = [[f.add(rt[i][j], f.scale(Q(-1, 3), trace)) if i == j else rt[i][j]
                for j in range(3)] for i in range(3)]
        direct = vector_pair(cotangent(rz), c)
        stress_work = sum((pair(M[i][j], rt[i][j]) for i in range(3) for j in range(3)), Q(0))
        anisotropic_work = sum((pair(M[i][j], dev[i][j]) for i in range(3) for j in range(3)), Q(0))
        require(direct == stress_work == anisotropic_work and direct > 0,
                'The positive work is exactly the anisotropic covariance contraction')
        # An actual unforced initial tangent, including positive viscosity.
        # The same general identity applies to the generated component with
        # its full parent-dependent source; that source must not be reset.
        viscosity = Q(2, 7)
        nonlinear = h.nonlinear(w)
        tangent = plus(times(viscosity, [f.lap(row) for row in w]), nonlinear)
        heated_tangent = rational_heat(tangent, q)
        heated_nonlinear = rational_heat(nonlinear, q)
        for i in range(3):
            for j in range(3):
                time_derivative = f.add(rational_heat([f.add(f.mul(w[i], tangent[j]),
                    f.mul(tangent[i], w[j]))], q)[0],
                    f.scale(-1, f.add(f.mul(rz[i], heated_tangent[j]),
                                     f.mul(heated_tangent[i], rz[j]))))
                gradient_covariance = f.add(*(f.add(
                    rational_heat([f.mul(f.diff(w[i], k), f.diff(w[j], k))], q)[0],
                    f.scale(-1, f.mul(f.diff(rz[i], k), f.diff(rz[j], k)))) for k in range(3)))
                nonlinear_covariance = f.add(rational_heat([f.add(
                    f.mul(w[i], nonlinear[j]), f.mul(nonlinear[i], w[j]))], q)[0],
                    f.scale(-1, f.add(f.mul(rz[i], heated_nonlinear[j]),
                                     f.mul(heated_nonlinear[i], rz[j]))))
                expected = f.add(f.scale(viscosity, f.lap(rt[i][j])),
                                 f.scale(-2*viscosity, gradient_covariance), nonlinear_covariance)
                f.equal(time_derivative, expected,
                        'The full actual NS tangent retains covariance diffusion and nonlinear regeneration')
        rows.append(dict(heat_parameter=str(q), covariance_work=str(direct)))
    return rows


def oblique_family():
    U = h.weighted_datum(2, (1, 1, 1))
    W = plus(U, times(h.EPS, h.nonlinear(U)))
    z = h.heat(W)
    F = h.profile(z)
    G = h.variation(z, h.heat(h.nonlinear(W)))
    E = h.variation(z, h.nonlinear(z))
    C = s.expand(G-E)
    zero(G.subs(h.eps, 0)-h.q**10*(11+16*h.q**4-3*h.q**8)/66,
         'The endpoint has the complete retained nonlinear source')
    zero(E.subs(h.eps, 0)-4*h.q**14/11, 'The endpoint intrinsic work')
    zero(C.subs(h.eps, 0)-h.q**10*(1-h.q**4)*(3*h.q**4+11)/66,
         'Strictly positive endpoint covariance work for positive finite heat ages')

    # Recheck the all-heat-age positivity needed by the selector, rather
    # than inferring it from a finite heat grid or an archived decimal.
    leading = G.subs(h.eps, 0)
    zero(F.coeff(h.eps, 1)-leading, 'First pressure-work shape derivative')
    loss = 0
    for (rate, power), coefficient in s.Poly(F-h.eps*leading, h.q, h.eps).terms():
        if coefficient < 0:
            require(rate >= 10 and power >= 3, 'Every adverse shape term has the required powers')
            loss -= coefficient*s.Rational(1, 4)**(power-1)
        elif coefficient:
            require(power >= 2 and rate > 0, 'All remaining shape terms are favorable')
    margin = s.factor(s.Rational(1, 6)-loss)
    require(margin == s.Rational(7561789, 56770560) > 0,
            'Strict pressure work at every heat age throughout 0<eps<=1/4')
    K = h.integrate(C)
    expected = -(3030593396175147016776848*h.eps**6
                 +30127225654212889893409335*h.eps**4
                 -31443097410545983207214400*h.eps**2
                 -20519961530778141239808000)/3742192984428750494522880000
    zero(K-expected, 'Exact whole-heat covariance integral')
    alpha = s.expand(K).coeff(h.eps, 2)
    beta = -s.expand(K).coeff(h.eps, 4)
    gamma = -s.expand(K).coeff(h.eps, 6)
    require(alpha > 0 and 0 < beta < s.Rational(1, 100)
            and 0 < gamma < s.Rational(1, 1000),
            'Simple exact coefficient bounds certify the whole shape interval')
    simple_margin = s.Rational(19, 3465)-s.Rational(1, 25600)-s.Rational(1, 4096000)
    require(simple_margin > s.Rational(1, 200), 'Short readable rational margin certificate')
    lower = 0
    for (power,), coefficient in s.Poly(K, h.eps).terms():
        if power == 0:
            lower += coefficient
        elif coefficient < 0:
            lower += coefficient*s.Rational(1, 4)**power
    require(lower > s.Rational(1, 200), 'Uniform positive covariance margin on the entire interval')
    require(K.subs(h.eps, 0) == s.Rational(19, 3465), 'Exact endpoint covariance integral')
    quarter = s.factor(K.subs(h.eps, s.Rational(1, 4)))
    require(quarter == s.Rational(1177196355408401737690033, 196957525496250026027520000),
            'The fixed shape has an exact positive integrated defect')
    Wquarter = plus(U, times(Q(1, 4), h.nonlinear(U)))
    specialized = s.expand(h.variation(h.heat(Wquarter), h.heat(h.nonlinear(Wquarter)))
                           -h.variation(h.heat(Wquarter), h.nonlinear(h.heat(Wquarter))))
    zero(specialized-C.subs(h.eps, s.Rational(1, 4)), 'Independent rational specialization agrees')
    return dict(parameter_range='0<eps<=1/4', pressure_work=str(s.factor(F)),
                full_work=str(s.factor(G)), intrinsic_work=str(s.factor(E)),
                covariance_work=str(s.factor(C)), covariance_integral=str(K),
                pressure_margin=str(margin), covariance_lower=str(lower),
                integral_coefficients=dict(alpha=str(alpha), beta=str(beta), gamma=str(gamma)),
                simple_lower='1/200', quarter_integral=str(quarter),
                endpoint=dict(pressure_work='0', full_integral=str(h.integrate(G.subs(h.eps, 0))),
                              intrinsic_integral=str(h.integrate(E.subs(h.eps, 0))),
                              signed_covariance_integral='19/3465'),
                tensor_fixtures=covariance_identities(Wquarter))


def cyclic_family():
    a, b, c, q = cyclic.a, cyclic.b, cyclic.c, cyclic.q
    U = h.weighted_datum(0, (cyclic.AA, cyclic.BB, cyclic.CC))
    A = h.nonlinear(U)
    require(all(sum(x*x for x in k) == 2 for k in set().union(*A)),
            'Every complete generated cyclic mode has the same Laplacian eigenvalue')
    z = cyclic.heat(A)
    F = -cyclic.average(f.mul(f.dot(z, z), f.adv(z, pressure(z))))
    G = cyclic.variation(z, cyclic.heat(h.nonlinear(A)))
    E = cyclic.variation(z, h.nonlinear(z))
    T = a*a*b*b*c*c
    S1 = a**4*b*b+b**4*c*c+c**4*a*a
    S2 = a**4*c*c+a*a*b**4+b*b*c**4
    K = -T*(S1+S2-27*T)/576
    zero(F, 'The complete generated cyclic pressure-work profile is zero')
    zero(G-K*q**14, 'The complete cyclic nonlinear return')
    zero(E-K*q**12, 'The intrinsic cyclic nonlinear return')
    zero(G-E-K*q**12*(q*q-1), 'The covariance changes sign with the parent balance')
    equal = {a: 1, b: 1, c: 1}
    require(K.subs(equal) == s.Rational(7, 192), 'Equal cyclic parents')
    require(K.subs({a: 8, b: 1, c: 1}) < 0, 'An unequal cyclic family reverses the covariance sign')
    require(s.factor((K/14)/(K/12)) == s.Rational(6, 7),
            'Covariance removes one seventh of intrinsic renewal when K is positive')
    for strengths in ((1, 1, 1), (8, 1, 1), (0, 1, 1)):
        coefficient = K.subs(dict(zip((a, b, c), strengths)))
        full = max(coefficient, 0)/14
        intrinsic = max(coefficient, 0)/12
        require(full-intrinsic == -max(coefficient, 0)/84,
                'The complete positive-part comparator retains adverse, favorable and degenerate branches')
    return dict(heat_work='0', coefficient=str(s.factor(K)), full_work=str(s.factor(G)),
                intrinsic_work=str(s.factor(E)), covariance_work=str(s.factor(G-E)),
                equal_parents=dict(full_right_derivative='1/384', intrinsic_positive_integral='7/2304',
                                   signed_covariance_integral='-1/2304', retained_fraction='6/7'),
                all_strengths=dict(full_right_derivative='max(K,0)/14',
                                   intrinsic_positive_integral='max(K,0)/12',
                                   covariance_comparator='-max(K,0)/84'),
                selector_scope='At an identically zero heat-work profile use the positive part of the complete direction. Negative K gives zero right derivative, not K/14.')


def checks():
    report = dict(oblique=oblique_family(), cyclic=cyclic_family(),
                  scope='Complete Fourier identities and exact whole-heat integrals; Gaussian positivity, large-frequency transfer and actual unforced intervals are analytic in README.md, not Lean-certified')
    root = Path(__file__).resolve().parent
    sources = ['heat_covariance_renewal.py', 'heat_work_reserve.py', 'joint_heat_cancellation.py',
               'heat_work_parent_payment.py', 'pressure_history_source.py', 'heat_remainder_pressure.py',
               'generated_fourth_moment.py', 'cyclic_pressure_history.py',
               'pressure_gradient_stock.py', 'pressure_quadratic_storage.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
    return report


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
