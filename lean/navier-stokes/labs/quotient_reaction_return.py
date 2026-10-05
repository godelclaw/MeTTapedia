#!/usr/bin/env python3
"""A certified elliptic coefficient for actual nonlinear cubic-work renewal.

Exact rational residuals bound the full inverse operator, not a Galerkin
fluid evolution. The small-parameter and positive-time NS consequences
are analytic in README.md; they are not Lean certificates.
"""

import hashlib
import json
from pathlib import Path

import optimal_cubic_gauge as og

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require = og.require


def scalar_pair(a, b):
    return am.pairing([a], [b])


def central_action(v):
    return wh.scalev(-1, og.action(v, (-1, -1, 1), False))


def full_coefficients(sign):
    base, G = og.datum(sign)
    h, j = f.dot(base, G), f.dot(G, G)
    w1 = wh.addv(G, wh.scalev(-Q(1)/2, og.scalar_vector(h, base)))
    w2 = wh.addv(og.scalar_vector(f.add(f.scale(-Q(1)/4, j),
                                       f.scale(Q(5)/8, f.mul(h, h))), base),
                  wh.scalev(-Q(1)/2, og.scalar_vector(h, G)))
    ws = [base, w1, w2]
    us = [wh.project(w) for w in ws]
    frequencies = set().union(*(a.keys() for v in us[:2] for a in v))
    require(og.s.Matrix(list(frequencies)).rank() == 3,
            'the exact leading velocity modes span all three spatial directions')
    require(-am.pairing(base, [f.lap(a) for a in base]) == Q(1),
            'the exact reference quotient diffusion is one')
    M = lambda v: wh.addv(v, og.scalar_vector(f.dot(base, v), base))
    wh.same_vectors(M(w1), G, 'exact derivative of the optimal dual')
    f.equal(f.trace(f.jac(G)), {}, 'the differentiated dual stays solenoidal')
    ns, pressures = [], []
    for n in range(3):
        conv = wh.addv(*(og.adv(us[a], us[n-a]) for a in range(n+1)))
        stress = [[f.add(*(f.mul(us[a][i], us[n-a][j]) for a in range(n+1)))
                   for j in range(3)] for i in range(3)]
        pressure = f.tensor_pressure(stress)
        rhs = wh.scalev(-1, wh.addv(conv, f.grad(pressure)))
        wh.same_vectors(rhs, wh.scalev(-1, wh.project(conv)),
                        'all nonlinear outputs and canonical pressure are retained')
        ns.append(rhs)
        pressures.append(pressure)
    wh.same_vectors(ns[0], [{}, {}, {}], 'the helical base is Euler-stationary')
    acceleration = []
    for n in range(3):
        conv = wh.addv(*(wh.addv(og.adv(us[a], ns[n-a]),
                                 og.adv(ns[n-a], us[a])) for a in range(n+1)))
        stress = [[f.add(*(f.add(f.mul(us[a][i], ns[n-a][j]),
                                    f.mul(ns[n-a][i], us[a][j])) for a in range(n+1)))
                   for j in range(3)] for i in range(3)]
        rhs = wh.scalev(-1, wh.addv(conv, f.grad(f.tensor_pressure(stress))))
        wh.same_vectors(rhs, wh.scalev(-1, wh.project(conv)),
                        'canonical pressure variation and full nonlinear acceleration agree')
        acceleration.append(rhs)
    L = lambda v: wh.scalev(-1, wh.project(
        wh.addv(og.adv(base, v), og.adv(v, base))))
    n = ns[1]
    wh.same_vectors(n, L(us[1]), 'the first generated source has its full linearization')
    frozen = am.pairing(base, acceleration[2])+am.pairing(G, acceleration[1])
    formula = am.pairing(wh.addv(G, wh.scalev(-1, us[1])), L(n))-am.pairing(n, n)
    require(frozen == formula, 'the frozen-dual coefficient retains second-generation outputs')
    require(am.pairing(base, acceleration[1]) == f.ZERO,
            'the first-order acceleration pairing vanishes')
    expected = -Q(775)/968 if sign == 0 else -Q(4261)/2904
    require(frozen == expected, 'exact frozen-observer coefficient')
    for v in (base, G):
        for diagonal, shift in (((1, -1, -1), False), ((-1, 1, -1), True)):
            wh.same_vectors(v, og.action(v, diagonal, shift),
                            'rotation symmetry forces zero mean in the exact normalized family')
    if sign == 0:
        for v in (base, G, *ws, *us):
            wh.same_vectors(central_action(v), v, 'the balanced datum has the exact central symmetry')
        for v in ns:
            wh.same_vectors(central_action(v), wh.scalev(-1, v),
                            'the full generated source leaves the balanced symmetry class')
        for v in us:
            wh.same_vectors(central_action([f.lap(a) for a in v]), [f.lap(a) for a in v],
                            'viscosity preserves the balanced symmetry class')
    vertical = scalar_pair(us[1][2], us[1][2])
    require(vertical.x > 0 and vertical.y == 0,
            'the physical perturbation has a genuinely nonzero vertical component')
    require(all(sum(k[i]**2 for i in (0, 1)) == 2 for a in n for k in a),
            'the elliptic source lies in the invariant horizontal blocks')
    return {'phase': sign, 'frozen_coefficient': str(frozen),
            'source_norm_squared': str(am.pairing(n, n)),
            'vertical_first_coefficient_norm_squared': str(vertical),
            'pressure_coefficient_modes': list(map(len, pressures)),
            'nonlinear_modes': [len(set().union(*(a.keys() for a in v))) for v in ns],
            'acceleration_modes': [len(set().union(*(a.keys() for a in v))) for v in acceleration]}, base, n, frozen, us[1]


def certify_metric(base, n, frozen):
    M = lambda v: wh.addv(v, og.scalar_vector(f.dot(base, v), base))
    A = lambda a: f.add(f.scale(-1, f.lap(a)),
                         f.scale(-1, f.adv(base, f.adv(base, a))))
    A0 = lambda a: f.clean({k: (k[2]**2+3)*v for k, v in a.items()})
    A0inv = lambda a: f.clean({k: v/(k[2]**2+3) for k, v in a.items()})
    b = f.trace(f.jac(M(n)))
    term = A0inv(b)
    phi = term
    rows = []
    for step in range(3):
        if step:
            term = f.scale(-1, A0inv(f.add(A(term), f.scale(-1, A0(term)))))
            phi = f.add(phi, term)
        operator_from_div = f.scale(-1, f.trace(f.jac(M(f.grad(phi)))))
        f.equal(operator_from_div, A(phi), 'literal divergence-form elliptic operator')
        residual = f.add(b, f.scale(-1, A(phi)))
        require(all(k[0]**2+k[1]**2 == 2 for k in phi.keys() | residual.keys()),
                'the complete residual stays in the coercive horizontal subspace')
        q = wh.addv(n, f.grad(phi))
        upper = am.pairing(q, M(q))
        expanded = am.pairing(n, M(n))-2*scalar_pair(b, phi)+scalar_pair(phi, A(phi))
        require(upper == expanded, 'Schur-complement trial energy and its full expansion agree')
        f.equal(f.trace(f.jac(M(q))), residual,
                'the omitted optimality is exactly the certified residual')
        residual_sq = scalar_pair(residual, residual)
        require(residual_sq.y == 0 and residual_sq.x >= 0, 'real nonnegative exact residual square')
        lower = upper-residual_sq/2
        require(lower.y == 0 and upper.y == 0, 'real bounds for the full constrained Hessian')
        rows.append({'neumann_step': step,
                     'metric_lower': str(lower), 'metric_upper': str(upper),
                     'return_lower': str(lower+frozen), 'return_upper': str(upper+frozen),
                     'residual_squared': str(residual_sq), 'residual_modes': len(residual)})
    return rows, lower+frozen, upper+frozen


def certify_cross(base, a, b):
    plus, pl, pu = certify_metric(base, wh.addv(a, b), Q(0))
    minus, ml, mu = certify_metric(base, wh.addv(a, wh.scalev(-1, b)), Q(0))
    lower, upper = (pl-mu)/4, (pu-ml)/4
    return {'plus': plus, 'minus': minus,
            'cross_lower': str(lower), 'cross_upper': str(upper)}, lower, upper


def completion_coefficients(sign, base, n, u1, metric_lower, metric_upper):
    L = lambda v: wh.scalev(-1, wh.project(
        wh.addv(og.adv(base, v), og.adv(v, base))))
    if sign == 0:
        direction = wh.addv([f.lap(a) for a in u1], u1)
        certificate, cl, cu = certify_cross(base, n, L(direction))
        lower, upper = -5*metric_upper+2*cl, -5*metric_lower+2*cu
        require(-8 < lower.x < upper.x < -7,
                'complete leading heat derivative of the generated-source metric is negative')
        return {'heat_cross': certificate, 'heat_derivative_lower': str(lower),
                'heat_derivative_upper': str(upper),
                'nonlinear_derivative': 'Exactly zero by the central symmetry, not just to this order.'}
    certificate, cl, cu = certify_cross(base, n, L(n))
    lower, upper = 2*cl, 2*cu
    if sign == 1:
        require(Q(57).x/100 < lower.x < upper.x < Q(58).x/100,
                'the positive phase regenerates the full source metric')
    else:
        require(-Q(58).x/100 < lower.x < upper.x < -Q(57).x/100,
                'the opposite phase reverses source-metric regeneration')
    _, opposite = og.datum(-sign)
    _, original = og.datum(sign)
    wh.same_vectors(central_action(original), opposite,
                    'central action exchanges the exact dual phases')
    return {'nonlinear_cross': certificate,
            'nonlinear_derivative_lower': str(lower),
            'nonlinear_derivative_upper': str(upper)}


def check_third_variation():
    s = og.s
    coordinates = s.symbols('x y z', real=True)
    radius = s.sqrt(sum(x*x for x in coordinates))
    for i in range(3):
        for j in range(i, 3):
            for k in range(j, 3):
                expected = (coordinates[i]*int(j == k)+coordinates[j]*int(i == k)
                            +coordinates[k]*int(i == j))/radius
                expected -= coordinates[i]*coordinates[j]*coordinates[k]/radius**3
                og.zero(s.diff(radius**3/3, coordinates[i], coordinates[j], coordinates[k])
                        -expected, 'all independent entries of the third variation off zero')


if __name__ == '__main__':
    rows = []
    for sign in (0, 1, -1):
        data, base, n, frozen, u1 = full_coefficients(sign)
        certificates, lower, upper = certify_metric(base, n, frozen)
        if sign == 0:
            require(Q(7).x/1000 < lower.x < upper.x < Q(8).x/1000,
                    'strict complete return in the balanced family')
        else:
            require(Q(19).x/100 < lower.x < upper.x < Q(1).x/5,
                    'strict complete return in both earlier phases')
        data['certificates'] = certificates
        data['coercive_completion'] = completion_coefficients(
            sign, base, n, u1, lower-frozen, upper-frozen)
        rows.append(data)
    require(rows[1]['certificates'] == rows[2]['certificates'],
            'both opposite initial phases have the same full leading return')
    eps, nu, horizon = og.s.symbols('epsilon nu H', positive=True)
    amplitude_sq = 8000*nu/(7*horizon*eps*eps)
    og.zero(horizon*amplitude_sq*og.s.Rational(7, 2000)*eps*eps-4*nu,
            'the stated clock-correction amplitude gives a strict positive margin')
    check_third_variation()
    dependencies = [Path(__file__), Path(og.__file__), Path(f.__file__),
                    Path(wh.__file__), Path(am.__file__)]
    result = {'candidate': 'The full nonlinear return DP(u)[N(u)] at P(u)=0, including the constrained optimal-dual Hessian.',
              'fixtures': rows,
              'inverse_certificate': 'On |k_h|^2=2, A=-div((I+F0 tensor F0)grad)>=2. Trial energy minus ||residual||2^2/2 <= exact Hessian <= trial energy.',
              'balanced_symmetry': 'C u=-R u(Rx), R=diag(-1,-1,1). C fixes the exact balanced datum; P(Cu)=-P(u), and heat commutes with C. Thus P(u0)=DP(u0)[Delta u0]=0 exactly.',
              'physical_consequence': 'For every nu>0 and A>0 and sufficiently small positive epsilon, the actual unforced local solution has P(0)=0 and P(t)>0 for all sufficiently small positive t. The small epsilon threshold and time interval are analytic existence statements, not numerical enclosures.',
              'clock_test': 'C_H=J+(H-t)P has C_H(0)=J(u0)>0 but increases initially for A^2=8000nu/(7H epsilon^2), for sufficiently small epsilon. This rejects this first-order signed forecast, not all history corrections.',
              'coercive_completion': 'With A_geo=H_u(N,N), S_H=J+(H-t)P+(3/4)(H-t)^2 A_geo >= J/2. It pays half-diffusion on a short actual interval of the balanced family for every positive amplitude, viscosity and horizon. The phase +1 has D A_geo[N]>0, so sufficiently large amplitude defeats this same payment for every fixed positive viscosity and horizon.',
              'completion_scope': 'The constrained Hessian and its third variation are used only near smooth nonvanishing optimizers. All generated-mode metric bounds include the full inverse residual. No arbitrary-history payment or global Hessian regularity is claimed.',
              'status': 'Exact Fourier/rational residual checks passed. Elliptic coercivity, analytic dependence and local-PDE consequences are analytic, not Lean-certified.',
              'limitation': 'The observable is optimized cubic work. This does not prove positive net cubic growth, positive vorticity stretching, repeated renewal, blowup, or failure of a full-datum allowance.',
              'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies}}
    print(json.dumps(result, indent=2), flush=True)
