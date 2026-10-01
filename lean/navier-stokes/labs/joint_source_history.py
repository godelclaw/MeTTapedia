#!/usr/bin/env python3
"""Causal joint-source payment and reciprocal pressure generation.

Full canonical NS jets and original two-index moment/packet jets retain
every Fourier output on the normalized period-2*pi torus. Independent
symbolic means check arbitrary amplitudes and viscosity. Pressure starts
at zero but its compatibility work has a positive first nonzero mean.
The source split retains its pressure-parent cross term and all spatial
diffusion. Jets do not certify a uniform turnover window, repeated
renewal, a continuum stochastic construction or a datum-paid allowance.

JointSourceHistory.lean certifies the finite metric and scalar physical-time
comparison. Its source integral and physical geometric conversion remain
separate obligations. The causal pressure-input square below is a leading
coefficient of that conditional estimate, not an established all-time cost.
"""

import json
import math
from fractions import Fraction

import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
import joint_receiver_tensor as jt
from cyclic_pressure_history import velocity_time_jets, zero
from pressure_impulse_history import matrix_transport


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def seed(amplitudes):
    u = [{}, {}, {}]
    for i, (a, k) in enumerate(zip(amplitudes, ((0, 1, 0), (0, 0, 1), (1, 0, 0)))):
        u[i] = {k: -f.II*f.QQ_I(a)/2,
                tuple(-v for v in k): f.II*f.QQ_I(a)/2}
    return [f.clean(q) for q in u]


def fourier_history(amplitudes, viscosity):
    nu = f.QQ_I(viscosity)
    us, ps = velocity_time_jets(seed(amplitudes), viscosity, 3)
    Bs, Ps = list(map(f.jac, us)), list(map(f.hess, ps))
    require(not ps[0], 'full canonical pressure initially zero')
    I = [[{f.ORIGIN: f.QQ_I.one} if i == j else {}
          for j in range(3)] for i in range(3)]
    Ls = [jt.scale(-1, jt.add(jt.kronecker(pm.transpose(B), I),
                            jt.kronecker(I, pm.transpose(B)))) for B in Bs]
    As, Cs = [Bs[0]], [jt.kronecker(I, I)]
    for n in range(3):
        As.append(jt.add(jt.scale(nu, [[f.lap(q) for q in row] for row in As[n]]), *(
            jt.scale(-math.comb(n, r), jt.add(
                pm.matrix_adv(us[r], As[n-r]),
                jt.multiply(pm.transpose(Bs[r]), As[n-r]),
                jt.multiply(As[n-r], Bs[r]))) for r in range(n+1))))
        if n < 2:
            Cs.append(jt.add(jt.scale(nu, [[f.lap(q) for q in row] for row in Cs[n]]), *(
                jt.scale(math.comb(n, r), jt.add(
                    jt.scale(-1, pm.matrix_adv(us[r], Cs[n-r])),
                    jt.multiply(Ls[r], Cs[n-r]),
                    jt.multiply(Cs[n-r], pm.transpose(Ls[r])))) for r in range(n+1))))
    Es = [jt.subtract(a, b) for a, b in zip(As, Bs)]
    Gs = [jt.add(*(jt.scale(math.comb(n, r), jt.multiply(pm.transpose(Bs[r]), Bs[n-r]))
                    for r in range(n+1))) for n in range(3)]
    sources = [jt.subtract(P, G) for P, G in zip(Ps, Gs)]
    for n in range(3):
        full_rate = jt.add(matrix_transport(us[0], Es[n], nu), sources[n],
                           jt.scale(-1, jt.add(jt.multiply(pm.transpose(Bs[0]), Es[n]),
                                                jt.multiply(Es[n], Bs[0]))), *(
            jt.scale(-math.comb(n, r), jt.add(
                pm.matrix_adv(us[r], Es[n-r]),
                jt.multiply(pm.transpose(Bs[r]), Es[n-r]),
                jt.multiply(Es[n-r], Bs[r]))) for r in range(1, n+1)))
        jt.equal(Es[n+1], full_rate, ('complete actual compatibility time law', n+1))
    for n, (E, A, u) in enumerate(zip(Es, As, us)):
        jt.equal(E, pm.transpose(E), ('symmetric actual defect', n))
        for i, q in enumerate((f.add(A[2][1], f.scale(-1, A[1][2])),
                               f.add(A[0][2], f.scale(-1, A[2][0])),
                               f.add(A[1][0], f.scale(-1, A[0][1])))):
            f.equal(q, f.curl(u)[i], ('original tensor retains literal physical curl', n, i))
    W1 = jt.scale(-1, Cs[1])
    W2 = jt.add(jt.scale(-1, Cs[2]), jt.scale(2, jt.multiply(Cs[1], Cs[1])))
    e1, e2, e3 = map(jt.flatten, Es[1:])
    G0, G1, G2 = map(jt.flatten, Gs)
    p1, p2 = map(jt.flatten, Ps[1:])
    pressure_legs = [f.dot(e2, p1), f.dot(e1, p2), jt.metric(e1, W1, p1)]
    pressure2 = f.scale(4, f.dot(e1, p1))
    pressure3 = f.scale(6, f.add(pressure_legs[0], pressure_legs[1],
                                f.scale(2, pressure_legs[2])))
    q2 = f.scale(2, f.dot(e1, e1))
    q3 = f.scale(6, f.add(f.dot(e1, e2), jt.metric(e1, W1, e1)))
    q4 = f.add(f.scale(8, f.dot(e1, e3)), f.scale(6, f.dot(e2, e2)),
               f.scale(24, jt.metric(e1, W1, e2)), f.scale(12, jt.metric(e1, W2, e1)))
    parent3 = f.scale(2, f.add(f.dot(e3, G0), f.scale(3, f.dot(e2, G1)),
                              f.scale(3, f.dot(e1, G2)), f.scale(3, jt.metric(e2, W1, G0)),
                              f.scale(6, jt.metric(e1, W1, G1)),
                              f.scale(3, jt.metric(e1, W2, G0))))
    diffusion2, diffusion3 = {}, {}
    for k in range(3):
        r1 = jt.flatten(pm.matrix_diff(Es[1], k))
        K1 = pm.matrix_diff(Cs[1], k)
        r2 = [f.add(x, f.scale(-2, y)) for x, y in
              zip(jt.flatten(pm.matrix_diff(Es[2], k)), f.matvec(K1, e1))]
        diffusion2 = f.add(diffusion2, f.scale(2, f.dot(r1, r1)))
        diffusion3 = f.add(diffusion3, f.scale(6, f.add(f.dot(r1, r2), jt.metric(r1, W1, r1))))
    f.equal(f.add(q4, f.adv(us[0], q3), f.scale(3, f.adv(us[1], q2)), f.scale(-nu, f.lap(q3))),
            f.add(pressure3, f.scale(-1, parent3), f.scale(-2*nu, diffusion3)),
            'pointwise fourth energy jet: full changing drift, metric, pressure, parents and diffusion')

    # The two source histories share the original metric and drift.
    # Reconstructing E retains their cross pairing instead of adding norms.
    L = lambda B, Y: jt.scale(-1, jt.add(jt.multiply(pm.transpose(B), Y), jt.multiply(Y, B)))
    YP2 = Ps[1]
    YP3 = jt.add(matrix_transport(us[0], YP2, nu), L(Bs[0], YP2), Ps[2])
    YG1 = Gs[0]
    YG2 = jt.add(matrix_transport(us[0], YG1, nu), L(Bs[0], YG1), Gs[1])
    YG3 = jt.add(matrix_transport(us[0], YG2, nu),
                 jt.scale(-2, pm.matrix_adv(us[1], YG1)), L(Bs[0], YG2),
                 jt.scale(2, L(Bs[1], YG1)), Gs[2])
    jt.equal(Es[1], jt.scale(-1, YG1), 'actual first joint history reconstruction')
    jt.equal(Es[2], jt.subtract(YP2, YG2), 'actual second joint history reconstruction')
    jt.equal(Es[3], jt.subtract(YP3, YG3), 'actual third joint history reconstruction')
    g1, g2, g3 = map(jt.flatten, (YG1, YG2, YG3))
    yp3 = jt.flatten(YP3)
    pressure_memory4 = f.scale(6, f.dot(p1, p1))
    parent_memory4 = f.add(f.scale(8, f.dot(g1, g3)), f.scale(6, f.dot(g2, g2)),
                           f.scale(24, jt.metric(g1, W1, g2)), f.scale(12, jt.metric(g1, W2, g1)))
    cross4 = f.add(f.scale(6, f.dot(p1, g2)), f.scale(4, f.dot(yp3, g1)),
                   f.scale(12, jt.metric(p1, W1, g1)))
    f.equal(q4, f.add(pressure_memory4, parent_memory4, f.scale(-2, cross4)),
            'full pressure-parent memory-square reconstruction, retaining cross terms')

    a, b, c = map(lambda v: f.QQ_I(v).x, amplitudes)
    S4, loop = a**4+b**4+c**4, a*a*b*b*c*c
    expected = {'pressure_second': 0, 'pressure_third': 27*loop,
                'q_second': 3*S4/4, 'q_third': -15*nu.x*S4/2,
                'q_fourth': 27*loop+69*nu.x**2*S4,
                'parent_third': -33*nu.x**2*S4,
                'diffusion_second': S4, 'diffusion_third': -18*nu.x*S4,
                'pressure_memory_fourth': 27*loop}
    fields = {'pressure_second': pressure2, 'pressure_third': pressure3,
              'q_second': q2, 'q_third': q3, 'q_fourth': q4,
              'parent_third': parent3, 'diffusion_second': diffusion2,
              'diffusion_third': diffusion3, 'pressure_memory_fourth': pressure_memory4}
    values = {name: pm.mean(field) for name, field in fields.items()}
    for name, value in values.items():
        require(value == expected[name], ('generic scalar jet formula', name))
    legs = list(map(pm.mean, pressure_legs))
    require(legs == [9*loop/2, 0, 0], 'complete pressure jet includes both changing fields and metric')
    require(pm.mean(pm.pair(sources[0], sources[0])) == 3*S4/8,
            'the combined causal source starts in the actual parent norm')
    return {'amplitudes': list(map(str, amplitudes)), 'nu': str(viscosity),
            'initial_gradient_energy': str((a*a+b*b+c*c)/2),
            'jets': {name: str(value) for name, value in values.items()},
            'pressure_legs': list(map(str, legs)),
            'parent_memory_fourth': str(pm.mean(parent_memory4)),
            'pressure_parent_cross_fourth': str(pm.mean(cross4)),
            'full_pointwise_energy_balance': 'PASS',
            'history_reconstruction_with_cross_terms': 'PASS',
            'scope': 'full actual NS and supplied original stochastic-packet jets; continuous time identification analytic'}


def symbolic_history():
    x, y, z = coordinates = s.symbols('x y z', real=True)
    a, b, c, nu = s.symbols('a b c nu', real=True)
    angles = s.symbols('sx cx sy cy sz cz')
    replace = {v: angles[2*i+j] for i, q in enumerate(coordinates)
               for j, v in enumerate((s.sin(q), s.cos(q)))}

    def mean(expression):
        polynomial = s.Poly(s.expand_trig(s.expand(expression)).xreplace(replace), *angles)
        value = 0
        for powers, coefficient in polynomial.terms():
            weight = s.Integer(1)
            for m, n in zip(powers[::2], powers[1::2]):
                if m % 2 or n % 2:
                    weight = 0
                    break
                r, t = m//2, n//2
                weight *= s.Rational(math.factorial(2*r)*math.factorial(2*t),
                                     4**(r+t)*math.factorial(r)*math.factorial(t)*math.factorial(r+t))
            value += weight*coefficient
        return s.factor(value)

    expand = lambda A: A.applyfunc(s.expand)
    lap = lambda A: A.applyfunc(lambda v: sum(s.diff(v, q, 2) for q in coordinates))
    adv = lambda v, A: A.applyfunc(lambda e: sum(v[j]*s.diff(e, coordinates[j]) for j in range(3)))
    pair = lambda A, B: s.trace(A.T*B)
    u = s.Matrix([a*s.sin(y), b*s.sin(z), c*s.sin(x)])
    B = u.jacobian(coordinates)
    u1 = expand(nu*lap(u)-B*u)
    B1 = u1.jacobian(coordinates)
    p1 = -2*a*b*c*s.cos(x)*s.cos(y)*s.cos(z)
    p2 = -s.Rational(2, 3)*a*b*c*(c*s.sin(2*x)*s.cos(y)*s.sin(z)
                                 +a*s.sin(x)*s.sin(2*y)*s.cos(z)
                                 +b*s.cos(x)*s.sin(y)*s.sin(2*z))-6*nu*p1
    P1, P2 = s.hessian(p1, coordinates), s.hessian(p2, coordinates)
    u2 = expand(nu*lap(u1)-B1*u-B*u1-s.Matrix([s.diff(p1, q) for q in coordinates]))
    B2 = u2.jacobian(coordinates)
    zero(s.trace(B*B), 'literal initial canonical pressure is zero')
    zero(sum(s.diff(p1, q, 2) for q in coordinates)+2*s.trace(B*B1),
         'first full canonical pressure jet')
    zero(sum(s.diff(p2, q, 2) for q in coordinates)+2*s.trace(B1*B1)+2*s.trace(B*B2),
         'second full canonical pressure jet')
    G0, G1 = B.T*B, expand(B1.T*B+B.T*B1)
    G2 = expand(B2.T*B+B.T*B2+2*B1.T*B1)
    S0, S1 = B+B.T, B1+B1.T
    L0, L1 = (lambda Y: -B.T*Y-Y*B), (lambda Y: -B1.T*Y-Y*B1)
    C1 = lambda Y: -S0*Y-Y*S0
    W1 = lambda Y: -C1(Y)
    DS = expand(nu*lap(S0)-adv(u, S0))
    C2 = lambda Y: -DS*Y-Y*DS-S1*Y-Y*S1+L0(C1(Y))+C1(-B*Y-Y*B.T)
    W2 = lambda Y: -C2(Y)+2*C1(C1(Y))
    E1 = -G0
    E2 = expand(nu*lap(E1)-adv(u, E1)+L0(E1)+P1-G1)
    E3 = expand(nu*lap(E2)-adv(u, E2)-2*adv(u1, E1)+L0(E2)+2*L1(E1)+P2-G2)
    S4, loop = a**4+b**4+c**4, a*a*b*b*c*c
    fields = {
        'pressure_hessian_square': (pair(P1, P1), 9*loop/2),
        'pressure_gradient_square': (sum(s.diff(p1, q)**2 for q in coordinates), 3*loop/2),
        'pressure_work_leg_E2P1': (pair(E2, P1), 9*loop/2),
        'pressure_work_leg_E1P2': (pair(E1, P2), 0),
        'pressure_work_leg_metric': (pair(E1, W1(P1)), 0),
        'q_E_second': (2*pair(E1, E1), 3*S4/4),
        'q_E_third': (6*(pair(E1, E2)+pair(E1, W1(E1))), -15*nu*S4/2),
        'q_E_fourth': (8*pair(E1, E3)+6*pair(E2, E2)+24*pair(E1, W1(E2))
                       +12*pair(E1, W2(E1)), 27*loop+69*nu**2*S4),
        'parent_work_third': (2*(pair(E3, G0)+3*pair(E2, G1)+3*pair(E1, G2)
                                 +3*pair(E2, W1(G0))+6*pair(E1, W1(G1))
                                 +3*pair(E1, W2(G0))), -33*nu**2*S4),
        'diffusion_second': (2*sum(pair(E1.diff(q), E1.diff(q)) for q in coordinates), S4),
        'diffusion_third': (6*sum(pair(E1.diff(q), E2.diff(q)+2*(S0.diff(q)*E1+E1*S0.diff(q)))
                                +pair(E1.diff(q), W1(E1.diff(q))) for q in coordinates), -18*nu*S4),
    }
    values = {}
    for name, (expression, expected) in fields.items():
        value = mean(expression)
        require(s.factor(value-expected) == 0, ('independent symbolic torus mean', name))
        values[name] = str(value)
    return {'datum': 'u0=(a sin y,b sin z,c sin x)', 'mean_jets': values,
            'pressure_work_first_nonzero': '(9/2)*a^2*b^2*c^2*t^3+o(t^3)',
            'pressure_memory_first_nonzero': '(9/8)*a^2*b^2*c^2*t^4+o(t^4)',
            'causal_pressure_input_square_first_nonzero': '(9/8)*a^2*b^2*c^2*t^4+o(t^4)',
            'cotangent_absorption_cost_first_nonzero': '(3/(2*nu))*a^2*b^2*c^2*t^3+o(t^3)',
            'scope': 'generic exact jets and leading comparison coefficients; no uniform positive-time window or paid arbitrary source cap'}


if __name__ == '__main__':
    cases = [((1, 1, 1), Fraction(1, 10)), ((1, 1, 1), Fraction(1)),
             ((2, 3, 5), Fraction(2, 7)), ((2, 3, 0), Fraction(2, 7)),
             ((-2, 3, 5), Fraction(1)), ((1, 1, 1), Fraction(0))]
    print(json.dumps({'symbolic_history': symbolic_history(),
                      'full_fourier_cases': [fourier_history(abc, nu) for abc, nu in cases],
                      'positive_viscosity_scope': 'five viscous cases; zero-viscosity jets are an algebraic diagnostic only',
                      'physical_claim': 'a finite positive pressure burst, not indefinite renewal or singularity',
                      'surviving_target': 'a full-datum causal source cap and sufficient actual curl-direction geometry'}, indent=2))
