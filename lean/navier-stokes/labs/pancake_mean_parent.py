#!/usr/bin/env python3
"""Exact checks for geometric payment with a large evolving planar mean.

The analytic estimate composes the existing mean-enstrophy payment with
the spectral-pancake estimate. Local solution histories and their uniform
remainders are proved in README.md, not by these finite Fourier fixtures.
"""

import ast
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import generated_mean_enstrophy as m
import pancake_concentration_threshold as pc
from reciprocal_pattern_cycles import inner, mode, require, vector_add, vector_scale


def zero(expression, label):
    require(s.simplify(expression) == 0, label)


def seed():
    u = [{}, {}, {}]
    for k, v, a in [((4, 0, 64), (0, 1, 0), Q(1)),
                    ((0, 4, 64), (1, 1, -Q(1, 16)), Q(1)),
                    ((1, 1, 64), (1, -1, 0), Q(1, 10))]:
        for j, value in enumerate(v):
            if value:
                u[j] = f.add(u[j], mode(k, a*value))
    return u


def in_core(k):
    squared = sum(x*x for x in k)
    return squared <= 1 or (k[0]**2+k[1]**2)**2 <= squared


def history_jet():
    w = seed()
    N, record = pc.full_source(w)
    M1, W1 = m.vertical_mean(N), m.oscillation(N)
    require(s.Matrix([[4, 0, 64], [0, 4, 64], [1, 1, 64]]).det() == 512,
            'three independent spatial frequency directions')
    require(not any(m.vertical_mean(w)), 'the actual mean starts empty')
    require({k[2] for k in pc.support(w)} == {-64, 64} and m.cubic(w) == 0,
            'three initial vertical frequencies cannot sum to zero')
    require(m.linear_cubic_term(w, m.minus_laplacian(w)) == 0,
            'viscous independence of the first cubic derivative holds for every viscosity')
    require(all(in_core(k) for k in pc.support(w)+pc.support(W1)),
            'initial field and complete first oscillatory source are inside the same core')
    require(not in_core((4, -4, 0)), 'the generated mean is outside that core')
    pressure = f.green(f.trace(f.matmul(f.jac(w), f.jac(w))))
    pressure_squared = inner([pressure], [pressure])
    require(pressure_squared == Q(1346441, 336610125) > 0,
            'canonical pressure is nonzero; the seed is not a passive triangular shear')
    expected = [f.II, f.II, -f.II/16]
    require([component.get((4, -4, 0), f.ZERO) for component in M1] == expected,
            'a specified generated mean coefficient survives the third parent')
    mean_return = m.linear_cubic_term(w, M1)
    side_return = m.linear_cubic_term(w, W1)
    require(mean_return == -Q(528846959, 32000), 'complete first mean return')
    require(side_return == Q(2629880556769, 52512000), 'complete first oscillatory return')
    require(mean_return+side_return == Q(35240853941, 1050240) > 0,
            'the full first stretching derivative is positive')
    feedback = vector_add(m.bilinear(M1, w), m.bilinear(w, M1))
    require(inner(w, feedback) == -inner(M1, M1) == -Q(10369, 2560),
            'the generated mean has nonzero reciprocal work in the original fluid')
    require(inner(feedback, feedback) > 0, 'the actual return is retained')
    jets = []
    for nu in (Q(0), Q(1, 7), Q(1)):
        rhs = vector_add(N, vector_scale(-nu, m.minus_laplacian(w)))
        Ndot = vector_add(m.bilinear(rhs, w), m.bilinear(w, rhs))
        acceleration = vector_add(Ndot, vector_scale(-nu, m.minus_laplacian(rhs)))
        f.equal(f.trace(f.jac(acceleration)), {}, 'complete second tangent is solenoidal')
        require(m.linear_cubic_term(w, rhs) == mean_return+side_return,
                'viscosity retains the full first stretching coefficient')
        require(m.linear_cubic_term(w, m.oscillation(rhs)) == side_return,
                'the actual fluctuation tangent retains the non-mean return')
        require(m.derivative_pair(rhs, N)+m.derivative_pair(w, Ndot) == mean_return+side_return,
                'independent derivative of the complete projected-source pairing')
        require(2*inner(rhs, rhs)+2*inner(w, acceleration) == -4*nu*m.derivative_pair(w, rhs),
                'the full second kinetic identity includes all generated outputs')
        jets.append(dict(normalized_viscosity=str(nu),
                         second_tangent_modes=len(pc.support(acceleration)),
                         full_stretching_derivative=str(mean_return+side_return)))
    return dict(initial=record, pressure_squared=str(pressure_squared),
                mean_source_squared=str(inner(M1, M1)),
                mean_return=str(mean_return), oscillatory_return=str(side_return),
                complete_return=str(mean_return+side_return),
                mean_to_fluctuation_work=str(inner(w, feedback)), jets=jets)


def large_mean_fixtures():
    w = seed()
    F = m.vertical_mean(m.nonlinear(w))
    rows = []
    for frequency in (1, 3):
        cell = [mode((0, frequency, 0), 2, True),
                mode((frequency, 0, 0), -2, True),
                f.add(mode((frequency, 0, 0), 2), mode((frequency, frequency, 0), 2))]
        pair = []
        for sign in (-1, 1):
            M = vector_add(cell, vector_scale(20*sign, F))
            u = vector_add(M, w)
            Nu, record = pc.full_source(u)
            cross = vector_add(m.bilinear(M, w), m.bilinear(w, M))
            m.equal_vectors(m.vertical_mean(Nu), vector_add(m.nonlinear(M), F),
                            'evolving mean retains its complete internal source')
            m.equal_vectors(m.oscillation(Nu), vector_add(cross, m.oscillation(m.nonlinear(w))),
                            'all oscillatory parent feedback remains')
            require(m.linear_cubic_term(M, w) == 0, 'two-mean one-fluctuation cubic vanishes')
            mixed = m.linear_cubic_term(w, M)
            require(m.cubic(u) == m.cubic(M)+mixed+m.cubic(w), 'complete stretching split')
            require(mixed == m.derivative_pair(w, cross)+m.derivative_pair(M, F),
                    'both receiving sides of the enstrophy transfer remain')
            work = inner(M, F)
            require(work == sign*20*inner(F, F) and work+inner(w, cross) == 0,
                    'large internally forced mean has the opposite kinetic charge in the fluctuation')
            require(m.gradient_norm_squared(u) == m.gradient_norm_squared(M)+m.gradient_norm_squared(w),
                    'actual mean gradient energy is bounded by the full paid quantity')
            pair.append(record['energy'])
            rows.append(dict(frequency=frequency, phase=sign, full_energy=record['energy'],
                             mean_stretching=str(m.cubic(M)), mixed_stretching=str(mixed),
                             kinetic_work_into_mean=str(work), full_source_modes=record['full_source_modes']))
        require(pair[0] == pair[1], 'opposite transfer directions have the same initial energy')
    return rows


def axis_and_clock():
    k, q = s.Matrix([4, 0, 64]), s.Matrix([4, -4, 0])
    k2, q2, cross2 = k.dot(k), q.dot(q), k.cross(q).dot(k.cross(q))
    require(k2 < 65**2 and q2 < 6**2 and q2 < s.Rational(5, 2)**4 and k2 < 9**4,
            'rational upper bounds for the two frequency norms and their square roots')
    require(cross2 > 360**2 and 65*s.Rational(5, 2)+6*9 < 360,
            'no single axis can put both modes in the B=R=1 gamma=1/2 core')
    A, nu = s.symbols('A nu', positive=True)
    tau = A**(-s.Rational(2, 3))
    zero(tau/A-A**(-s.Rational(5, 3)), 'actual physical time')
    zero(A*tau-A**s.Rational(1, 3), 'generated mean grows in absolute size')
    zero(A*tau**2-A**(-s.Rational(1, 3)), 'oscillatory exterior remainder becomes small')
    c, D0 = s.symbols('c D0', positive=True)
    zero(A*A*c*tau**2-nu*A*D0*tau
         -(c*A**s.Rational(2, 3)-nu*D0*A**s.Rational(1, 3)),
         'actual integrated excess retains its leading viscous cost')
    return dict(input_frequency=[int(a) for a in k], mean_frequency=[int(a) for a in q],
                cross_product_squared=int(cross2),
                no_common_axis=True, physical_time='A^(-5/3)',
                generated_mean_lower='c A^(1/3)', oscillatory_exterior_upper='C A^(-1/3)',
                scope='Fixed B=R=1 and gamma=1/2; changing these datum-dependent parameters is not excluded. Uniform local remainders are analytic.')


def payment_algebra():
    nu, beta, Z, M, D, L, phi, loss, h, b, g0 = s.symbols(
        'nu beta Z M D L phi loss h b g0', real=True)
    # phi=exp(2L(H-t)+beta E/(2nu)), using the same full kinetic stock.
    Zdot = -nu*D/2+2*L*Z+beta*M*Z-loss
    phidot = (-2*L-beta*Z)*phi
    Sdot = phidot*Z+phi*Zdot
    zero(Sdot+nu*phi*D/2+beta*phi*(Z-M)*Z+phi*loss,
         'initial kinetic energy pays the entire evolving mean coefficient')
    R = (2*phi-1)*Z+2*h*b
    zero(R-Z-2*(phi-1)*Z-2*h*b, 'nonnegative reserve dominates enstrophy')
    Rdot = 2*Sdot-Zdot-2*b
    cost = Zdot+nu*D-2*g0
    zero(Rdot+cost+nu*(phi-1)*D+2*beta*phi*(Z-M)*Z+2*phi*loss+2*(b+g0),
         'the reserve pays the original signed-renewal cost')
    Wkin, Wvort = s.symbols('W_kin W_vort', real=True)
    Gamma = beta/(2*nu)
    forced_Sdot = Sdot+2*phi*(Wvort+Gamma*Z*Wkin)
    forced_Rdot = 2*forced_Sdot-(Zdot+2*Wvort)-2*b
    zero(forced_Rdot-Rdot-((4*phi-2)*Wvort+4*Gamma*phi*Z*Wkin),
         'zero kinetic forcing work does not erase the vorticity forcing defect')
    E = s.symbols('E', real=True)
    factor = s.exp(2*L*h+Gamma*E)
    value = (2*factor-1)*Z+2*h*b
    hjb = -s.diff(value, h)-2*nu*Z*s.diff(value, E)+Zdot*s.diff(value, Z)+cost
    zero(hjb+nu*(factor-1)*D+2*beta*factor*(Z-M)*Z+2*factor*loss+2*(b+g0),
         'direct Bellman supersolution calculation retains all admissible controls')
    return dict(weight='phi=exp(2 L (H-t)+C^2 E(t)/(4 nu^2))',
                reserve='R=(2 phi-1) Z+2 (H-t)|g(0)|',
                paid_cost='2(g(t)-g(0))-nu D(t)',
                initial_allowance='(2 exp(2 L H+C^2 E0/(4 nu^2))-1) Z0+2H|g(0)|',
                forced_defect='(4 phi-2)<omega,curl f>+4 Gamma phi Z<u,f>',
                hypothesis='The actual oscillatory remainder satisfies the fixed geometric and critical-exterior conditions at every time. Its propagation remains open.')


def source_hashes():
    root = Path(__file__).resolve().parent
    pending, seen = [Path(__file__).resolve()], set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for node in ast.walk(ast.parse(path.read_text())):
            names = ([a.name for a in node.names] if isinstance(node, ast.Import)
                     else [node.module] if isinstance(node, ast.ImportFrom) and node.level == 0 else [])
            for name in names:
                if name:
                    dependency = root / (name.split('.')[0]+'.py')
                    if dependency.is_file():
                        pending.append(dependency)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)}


def checks():
    return dict(history=history_jet(), large_mean=large_mean_fixtures(),
                axis_and_clock=axis_and_clock(), reserve=payment_algebra(),
                source_sha256=source_hashes(),
                scope='Complete exact source and reserve checks. The physical mean estimate, spectral estimate, local solution and uniform remainders are analytic. No arbitrary-history propagation or new Lean theorem is claimed.')


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
