#!/usr/bin/env python3
"""Actual vorticity geometry with retained passive and impulse parents.

Exact matrix and full Fourier time-jet checks retain the original actual
gradient. Optional spatial quadratures use the full initial NS generator
and a datum-fixed threshold above the initial envelope. They do not
construct a time history or prove a nonlinear renewal allowance.
"""

import argparse
import json
import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
import pressure_diffusion_completion as completion
from pressure_impulse_history import vector_transport
from signed_viscous_pressure import interacting_datum


KAPPA = 192


def coefficient_checks():
    R, q, e, g = s.symbols('R q e g', nonnegative=True)
    radial = 2*(R+q)*e+s.Rational(2, 5)*g
    lower = 32*(R+q)*e+s.Rational(56, 5)*g
    core = -s.Rational(6976, 21)*R*e+KAPPA*radial-lower
    pressure = -(352*R+16*q)*e-8*g+KAPPA*radial-lower
    if s.expand(core-(s.Rational(416, 21)*R*e+352*q*e+s.Rational(328, 5)*g)) != 0:
        raise ArithmeticError('joint core curvature margin')
    if s.expand(pressure-(336*q*e+s.Rational(288, 5)*g)) != 0:
        raise ArithmeticError('joint pressure curvature margin')
    if s.expand(2*(R+q)**2-8*R*q-2*(R-q)**2) != 0:
        raise ArithmeticError('positive pressure branch scale')
    return {'completion_constant': KAPPA,
            'mixed_curvature_lower': '32 Q (|E_H|^2+|E_I|^2)+(56/5)|L|^2',
            'actual_parent_payment': 'mixed curvature >=8 |B|^2 |E_H-E_I|^2',
            'actual_vorticity_coercivity': 'Phi_joint>=1+12|omega|^4+|P|^2',
            'signed_history_allowance': 'OPEN'}


def matrix_checks():
    import numpy as np
    t = s.symbols('t', real=True)
    B = s.Matrix([[3, 0, 3], [4, 4, 2], [3, 1, -7]])
    A = s.Matrix([[1, 2, 0], [0, -1, 3], [2, 0, 0]])
    EH = s.Matrix([[2, -1, 3], [4, 1, 0], [0, 2, -3]])
    EI = s.Matrix([[1, 2, 0], [0, -1, 3], [2, 0, 0]])
    P = s.diag(2, 2, 0)
    L = s.Matrix([[1, -2, 3], [-2, 4, 0], [3, 0, -1]])
    norm = lambda M: s.trace(M.T*M)

    def branches(H, I, Ph):
        p0, c0 = completion.branches(H-I, Ph, s.Integer(1))
        Q = norm(H)+norm(I)+s.sqrt(1+norm(Ph))
        return p0+KAPPA*Q**2, c0+KAPPA*Q**2

    cases = []
    for H0, I0 in [(B, s.zeros(3)), (B+A, A), (A, A), (-A, A)]:
        a, b = branches(H0+t*EH, I0+t*EI, P+t*L)
        a0, b0 = a.subs(t, 0), b.subs(t, 0)
        da, db = s.diff(a, t).subs(t, 0), s.diff(b, t).subs(t, 0)
        dda, ddb = s.diff(a, t, 2).subs(t, 0), s.diff(b, t, 2).subs(t, 0)
        Q0 = norm(H0)+norm(I0)+3
        lower = 32*Q0*(norm(EH)+norm(EI))+s.Rational(56, 5)*norm(L)
        if not (dda >= lower and ddb >= lower and a0 >= 190*Q0**2 and b0 >= 192*Q0**2):
            raise ArithmeticError('independent exact mixed branch curvature')
        rho2 = a0*a0+b0*b0
        numerator = (a0*dda+b0*ddb)*rho2+(b0*da-a0*db)**2
        # Squaring is legitimate after the independent nonnegative signs.
        if not (numerator >= 0 and lower >= 0 and numerator**2 >= lower**2*rho2**3):
            raise ArithmeticError('exact radial Hessian lower by rational square comparison')
        actual = H0-I0
        omega2 = norm(completion.curl_matrix(actual))
        if not 12*omega2**2 <= 192*Q0**2:
            raise ArithmeticError('actual, rather than passive, vorticity coercivity')
        # Independently differentiated exact expressions also test the
        # array adapter away from the zero-impulse initial slice.
        array = lambda M: np.array(M.tolist(), dtype=float)
        observed = joint_jet(array(H0), array(I0), array(P),
                             (array(EH), array(EI), array(L)))
        expected = [float(1+s.sqrt(rho2)), float((a0*da+b0*db)/s.sqrt(rho2)),
                    float(numerator/rho2**s.Rational(3, 2))]
        relative = [abs(float(v)-w)/max(1, abs(w)) for v, w in zip(observed, expected)]
        if max(relative) > 3e-12:
            raise ArithmeticError(('joint array adapter versus exact matrix derivatives', relative))
        cases.append({'actual_gradient': str(actual), 'retained_square': str(norm(H0)+norm(I0)),
                      'mixed_increment_square': str(norm(EH)+norm(EI)),
                      'radial_Hessian_lower_exact': True,
                      'array_adapter_relative_errors': relative,
                      'scope': 'matrix domain test; no reachable-history claim'})

    def value(H, I):
        a, b = branches(H, I, P)
        return 1+s.sqrt(a*a+b*b)

    old = s.diff(value(B-t*P, s.zeros(3)), t).subs(t, 0)
    retained = s.diff(value(B, t*P), t).subs(t, 0)
    a0, b0 = branches(B, s.zeros(3), P)
    expected = 4*KAPPA*(norm(B)+3)*s.trace(B.T*P)*(a0+b0)/s.sqrt(a0*a0+b0*b0)
    if s.simplify(retained-old-expected) != 0:
        raise ArithmeticError('initial radial pressure transfer preserves actual geometry')
    return cases


def exact_parent_laws(sign):
    u = [f.scale(sign, q) for q in interacting_datum()]
    nu = f.QQ_I(1)/10
    B = f.jac(u)
    p = f.tensor_pressure(f.tensor(u, u))
    gp, P = f.grad(p), f.hess(p)
    Ht = vector_transport(u, u, nu)
    ut = [f.add(v, f.scale(-1, w)) for v, w in zip(Ht, gp)]
    BHt, Bt = f.jac(Ht), f.jac(ut)
    DH = pm.matrix_add(BHt, pm.matrix_adv(u, B),
        pm.matrix_scale(-nu, [[f.lap(q) for q in row] for row in B]))
    f.same_matrices(DH, pm.matrix_scale(-1, f.matmul(B, B)),
                    'actual passive-gradient parent deformation')
    f.same_matrices(pm.matrix_add(BHt, pm.matrix_scale(-1, Bt)), P,
                    'actual initial impulse gradient source')
    DB = pm.matrix_add(Bt, pm.matrix_adv(u, B),
        pm.matrix_scale(-nu, [[f.lap(q) for q in row] for row in B]))
    f.same_matrices(DB, pm.matrix_add(pm.matrix_scale(-1, f.matmul(B, B)),
                                    pm.matrix_scale(-1, P)), 'complete actual gradient law')
    r = pm.pair(B, B)
    parent = -4*pm.mean(f.mul(r, pm.pair(B, f.matmul(B, B))))
    pressure = -4*pm.mean(f.mul(r, pm.pair(B, P)))
    force = f.curl(u)
    if pm.mean(f.dot(u, force)) != 0:
        raise ArithmeticError('initial kinetic force work')
    forced_ut = [f.add(v, w) for v, w in zip(ut, force)]
    forced_I = pm.matrix_add(BHt, pm.matrix_scale(-1, f.jac(forced_ut)))
    f.same_matrices(forced_I, pm.matrix_add(P, pm.matrix_scale(-1, f.jac(force))),
                    'force impulse retained in the actual split')
    extraP = pm.observe(pm.symmetric_product(u, force))
    if all(not q for row in extraP for q in row):
        raise ArithmeticError('nonzero force-pressure leg required')
    return {'velocity_sign': sign, 'quartic_parent_reaction': str(parent),
            'quartic_pressure_reaction': str(pressure), 'complete_parent_laws': 'exact',
            'fixed_force_impulse_and_pressure': 'retained',
            'scope': 'all Fourier outputs, initial NS jets; no history bound'}


def joint_jet(H, I, P, increments=None):
    import numpy as np
    from joint_receiver_quadrature import dot, vecdot, mv, curl, sym
    B = H-I
    S, w = sym(B), curl(B)
    W, Sw = vecdot(w, w), mv(S, w)
    V, Z, ss = vecdot(w, Sw), vecdot(Sw, Sw), dot(S, S)
    R, q = dot(H, H)+dot(I, I), np.sqrt(1+dot(P, P))
    Q = R+q
    T = V*V/(W+1)
    p0 = 5*T+(63/95)*W*W-2*vecdot(w, mv(P, w))
    c0 = 5*T+(4/7)*Z+(10/21)*ss*W+(44/95)*W*W
    a, b = p0+KAPPA*Q*Q, c0+KAPPA*Q*Q
    rho = np.sqrt(a*a+b*b)
    value = 1+rho
    if increments is None:
        return value
    EH, EI, L = increments
    E = EH-EI
    ES, v = sym(E), curl(E)
    dW, ddW = 2*vecdot(w, v), 2*vecdot(v, v)
    dV = 2*vecdot(v, Sw)+vecdot(w, mv(ES, w))
    ddV = 2*vecdot(v, mv(S, v))+4*vecdot(v, mv(ES, w))
    dT = 2*V*dV/(W+1)-V*V*dW/(W+1)**2
    ddT = 2*(dV-V*dW/(W+1))**2/(W+1)+2*V*ddV/(W+1)-(V/(W+1))**2*ddW
    dSw = mv(ES, w)+mv(S, v)
    dZ, ddZ = 2*vecdot(Sw, dSw), 2*vecdot(dSw, dSw)+4*vecdot(Sw, mv(ES, v))
    dss, ddss = 2*dot(S, ES), 2*dot(ES, ES)
    dwPw = 2*vecdot(v, mv(P, w))+vecdot(w, mv(L, w))
    ddwPw = 2*vecdot(v, mv(P, v))+4*vecdot(v, mv(L, w))
    dp, ddp = 5*dT+(126/95)*W*dW-2*dwPw, 5*ddT+(126/95)*(dW*dW+W*ddW)-2*ddwPw
    dc = 5*dT+(4/7)*dZ+(10/21)*(dss*W+ss*dW)+(88/95)*W*dW
    ddc = 5*ddT+(4/7)*ddZ+(10/21)*(ddss*W+2*dss*dW+ss*ddW)+(88/95)*(dW*dW+W*ddW)
    d = dot(H, EH)+dot(I, EI)
    e, g, ell = dot(EH, EH)+dot(EI, EI), dot(L, L), dot(P, L)/q
    dR = 2*Q*(2*d+ell)
    ddR = 8*d*d+4*Q*e+8*d*ell+2*g+2*R/q*(g-ell*ell)
    da, db, dda, ddb = dp+KAPPA*dR, dc+KAPPA*dR, ddp+KAPPA*ddR, ddc+KAPPA*ddR
    first = (a*da+b*db)/rho
    second = (a*dda+b*ddb)/rho+(b*da-a*db)**2/rho**3
    return value, first, second


def datum_threshold():
    u = interacting_datum()
    B, P = f.jac(u), f.hess(f.tensor_pressure(f.tensor(u, u)))
    square_bound = lambda M: sum(sum(abs(a.x)+abs(a.y) for a in q.values())**2
                                 for row in M for q in row)
    r, pressure = square_bound(B), square_bound(P)
    return int(300+1024*(r*r+r+2*pressure))+1


def spatial_case(n, sign):
    import numpy as np
    from signed_viscous_pressure_quadrature import Grid
    from joint_receiver_quadrature import dot, vecdot, mv, outer, sm, slots, curl
    g, nu = Grid(n), .1
    u = np.stack([sign*g.field(q) for q in interacting_datum()], axis=-1)
    B = g.jac(u)
    p = g.potential(outer(u, u))
    gp, P = g.jac(p), g.jac(g.jac(p))
    zero = np.zeros_like(B)
    G = B@np.swapaxes(B, -1, -2)
    PG = g.observe(G)
    ut = -mv(B, u)-gp+nu*g.lap(u)
    Bt = g.jac(ut)
    Pt = g.observe(outer(u, ut)+outer(ut, u))
    Ph_t = Pt+2*nu*PG
    value, first, _ = joint_jet(B, zero, P, (Bt+P, P, Ph_t))
    Phi = value+dot(P, P)
    b = datum_threshold()
    omega2 = vecdot(curl(B), curl(B))
    if np.max(Phi) >= b or np.min(Phi-12*omega2**2) <= 0:
        raise ArithmeticError('above-initial threshold and actual-vorticity coercivity')
    direct = 8*np.mean(first+2*dot(P, Pt))
    _, oldfirst, _ = joint_jet(B, zero, P, (Bt, zero, Ph_t))
    olddirect = 8*np.mean(oldfirst+2*dot(P, Pt))
    native, parent = np.zeros(g.k2.shape), np.zeros(g.k2.shape)
    for j in range(3):
        E, L = g.deriv(B, j), g.deriv(P, j)
        _, _, curvature = joint_jet(B, zero, P, (E, zero, L))
        Q = dot(B, B)+np.sqrt(1+dot(P, P))
        lower = 32*Q*dot(E, E)+(56/5)*dot(L, L)
        if np.min(curvature-lower) < -2e-10*max(1, np.max(curvature)):
            raise ArithmeticError('mixed diffusion lower')
        native += nu*(curvature+2*dot(L, L))
        parent += dot(B, B)*dot(E, E)
    stress = outer(u, u)
    comm = sum(sm(u[..., j], g.deriv(P, j)) for j in range(3))-g.observe(
        sum(sm(u[..., j], g.deriv(stress, j)) for j in range(3)))
    reactionP = comm-g.observe(outer(u, gp)+outer(gp, u))
    _, reactionPsi, _ = joint_jet(B, zero, P, (-B@B, P, reactionP))
    reaction = 8*np.mean(reactionPsi+2*dot(P, reactionP))
    source = -32*nu*np.mean(dot(P, PG))
    Dtotal = 8*np.mean(native)
    scale = max(1, abs(direct), abs(reaction), Dtotal)
    residual = abs(direct+Dtotal-reaction-source)/scale
    if residual > 2e-7:
        raise ArithmeticError(('complete joint physical generator', residual))
    tol = 2e-10*max(1, Dtotal)
    if 8*nu*np.mean(parent) > np.mean(native)+tol:
        raise ArithmeticError('actual derivative parents paid by joint diffusion')
    if abs(source) > .75*Dtotal+tol or direct+.25*Dtotal > reaction+tol:
        raise ArithmeticError('prior viscous absorption preserved')
    # The actual geometry remains in both variants; only radial pressure
    # injection is transferred. The direct complete pressure slots remain.
    _, *_, TB, _ = slots(B, P)
    return {'grid': n, 'velocity_sign': sign, 'datum_fixed_threshold': b,
            'joint_initial_envelope_max': float(np.max(Phi)),
            'joint_initial_reserve_derivative': float(direct),
            'same_constant_untransferred_derivative': float(olddirect),
            'radial_pressure_transfer': float(direct-olddirect),
            'complete_joint_nonlinear_work': float(reaction),
            'total_joint_diffusion': float(Dtotal),
            'actual_parent_diffusion_cost': float(8*nu*np.mean(parent)),
            'explicit_viscous_pressure_work': float(source),
            'generator_relative_residual': float(residual),
            'earlier_constant_direct_pressure_leg': float(-8*np.mean(dot(TB, P))),
            'scope': 'initialized actual initial PDE generator; no time trajectory or continuum enclosure'}


def quadrature():
    cases = [spatial_case(n, sign) for n in (96, 128) for sign in (-1, 1)]
    comparisons = []
    for sign in (-1, 1):
        old = next(c for c in cases if c['grid'] == 96 and c['velocity_sign'] == sign)
        new = next(c for c in cases if c['grid'] == 128 and c['velocity_sign'] == sign)
        changes = {name: abs(new[name]-old[name])/max(1, abs(new[name])) for name in
                   ('joint_initial_reserve_derivative', 'complete_joint_nonlinear_work',
                    'total_joint_diffusion', 'radial_pressure_transfer')}
        if max(changes.values()) > 2e-5:
            raise ArithmeticError(('independent joint quadrature', changes))
        comparisons.append({'velocity_sign': sign, 'relative_changes': changes})
    return {'cases': cases, 'independent_comparisons': comparisons,
            'nonlinear_history_allowance': 'OPEN'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--quadrature', action='store_true')
    args = parser.parse_args()
    report = {'coefficients': coefficient_checks(), 'exact_matrix_cases': matrix_checks(),
              'exact_physical_parents': [exact_parent_laws(sign) for sign in (-1, 1)]}
    if args.quadrature:
        report['quadrature'] = quadrature()
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
