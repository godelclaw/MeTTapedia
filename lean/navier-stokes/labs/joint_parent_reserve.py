#!/usr/bin/env python3
"""Joint parent accounting: a tested metric and a full-energy Bellman payment.

Exact full NS initial tangents test an adaptive positive hidden-energy
correction, retaining its pressure and coefficient derivatives. A separate
finite-horizon Bellman certificate pays bounded strain observations from
total kinetic energy. Its finite-band constant cannot be erased. The
continuous estimates and remaining high-strain obligation are in README.md.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
import planar_parent_reserve as p


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def joint_metric():
    # The frequency constants 5 and 1 are fixed from the original mean.
    # All dependence on its evolving Z,Y,E must still be differentiated.
    Z, Y, E, nu = s.symbols('Z Y E nu', positive=True)
    r = 8*s.sqrt(Y)*s.exp(64*Z/nu**2)/nu
    V = E*(s.exp(2*r)-1)
    ch = 5*s.diff(V, Z)+25*s.diff(V, Y)
    cz = s.diff(V, E)
    x, sigma, R, S = s.symbols('x sigma R S', real=True)
    rows = []
    for phase in (-1, 1):
        u = p.feedback_datum(Q(1), phase)
        U, P = p.velocity_time_jets(u, Q(8), 1)
        physical = p.check_split(u, Q(8), 'adaptive joint metric')
        require(Q(physical['actual_parent_reserve_rate_over_reserve']) == -80+8*phase,
                'complete mean reserve rate at the tested viscosity')
        require(Q(physical['parent_gradient_rate']) == -200+20*phase,
                'complete mean gradient rate')
        require(2*p.gradient_inner(p.average(u[2]), p.average(U[1][2])) == -32,
                'complete mean receiver rate')
        a = [f.add(q, f.scale(-1, p.average(q))) for q in u]
        a1 = [f.add(q, f.scale(-1, p.average(q))) for q in U[1]]
        aU, _ = p.velocity_time_jets(a, Q(0), 1)
        # Cubic self-work is exactly zero on this two-mode support;
        # no degree-three term is inferred merely from sampling amplitudes.
        for i in range(3):
            require(p.inner(a[i], aU[1][i]) == 0, 'zero hidden cubic self-work')
        khp = 2*sum(p.inner(a[i], a1[i]) for i in (0, 1))
        kzp = 2*p.inner(a[2], a1[2])
        ph = -2*sum(p.inner(a[i], f.diff(P[0], i)) for i in (0, 1))
        pz = -2*p.inner(a[2], f.diff(P[0], 2))
        require(khp == -80-Q(7, 10)*phase and kzp == -16-Q(1, 10)*phase,
                'full hidden kinetic rates, including pressure')
        require(ph == Q(phase, 10) and pz == -ph, 'signed anisotropic pressure transfer')
        rows.append({'phase':phase, 'Kh_rate_over_epsilon_squared':str(khp),
                     'Kz_rate_over_epsilon_squared':str(kzp),
                     'horizontal_pressure_work_over_epsilon_squared':str(ph)})
    # At nu=8, Z=1/2,Y=5/2,E=2, use exact symbols R=r and S=exp(2r).
    # Z'=-40+4 sigma*x, Y'=5Z', E'=-32, x=epsilon^2.
    beta = -80+8*sigma*x
    Vr = -32*(S-1)+4*S*R*beta
    chr = 2*S*R*(20*(-16+(1+2*R)*beta)+800-80*sigma*x)
    czr = 2*S*R*beta
    total = s.expand(Vr + 2*x*chr + 40*S*R*(-80-s.Rational(7,10)*sigma)*x
                     + x*czr/2 + (S-1)*(-16-s.Rational(1,10)*sigma)*x)
    leading = s.expand(total).coeff(x, 2)
    require(s.factor(leading-sigma*S*R*(1280*R+328)) == 0,
            'positive quartic weight-renewal defect')
    # Independently differentiate the original functional, then substitute.
    rates = {Z:-40+4*sigma*x, Y:-200+20*sigma*x, E:-32}
    deriv = lambda F: sum(s.diff(F, z)*rate for z, rate in rates.items())
    subs = {nu:8, Z:s.Rational(1,2), Y:s.Rational(5,2), E:2}
    rr = r.subs(subs)
    raw = deriv(V)+2*x*deriv(ch)+ch*(-80-s.Rational(7,10)*sigma)*x
    raw += x*deriv(cz)/2+cz*(-16-s.Rational(1,10)*sigma)*x
    require(s.simplify(raw.subs(subs)-total.subs({R:rr,S:s.exp(2*rr)})) == 0,
            'independent derivative of positive joint state functional')
    # epsilon=4 already has a positive derivative, proved by a polynomial
    # lower bound using R>=1 and S>=1, without floating transcendental values.
    value = s.expand(total.subs({sigma:1,x:16}))
    shifted = s.Poly(s.expand(value.subs({R:R+1,S:S+1})),R,S)
    require(all(c>0 for c in shifted.coeffs()), 'strict positivity at epsilon=4')
    return {'canonical_checks':rows,'candidate':'V+ch*Kh+cz*Kz, ch=5 V_Z+25 V_Y, cz=V_E',
            'quartic_coefficient':str(leading), 'positive_epsilon':4,
            'positive_derivative_shifted_coefficients':list(map(str,shifted.coeffs())),
            'scope':'actual initial derivative; positive short interval by local smooth existence'}


def bellman():
    nu, h, E, d, C = s.symbols('nu h E d C', positive=True)
    R = C*s.sqrt(h*E/(2*nu))
    loss = -(-s.diff(R,h)-2*nu*d*s.diff(R,E))
    gap = C*(s.sqrt(E)-s.sqrt(2*nu*h*d))**2/(2*s.sqrt(2*nu*h*E))
    require(s.simplify(loss-C*s.sqrt(d)-gap) == 0, 'Bellman square completion')
    require(s.simplify((loss-C*s.sqrt(d)).subs(d,E/(2*nu*h))) == 0,
            'relaxed optimal dissipation control')
    return {'reserve':str(R),'loss_gap':str(gap),
            'optimal_relaxed_dissipation':'E/(2*nu*h)',
            'scope':'relaxation of the actual energy equation, not freely controlled fluid forcing'}


def sharp_band(N):
    # Real, solenoidal dual maximizer of partial_x u1 at the origin,
    # normalized against the complete squared gradient energy.
    u=[{}, {}, {}]
    expected=Q(0)
    for i in range(N,2*N+1):
        for j in range(N,2*N+1):
            for ell in range(N,2*N+1):
                k=(i,j,ell); kk=sum(v*v for v in k)
                expected += 2*Q(i*i,kk)*(1-Q(i*i,kk))
                for m in range(3):
                    z=-f.II*f.QQ_I(Q(i,kk)*(int(m==0)-Q(k[m]*i,kk)))
                    u[m][k]=z
                    u[m][tuple(-v for v in k)]=-z
    f.equal(f.trace(f.jac(u)),{},'sharp strain datum is solenoidal')
    # Parseval directly, avoiding an unnecessary quadratic product expansion.
    Z=sum(Q(sum(v*v for v in k))*Q(str(z.x*z.x+z.y*z.y))
          for row in u for k,z in row.items())
    observed=Q(str(f.evaluate(f.diff(u[0],0))))
    require(Z==expected and observed==expected,'exact attained strain dual norm')
    cardinal=2*(N+1)**3
    # Each k1^2/|k|^2 is in [1/12,2/3]; x(1-x)>=11/144.
    require(expected>=Q(11,144)*cardinal,'scale growth cannot be removed')
    return {'N':N,'modes':cardinal,'gradient_energy':str(Z),
            'point_strain':str(observed),'dual_norm_squared':str(expected),
            'lower_bound_squared':str(Q(11,144)*cardinal)}


def main():
    print(json.dumps({'joint_metric':joint_metric(), 'bellman':bellman(),
                      'sharp_finite_bands':[sharp_band(n) for n in (1,2,4,8)],
                      'scope':'exact checks; analytic physical history and smoothing identification in README'},indent=2))


if __name__=='__main__':
    main()
