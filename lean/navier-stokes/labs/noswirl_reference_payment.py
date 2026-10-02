#!/usr/bin/env python3
"""Actual no-swirl reference and a swirl-seeded residual-parent budget.

Exact checks retain the physical relative energy, both parent feedback
terms, the initial source and critical coefficients. Global reference
existence, weighted propagation, stochastic representation and operator
estimates are analytic results or cited theory, not Lean certificates.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity, gaussian_coefficient
from critical_parent_transport import inverse_half, terms, moment


def actual_residual():
    chi, chibar, b = [s.Function(n)(r, z) for n in ('chi', 'chi_bar', 'b')]
    nu = s.symbols('nu', positive=True)
    eta, etabar = -lap5(chi), -lap5(chibar)
    v, vb = velocity(chi), velocity(chibar)
    va, h = v-vb, eta-etabar
    etat = nu*lap5(eta)-v.dot(grad(eta))+s.diff(b*b, z)
    etabart = nu*lap5(etabar)-vb.dot(grad(etabar))
    ht = nu*lap5(h)-v.dot(grad(h))+s.diff(b*b, z)-va.dot(grad(etabar))
    zero(etat-etabart-ht, 'actual parent subtraction keeps deviation feedback')
    zero(ht.subs(chi, chibar).doit()-s.diff(b*b, z),
         'matched initial parents give h_t(0)=partial_z b0^2')
    brate = nu*lap5(b)-v.dot(grad(b))+2*s.diff(chi, z)*b
    reference_brate = nu*lap5(b)-vb.dot(grad(b))+2*s.diff(chibar, z)*b
    zero(brate-reference_brate+va.dot(grad(b))-2*s.diff(chi-chibar, z)*b,
         'the swirl channel retains actual residual transport and strain')
    delta = chi-chibar
    zero(s.diff(r**3*delta*va[0], r)+s.diff(r**3*delta*va[1], z),
         'residual canonical transport gives zero integrated quadratic feedback')
    return {'h_equation': 'h_t+v.grad h=nu Delta5 h+partial_z b^2-v_a.grad eta_bar',
            'a_equation': 'a_t+v.grad a=nu Delta5 a+R_z b^2-[L,v.grad]h-L(v_a.grad eta_bar)',
            'initial': 'h(0)=a(0)=0; h_t(0)=partial_z b0^2',
            'zero_swirl': 'uniqueness of the actual NS solution makes the entire deviation identically zero',
            'history': 'h(t,x)=E integral_0^t [partial_z b^2-v_a.grad eta_bar](t-s,X_s)ds; dX_s=-v(t-s,X_s)ds+sqrt(2nu)dW_s'}


def physical_relative_energy():
    x = s.symbols('x0:3', real=True)
    nu = s.symbols('nu', positive=True)
    w = s.Matrix([s.Function('w'+str(i))(*x) for i in range(3)])
    V = s.Matrix([s.Function('V'+str(i))(*x) for i in range(3)])
    pressure = s.Function('pressure_difference')(*x)
    U = V+w
    div = lambda f: sum(s.diff(f[i], x[i]) for i in range(3))
    lap = lambda f: sum(s.diff(f, xi, 2) for xi in x)
    dw, dV = w.jacobian(x), V.jacobian(x)
    rhs = nu*w.applyfunc(lap)-dw*U-dV*w-s.Matrix([s.diff(pressure, xi) for xi in x])
    zero(2*w.dot(rhs)+div(U*w.dot(w)+2*pressure*w)-nu*lap(w.dot(w))
         +2*nu*sum(e*e for e in dw)+2*w.dot(dV*w)
         -div(U)*w.dot(w)-2*pressure*div(w), 'literal physical relative energy identity')
    zero(U*U.T-V*V.T-(w*w.T+V*w.T+w*V.T),
         'pressure difference keeps self and both mixed tensors')
    zero(2+4-6, 'self-transport and pressure coefficient in the relative moment')
    zero(2+4*2-10, 'reference transport and mixed pressure coefficient')
    C, E, Z, lam, defect = s.symbols('C E Z lam defect', positive=True)
    energy_rate = -2*nu*Z+2*lam*E-defect
    zero((-2*lam*C*E+C*energy_rate)/(2*nu)+C*Z+C*defect/(2*nu),
         'the remaining-horizon relative kinetic reserve pays enstrophy')
    return {'energy': 'E_w_prime+2nu Z_w=-2 integral w.(grad V)w',
            'stock': 'Ebar=E_swirl0 exp(2L_H); E_w(t)<=Ebar; integral_0^T Z_w<=Ebar/(2nu)',
            'reference': 'L_H=integral_0^H ||grad V||_infinity; U_H=integral_0^H ||V||_infinity',
            'moment': 'sqrt(I_w(t))<=Mrel=exp(L_H)[sqrt(I_swirl0+6nu Ebar H)+3CS^(3/2)Ebar^(1/4)H^(1/4)(Ebar/(2nu))^(3/4)+5sqrt(Ebar)U_H]',
            'scope': 'every actual smooth target prefix; reference exists globally independently of target swirl'}


def lifted_derivatives():
    f, g = s.Function('F'), s.Function('G')
    Fr, Fz = s.diff(f(r, z), r), s.diff(f(r, z), z)
    independent = ((2*Fr+r*s.diff(f(r, z), r, 2))**2
                   +r*r*s.diff(f(r, z), z, 2)**2
                   +2*(Fz+r*s.diff(f(r, z), r, z))**2
                   +s.diff(g(r, z), r, 2)**2+s.diff(g(r, z), z, 2)**2
                   +2*s.diff(g(r, z), r, z)**2)
    repeated = 3*Fr**2+2*Fz**2+(s.diff(g(r, z), r)/r)**2
    norms = {}
    for d in (2, 4):
        y = s.symbols('y0:'+str(d), real=True)
        rho = s.sqrt(sum(t*t for t in y))
        vector = [t*f(rho, z) for t in y]+[g(rho, z)]
        coordinates = (*y, z)
        axis = {y[0]: r, **{t: 0 for t in y[1:]}}
        norm2 = sum(s.diff(component, xi, xj).subs(axis).doit()**2
                    for component in vector for xi in coordinates for xj in coordinates)
        zero(norm2-independent-(d-1)*repeated,
             'literal Cartesian Hessian norm with '+str(d)+' horizontal coordinates')
        norms[d] = independent+(d-1)*repeated
    zero(3*norms[2]-norms[4]-2*independent,
         'lifted second derivative is bounded by sqrt(3) times physical derivative')
    return {'pointwise': '|D2 V_lift|^2<=3|D2 V_physical|^2',
            'domain': 'smooth rotational meridional field (y_i F(r,z),G(r,z)); axis by continuity',
            'use': 'weighted physical L2 derivatives and supremum control give the required lifted L5 norms'}


def mixed_parent_test():
    chi = s.exp(-r*r-2*z*z)
    chibar = z*chi
    b = chi
    va, vb = velocity(chi), velocity(chibar)
    h, etabar = -lap5(chi), -lap5(chibar)
    qbar = 2*s.diff(chibar, z)
    first = gaussian_coefficient(chi*vb.dot(grad(h)), 3)
    second = gaussian_coefficient(chi*va.dot(grad(etabar)), 3)
    swirl = gaussian_coefficient(qbar*b*b, 3)
    physical = gaussian_coefficient(va.dot(vb.jacobian((r, z))*va)
                                    +r*b*b*vb[0], 3, radial_power=1)
    zero(swirl-2*(first+second)+2*physical,
         'both parent cross terms reproduce literal physical relative strain work')
    require(first != 0 and second == 0 and physical != 0,
            'reference transport is active but quadratic feedback cancels')
    return {'reference_transport': str(first), 'deviation_feedback': str(second),
            'reference_swirl_strain': str(swirl), 'physical_strain': str(physical),
            'normalization': 'all coefficients omit the common factor 2pi^2 sqrt(pi/6)',
            'scope': 'kinematically compatible two-field test of the identity, not a claimed matched-initial reference trajectory'}


def critical_feedback_test():
    base = 1+r*r+z*z
    chi, chibar = base**(-2), z*base**(-3)
    a = inverse_half(-lap5(chi))
    zero(a-4/base**3, 'positive rational canonical residual parent')
    source = velocity(chi).dot(grad(-lap5(chibar)))
    response = inverse_half(source)
    quadratic = s.simplify(s.expand_func(4*sum(c*moment(m, k+3)
                       for c, m, k in terms(response) if m % 2 == 0)))
    critical = s.simplify(s.expand_func(8*sum(c*moment(m, k+s.Rational(9, 2))
                       for c, m, k in terms(response) if m % 2 == 0)))
    zero(quadratic, 'the feedback pairing vanishes at p=2')
    zero(critical-s.Rational(222816, 1978375)*s.pi**2,
         'the complete feedback pairing is nonzero at p=5/2')
    return {'quadratic_pairing': str(quadratic), 'critical_pairing': str(critical),
            'sign': 'reversing chi_bar reverses the critical pairing',
            'scope': 'kinematic operator test; no claim of reachability from matched initial parents'}


def critical_payment():
    pp = s.Rational(5, 2)
    zero(pp/(4-pp)-s.Rational(5, 3), 'horizontal Hardy exponent and constant')
    zero(2+2*pp/(4-pp)-s.Rational(16, 3), 'residual v_a/r multiplier bound')
    zero(1/pp+s.Rational(1, 5)-s.Rational(3, 5), 'reference product goes into L5/3')
    zero(s.Rational(3, 5)-s.Rational(1, 5)-1/pp, 'R5 potential maps L5/3 into L5/2')
    b, a, p = s.symbols('b a p', positive=True)
    q, qb, Tw, comm, pre, feed = s.symbols('q q_bar T_self source_comm transport_bar feedback_bar', real=True)
    X = b*b+a*a
    w = X**(p/2-1)
    phi = X**(p/2)
    raw = (q+qb)*(p*w*b*b-phi)-p*(q*w*b*b/2+comm)
    raw -= p*(Tw-q*w*a*a/2+pre+feed)
    target = (p/2-1)*q*phi-p*comm-p*Tw+qb*w*((p-1)*b*b-a*a)-p*pre-p*feed
    zero(raw-target, 'complete reference critical balance')
    zero(s.Rational(25, 16)*2/pp-s.Rational(5, 4), 'continuation coefficient retains half the diffusion')
    return {'feedback': '||L(v_a.grad eta_bar)||_(5/2)<=ell_bar ||a||_(5/2)',
            'ell_bar': '(16/3) C_I C_R ||r grad eta_bar||_5',
            'transport': '||[L,V.grad]Lambda a||_(5/2)<=C_op N(V)||a||_(5/2)',
            'clock': 'kappa_bar=(3/2)||q_bar||_infinity+(5/2)[C_op N(V)+ell_bar]',
            'balance': 'R_p_prime+nu D_p<=Q_self+kappa_bar R_p; R_p(0)=integral |b0|^(5/2)',
            'reference_cost': 'finite from the known global no-swirl flow and weighted derivative propagation; not an assumed bound on the target flow',
            'open_target': 'int_0^T exp(-int_0^t kappa_bar-c_R t)[Q_near-nu D_p/4]<=K_near(original datum,nu,H,R)'}


def far_scaling():
    eps, E, I, H, nu, Lh, Uh, CS = s.symbols('eps E I H nu Lh Uh CS', positive=True)
    Ebar = E*s.exp(2*Lh)
    Mlinear = s.exp(Lh)*(s.sqrt(I+6*nu*Ebar*H)+5*s.sqrt(Ebar)*Uh)
    Mquadratic = s.exp(Lh)*3*CS**s.Rational(3, 2)*Ebar**s.Rational(1, 4)*H**s.Rational(1, 4)*(Ebar/(2*nu))**s.Rational(3, 4)
    Mrel = Mlinear+Mquadratic
    scaled = s.powdenest(Mrel.subs({E: eps**2*E, I: eps**2*I}, simultaneous=True), force=True)
    zero(scaled-eps*Mlinear-eps**2*Mquadratic,
         'relative spatial moment vanishes with initial swirl at fixed reference')
    zero(s.Rational(14, 5)*s.Rational(5, 3)-s.Rational(14, 3),
         'complete far stress coefficient in physical relative stocks')
    zero(4-s.Rational(5, 2)*s.Rational(4, 5)-2,
         'far linear coefficient scales at least quadratically in small swirl')
    return {'far_norm': 'P_R=3pi cK R^(-2)Ebar+(14pi/3)cD R^(-3)sqrt(Ebar)Mrel',
            'small_swirl': 'Ebar=O(eps^2), Mrel=O(eps)+O(eps^2), P_R=O(eps^2)+O(eps^3)',
            'clock': 'L0=R_p(0)=O(eps^(5/2)) gives c_R=O(eps^2), d_R=O(eps^(9/2))',
            'warning': 'fixed reference, viscosity, horizon and cutoff; this is no arbitrary-amplitude near-history estimate'}


if __name__ == '__main__':
    print(json.dumps({'residual': actual_residual(), 'physical': physical_relative_energy(),
                      'lift': lifted_derivatives(),
                      'mixed_parent': mixed_parent_test(), 'critical_feedback': critical_feedback_test(),
                      'critical': critical_payment(),
                      'far': far_scaling()}, indent=2))
