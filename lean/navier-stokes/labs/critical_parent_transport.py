#!/usr/bin/env python3
"""Critical parent transport, exact rational fields and a nodal Young-cost test.

Exact algebra and beta moments retain the complete unforced meridional
nonlinearity. Identification of the fractional operator, smooth NS histories
and the local nonintegrability argument are analytic, not Lean-certified.
Optional quadrature checks the Riesz potential independently of its rational
recursion; it supplies numerical evidence, not a certified error bound.
"""

import argparse
from functools import lru_cache
import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity


R, tau, radial_square = s.symbols('R tau radial_square', positive=True)
p = s.Rational(5, 2)


def terms(f):
    """Coefficients of z^m/R^k after R=1+r^2+z^2; special rational class."""
    f = s.cancel(f.subs(r*r, R-1-z*z))
    out = []
    for term in s.Add.make_args(s.expand(f)):
        powers = term.as_powers_dict()
        m, k = powers.get(z, 0), -powers.get(R, 0)
        c = term/(z**m*R**(-k))
        require(c.is_Rational and m >= 0 and k > 0, 'rational moment domain')
        out.append((c, int(m), int(k)))
    return out


@lru_cache(None)
def inverse_radial(k):
    if k == 3:
        return 1/(4*tau*(tau*tau+radial_square)**2)
    require(k > 3, 'inverse radial recursion stays above its base exponent')
    return s.factor(-s.diff(inverse_radial(k-1), tau)/(2*(k-1)*tau))


def axial_derivative(f):
    return s.diff(f, z)+2*z*s.diff(f, radial_square)


@lru_cache(None)
def inverse_monomial(m, k):
    if m == 0:
        return inverse_radial(k)
    lower = (m-1)*inverse_monomial(m-2, k-1) if m >= 2 else 0
    return s.factor((lower-axial_derivative(inverse_monomial(m-1, k-1)))
                    /(2*(k-1)))


def inverse_half(f):
    value = sum(c*inverse_monomial(m, k) for c, m, k in terms(f))
    return s.factor(value.subs(tau, 1).subs(radial_square, r*r+z*z))


def inverse_horizontal_coefficient(f):
    """L(y_i f) / y_i for a horizontal Cartesian coordinate, not L(f)."""
    value = sum(-c*s.diff(inverse_monomial(m, k-1), radial_square)/(k-1)
                for c, m, k in terms(f))
    return s.factor(value.subs(tau, 1).subs(radial_square, r*r+z*z))


def moment(m, k):
    """Integral over R5 of |z|^m (1+r^2+z^2)^(-k)."""
    m, k = s.Rational(m), s.Rational(k)
    require(m > -1 and k > (m+5)/2, 'absolute convergence of beta moment')
    return s.pi**2*s.gamma((m+1)/2)*s.gamma(k-(m+5)/2)/s.gamma(k)


def weighted_moment(f, exponent):
    # Here a=6z/(1+r^2+z^2)^4, including its sign.
    value = 6**exponent*sum(c*moment(m+exponent, k+4*exponent)
                           for c, m, k in terms(f) if m % 2 == 0)
    return s.simplify(s.expand_func(value))


def weight_difference_identity():
    chi, a, h, w = [s.Function(n)(r, z) for n in ('chi', 'a', 'h', 'w')]
    v = velocity(chi)
    q = 2*s.diff(chi, z)
    div5 = lambda f: s.diff(f[0], r)+3*f[0]/r+s.diff(f[1], z)
    zero(div5(v*chi), 'canonical velocity preserves its kinetic potential')
    local = w*chi*v.dot(grad(h))-w*a*v.dot(grad(a))+q*w*a*a/2
    residual = (a*a/2-h*chi)*v.dot(grad(w))
    flux = v*(w*chi*h-w*a*a/2)
    zero(local-residual-div5(flux), 'complete local weighted transport flux')
    chiz, chir = s.diff(chi, z), s.diff(chi, r)
    stress = s.Matrix([-2*chiz*chir, chir*chir-chiz*chiz])
    zero(div5(stress)+2*chiz*lap5(chi), 'canonical stress retains the divergence correction q h')
    X, dX, pp = s.symbols('X dX pp', positive=True)
    ww = X**((pp-2)/2)
    diff = pp*(pp-2)*X**((pp-4)/2)*dX*dX/4
    zero(diff-pp/(pp-2)*X**((4-pp)/2)*(s.diff(ww, X)*dX)**2,
         'diffusion pays the weighted gradient, not the unweighted one')
    bb, aa, db, da, weight = s.symbols('b a db da weight', real=True)
    XX = bb*bb+aa*aa
    inner = bb*db+aa*da
    dwb = weight*(db+(pp-2)*bb*inner/XX)
    dwa = weight*(da+(pp-2)*aa*inner/XX)
    full_diff = pp*weight*(db*db+da*da+(pp-2)*inner*inner/XX)
    zero((pp-1)*full_diff/pp-(dwb*dwb+dwa*dwa)/weight
         -(pp-2)*weight*(bb*da-aa*db)**2/XX,
         'full observer gradients are paid by diffusion with an exact orientation remainder')
    zero(p*(p-1)/2-s.Rational(15, 8), 'complete flux Young coefficient')
    return {
        'identity': 'T_w=<[L,w]a,v_a.grad h>+integral (a^2/2-h chi_a) v_a.grad w',
        'meaning': 'use chi_a=L a, h=Lambda a and canonical v_a before integration',
        'diffusion': 'D_p second term = p/(p-2) integral X^((4-p)/2)|grad w|^2',
        'critical_weight': 'p=5/2: coefficient 5 X^(3/4); X=b^2+a^2',
        'regular_observer': 'integral (|grad(wb)|^2+|grad(wa)|^2)/w <= (3/5)D_(5/2)',
        'remainder': '(p-1)D_p/p - observer_gradient_cost = (p-2)integral (w/X)|b grad a-a grad b|^2 >=0',
        'flux': 'T=e_z |grad chi|^2-2chi_z grad chi; J_b=-v b; J_a=e_z L(b^2)-L(v h+T)',
        'signed_pairing': 'Q_self=-p integral [grad(wb).J_b+grad(wa).J_a]',
        'finite_bound': '|Q_self|<=nu D_p/2+(15/(8nu)) integral w(|J_b|^2+|J_a|^2)',
        'unpaid': 'the time integral of this critical flux cost is not bounded from initial data here',
    }


def rational_parent():
    base = (tau*tau+r*r+z*z)**(-2)
    zero(s.diff(base, tau, 2)+lap5(base), 'decaying six-dimensional harmonic extension')
    zero(-s.diff(base, tau)-4*tau/(tau*tau+r*r+z*z)**3,
         'Poisson semigroup normal derivative giving Lambda')
    chi = z/(1+r*r+z*z)**3
    h = s.factor(-lap5(chi))
    v = velocity(chi)
    a = inverse_half(h)
    zero(a-6*z/(1+r*r+z*z)**4, 'canonical fractional parent from the actual curl')
    q = 2*s.diff(chi, z)
    adv = s.factor(v.dot(grad(h)))
    Ladv = inverse_half(adv)
    chiz, chir = s.diff(chi, z), s.diff(chi, r)
    fr = s.factor((v[0]*h-2*chiz*chir)/r)
    fz = s.factor(v[1]*h+chir*chir-chiz*chiz)
    Jr = -r*inverse_horizontal_coefficient(fr)
    Jz = -inverse_half(fz)
    zero(s.diff(Jr, r)+3*Jr/r+s.diff(Jz, z)+Ladv,
         'componentwise Cartesian potential gives the exact parent flux divergence')
    C = Ladv-v.dot(grad(a))
    Q = -p*weighted_moment(a*Ladv, p-2)
    D = p*(p-1)*weighted_moment(grad(a).dot(grad(a)), p-2)
    initial = weighted_moment(a*a, p-2)
    qPhi = weighted_moment(q*a*a, p-2)
    Tw = weighted_moment(a*C, p-2)+qPhi/2
    zero(Q-(p-2)*qPhi/2+p*Tw, 'joint signed defect agrees with literal nonlinear derivative')
    zero(weighted_moment(a*Ladv, s.Integer(0)), 'exact quadratic kinetic cancellation')
    expected_Q = s.Rational(130880331, 1446867107840)*s.sqrt(3)*s.pi**3
    expected_D = s.Rational(3928275, 11534336)*s.sqrt(3)*s.pi**3
    zero(Q-expected_Q, 'exact strictly positive critical production')
    zero(D-expected_D, 'complete positive critical diffusion')
    ratio = s.Rational(855427, 3220672000)
    zero(Q/D-ratio, 'dimensionless production to diffusion ratio')
    Qflux = -p*(p-1)*weighted_moment(s.diff(a, r)*Jr+s.diff(a, z)*Jz, p-2)
    zero(Qflux-Q, 'regular-observer flux reproduces complete signed production')
    flux_cost = weighted_moment(Jr*Jr+Jz*Jz, p-2)
    zero(flux_cost-s.Rational(7147841286819, 37039797960704000)*s.sqrt(3)*s.pi**3,
         'finite complete flux cost on the positive-production fixture')
    require(Q*Q <= p*(p-1)*D*flux_cost, 'complete observer-gradient Cauchy bound')
    zero(4000*ratio-1-s.Rational(50259, 805168), 'strict viscous growth at amplitude 4000 nu')
    require(Q > 0 and D > 0 and Tw > 0, 'net positive production with favorable transport correction')
    return {
        'chi': str(chi), 'h': str(h), 'a': str(a),
        'L_adv_terms': [[str(c), m, k] for c, m, k in terms(Ladv)],
        'Q': str(Q), 'D': str(D), 'R_initial': str(initial),
        'strain_piece': str(s.simplify(qPhi/4)),
        'transport_piece': str(s.simplify(-p*Tw)),
        'Q_over_D': str(ratio),
        'finite_flux_cost': str(flux_cost),
        'amplitude': 'Q(A)=A^(7/2)Q, D(A)=A^(5/2)D; A=4000 nu gives R_p_prime(0)>0',
        'scope': 'actual smooth unforced no-swirl initial datum; interval follows analytically from local well-posedness',
        'refuted': 'universal direct critical absorption Q_self<=nu D_p/2 after prepared payments vanish',
        'not_refuted': 'a nonzero full-datum integrated allowance or global regularity',
    }, (a, adv, Ladv, q)


def nodal_young_obstruction():
    y = s.symbols('y', nonnegative=True)
    chi = (1+y)**(-2)-s.Rational(125, 16)*(4+y)**(-2)
    a = 4/(1+y)**3-s.Rational(125, 2)/(4+y)**3
    h = -4*y*s.diff(chi, y, 2)-10*s.diff(chi, y)
    values = {'a': a.subs(y, 1), 'a_y': s.diff(a, y).subs(y, 1),
              'chi': chi.subs(y, 1), 'h': h.subs(y, 1)}
    expected = {'a': 0, 'a_y': -s.Rational(9, 20),
                'chi': -s.Rational(1, 16), 'h': s.Rational(1, 20)}
    for name in values:
        zero(values[name]-expected[name], 'exact nodal value '+name)
    zero((a*a/2-h*chi).subs(y, 1)-s.Rational(1, 320), 'flux numerator stays nonzero on the node')
    zero(4*values['chi']*s.Rational(1, 2)+s.Rational(1, 8),
         'canonical drift crosses the nodal sphere at z=1/2')
    zero(s.Rational(1, 320)*4*values['chi']*s.Rational(1, 2)/2+s.Rational(1, 5120),
         'the flux normal component is nonzero on the nodal patch')
    aa, delta = s.symbols('a delta', positive=True)
    XX = aa*aa+delta*delta
    ww = XX**((p-2)/2)
    full_hessian = p*ww+p*(p-2)*aa*aa*XX**((p-4)/2)
    optimal_ratio = aa*aa/(10*XX**s.Rational(3, 4)*(delta*delta+s.Rational(3, 2)*aa*aa))
    zero(s.diff(ww, aa)**2/full_hessian-optimal_ratio,
         'the complete regularized diffusion still gives the nodal Young singularity')
    zero(optimal_ratio.subs(aa, delta)*delta**s.Rational(3, 2)
         -1/(25*2**s.Rational(3, 4)), 'full-diffusion Young cost at distance comparable to delta')
    zero(4-p-s.Rational(3, 2), 'Young cost has a nonintegrable normal singularity')
    zero(p-3+s.Rational(1, 2), 'regularized Young cost diverges as delta^(-1/2)')
    return {
        'chi': str(chi), 'a': str(a), 'h': str(s.factor(h)),
        'values_at_r2_plus_z2_1': {k: str(v) for k, v in values.items()},
        'cost': 'integral |(a^2/2-h chi)v|^2/X^(3/4), X=a^2, is infinite near a transverse nodal patch',
        'actual_gradient_term': 'locally integrable as |normal_distance|^(-1/2)',
        'actual_diffusion': 'locally integrable as |normal_distance|^(1/2)',
        'actual_production': 'Q_self=0 initially by axial reflection; full unforced no-swirl evolution is regular',
        'regularized_cost': 'replacing X by delta^2+a^2 gives a lower bound c delta^(-1/2)',
        'complete_diffusion': 'the optimal local ratio is a^2/[10(delta^2+a^2)^(3/4)(delta^2+3a^2/2)]; the strip delta<=|a|<=2delta has the same divergence',
        'small_swirl': 'adding b0=epsilon exp(-r^2-z^2) gives the same divergent auxiliary cost as epsilon->0',
        'scope': 'refutes separate Young absorption with a finite auxiliary cost, not combined signed payment',
    }


def quadrature(fields):
    import numpy as np
    from scipy.special import roots_jacobi, roots_legendre
    a, adv, Ladv, q = fields
    af, adf, laf = [s.lambdify((r, z), f, 'numpy') for f in (a, adv, Ladv)]
    grad2f = s.lambdify((r, z), grad(a).dot(grad(a)), 'numpy')
    rows = []
    for n in (48, 96, 192):
        xx, ww = roots_legendre(n)
        theta, wt = (xx+1)*np.pi/4, ww*np.pi/4
        rho = np.tan(theta)[:, None]
        radial_weight = (wt/np.cos(theta)**2)[:, None]
        ss, ws = roots_jacobi(n, 0, .5)
        cc = ((ss+1)/2)[None, :]
        angular_weight = (ws/2**1.5)[None, :]*(1-cc**2)
        rr, zz = rho*np.sqrt(1-cc**2), rho*cc
        aa = af(rr, zz)
        volume = 4*np.pi**2*rho**4*radial_weight*angular_weight/np.sqrt(cc)
        Q = np.sum(volume*(-2.5)*aa**1.5*laf(rr, zz))
        D = np.sum(volume*3.75*np.sqrt(aa)*grad2f(rr, zz))
        # Independent Riesz integral on the axis: zeta=z0+r*tan(phi).
        phi, wp = xx*np.pi/2, ww*np.pi/2
        z0 = .4
        rz = z0+rho*np.tan(phi)[None, :]
        pot = np.sum(radial_weight*(wp*np.cos(phi)**2)[None, :]*adf(rho, rz))/np.pi
        exact_pot = laf(0., z0)
        rows.append({'n': n, 'Q': float(Q), 'D': float(D),
                     'axis_Riesz': float(pot), 'axis_rational': float(exact_pot),
                     'axis_abs_error': float(abs(pot-exact_pot))})
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quadrature', action='store_true')
    args = parser.parse_args()
    production, fields = rational_parent()
    output = {'weight_identity': weight_difference_identity(),
              'critical_production': production, 'young_obstruction': nodal_young_obstruction()}
    if args.quadrature:
        output['quadrature'] = quadrature(fields)
    print(json.dumps(output, indent=2))
