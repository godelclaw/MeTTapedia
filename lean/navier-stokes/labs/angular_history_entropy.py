#!/usr/bin/env python3
"""Angular contrast, actual viscous growth, and a heat-compatible entropy.

Exact checks retain the radial weight contribution to angular contrast,
give a smooth-cutoff sign certificate, and derive the literal fluid defect
of a fixed-reference perspective entropy. The PDE interval argument,
integrated entropy estimates and continuation implication are analytic.
The full signed history allowance remains open.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity
from generated_parent_return import sphere_mean


def contrast_rate():
    alpha, beta, nu = s.symbols('alpha beta nu', positive=True)
    p, exponent = s.Rational(5, 2), s.Rational(1, 2)
    radius = r*r+z*z
    H2 = z*z-radius/5
    B = s.exp(-alpha*radius)
    h = H2*s.exp(-beta*radius)
    zero(lap5(B)-(4*alpha**2*radius-10*alpha)*B,
         'complete radial heat derivative')
    zero(lap5(h)-(4*beta**2*radius-18*beta)*h,
         'complete degree-two heat derivative')
    mean_radius = s.Rational(9, 2)/(exponent*alpha+2*beta)
    rate = s.factor((4*exponent*alpha**2+8*beta**2)*mean_radius
                    -10*exponent*alpha-36*beta)
    zero(rate-(13*alpha**2-56*alpha*beta-72*beta**2)/(alpha+4*beta),
         'radial heat weight and angular damping both remain')
    zero(rate.subs({alpha: 6, beta: 1})-6, 'strictly positive full contrast rate')
    zero(p*(p-1)/2-p/2-s.Rational(5, 8),
         'subtracting the angular second-moment baseline gives the right Hessian')
    ss = next(iter((sphere_mean(z*z)).free_symbols))
    zero(sphere_mean((z*z-ss/5)**2)-s.Rational(8, 175)*ss**2,
         'degree-two angular variance')
    I = s.Rational(2, 5)*s.pi**s.Rational(5, 2)/5**s.Rational(9, 2)
    sphere = 8*s.pi**2/3
    zero(I-sphere/2*s.Rational(8, 175)*s.gamma(s.Rational(9, 2))/5**s.Rational(9, 2),
         'exact uncut Gaussian norm')
    return {'contrast': 'A_p(b)=integral_R5[|b|^p-(mean_S4 b^2)^(p/2)]>=0, p=5/2',
            'family': 'b=B+epsilon h, B=exp(-alpha |y|^2), h=(z^2-|y|^2/5)exp(-beta |y|^2)',
            'epsilon2_coefficient': '(5/8) integral B^(1/2) h^2',
            'normalized_heat_rate': str(rate),
            'at_alpha6_beta1': '6nu>0; angular damping alone does not control the contrast',
            'uncut_norm': str(I),
            'actualization': 'use the compact radial cutoff certified below, then sufficiently small nonzero epsilon; actual pure-swirl NS has b_t(0)=nu Delta5 b0'}


def cutoff_certificate():
    # A smooth radial cutoff is one on rho<=3, zero on rho>=6, in [0,1],
    # with |d_rho cutoff|<=2/3. Only this derivative is used after IBP.
    a, b, rho = s.symbols('a b rho', nonnegative=True)
    raw = 2*((a+2*b)**2+a*a)+24*rho*b*(2*a+2*b)+72*rho*rho*b*b
    bound = 32*a*a+(36+120*rho*rho)*b*b
    zero(bound-raw-4*(a-b)**2-24*(a-rho*b)**2-24*b*b*(rho-1)**2,
         'cutoff error uses only nonnegative square bounds')
    x = s.symbols('x', positive=True)
    poly = 2048*x+4672*x*x+3968*x**3
    zero(32*s.Rational(64, 25)*x*(1+x)**2
         +(36+120*x)*s.Rational(16, 25)*x*x-poly/25,
         'explicit Gaussian tail polynomial')
    tail = sum(c*s.factorial(n)/s.Integer(5)**(n+1)*sum(
        s.Integer(45)**k/s.factorial(k) for k in range(n+1))
               for n, c in [(3, 2048), (4, 4672), (5, 3968)])/50
    zero(tail-s.Rational(3724756896, 3125), 'exact tail coefficient multiplying exp(-45)')
    rational_bound = tail/s.Integer(2)**45
    main_lower = s.Rational(9, 31250)
    require(rational_bound < main_lower/2,
            'cutoff error is strictly below half the positive uncut rate')
    return {'cutoff': 'chi(rho)=1 for rho<=3, 0 for rho>=6, 0<=chi<=1, |chi_prime|<=2/3; choose smooth',
            'rate_formula': 'J(h)=integral exp(-3|y|^2)[-2|grad h|^2+24h y.grad h+36|y|^2 h^2]',
            'uncut_rate': 'J(h)=6I; J(h)/|S4|>9/31250',
            'cutoff_error_over_sphere': str(rational_bound),
            'sign_certificate': 'J(chi h)>|S4|*9/62500>0',
            'positive_data': 'for each such fixed cutoff, B+epsilon chi h>0 for all sufficiently small |epsilon|',
            'actual_rate': 'A_p_prime(0)=(5nu/8)epsilon^2 J(chi h)+o(epsilon^2)>0',
            'scope': 'actual smooth positive-viscosity unforced local flows; no future or blowup claim'}


def radial_kick_payment():
    f, g, fp, gp = s.symbols('f g fp gp', real=True)
    A = 12*g*fp-16*gp*f
    zero(288*g*g*fp*fp+512*gp*gp*f*f-A*A-(12*g*fp+16*gp*f)**2,
         'full angular kick has a two-term square bound')
    p = s.Rational(5, 2)
    sphere = 8*s.pi**2/3
    zero((p/2)*(p/2-1)/8*(4*sphere/175)-s.pi**2/420,
         'critical contrast starts at the fourth time order')
    zero(s.pi**2/420*288*2/sphere-s.Rational(18, 35),
         'first angular payment uses initial critical diffusion')
    zero(s.pi**2/420*512*105/(64*s.pi**2*13)-s.Rational(2, 13),
         'second angular payment uses the depleted parent return')
    return {'leading_contrast': 'A_p(b(t))=L_ang t^4+o(t^4), for smooth rapidly decaying radial seeds, by the C2 contrast and actual Lp time jets',
            'L_ang': '(pi^2/420) integral_0^infinity s^(7/2) f^(-3/4)(12g f_prime-16g_prime f)^2 ds',
            'bound': 'L_ang <=(18/35)G Dcrit0+(2/13)||f||_infinity^(1/4)(-C_return)',
            'G': 'sup_(s>=0) s g(s)^2, finite from the original smooth radial source',
            'Dcrit0': 'integral_R5 |b0|^(1/2)|grad b0|^2',
            'scope': 'a leading source-kick estimate; no bound for its repeated regeneration'}


def perspective_identity():
    # Cartesian chain rule; a general drift is allowed until its actual
    # lifted divergence -q is imposed in the final integral identity.
    p, nu = s.symbols('p nu', positive=True)
    bb, ww = s.symbols('bb ww', positive=True)
    e = bb**p*ww**(1-p)
    b1, w1 = s.symbols('b1 w1', real=True)
    quadratic = (s.diff(e, bb, 2)*b1*b1+2*s.diff(e, bb, ww)*b1*w1
                 +s.diff(e, ww, 2)*w1*w1)
    diffusion = p*(p-1)*ww*(bb/ww)**(p-2)*(b1/ww-bb*w1/ww**2)**2
    zero(s.powsimp(quadratic-diffusion, force=True),
         'the full perspective diffusion is one nonnegative square')
    q, advlog = s.symbols('q advlog', real=True)
    rate = s.diff(e, bb)*(q*bb)+s.diff(e, ww)*(ww*advlog)-q*e
    zero(rate-(p-1)*(q-advlog)*e,
         'actual drift divergence and fixed-reference transport both retained')
    chi = s.Function('chi')(r, z)
    v, qfield = velocity(chi), 2*s.diff(chi, z)
    scalar = s.Function('bfield')(r, z)
    div5 = lambda a: s.diff(a[0], r)+3*a[0]/r+s.diff(a[1], z)
    zero(nu*lap5(scalar)-v.dot(grad(scalar))+qfield*scalar
         -nu*lap5(scalar)+div5(v*scalar),
         'the actual lifted swirl equation is conservative')
    return {'reference': 'W=(1-exp(-r^2/(ell^2+4nu t)))/r^2, ell>0 fixed at the original time',
            'entropy': 'E=integral W|b/W|^(5/2)>=0',
            'diffusion': 'D_W=integral W|b/W|^(1/2)|grad(b/W)|^2>=0',
            'balance': 'E_prime+(15nu/4)D_W=(3/2)integral theta q W|b/W|^(5/2); theta=x/(exp(x)-1), x=r^2/(ell^2+4nu t)',
            'heat': 'when only the literal heat contribution is taken, E_prime=-(15nu/4)D_W',
            'physical_density': 'b_t+div5(v b)=nu Delta5 b; this is a lifted scalar law, not compressibility of the physical R3 fluid',
            'unpaid': 'the full signed actual drift/strain history; no independent auxiliary force or bound on future target derivatives'}


def physical_volume_reference():
    t, ell, nu = s.symbols('t ell nu', positive=True)
    d = ell*ell+4*nu*t
    x = s.symbols('x', positive=True)
    W = (1-s.exp(-r*r/d))/(r*r)
    theta = (r*r/d)/(s.exp(r*r/d)-1)
    zero(s.diff(W, t)-nu*lap5(W), 'the complete transverse reference solves heat')
    zero(1+r*s.diff(W, r)/(2*W)-theta,
         'physical lifted volume cancels transport against strain exactly')
    zero(s.limit(W, r, 0)-1/d, 'smooth finite reference on the axis')
    zero(s.limit(theta, r, 0)-1, 'all near-axis strain remains at the axis')
    zero(s.diff((1-x)*s.exp(x), x)+x*s.exp(x),
         'elementary monotonicity giving one-minus-theta at most x')
    zero(s.diff(s.exp(-x), x)+s.exp(-x), 'Laplace integral for the explicit reference')
    chi = s.Function('chi')(r, z)
    v, q = velocity(chi), 2*s.diff(chi, z)
    zero(q-v.dot(grad(W))/W-theta*q,
         'cancellation holds for the full actual meridional field, including every parent')
    return {'reference': 'W(t,r)=(1-exp(-r^2/d))/r^2, d=ell^2+4nu t; W(t,0)=1/d',
            'stochastic_mean': 'W is the four-transverse-dimensional heat average of r^(-2) at time t+ell^2/(4nu)',
            'theta': 'theta=x/(exp(x)-1), x=r^2/d, theta(0)=1; 0<theta<=1',
            'coercive_bounds': 'W<=ell^(-2); |grad log W|<=2/ell; W^(-1)<=r^2+d',
            'physical_entropy': 'E=pi integral_R3 |Gamma|^(5/2)/(1-exp(-r^2/d))^(3/2), Gamma=r u_theta',
            'initial_stock': 'E0<=sqrt(2)[pi ||Gamma0||_(5/2)^(5/2)+ell^3 M0]',
            'meaning': 'the singular physical-volume weight is smoothed from the original clock; no new fluid force, time reset, or unknown reference concentration'}


def far_payment():
    rho, R = s.symbols('rho R', positive=True)
    zero(s.integrate(rho**(-6), (rho, R, s.oo))-1/(5*R**5),
         'far derivative kernel L2 norm')
    zero(4+2*s.Rational(3, 2)-7, 'every cutoff derivative remains in the bound')
    return {'kernel': 'K_R=theta_cut(|y|/R)/(2pi^3 |y|^4); theta_cut=0 below1,1 above2, |theta_cut_prime|<=3/2',
            'constant': 'd_R=(7/(2pi^3))sqrt(|S4|/(5R^5))',
            'complete_far': '|q_a,far|<=2 d_R sqrt(pi Ebar); q_a,far=2partial_z(K_R*a)',
            'kinetic_stock': 'Ebar=E_swirl0 exp(2 integral_0^H ||grad V||_infinity), from the actual no-swirl reference',
            'clock': 'kappa_far=3 d_R sqrt(pi Ebar)',
            'scope': 'fixed original cutoff; exact far derivative includes the cutoff derivative; remaining near cost unbounded'}


def consumer():
    nu, C5, H, stock, ell = s.symbols('nu C5 H stock ell', positive=True)
    p = s.Rational(5, 2)
    zero(p*(p-1)-s.Rational(15, 4), 'full relative diffusion coefficient')
    zero(2*(2/(p*(p-1)*nu))-s.Rational(16, 15)/nu,
         'half-diffusion history payment retains the correct physical gradient budget')
    zero(3*s.Rational(7, 5)+3-s.Rational(36, 5), 'reference scale in the critical consumer')
    result = s.Rational(25, 16)*C5*ell**(-s.Rational(36, 5))*(s.Rational(16, 15)/nu+8*H/ell**2)*stock**s.Rational(12, 5)
    return {'coercivity': 'M<=ell^(-3)E; Dcrit<=2ell^(-3)[D_W+4E/ell^2]',
            'conditional_payment': 'if integral P <=(15nu/8)integral D_W+K on every available prefix, E+(15nu/8)integral D_W<=E0+K',
            'critical_clock_bound': str(result),
            'stock': 'stock=E0+K; S=integral_R5 |b|^3; result bounds integral_0^T S^2',
            'actual_noswirl_reference': 'split q=q_a+q_bar; kappa_ref=(3/2)||q_bar||_infinity has finite reference integral',
            'weighted_open_target': 'integral Omega[P_near-(15nu/8)D_W]<=K; P_near=(3/2)integral theta q_a,near W|b/W|^(5/2)',
            'weighted_consumer': 'Omega=exp(-integral kappa_ref-kappa_far t); multiply the displayed critical clock bound by exp((12/5)(integral_0^H kappa_ref+kappa_far H))',
            'scope': 'analytic alternative continuation consumer; its arbitrary-history payment is OPEN; previous joint-parent target is retained'}


if __name__ == '__main__':
    print(json.dumps({'contrast': contrast_rate(), 'cutoff': cutoff_certificate(),
                      'first_kick': radial_kick_payment(), 'perspective': perspective_identity(),
                      'physical_reference': physical_volume_reference(),
                      'far_payment': far_payment(), 'consumer': consumer()}, indent=2))
