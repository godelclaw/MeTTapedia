#!/usr/bin/env python3
"""Exact initial parent generation from smooth, whole-space pure swirl.

The heat-resolvent calculation retains the actual nonlocal meridional
acceleration. It gives positive stretching production with no initial
meridional parent. The positive-viscosity interval argument uses uniform
local Sobolev estimates and is analytic, not certified by this checker.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, gaussian_coefficient


def weighted_evolution():
    f = s.Function('chi')(r, z)
    b = s.Function('b')(r, z)
    nu = s.symbols('nu', nonnegative=True)
    v = s.Matrix([-r*s.diff(f, z), 2*f+r*s.diff(f, r)])
    a = v[0]/r
    b_rate = nu*lap5(b)-v.dot(grad(b))-2*a*b
    source = s.diff(b*b, z)
    source_rate = s.diff(2*b*b_rate, z)
    source_defect = (-v.diff(z).dot(grad(b*b))-4*a*source
                     -4*s.diff(a, z)*b*b-2*nu*s.diff(grad(b).dot(grad(b)), z))
    zero(source_rate+v.dot(grad(source))-nu*lap5(source)-source_defect,
         'the internally generated source retains parent feedback and diffusion')
    I = r**3*s.diff(f, r)
    radial_lap = s.diff(I, r, 2)-3*s.diff(I, r)/r+s.diff(I, z, 2)
    zero(r**3*s.diff(lap5(f), r)-radial_lap,
         'actual viscosity for the geometric parent quantity')
    zero(radial_lap+lap5(I)-2*(s.diff(I, r, 2)+s.diff(I, z, 2)),
         'the weight uses the positive adjoint diffusion')
    y, ell = s.symbols('y ell', positive=True)
    psi = y*y/(ell*ell+y*y)
    zero(s.diff(psi, y)-2*y*ell**2/(ell**2+y**2)**2,
         'first derivative of bounded weight')
    zero(s.diff(psi, y, 2)-2*ell**2*(ell**2-3*y**2)/(ell**2+y**2)**3,
         'second derivative of bounded weight, including its changing sign')
    return {'I_t': 'nu*(I_rr-3*I_r/r+I_zz) + r^3*d_r*(-L5)^-1*N_eta',
            'N_eta': '-v.grad(eta)+d_z(b^2)',
            'source_equation': '(d_t+v.grad-nu*L5)S=-(d_z v).grad(b^2)-4*a*S-4*a_z*b^2-2*nu*d_z(|grad(b)|^2)',
            'A_weight': '-alpha*psi(I)+alpha*(H-t)*(psi_prime(I)*(I_t+v.grad(I)+nu*L5(I))+nu*psi_second(I)*|grad(I)|^2)',
            'scope': 'the elliptic normalization is the decaying whole-space inverse'}


def moment(expr, qr, qz, radial_power):
    """Exact physical integral of a polynomial times a separated Gaussian."""
    polynomial = s.Poly(s.expand(s.simplify(expr*s.exp(qr*r*r+qz*z*z))), r, z)
    result = 0
    for (i, j), co in polynomial.terms():
        if j % 2:
            continue
        radial = s.gamma(s.Rational(i+radial_power+1, 2))/(2*qr**s.Rational(i+radial_power+1, 2))
        axial = s.gamma(s.Rational(j+1, 2))/qz**s.Rational(j+1, 2)
        result += co*radial*axial
    return s.factor(2*s.pi*result)


def generated_stretching():
    h = s.symbols('h', nonnegative=True)
    A, C = s.symbols('A C', positive=True)
    b = s.exp(-r*r-2*z*z)
    source = s.diff(b*b, z)
    heat = -8*z*A**-2*C**s.Rational(-3, 2)*s.exp(-2*r*r/A-4*z*z/C)
    heat_time = heat.subs({A: 1+8*h, C: 1+16*h})
    zero(s.diff(heat_time, h)-lap5(heat_time), 'full five-dimensional heat equation')
    zero(heat_time.subs(h, 0)-source, 'heat source at zero time')
    zero(r**3*s.diff(heat, r)-32*r**4*z*A**-3*C**s.Rational(-3, 2)
         *s.exp(-2*r*r/A-4*z*z/C), 'generated I has positive sign when z is positive')
    # chi_1 = integral_0^infinity heat_h(source) dh. Decay of this
    # kernel identifies (-L5) chi_1 = source; no independent force is added.
    v = s.Matrix([-r*s.diff(heat, z), 2*heat+r*s.diff(heat, r)])
    a = v[0]/r
    B = v.jacobian((r, z))
    gb = grad(b)
    H = -gb.dot((B+a*s.eye(2))*gb)
    qr, qz = 2+2/A, 4+4/C
    from_joint = moment(H, qr, qz, 3)

    # Independently differentiate literal omega^T grad(u) omega at
    # the pure-swirl datum. The kernel supplies the meridional acceleration.
    omega = s.Matrix([-r*s.diff(b, z), 0, 2*b+r*s.diff(b, r)])
    omega_rate = s.Matrix([0, -r*lap5(heat), 0])
    B0 = s.Matrix([[0, -b, 0], [b+r*s.diff(b, r), 0, r*s.diff(b, z)], [0, 0, 0]])
    B1 = s.Matrix([[B[0, 0], 0, B[0, 1]], [0, a, 0], [B[1, 0], 0, B[1, 1]]])
    zero(omega.dot(B0*omega), 'initial pure-swirl stretching vanishes pointwise')
    literal = omega_rate.dot(B0*omega)+omega.dot(B1*omega)+omega.dot(B0*omega_rate)
    from_curl = moment(literal, qr, qz, 1)
    zero(from_joint-from_curl, 'complete literal physical stretching derivative')
    expected = -2*s.pi**s.Rational(3, 2)*(3*A*C-6*A-C-10)/((A+1)**3*(C+1)**s.Rational(5, 2))
    zero(from_joint-expected, 'exact heat-resolvent pairing')

    integrand = expected.subs({A: 1+8*h, C: 1+16*h})
    y = s.symbols('y', positive=True)
    rational = -(6*y**4-11*y**2-9)/(16*y**4*(y*y+1)**3)
    zero(integrand.subs(h, (y*y-1)/8)*y/4
         -s.sqrt(2)*s.pi**s.Rational(3, 2)*rational,
         'change of variable in the exact resolvent integral')
    primitive = (33*s.atan(y)/32
        -(-33*y**6-55*y**4-20*y**2+6)/(32*y**7+64*y**5+32*y**3))
    zero(s.diff(primitive, y)-rational, 'rational integration certificate')
    integral = s.simplify(s.limit(primitive, y, s.oo)-primitive.subs(y, 1))
    zero(integral-3*(11*s.pi-34)/128, 'exact resolvent endpoint values')
    G1 = s.sqrt(2)*s.pi**s.Rational(3, 2)*integral

    # E,Z,D,L are respectively ||u||^2, ||omega||^2,
    # ||grad omega||^2 and ||Delta omega||^2. Divide by pi^(3/2).
    E = gaussian_coefficient(b*b, 2)
    Z = gaussian_coefficient(gb.dot(gb), 2)
    D = gaussian_coefficient(lap5(b)**2, 2)
    L = gaussian_coefficient(grad(lap5(b)).dot(grad(lap5(b))), 2)
    for got, want in zip((E, Z, D, L), (s.Rational(1, 8), s.Rational(3, 4), s.Rational(13, 2), 75)):
        zero(got-want, 'exact initial physical norm')
    lb = lap5(b)
    viscous_curl = s.Matrix([-r*s.diff(lb, z), 0, 2*lb+r*s.diff(lb, r)])
    viscous_gradient = s.Matrix([[0, -lb, 0], [lb+r*s.diff(lb, r), 0, r*s.diff(lb, z)], [0, 0, 0]])
    zero(viscous_curl.dot(B0*omega)+omega.dot(viscous_gradient*omega)
         +omega.dot(B0*viscous_curl), 'viscosity contributes zero to initial stretching production')
    def dissipation_pair(q):
        return (omega.diff(r).dot(q.diff(r))+omega.diff(z).dot(q.diff(z))
                +(omega[0]*q[0]+omega[1]*q[1])/r**2)
    zero(dissipation_pair(omega_rate), 'new meridional curl is orthogonal in dissipation')
    zero(moment(dissipation_pair(viscous_curl), 2, 4, 1)
         +s.pi**s.Rational(3, 2)*L, 'full initial viscous dissipation derivative')
    # Using the elementary bounds pi > 157/50 and sqrt(2) > 7/5.
    lower = 3*s.Rational(7, 5)*(11*s.Rational(157, 50)-34)/128
    zero(lower-s.Rational(567, 32000), 'rational lower bound for G1/pi^(3/2)')
    c = 1000
    require(c*c*lower-2*c*D > 0, 'strict leading enstrophy growth at t=c*nu')
    require(c*c*lower-c*D > 0, 'strict leading signed renewal excess at t=c*nu')
    return {'initial_datum': 'u=(-y*b,x*b,0), b=exp[-(x^2+y^2)-2*z^2]',
            'G_initial': 0, 'G_prime_initial': s.simplify(G1),
            'G_prime_independent_of_viscosity': 'viscous initial acceleration remains pure swirl, whose stretching is identically zero',
            'norms_over_pi_power_3_over_2': dict(E=E, Z=Z, D=D, Laplacian_vorticity=L),
            'Z_prime_initial': '-2*nu*D0', 'Z_second_initial': '2*G1+4*nu^2*L0',
            'time': 't=1000*nu',
            'Z_increment_leading_lower_over_pi_power_3_over_2': c*c*lower-2*c*D,
            'renewal_excess_leading_lower_over_pi_power_3_over_2': c*c*lower-c*D,
            'interval_scope': 'uniform local Sobolev estimates supply the O(nu^3) remainder; this PDE argument is analytic, not verified by symbolic integration'}


def main():
    print(json.dumps({'weight_evolution': weighted_evolution(),
                      'pure_swirl': generated_stretching()}, indent=2, default=str))


if __name__ == '__main__':
    main()
