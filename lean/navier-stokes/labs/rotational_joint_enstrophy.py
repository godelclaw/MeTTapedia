#!/usr/bin/env python3
"""Joint physical vorticity payment in the axisymmetric equations.

Exact Green identities cancel the swirl source between both vorticity
channels. Gaussian integrations retain the remaining deformation and check
it against the literal three-dimensional curl, gradient and dissipation.
The finite source-pairing summary does not determine stretching's sign.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero


r = s.symbols('r', positive=True)
z = s.symbols('z', real=True)
coordinates = (r, z)
radius = r*r+2*z*z


def grad(f):
    return s.Matrix([s.diff(f, x) for x in coordinates])


def lap5(f):
    return s.diff(f, r, 2)+3*s.diff(f, r)/r+s.diff(f, z, 2)


def weighted_div(v):
    return s.diff(r**3*v[0], r)+s.diff(r**3*v[1], z)


def velocity(chi):
    return s.Matrix([-r*s.diff(chi,z), 2*chi+r*s.diff(chi,r)])


def local_green_identities():
    chi, b = [s.Function(name)(r,z) for name in ('chi','b')]
    v = velocity(chi)
    a, eta = v[0]/r, -lap5(chi)
    w, gb = r**3, grad(b)
    source = s.diff(b*b,z)
    zero(weighted_div(v)-2*w*a, 'exact weighted transport divergence')
    zero(s.diff(eta,z)-lap5(a), 'elliptic compatibility of the actual parent')
    direct_source_flux = (s.diff(w*eta*b*b,z)-weighted_div(b*b*grad(a)))
    zero(w*eta*source-2*w*b*gb.dot(grad(a))-direct_source_flux,
         'source cancellation uses both gradient and elliptic compatibility')
    weight = s.Function('weight')(r,z)
    weighted_source_flux = (s.diff(w*weight*eta*b*b,z)
                           - weighted_div(weight*b*b*grad(a)))
    correction = b*b*(grad(weight).dot(grad(a))-eta*s.diff(weight,z))
    zero(w*weight*eta*source-2*w*weight*b*gb.dot(grad(a))
         -w*correction-weighted_source_flux,
         'a spatial reserve weight retains its full compatibility defect')
    zero(grad(lap5(b))-s.Matrix([lap5(gb[0]),lap5(gb[1])])
         +s.Matrix([3*gb[0]/r**2,0]), 'full gradient diffusion commutator')
    hessian = gb.jacobian(coordinates)
    bochner = sum(entry**2 for entry in hessian)+3*gb[0]**2/r**2
    zero(lap5(gb.dot(gb))/2-gb.dot(grad(lap5(b)))-bochner,
         'complete nonnegative physical diffusion in the gradient channel')
    source_flux = (s.diff(w*eta*b*b,z)
                   - weighted_div(b*b*grad(a)-a*grad(b*b)))
    zero(w*eta*source+2*w*a*(b*lap5(b)+gb.dot(gb))-source_flux,
         'higher source pairing and reaction cancel with full boundary flux')
    transport_flux = weighted_div(v.dot(gb)*gb-gb.dot(gb)*v/2)
    zero(w*lap5(b)*v.dot(gb)+w*gb.dot(v.jacobian(coordinates)*gb)
         -w*a*gb.dot(gb)-transport_flux,
         'remaining deformation includes the physical weighted transport')
    B = v.jacobian(coordinates)
    S0 = (B+B.T)/2+a*s.eye(2)/2
    zero(s.trace(S0), 'traceless meridional strain')
    deformation = a*eta*eta-gb.dot(B*gb)-a*gb.dot(gb)
    zero(deformation-(a*(eta*eta-gb.dot(gb)/2)-gb.dot(S0*gb)),
         'signed radial and traceless directional splitting')
    omega = s.Matrix([-r*s.diff(b,z), r*eta, 2*b+r*s.diff(b,r)])
    full_gradient = s.Matrix([
        [s.diff(v[0],r), -b, s.diff(v[0],z)],
        [b+r*s.diff(b,r), a, r*s.diff(b,z)],
        [s.diff(v[1],r), 0, s.diff(v[1],z)]])
    curl_flux = (s.diff(2*r*r*b*b*s.diff(v[1],z),r)
                 - s.diff(2*r*r*b*b*s.diff(v[1],r),z))
    zero(r*omega.dot(full_gradient*omega)-w*deformation-curl_flux,
         'universal literal three-dimensional stretching with exact boundary flux')
    flux_field = grad(a)-s.Matrix([0,eta])
    zero(weighted_div(flux_field), 'parent flux field has zero weighted divergence')
    level = r**3*s.diff(chi,r)
    zero(grad(level)-s.Matrix([w*flux_field[1],-w*flux_field[0]]),
         'physical parent streamfunction for the retained flux')
    zero(flux_field.dot(grad(level)), 'parent level is constant along the internal flux')
    alpha = s.symbols('alpha', nonnegative=True)
    zero(flux_field.dot(grad(1+alpha*level**2)),
         'nonnegative geometric weight preserves source compatibility')
    nu = s.symbols('nu', positive=True)
    density = (eta*eta+gb.dot(gb))/2
    eta_rate = nu*lap5(eta)-v.dot(grad(eta))+source
    b_rate = nu*lap5(b)-v.dot(gb)-2*a*b
    density_rate = eta*eta_rate+gb.dot(grad(b_rate))
    complete_diss = grad(eta).dot(grad(eta))+bochner
    zero(w*density_rate+weighted_div(v*density+b*b*flux_field)
         -nu*w*lap5(density)-w*(deformation-nu*complete_diss),
         'full compatible physical density equation with internal flux and viscosity')
    return {'source_cancellation':'C_theta cancels between both vorticity channels',
            'remaining_G':'integral [a*eta^2-grad(b)^T*(grad(v)+a*I)*grad(b)] r^2 dx',
            'weighted_compatibility_defect':'integral b^2*(grad(weight).grad(a)-eta*weight_z) r^2 dx',
            'internal_flux':'b^2*(a_r,a_z-eta); weighted divergence of (a_r,a_z-eta) is zero',
            'compatible_weight':'1+alpha*(r^3*chi_r)^2, alpha>=0, has zero source-weight defect',
            'scope':'exact local identities; interval integration uses stated decay and regularity'}


def gaussian_coefficient(expr, degree, radial_power=3):
    """Integrate r^m expr dr dz, divided by sqrt(pi/(2*degree)).

Every input is a polynomial times exp[-degree*(r^2+2z^2)]. The full
three-dimensional integral additionally has the factor 2*pi. This
routine performs exact Gaussian moments, not numerical quadrature.
"""
    polynomial = s.Poly(s.expand(s.simplify(expr*s.exp(degree*radius))), r,z)
    value = 0
    for (i,j), coefficient in polynomial.terms():
        if j % 2:
            continue
        radial = s.gamma(s.Rational(i+radial_power+1,2))/(2*s.Integer(degree)**s.Rational(i+radial_power+1,2))
        axial = s.gamma(s.Rational(j+1,2))/s.Integer(2*degree)**s.Rational(j+1,2)
        value += coefficient*radial*axial
    return s.simplify(value/s.sqrt(s.pi/(2*s.Integer(degree))))


def gaussian_fixture(chi, name):
    b = s.exp(-radius)
    v = velocity(chi)
    a, eta = s.simplify(v[0]/r), s.simplify(-lap5(chi))
    gb, B, source = grad(b), v.jacobian(coordinates), s.diff(b*b,z)
    T = gaussian_coefficient(chi*source,3)
    C = gaussian_coefficient(eta*source,3)
    Gm = gaussian_coefficient(a*eta*eta,3)
    Gs = gaussian_coefficient(-gb.dot(B*gb)-a*gb.dot(gb),3)
    Zm = gaussian_coefficient(eta*eta,2)
    Zs = gaussian_coefficient(gb.dot(gb),2)
    Dm = gaussian_coefficient(grad(eta).dot(grad(eta)),2)
    Ds = gaussian_coefficient(lap5(b)**2,2)
    Neta = -v.dot(grad(eta))+source
    Nb = -v.dot(gb)-2*a*b
    zero(gaussian_coefficient(eta*Neta,3)-Gm-C, 'complete meridional nonlinear rate')
    zero(gaussian_coefficient(gb.dot(grad(Nb)),3)-Gs+C, 'complete swirl-gradient nonlinear rate')
    zero(gaussian_coefficient(eta*lap5(eta),2)+Dm, 'full meridional diffusion')
    zero(gaussian_coefficient(gb.dot(grad(lap5(b))),2)+Ds, 'full swirl diffusion')
    swirl = r*b
    omega = s.Matrix([-s.diff(swirl,z), r*eta, s.diff(swirl,r)+swirl/r])
    full_gradient = s.Matrix([
        [s.diff(v[0],r), -swirl/r, s.diff(v[0],z)],
        [s.diff(swirl,r), v[0]/r, s.diff(swirl,z)],
        [s.diff(v[1],r), 0, s.diff(v[1],z)]])
    zero(s.trace(full_gradient), 'actual three-dimensional incompressibility')
    physical_G = gaussian_coefficient(omega.dot(full_gradient*omega),3,1)
    physical_Z = gaussian_coefficient(omega.dot(omega),2,1)
    physical_D = gaussian_coefficient(omega.diff(r).dot(omega.diff(r))
        +omega.diff(z).dot(omega.diff(z))+(omega[0]**2+omega[1]**2)/r**2,2,1)
    zero(physical_G-Gm-Gs, 'literal full physical cubic stretching')
    zero(physical_Z-Zm-Zs, 'literal full physical enstrophy')
    zero(physical_D-Dm-Ds, 'literal full physical vorticity dissipation')
    E = gaussian_coefficient(grad(chi).dot(grad(chi))+b*b,2)
    zero(E-gaussian_coefficient(v.dot(v)+swirl*swirl,2,1), 'full physical kinetic square')
    weight = 1+r*r
    density = eta*eta+gb.dot(gb)
    weighted_G = gaussian_coefficient(weight*(a*eta*eta-gb.dot(B*gb)-a*gb.dot(gb)),3)
    weighted_J = gaussian_coefficient(b*b*(grad(weight).dot(grad(a))-eta*s.diff(weight,z)),3)
    weighted_rate = gaussian_coefficient(weight*(eta*Neta+gb.dot(grad(Nb))),3)
    clock_rate = gaussian_coefficient(v.dot(grad(weight))*density,3)/2
    zero(weighted_rate-weighted_G-weighted_J-clock_rate, 'full weighted nonlinear rate')
    hessian = gb.jacobian(coordinates)
    weighted_D = gaussian_coefficient(weight*(grad(eta).dot(grad(eta))
        +sum(entry**2 for entry in hessian)+3*gb[0]**2/r**2),2)
    viscous_rate = gaussian_coefficient(weight*(eta*lap5(eta)+gb.dot(grad(lap5(b)))),2)
    zero(viscous_rate+weighted_D-gaussian_coefficient(lap5(weight)*density,2)/2,
         'complete weighted diffusion and the positive adjoint Laplacian')
    return {'name':name, 'T':T, 'C_theta':C, 'G_meridional':Gm,
            'G_swirl_deformation':Gs, 'G_physical':physical_G,
            'E':E, 'Z':physical_Z, 'D':physical_D,
            'weighted_J_for_1_plus_r_squared':weighted_J}


def sign_pair():
    chi = z*(1-3*r*r+4*z*z)*s.exp(-radius)/2
    plus = gaussian_fixture(chi, 'positive_stretching')
    minus = gaussian_fixture(-chi, 'negative_stretching')
    for key in ('E','Z','D'):
        zero(plus[key]-minus[key], 'identical '+key+' in the two physical data')
    for fixture in (plus,minus):
        zero(fixture['T'], 'zero paid kinetic transfer')
        zero(fixture['C_theta'], 'zero higher source pairing')
    zero(plus['G_physical']-s.Rational(8,729), 'exact positive stretching')
    zero(minus['G_physical']+s.Rational(8,729), 'exact negative stretching')
    zero(plus['D']-s.Rational(19537,128), 'exact physical dissipation')
    require(plus['weighted_J_for_1_plus_r_squared'] != 0,
            'spatial weighting restores a source defect even when unweighted pairings vanish')
    nu = s.Rational(1,100000)
    # Quadratic integrals have factor K2, cubic integrals K3:
    # K_j=2*pi*sqrt(pi/(2*j)), so K3/K2=sqrt(2/3).
    growth_half = plus['G_physical']*s.sqrt(s.Rational(2,3))-nu*plus['D']
    require(growth_half>0, 'actual enstrophy initially grows at positive viscosity')
    negative_half = minus['G_physical']*s.sqrt(s.Rational(2,3))-nu*minus['D']
    require(negative_half<0, 'opposite datum has decreasing actual enstrophy')
    # A nonzero-source fixture tests the cancellation before either pairing
    # is set to zero. No mode or generated source is discarded.
    source_fixture = gaussian_fixture(z*s.exp(-radius)/2, 'nonzero_source')
    require(source_fixture['C_theta'] != 0, 'nontrivial channel cancellation fixture')
    return {'data':[plus,minus,source_fixture], 'positive_viscosity':str(nu),
            'half_Z_rate_over_K2':str(growth_half),
            'integral_factors':'E,Z,D multiply K2; T,C_theta,G multiply K3; K_j=2*pi*sqrt(pi/(2*j))',
            'scope':'exact initial rates of smooth Schwartz unforced data; no future-time allowance is refuted'}


def main():
    print(json.dumps({'joint_identity':local_green_identities(),
                      'physical_sign_pair':sign_pair()},indent=2,default=str))


if __name__ == '__main__':
    main()
