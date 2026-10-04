#!/usr/bin/env python3
"""Exact whole-space pressure work for the evolving strain/swirl perspective.

The full canonical pressure, axis boundary and viscous cost are retained.
The local PDE interval and conditional history estimates are analytic.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

from rotational_joint_enstrophy import r, z, grad, lap5, velocity
from circulation_source_reserve import div3, lap3
from rotational_curl_reserve import require, zero


d = s.symbols('d', positive=True)


def gaussian_pair(poly, rate, radial_measure=False):
    """Integral on r>=0,z in R, with optional physical factor 2*pi*r."""
    result = 0
    for (ir, iz), coefficient in s.Poly(s.expand(poly), r, z).terms():
        if iz % 2:
            continue
        power_r = ir+int(radial_measure)
        result += coefficient*s.gamma(s.Rational(power_r+1,2))*s.gamma(s.Rational(iz+1,2)) \
            /(2*rate**s.Rational(power_r+iz+2,2))
    return s.simplify(result*(2*s.pi if radial_measure else 1))


def source_and_heat():
    e = s.exp(-r*r-z*z)
    chi = z*e
    v = velocity(chi)
    ur, uz = v
    m, b = -ur/r, 2*s.sqrt(2)*z*e
    zero(div3(v), 'the complete meridional datum is physically incompressible')
    zero(m*m+b*b-(1+2*z*z)**2*e**2, 'paired strain and swirl give an exact positive square')
    G = s.Matrix([[s.diff(ur,r),-b,s.diff(ur,z)],
                  [b+r*s.diff(b,r),ur/r,r*s.diff(b,z)],
                  [s.diff(uz,r),0,s.diff(uz,z)]])
    J = G.applyfunc(lambda f:s.cancel(f/e))
    source = s.expand(s.trace(J*J))
    convection = s.Matrix([v.dot(grad(ur))-r*b*b,v.dot(grad(uz))])
    zero(div3(convection)-source*e**2, 'all vector-convection terms supply the canonical pressure')
    zero(gaussian_pair(source,s.Integer(2),True),
         'the complete pressure source has zero mass, retaining the correct far decay')
    energy_poly = s.cancel((v.dot(v)+r*r*b*b)/e**2)
    energy = s.simplify(gaussian_pair(energy_poly,s.Integer(2),True)/s.pi**s.Rational(3,2))
    enstrophy = s.simplify(gaussian_pair(s.trace(J.T*J),s.Integer(2),True)/s.pi**s.Rational(3,2))
    zero(energy-s.Rational(15,32)*s.sqrt(2), 'complete initial kinetic energy')
    zero(enstrophy-s.Rational(119,32)*s.sqrt(2), 'complete physical kinetic dissipation')

    variance = (d-1)/(4*d)
    heat = 0
    for (ir, iz), coefficient in s.Poly(source,r,z).terms():
        require(ir%2==0 and iz%2==0, 'even Gaussian pressure-source powers')
        i,j = ir//2,iz//2
        radial = sum(s.binomial(i,k)**2*s.factorial(k)*(2*variance)**k
                     *(r*r/d**2)**(i-k) for k in range(i+1))
        axial = sum(s.binomial(2*j,2*k)*s.factorial2(2*k-1)*variance**k
                    *(z/d)**(2*j-2*k) for k in range(j+1))
        heat += coefficient*radial*axial
    heat = s.expand(heat)
    zero(heat.subs(d,1)-source, 'pressure heat evolution starts from its complete source')
    full = heat*d**s.Rational(-3,2)*s.exp(-2*(r*r+z*z)/d)
    zero(8*s.diff(full,d)-lap3(full), 'entire three-dimensional pressure heat equation')
    # Actual p is the time integral of this heat evolution; d=1+8*t.
    return source, heat, dict(E0_over_pi_three_halves=str(energy),
                              gradient_energy_over_pi_three_halves=str(enstrophy),
                              physical_energy_rate='E_prime(0)=-(119 sqrt(2)/16) nu A^2 pi^(3/2)<0')


def exact_pressure_moment(heat, exponent):
    weight = (1-4*z**4)*(1+r*r+z*z)**exponent
    rate = 2*(d+1)/d
    derivative = s.diff(heat,r)-4*r*heat/d
    direct = s.factor(gaussian_pair(weight*derivative,rate)/d**s.Rational(3,2))
    derivative_weight = s.diff(weight,r)-4*r*weight
    volume = gaussian_pair(derivative_weight*heat,rate)/d**s.Rational(3,2)
    axis_poly = s.Poly(s.expand((weight*heat).subs(r,0)),z)
    boundary = sum(co*s.gamma(s.Rational(iz+1,2))/rate**s.Rational(iz+1,2)
                   for (iz,),co in axis_poly.terms())/d**s.Rational(3,2)
    zero(direct+volume+boundary, 'global radial integration by parts retains the axis pressure')

    x = s.symbols('x', positive=True)
    rational = s.factor(direct.subs(d,x*x-1)*2*x/s.sqrt(2*s.pi))
    primitive = s.integrate(rational,x)
    zero(s.diff(primitive,x)-rational, 'rational/logarithmic primitive of the whole pressure work')
    endpoint = s.limit(primitive,x,s.oo)-primitive.subs(x,s.sqrt(2))
    # Both sqrt(2)-1 and sqrt(2)+1 are positive reciprocals.
    zero((s.sqrt(2)-1)*(s.sqrt(2)+1)-1, 'real logarithmic endpoint identity')
    endpoint = s.expand(endpoint).subs(s.log(s.sqrt(2)-1),-s.log(s.sqrt(2)+1))
    W = s.simplify(s.Rational(3,4)*s.pi*s.sqrt(2*s.pi)*endpoint)
    if exponent == 0:
        expected = -s.Rational(8317,35840)*s.pi**s.Rational(3,2)
    elif exponent == 5:
        expected = s.pi**s.Rational(3,2)*(-s.Rational(20189482811,1174405120)
                    +45*s.sqrt(2)*s.log(1+s.sqrt(2))/32)
    else:
        raise ValueError('Unlisted exact calibration')
    zero(W-expected, 'complete integrated pressure work has its stated exact value')
    return dict(weight_power=exponent, heat_pair=str(direct),
                transformed_integrand=str(rational), primitive=str(primitive), W=str(expected))


def full_diffusion():
    U, L = 1+r*r+z*z, 1+2*z*z
    M, B = 1-2*z*z, 2*s.sqrt(2)*z
    stock = L**3*U**5
    relative = sum((s.diff(f,c)-2*c*f+s.Rational(20,3)*c*f/U)**2
                   for f in (M,B) for c in (r,z))
    D1 = s.Poly(s.cancel(3*L*U**5*relative),r,z).as_expr()
    logr = -4*r+s.Rational(20,3)*r/U
    logz = 8*z/L-4*z+s.Rational(20,3)*z/U
    D2 = s.Poly(s.cancel(s.Rational(3,4)*stock*(logr**2+logz**2)),r,z).as_expr()
    scale = s.pi**s.Rational(3,2)
    initial = s.simplify(gaussian_pair(stock,s.Integer(3),True)/scale)
    relative_value = s.simplify(gaussian_pair(D1,s.Integer(3),True)/scale)
    gradient_value = s.simplify(gaussian_pair(D2,s.Integer(3),True)/scale)
    axis_value = s.simplify(4*sum(co*s.gamma(s.Rational(iz+1,2))/3**s.Rational(iz+1,2)
                                for (iz,),co in s.Poly(stock.subs(r,0),z).terms())/s.sqrt(s.pi))
    zero(initial-s.Rational(189619,5832)*s.sqrt(3), 'critical initial stock')
    zero(relative_value-s.Rational(242249,729)*s.sqrt(3), 'both relative-gradient diffusion terms')
    zero(gradient_value-s.Rational(205049,1458)*s.sqrt(3), 'critical power gradient diffusion')
    zero(axis_value-s.Rational(28153,162)*s.sqrt(3), 'physical axis diffusion loss')
    total = s.simplify(relative_value+gradient_value+axis_value)
    zero(total-s.Rational(157154,243)*s.sqrt(3), 'complete diffusion including the axis')
    # asinh(1)=integral_0^1(1+t^2)^(-1/2)dt<1; sqrt(2)<3/2.
    pressure_lower = s.Rational(20189482811,1174405120)-s.Rational(135,64)
    require(pressure_lower>15, 'exact positive lower bound for the reversed pressure work')
    require(s.Rational(157154,243)*s.Rational(7,4)<1200,
            'sqrt(3)<7/4 gives an exact diffusion upper bound')
    A,nu = s.symbols('A nu',positive=True)
    zero(15*A**4-1200*(A/100)*A**3-3*A**4,
         'amplitude at least one hundred viscosities beats all diffusion')
    return dict(R0_over_pi_three_halves=str(initial),
                relative_diffusion_over_nu_pi_three_halves=str(relative_value),
                gradient_diffusion_over_nu_pi_three_halves=str(gradient_value),
                axis_diffusion_over_nu_pi_three_halves=str(axis_value),
                D_over_nu_pi_three_halves=str(total),
                reversed_pressure_lower='W0 > 15 pi^(3/2)',
                physical_family='u0=-A V, h0=(1+|x|^2)^(-10/3), A>=100 nu',
                actual_rate='R_prime(0)=W(0)-D(0)>3 pi^(3/2) A^4')


def integrated_absorption():
    pressure, pa, chi, weight = [s.Function(n)(r,z)
                                for n in ('pressure','pa','cutoff','weight')]
    localized = pressure-chi*pa
    zero(weight*s.diff(pressure,r)+localized*s.diff(weight,r)
         -weight*s.diff(chi,r)*pa-s.diff(weight*localized,r)
         -weight*chi*s.diff(pa,r),
         'localized pressure subtraction retains every derivative; pa is constant in r')
    # After pa_r=0, integration has the seam term +integral weight*chi_r*pa.
    q,h,nu = s.symbols('q h nu',positive=True)
    p,dm,dq,m = s.symbols('p dm dq m',real=True)
    cost1 = 3*s.sqrt(q)*p*p/(2*nu*h*r*r)
    diffusion1 = 3*nu*s.sqrt(q)*dm*dm/(2*h)
    work1 = -3*s.sqrt(q)*p*dm/(r*h)
    square1 = 3*nu*s.sqrt(q)/(2*h)*(dm+p/(nu*r))**2
    zero(diffusion1+cost1-work1-square1, 'first absorbed derivative is an exact square')
    cost2 = 3*m*m*p*p/(2*nu*h*h*s.sqrt(q)*r*r)
    diffusion2 = 3*nu*dq*dq/(8*s.sqrt(q))
    work2 = -3*m*p*dq/(2*r*h*s.sqrt(q))
    square2 = 3*nu/(8*s.sqrt(q))*(dq+2*m*p/(nu*r*h))**2
    zero(diffusion2+cost2-work2-square2, 'second absorbed derivative is an exact square')
    zero(cost1-cost2-3*p*p*(h*q-m*m)/(2*nu*r*r*h*h*s.sqrt(q)),
         'the retained swirl square makes the second pressure cost no larger')
    ell = s.symbols('ell',positive=True)
    radial_cutoff = s.exp(-r*r/(ell*ell))
    zero(s.diff(radial_cutoff,r)+2*r*radial_cutoff/(ell*ell),
         'one fixed smooth subtraction has a retained decaying seam derivative')
    exponent = s.symbols('exponent',real=True)
    zero((3*exponent-5)-8+2-(3*exponent-11),
         'far pressure-square radial integrability requires exponent below ten thirds')
    return dict(subtraction='p_tilde=p-exp(-r^2/ell^2)*p_axis(z)',
                exact_identity='W=-6pi integral p_tilde partial_r(sqrt(Q)m/h) drdz + J',
                seam='J=6pi integral sqrt(Q)m/h * cutoff_prime * p_axis drdz',
                pressure_square='V=integral_R3 sqrt(Q)/h * (p_tilde/r)^2 dx',
                estimate='W <= D/2 + (3/nu)V + J',
                scope='Finite for the original exponent-three density under the stated prefix-local decay; no original-datum bound on the new pressure history is supplied.')


if __name__ == '__main__':
    source,heat,kinetic = source_and_heat()
    output = dict(source_polynomial=str(source), kinetic=kinetic,
                  exact_weight=exact_pressure_moment(heat,5),
                  flat_limit=exact_pressure_moment(heat,0),
                  diffusion=full_diffusion(), absorption=integrated_absorption(),
                  limitation='Exact Gaussian initial rates and square certificates; actual local evolution and large-envelope limits are analytic. No full-datum arbitrary-horizon pressure budget or blowup is established.')
    paths = [Path(__file__)] + [Path(__file__).with_name(n) for n in
             ('rotational_joint_enstrophy.py','circulation_source_reserve.py','rotational_curl_reserve.py')]
    output['source_sha256'] = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    print(json.dumps(output,indent=2))
