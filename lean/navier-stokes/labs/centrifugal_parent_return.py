#!/usr/bin/env python3
"""A complete centrifugal return into self-generated periodic NS parents.

Exact pressure, jet and sign identities support the analytic local-history
theorem in README.md. No linearized flow is substituted for actual NS.
"""

from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import sympy as s

from rotational_curl_reserve import require, zero


def parity_jets():
    """Free symmetric bilinear algebra for u'=L u+B(u,u)."""
    U = ('U',)
    def add(*fields):
        result = defaultdict(Fraction)
        for field in fields:
            for key, value in field.items():
                result[key] += value
        return {key:value for key,value in result.items() if value}
    def scale(field, factor):
        return {key:value*factor for key,value in field.items() if value*factor}
    def linear(field):
        return {('L',key):value for key,value in field.items()}
    def bilinear(left, right):
        result = defaultdict(Fraction)
        for a,ca in left.items():
            for b,cb in right.items():
                a1,b1 = sorted((a,b), key=repr)
                result[('B',a1,b1)] += ca*cb
        return dict(result)
    def parity(key):
        if key == U:
            return 1
        if key[0] == 'L':
            return parity(key[1])
        return (parity(key[1])+parity(key[2]))%2
    def even(field):
        return {key:value for key,value in field.items() if parity(key)==0}

    heat = [{U:Fraction(1)}]
    actual = [heat[0]]
    forecast = [{}]
    for n in range(3):
        heat.append(scale(linear(heat[n]), Fraction(1,n+1)))
        actual_source = add(*(bilinear(actual[j],actual[n-j]) for j in range(n+1)))
        actual.append(scale(add(linear(actual[n]),actual_source), Fraction(1,n+1)))
        original_source = add(*(bilinear(heat[j],heat[n-j]) for j in range(n+1)))
        forecast.append(scale(add(linear(forecast[n]),original_source), Fraction(1,n+1)))
    for n in range(3):
        require(even(actual[n])==forecast[n], 'actual even parent matches the caloric forecast through order two')
    N = bilinear(heat[0],heat[0])
    expected = add(scale(bilinear(heat[0],bilinear(heat[0],N)),Fraction(2,3)),
                   scale(bilinear(N,N),Fraction(1,3)))
    difference = add(even(actual[3]),scale(forecast[3],-1))
    require(difference==expected, 'third Taylor coefficient retains the full nonlinear return')
    require(all('L' not in repr(key) for key in difference),
            'all viscosity-dependent difference terms vanish by parity, not by omission')
    t,a,b,c,d = s.symbols('t a b c d',real=True)
    old=t*a+t*t*b/2+t**3*c/6
    new=old+t**3*d/6
    zero(s.expand(new*new-old*old).coeff(t,4)-a*d/3,
         'Hilbert norm comparison has the correct fourth-order coefficient')
    return dict(
        setting='Any orthogonal reflection commuting with heat and the full Leray nonlinearity; initial velocity is reflection-odd.',
        parent='P_even u(t), P_even=(I+R)/2',
        forecast='Z(t)=integral_0^t exp(nu(t-s)Delta)N(exp(nu s Delta)u0) ds',
        third_derivative_difference='DN(u0)DN(u0)N(u0)+D2N[N(u0),N(u0)]',
        energy_coefficient='C/3, C=<N(u0),DN(u0)DN(u0)N(u0)>; <N,D2N[N,N]>=0 by incompressible kinetic cancellation',
        terms_after_projection=len(difference),
        scope='Free-algebra identities checked; reflection equivariance, PDE smoothness and Hilbert Taylor passage are analytic.')


def physical_return():
    r,theta = s.symbols('r theta',real=True,positive=True)
    k = s.symbols('k',integer=True,positive=True)
    eps = s.symbols('eps',real=True)
    chi,f0 = s.Function('chi')(r),s.Function('f0')(r)
    source=(s.diff(chi,r,2)+3*s.diff(chi,r)/r-k*k*chi)/k
    vr=-k*r*chi*s.cos(theta)
    vz=(2*chi+r*s.diff(chi,r))*s.sin(theta)
    p1=(2*chi+r*s.diff(chi,r))*s.cos(theta)/k
    Dz=lambda f:k*s.diff(f,theta)
    zero(s.diff(vr,r)+vr/r+Dz(vz), 'the generated meridional parent is incompressible')
    zero(r*source*s.cos(theta)-s.diff(p1,r)-vr,
         'the full initial centrifugal acceleration retains its radial pressure')
    zero(-Dz(p1)-vz, 'the same compact pressure gives the full axial acceleration')
    lap3=lambda f:s.diff(f,r,2)+s.diff(f,r)/r+Dz(Dz(f))
    zero(lap3(p1)-(2*source+r*s.diff(source,r))*s.cos(theta),
         'complete perturbation Poisson source, including cylindrical divergence')

    # The mixed meridional/toroidal pressure source vanishes pointwise.
    bb=s.Function('b')(r,theta)
    tor=s.Matrix([[0,-bb,0],[bb+r*s.diff(bb,r),0,r*Dz(bb)],[0,0,0]])
    mer=s.Matrix([[s.diff(vr,r),0,Dz(vr)],[0,vr/r,0],[s.diff(vz,r),0,Dz(vz)]])
    zero(s.trace(tor*mer+mer*tor), 'no pressure is suppressed in the first returned toroidal field')
    T=-r*(vr*s.diff(bb,r)+vz*Dz(bb))-2*vr*bb
    f2=-vr*s.diff(bb*bb,r)-vz*Dz(bb*bb)-4*vr*bb*bb/r
    zero(2*bb*T-r*f2, 'two toroidal factors return the complete radial source')

    f=f0+eps*source*s.cos(theta)
    ar,az=eps*vr,eps*vz
    f2=-ar*s.diff(f,r)-az*Dz(f)-4*ar*f/r
    density=s.expand(r*r*ar*f2)
    period_integral=s.integrate(density,(theta,0,2*s.pi))
    expected=-s.pi*eps**2*k*k*r**3*chi**2*(4*f0+r*s.diff(f0,r))
    zero(period_integral-expected, 'all cubic modulation terms vanish in the complete axial integral')
    alpha=s.symbols('alpha',real=True)
    zero(4*r**(-alpha)+r*s.diff(r**(-alpha),r)-(4-alpha)*r**(-alpha),
         'power-law angular momentum separates the two return signs')
    zero(s.diff(r**4*f0,r)/r**3-(4*f0+r*s.diff(f0,r)),
         'the actual feedback weight is the Rayleigh discriminant')
    return dict(
        domain='T3=(R/(2pi Z))^3, circular data supported transversely in r<5/2<pi',
        source='b0^2=f0(r)+eps*a(r)*cos(kz), a=(chi_second+3chi_prime/r-k^2chi)/k',
        canonical_pressure='p0(r)+eps*(2chi+r chi_prime)*cos(kz)/k, p0_prime=r*f0; subtract its mean',
        generated_parent='N(u0)=eps*(-k r chi cos(kz),0,(2chi+r chi_prime)sin(kz)) in cylindrical components',
        exact_return='C=-2pi^2 eps^2 k^2 integral r^3 chi^2*(4f0+r f0_prime) dr',
        growing_example='f0=r^-6 on supp chi: C=4pi^2 eps^2 k^2 integral r^-3 chi^2 dr>0',
        depleting_example='f0=1 on supp chi: C=-8pi^2 eps^2 k^2 integral r^3 chi^2 dr<0',
        generality='Any smooth nonzero compact circular swirl has an annulus with decreasing squared angular momentum, permitting the growing construction.')


def explicit_parameters():
    r=s.symbols('r',real=True)
    tau=(r-1)*(2-r)
    zero(s.diff(tau,r,2)+2, 'compact bump second denominator derivative')
    zero(tau-s.Rational(3,16)-(r-s.Rational(5,4))*(s.Rational(7,4)-r),
         'positive denominator lower bound on the middle half-annulus')
    # exp(x)>=x^j/j! for x>0 bounds tau^-j exp(-1/tau) by j!.
    chi_prime_bound=s.factorial(2)
    chi_second_bound=s.factorial(4)+2*s.factorial(3)+2*s.factorial(2)
    source_bound=chi_second_bound+3*chi_prime_bound+1
    zero(source_bound-47, 'every compact bump derivative is included in a')
    eps=s.Rational(1,10000)
    require(eps*64*source_bound<s.Rational(1,2), 'explicit modulation retains positive source')
    integral_lower=s.Rational(1,2)*(s.Rational(4,7))**3
    zero(integral_lower-s.Rational(32,343), 'entire positive annular integration window')
    coefficient=4*s.pi**2*eps**2*integral_lower*s.exp(-s.Rational(32,3))
    return dict(
        profile='chi=exp(-1/((r-1)(2-r))) on 1<r<2, zero elsewhere',
        base='b_base=psi(r)*r^-3, psi smooth, equal one on [1,2], supported in (1/2,5/2)',
        parameters='k=1, eps=1/10000',
        ratio_bound='|eps*a/f0|<=3008/10000<1/2 on the modulation support; zero outside',
        lower_bound_C=str(coefficient),
        conclusion='The actual even-parent energy exceeds its original caloric forecast on a nonzero short interval at every fixed nu>0.',
        not_claimed='No uniform time window, repeated renewal, growing total kinetic energy, whole-space realization, or singularity follows.')


if __name__ == '__main__':
    result=dict(jets=parity_jets(),physical=physical_return(),explicit=explicit_parameters(),
                status='Analytic actual unforced periodic history theorem with exact pressure, parity, integral and positivity checks; not a new Lean certificate.')
    paths=[Path(__file__),Path(__file__).with_name('rotational_curl_reserve.py')]
    result['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    print(json.dumps(result,indent=2))
