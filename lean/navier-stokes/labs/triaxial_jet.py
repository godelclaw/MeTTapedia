#!/usr/bin/env python3
"""Exact initial production derivative, including the whole-space Leray projection.

Polynomial vectors store the factor exp(-rate*rho).
The Fourier convention is integral f(x) exp(-i k.x) dx.
The velocity is curl((0,x*z,2*x*y)*exp(-rho)). This checks its initial
unforced production derivative, including pressure; it supplies no time
remainder or arbitrary-data bound. Requires SymPy.
"""
import json
from functools import lru_cache
from math import factorial
import sympy as s

x,y,z=s.symbols('x y z', real=True)
coords=(x,y,z)

def derivative(p,j,rate=1):
    return s.expand(s.diff(p,coords[j])-2*rate*coords[j]*p)

def gradient(v,rate=1):
    return s.Matrix(3,3,lambda i,j:derivative(v[i],j,rate))

def moment(p,rate,radial_inverse=False):
    """Integral normalized by (pi/rate)^(3/2), optionally with 1/rho."""
    rate=s.sympify(rate);ans=0
    for powers,c in s.Poly(s.expand(p),*coords).terms():
        if any(j%2 for j in powers):continue
        for j in powers:
            n=j//2
            c*=s.Rational(factorial(2*n),4**n*factorial(n))/rate**n
        if radial_inverse:c*=rate/(s.Rational(sum(powers),2)+s.Rational(1,2))
        ans+=c
    return s.factor(ans)

@lru_cache(None)
def transformed_power(j,n,rate):
    if not n:return s.Integer(1)
    old=transformed_power(j,n-1,rate)
    return s.expand(s.I*(s.diff(old,coords[j])-coords[j]*old/(2*rate)))

def transform(p,rate):
    """Fourier polynomial after removing (pi/rate)^1.5 exp(-rho/(4rate))."""
    return s.expand(sum(c*s.prod(transformed_power(j,n,s.sympify(rate))
                       for j,n in enumerate(powers))
                       for powers,c in s.Poly(s.expand(p),*coords).terms()))

def zero(p,label):
    if s.expand(p)!=0:raise ArithmeticError(label+': '+str(s.factor(p)))

v=s.Matrix([x-4*x*y*y+2*x*z*z,-2*y+4*x*x*y,z-2*x*x*z])
dv=gradient(v);strain=(dv+dv.T)/2
omega=s.Matrix([dv[2,1]-dv[1,2],dv[0,2]-dv[2,0],dv[1,0]-dv[0,1]])
zero(s.trace(dv),'divergence')
pi=moment(omega.dot(strain*omega),3)
zero(pi-s.Rational(32,27),'initial production')
cofactor=strain.cofactor_matrix().applyfunc(s.expand)
G=s.Matrix([4*sum(derivative(cofactor[i,j],j,2) for j in range(3)) for i in range(3)])
zero(moment(G.dot(v),3)-3*pi,'cubic homogeneity of variational gradient')
potential=s.Matrix([y*z,0,0])
variation=s.Matrix([derivative(potential[2],1)-derivative(potential[1],2),
                    derivative(potential[0],2)-derivative(potential[2],0),
                    derivative(potential[1],0)-derivative(potential[0],1)])
a=s.symbols('a',real=True)
expected=s.diff(-s.Rational(16,27)*(a-1)*(a-2)*(1-2),a).subs(a,0)
zero(moment(G.dot(variation),3)-expected,'independent solenoidal variation')

adv=-(dv*v)
rot= v.cross(omega)
Ghat=G.applyfunc(lambda q:transform(q,2))
Fhat=adv.applyfunc(lambda q:transform(q,2))
k=s.Matrix(coords)
raw=moment(s.conjugate(Ghat).dot(Fhat),s.Rational(1,4))/8
longitudinal=moment(s.conjugate(k.dot(Ghat))*k.dot(Fhat),s.Rational(1,4),True)/8
zero(raw-moment(G.dot(adv),4)/8,'unprojected Fourier Parseval')
euler=s.factor(raw-longitudinal)
rothat=rot.applyfunc(lambda q:transform(q,2))
euler_rot=(moment(s.conjugate(Ghat).dot(rothat),s.Rational(1,4))
           -moment(s.conjugate(k.dot(Ghat))*k.dot(rothat),s.Rational(1,4),True))/8
zero(euler-euler_rot,'advective versus rotational projected RHS')
somega=strain*omega
Gomega=2*s.Matrix([derivative(somega[2],1,2)-derivative(somega[1],2,2),
                   derivative(somega[0],2,2)-derivative(somega[2],0,2),
                   derivative(somega[1],0,2)-derivative(somega[0],1,2)])
Gomega-=s.Matrix([sum(derivative(omega[i]*omega[j],j,2) for j in range(3))
                  for i in range(3)])
Hhat=Gomega.applyfunc(lambda q:transform(q,2))
for component in k.cross(Ghat-Hhat):
    zero(component,'Betchov and vorticity variations differ by a gradient')
omega_raw=moment(s.conjugate(Hhat).dot(Fhat),s.Rational(1,4))/8
omega_pressure=-moment(s.conjugate(k.dot(Hhat))*k.dot(Fhat),s.Rational(1,4),True)/8
zero(euler-omega_raw-omega_pressure,'independent vorticity variation with pressure')
lap=v.applyfunc(lambda q:sum(derivative(derivative(q,j),j) for j in range(3)))
heat=moment(G.dot(lap),3)
zero(heat-moment(Gomega.dot(lap),3),'independent heat variation')
zero(euler-s.Rational(56064597,82001920),'Euler production derivative')
zero(omega_raw-s.Rational(7517,16384),'unprojected production derivative')
zero(omega_pressure-s.Rational(4610503,20500480),'pressure production derivative')
zero(heat+s.Rational(128,3),'heat production derivative')
result={'scope':'exact initial derivative only; no time remainder or budget',
        'production_over_g3':str(pi),
        'euler_Pdot_over_pi32':str(euler),
        'betchov_unprojected_advection_over_pi32':str(raw),
        'betchov_pressure_correction_over_pi32':str(-longitudinal),
        'vorticity_unprojected_advection_over_pi32':str(omega_raw),
        'vorticity_pressure_correction_over_pi32':str(omega_pressure),
        'viscous_Pdot_over_nu_g3':str(heat),
        'euler_Pdot_float':float(euler*s.pi**s.Rational(3,2)),
        'heat_Pdot_per_nu_float':float(heat*(s.pi/3)**s.Rational(3,2)),
        'checks':'homogeneity, independent variation, Parseval, both RHS forms, both functionals'}
print(json.dumps(result,indent=2))
