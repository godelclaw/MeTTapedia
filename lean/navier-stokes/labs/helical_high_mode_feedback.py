#!/usr/bin/env python3
"""Exact pressure identities for growing circulation from high angular modes.

For the Gaussian swirl and a horizontal helical parent r^m exp(-r^2),
the complete initial mean-circulation acceleration is strictly positive
when m >= 5. Total enstrophy curvature is also positive for m >= 6.
This checks symbolic identities and polynomial bounds for the signed
heat-resolvent terms. The nonlinear time window is analytic, not
certified by this script. Requires Sympy.
"""
import json
import sympy as s

r, t = s.symbols('r t', positive=True)
m = s.symbols('m', integer=True, positive=True)
j = s.symbols('j', nonnegative=True)
E = s.exp(-r*r)
Omega = 2*E
zeta = 4*(1-r*r)*E
f = r**m*E
q = r**m*E**2
Lm = lambda v: s.diff(v,r,2)+s.diff(v,r)/r-m*m*v/r**2
p = s.Function('p', real=True)(r)


def check(expression, label):
    residual = s.simplify(s.expand(expression))
    if residual != 0:
        raise ArithmeticError((label, residual))


W = s.Matrix([s.I*m*f/r, -s.diff(f,r), 0])
M = s.Matrix([[0,-Omega,0], [Omega+r*s.diff(Omega,r),0,0], [0,0,0]])
MW = s.Matrix([
    [s.diff(W[0],r), (s.I*m*W[0]-W[1])/r, 2*s.I*W[0]],
    [s.diff(W[1],r), (s.I*m*W[1]+W[0])/r, 2*s.I*W[1]],
    [0,0,0]])
source = 2*s.trace(M*MW)
expected_source = 8*(4*r*r+m*m-3*m-2)*q
check(source-expected_source, 'full cylindrical linear-pressure source')
coefficient = 8*(m*m-m+1)
check(-Lm(-2*q)+4*(-2*q)+coefficient*q-source,
      'exact pressure resolvent decomposition')

at = -s.I*m*Omega*W[0]+2*Omega*W[1]-s.diff(p,r)
bt = -s.I*m*Omega*W[1]-zeta*W[0]-s.I*m*p/r
stress = (at*s.conjugate(W[1])+W[0]*s.conjugate(bt))/2
expected_stress = (2*Omega*s.diff(f,r)**2-m*m*zeta*f*f/r**2
                  +s.diff(f,r)*s.diff(p,r)-m*m*f*p/r**2)/2
check(stress-expected_stress, 'complete mean stress derivative')
acceleration = -s.diff(r*r*expected_stress,r)/r
acceleration = acceleration.subs(s.diff(p,r,2),
    -s.diff(p,r)/r+(m*m/r**2+4)*p-source)
p1, pr1, R1, Rr1 = s.symbols('p1 pr1 R1 Rr1', real=True)
acceleration = acceleration.subs(r,1).subs({
    s.Subs(s.Derivative(p,r),r,1):pr1, p.subs(r,1):p1})
formula = (4*m*(m-4)*s.exp(-3)-2*(m-2)*s.exp(-1)*p1
           +2*m*s.exp(-1)*pr1)
check(acceleration-formula, 'peak acceleration after pressure equation')
resolved = formula.subs({p1:-2*s.exp(-2)+coefficient*R1,
                         pr1:-2*(m-4)*s.exp(-2)+coefficient*Rr1})
resolved_formula = (4*(m-2)*s.exp(-3)
    +coefficient*s.exp(-1)*(2*m*Rr1-2*(m-2)*R1))
check(resolved-resolved_formula, 'resolved peak acceleration')

a = 1+8*t
heat = r**m/a**(m+1)*s.exp(-2*r*r/a)
check(s.diff(heat,t)-Lm(heat), 'angular heat equation')
check(heat.subs(t,0)-q, 'angular heat initial value')
check(s.diff(heat,r).subs(r,1)-(m-4/a)*heat.subs(r,1),
      'radial derivative of the heat kernel at the peak')
bracket = 2*m*(m-4/a)-2*(m-2)
lower = 2*(m*m-5*m+2)
check(bracket-lower-64*m*t/a, 'positive heat-bracket remainder')
lower_poly = s.Poly(s.expand(lower.subs(m,j+5)),j)
if any(c <= 0 for c in lower_poly.all_coeffs()):
    raise ArithmeticError('heat-bracket lower bound is not positive')

# Keep every parent-vorticity component and the base pressure Hessian
# in the signed enstrophy calculation.
shear = -4*r*r*E
omega = s.Matrix([2*s.I*s.diff(f,r), -2*m*f/r, -Lm(f)])
stretching = M*omega+2*s.I*zeta*W
check(s.re(s.conjugate(omega).dot(stretching))/2,
      'zero initial quadratic total production')
p0prime = r*Omega**2
H0 = s.diag(s.diff(p0prime,r),p0prime/r,0)
density = (s.conjugate(stretching).dot(stretching)
           -s.conjugate(omega).dot(H0*omega))/2
check(density-2*shear*(zeta*m*m*f*f/r**2-2*Omega*s.diff(f,r)**2),
      'complete non-pressure part of quadratic enstrophy production')
pp, pr = s.symbols('pp pr',real=True)
Hz = s.Matrix([2*s.I*pr,-2*m*pp/r,-4*pp])
pressure_density = -r*zeta*s.conjugate(omega).dot(Hz)
boundary = s.diff(r*zeta*s.diff(f,r),r)*pp+r*zeta*s.diff(f,r)*pr
check(pressure_density-4*r*s.diff(zeta,r)*s.diff(f,r)*pp+4*boundary,
      'full pressure pairing after radial integration')
I_density = r*shear*(zeta*m*m*f*f/r**2-2*Omega*s.diff(f,r)**2)
check(I_density-16*r**(2*m+3)*s.exp(-4*r*r)*(m*m-4*m+4*r*r),
      'Gaussian non-pressure integral density')
# Gaussian moments give I/d_m = (m-1)(m-2)/2^m.
check((m*m-4*m)+(m+2)-(m-1)*(m-2), 'Gaussian moment reduction')

aa, x = s.symbols('aa x',positive=True)
B = 2*(aa+1)/aa
c0 = m*(m-1)-2*(m+1)/aa
heated_source = 8*heat*(16*t*(m+1)/a+4*r*r/a**2+m*m-3*m-2)
check(heated_source.subs(t,0)-source, 'heated pressure source at time zero')
check(s.diff(heated_source,t)-Lm(heated_source), 'pressure source heat equation')
pairing_density = r*s.diff(zeta,r)*s.diff(f,r)*heated_source
expected_pairing = (64*a**(-m-1)*r**(2*m+1)*s.exp(-(2+2/a)*r*r)
                   *(r*r-2)*(m-2*r*r)*(c0.subs(aa,a)+4*r*r/a**2))
check(pairing_density-expected_pairing, 'complete heat-pressure integrand')
poly = s.Poly((x-2)*(m-2*x)*(c0+4*x/aa**2),x)
moment_sum = sum(c*s.rf(m+1,k[0])/B**k[0] for k,c in poly.terms())
A3 = 2*m*(m-1)**2
A2 = -m**4+6*m**3-15*m*m+6*m+4
A1 = -m**4+10*m**3-13*m*m+8*m+8
A0 = 4*m**3-14*m*m-18*m-8
P = A3*aa**3+A2*aa**2+A1*aa+A0
check(moment_sum+P/(2*(aa+1)**3), 'Gaussian heat-pressure integral')

def positive_coefficients(expression, strict, label):
    coefficients = s.Poly(s.expand(expression.subs(m,j+6)),j).all_coeffs()
    if any(c < 0 or (strict and c == 0) for c in coefficients):
        raise ArithmeticError(label)


positive_coefficients(-A2, True, 'negative quadratic coefficient of P')
positive_coefficients(2*m**3+20-A1, False, 'linear coefficient upper bound')
positive_coefficients(4*m**3-A0, True, 'constant coefficient upper bound')
# After dropping e^(-4t) only from a nonpositive lower bound, integrate
# the positive majorant of P using aa=1+8t. These are the three exact
# integrals, with their common factor 2^(-m) removed.
F3 = 1/m-s.Rational(3,2)/(m+1)+s.Rational(3,4)/(m+2)-s.Rational(1,8)/(m+3)
F1 = s.Rational(1,4)/(m+2)-s.Rational(1,8)/(m+3)
F0 = s.Rational(1,8)/(m+3)
ratio = 4*(A3*F3+(2*m**3+20)*F1+4*m**3*F0)/((m+1)*(m-1)*(m-2))
ratio_closed = (4*m**5+18*m**4+23*m**3+3*m*m-14*m+88)/(
    (m-2)*(m-1)*(m+1)**2*(m+2)*(m+3))
check(ratio-ratio_closed, 'integrated negative-pressure allowance')
gap_num, gap_den = s.cancel((1-ratio_closed).subs(m,j+6)).as_numer_denom()
for polynomial in [gap_num,gap_den]:
    if any(c <= 0 for c in s.Poly(polynomial,j).all_coeffs()):
        raise ArithmeticError('strictly positive enstrophy margin')

print(json.dumps({
    'status':'all exact residuals zero',
    'pressure_source_divided_by_q':str(expected_source/q),
    'resolvent_coefficient':str(coefficient),
    'heat_bracket_lower_bound_at_m_equals_j_plus_five':str(lower_poly.as_expr()),
    'circulation_acceleration_lower_bound':'4 (m-2) exp(-3), strictly, for m >= 5',
    'negative_pressure_allowance_ratio':str(s.factor(ratio_closed)),
    'enstrophy_margin_numerator_at_m_equals_j_plus_six':str(gap_num),
    'enstrophy_coefficient_lower_bound':'4 pi I_m (1-R_m) > 0 for m >= 6',
    'scope':'initial identities and heat-integrand sign; the unforced viscous time window is analytic'
},indent=2))
