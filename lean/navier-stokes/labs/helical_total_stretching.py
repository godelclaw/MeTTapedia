#!/usr/bin/env python3
"""Exact identities for the full signed response of a helical perturbation.

The pressure pairing includes all three vorticity components. The positive
Laplace integral and the actual local evolution are justified analytically
in papers/ns_symmetry_defect.tex. This is not a Lean certificate.
Requires Sympy; numerical evolution is not used by this checker.
"""
import json
import sympy as s

r, kappa, t, beta = s.symbols('r kappa t beta', positive=True)
m = 2
f = r**2*s.exp(-r**2)
v = 2*r*s.exp(-r**2)
Omega = v/r
zeta = s.diff(v,r)+v/r
shear = s.diff(v,r)-v/r
Lm = lambda q: s.diff(q,r,2)+s.diff(q,r)/r-m*m*q/r**2

def check(expr,label):
    entries=list(expr) if isinstance(expr,s.MatrixBase) else [expr]
    for entry in entries:
        residual=s.simplify(s.expand(entry))
        if residual != 0: raise ArithmeticError((label,residual))

# Cylindrical velocity-gradient matrices at a fixed azimuth. The column
# for the azimuthal derivative includes the derivatives of the basis.
M = s.Matrix([[0,-Omega,0],[s.diff(v,r),0,0],[0,0,0]])
W = s.Matrix([s.I*m*f/r,-s.diff(f,r),0])
MW = s.Matrix([
    [s.I*m*(s.diff(f,r)/r-f/r**2), s.diff(f,r)/r-m*m*f/r**2,
     s.I*kappa*W[0]],
    [-s.diff(f,r,2), s.I*m*(-s.diff(f,r)/r+f/r**2),
     s.I*kappa*W[1]],
    [0,0,0]])
source = s.simplify(2*s.trace(M*MW))
source_expected = 32*r*r*(r*r-1)*s.exp(-2*r*r)
check(source-source_expected,'linearized physical pressure source')

omega1 = s.Matrix([s.I*kappa*s.diff(f,r),-kappa*m*f/r,-Lm(f)])
stretch1 = M*omega1+zeta*s.I*kappa*W
p0prime = v*v/r
H0 = s.diag(s.diff(p0prime,r),p0prime/r,0)
without_pressure1 = s.simplify(
    (s.conjugate(stretch1).dot(stretch1)
     -s.conjugate(omega1).dot(H0*omega1))/2)
expected = kappa*kappa*shear*(zeta*m*m*f*f/r**2
                             -2*Omega*s.diff(f,r)**2)/2
check(without_pressure1-expected,'quadratic source and base-pressure pairing')
check(s.integrate(r*without_pressure1,(r,0,s.oo)),
      'integrated non-linearized-pressure part vanishes')

# Keep the vertical vorticity -L_m f as well as its horizontal components.
# Omitting it would leave a spurious zeta*L_m(f) term after integration.
p, pr = s.symbols('p pr',real=True)
Hz = s.Matrix([s.I*kappa*pr,-kappa*m*p/r,-kappa*kappa*p])
pressure_density = s.simplify(-r*zeta*s.conjugate(omega1).dot(Hz))
pressure_after_ibp = kappa*kappa*r*s.diff(zeta,r)*s.diff(f,r)*p
boundary_derivative = (s.diff(r*zeta*s.diff(f,r),r)*p
                       +r*zeta*s.diff(f,r)*pr)
check(pressure_density-pressure_after_ibp+kappa*kappa*boundary_derivative,
      'full pressure pairing with its exact radial boundary derivative')

# Heat kernel of the angular-m Gaussian. Differentiating beta creates
# the radial polynomial in the pressure source, with no approximation.
heat = r**m*(1+4*beta*t)**(-m-1)*s.exp(-beta*r*r/(1+4*beta*t))
check(s.diff(heat,t)-Lm(heat),'radial heat equation')
check(heat.subs(t,0)-r**m*s.exp(-beta*r*r),'radial heat initial value')
heat_source = 32*(-s.diff(heat,beta)-heat).subs(beta,2)
check(heat_source.subs(t,0)-source,'heated source at time zero')
target = s.diff(zeta,r)*s.diff(f,r)
a = s.symbols('a',nonnegative=True)
rate = 2+2/(1+8*t)
radial_polynomial = s.simplify(
    (heat_source*target*s.exp(rate*r*r)/2).subs(r,s.sqrt(a)))
polynomial = s.Poly(radial_polynomial,a)
pairing = s.factor(sum(c*s.factorial(power[0])/rate**(power[0]+1)
                      for power,c in polynomial.terms()))
J = -(256*t**3+24*t-5)/(2*(4*t+1)**6)
B = t*(128*t**4+160*t**3+112*t**2+28*t+5)/(2*(4*t+1)**5)
check(pairing-J,'exact heat-pressure pairing')
check(s.diff(B,t)-J,'positive primitive derivative')
check(B.subs(t,0),'positive primitive initial value')
check(s.limit(B,t,s.oo)-s.Rational(1,16),'positive primitive limit')
if any(c<=0 for c in s.Poly(s.cancel(B/t).as_numer_denom()[0],t).all_coeffs()):
    raise ArithmeticError('primitive numerator has a nonpositive coefficient')

print(json.dumps({
    'status':'all exact residuals zero',
    'linear_pressure_source':str(source),
    'radial_heat_pairing':str(J),
    'positive_primitive':str(B),
    'primitive_limit':'1/16',
    'quadratic_coefficient':'2*pi*kappa^4 * integral_0^infinity exp(-kappa^2*t)*B(t) dt > 0',
    'scope':'full signed initial response; the uniform evolution window is analytic'
},indent=2))
