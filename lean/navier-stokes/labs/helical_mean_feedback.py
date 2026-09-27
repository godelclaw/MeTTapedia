#!/usr/bin/env python3
"""Exact identities for simultaneous stretching and mean-circulation growth.

The two real radial profiles have identical first two jets at radius one.
Their initial averaged-circulation accelerations have opposite signs.
The changed profile also has positive total enstrophy curvature. Integral
signs and the viscous time window are justified in ns_symmetry_defect.tex;
this algebraic checker is not a Lean theorem. Requires Sympy.
"""
import json
import sympy as s

r, t, beta, a = s.symbols('r t beta a', positive=True)
E = s.exp(-r*r)
m = 2
kappa = s.Integer(2)
Omega = 2*E
zeta = 4*(1-r*r)*E
shear = -4*r*r*E
Lm = lambda q: s.diff(q,r,2)+s.diff(q,r)/r-4*q/r**2
f0 = r*r*E
f1 = f0*(1+(r*r-1)**3)


def check(expr, label):
    entries = list(expr) if isinstance(expr,s.MatrixBase) else [expr]
    for entry in entries:
        residual = s.simplify(s.expand(entry))
        if residual != 0:
            raise ArithmeticError((label,residual))


for j in range(3):
    check(s.diff(f1-f0,r,j).subs(r,1), 'matching radial jets')

p = s.Function('p', real=True)(r)
pr1 = s.symbols('pr1',real=True)
sources = []
for f in [f0,f1]:
    W = s.Matrix([s.I*m*f/r,-s.diff(f,r),0])
    M = s.Matrix([[0,-Omega,0],[Omega+r*s.diff(Omega,r),0,0],[0,0,0]])
    MW = s.Matrix([
        [s.diff(W[0],r),(s.I*m*W[0]-W[1])/r,s.I*kappa*W[0]],
        [s.diff(W[1],r),(s.I*m*W[1]+W[0])/r,s.I*kappa*W[1]],
        [0,0,0]])
    F = s.simplify(2*s.trace(M*MW))
    check(F-4*E*(Lm(f)-2*r*s.diff(f,r)+8*f),'full linear pressure source')
    sources.append(F)

    # Differentiate the mean radial/azimuthal stress using the complete
    # cylindrical linearized equations, including their pressure terms.
    at = -s.I*m*Omega*W[0]+2*Omega*W[1]-s.diff(p,r)
    bt = -s.I*m*Omega*W[1]-zeta*W[0]-s.I*m*p/r
    stress = s.simplify((at*s.conjugate(W[1])+W[0]*s.conjugate(bt))/2)
    expected = (2*Omega*s.diff(f,r)**2-zeta*m*m*f*f/r**2
                +s.diff(f,r)*s.diff(p,r)-m*m*f*p/r**2)/2
    check(stress-expected,'real angular mean stress derivative')
    acceleration = (-s.diff(r*r*expected,r)/r).subs(r,1)
    acceleration = acceleration.subs(s.Subs(s.Derivative(p,r),r,1),pr1)
    check(acceleration-(4*s.exp(-1)*pr1-16*s.exp(-3)),
          'circulation acceleration at the initial peak')

    # Check the full signed production identity, including the vertical
    # component of the parent vorticity and the base pressure Hessian.
    omega = s.Matrix([s.I*kappa*s.diff(f,r),-kappa*m*f/r,-Lm(f)])
    stretching = M*omega+zeta*s.I*kappa*W
    p0prime = r*Omega**2
    H0 = s.diag(s.diff(p0prime,r),p0prime/r,0)
    density = (s.conjugate(stretching).dot(stretching)
               -s.conjugate(omega).dot(H0*omega))/2
    check(density-kappa*kappa*shear*(zeta*m*m*f*f/r**2
                                    -2*Omega*s.diff(f,r)**2)/2,
          'complete quadratic production outside linear pressure')
    pp,pr = s.symbols('pp pr',real=True)
    Hz = s.Matrix([s.I*kappa*pr,-kappa*m*pp/r,-kappa*kappa*pp])
    pressure_density = -r*zeta*s.conjugate(omega).dot(Hz)
    boundary = s.diff(r*zeta*s.diff(f,r),r)*pp+r*zeta*s.diff(f,r)*pr
    check(pressure_density-kappa*kappa*r*s.diff(zeta,r)*s.diff(f,r)*pp
          +kappa*kappa*boundary,'all pressure components after radial integration')

q = r*r*E**2
part0 = -2*q
part1 = q*(-2*r**6+s.Rational(15,2)*r**4
           -s.Rational(75,8)*r*r-s.Rational(57,32))
check(-Lm(part0)+4*part0+24*q-sources[0],'first exact resolvent decomposition')
check(-Lm(part1)+4*part1+s.Rational(651,8)*q-sources[1],
      'changed exact resolvent decomposition')
check(s.diff(part0,r).subs(r,1)-4*s.exp(-2),'first explicit pressure derivative')
check(s.diff(part1,r).subs(r,1)-s.Rational(169,16)*s.exp(-2),
      'changed explicit pressure derivative')

heat = r*r/(1+4*beta*t)**3*s.exp(-beta*r*r/(1+4*beta*t))
check(s.diff(heat,t)-Lm(heat),'angular heat equation')
check(heat.subs(t,0)-r*r*s.exp(-beta*r*r),'angular heat initial value')
h = 2*(8*t-1)/(1+8*t)**4*s.exp(-2/(1+8*t))
check(s.diff(heat,r).subs({beta:2,r:1})-h,'resolvent derivative kernel')
v = 1/(1+8*t)
C = (s.Rational(7,4)*s.exp(-2)
     -(v*v+v/2+s.Rational(1,4))*s.exp(-2*v))/4
check(s.diff(C,t)-h,'signed primitive derivative')
check(C.subs(t,0),'signed primitive initial value')
check(C.subs(t,s.Rational(1,8))-(7*s.exp(-2)-3*s.exp(-1))/16,
      'primitive minimum')
check(s.limit(C,t,s.oo)-(7*s.exp(-2)-1)/16,'primitive limit')
# The elementary exponential-series bounds give e>8/3 and e<49/18<11/4.
if not s.Rational(8,3)**2 > 7 or not s.Rational(49,18) < s.Rational(11,4):
    raise ArithmeticError('elementary exponential bounds')
lower_pressure = s.Rational(169,16)-s.Rational(651,8)*s.Rational(5,64)
check(4*(lower_pressure-4)-s.Rational(105,128),
      'strict positive circulation coefficient after the heat bound')

source_poly = s.Poly(s.simplify(sources[1]/q).subs(r,s.sqrt(a)),a)
heat_source = sum(c*(-1)**j[0]*s.diff(heat,beta,j[0])
                  for j,c in source_poly.terms()).subs(beta,2)
check(heat_source.subs(t,0)-sources[1],'changed heated source')
target = s.diff(zeta,r)*s.diff(f1,r)
rate = 2+2/(1+8*t)
polynomial = s.Poly(s.simplify(heat_source*target*s.exp(rate*r*r)/2)
                    .subs(r,s.sqrt(a)),a)
J = s.factor(sum(c*s.factorial(j[0])/rate**(j[0]+1)
                 for j,c in polynomial.terms()))
J_expected = 9*(67108864*t**9+201326592*t**8+127401984*t**7
    +60293120*t**6+7004160*t**5+3280896*t**4+77568*t**3
    +51456*t*t+1680*t+5)/(256*(4*t+1)**12)
check(J-J_expected,'changed heat-pressure pairing')
numerator,denominator = s.cancel(J).as_numer_denom()
for poly in [numerator,denominator]:
    if any(c <= 0 for c in s.Poly(poly,t).all_coeffs()):
        raise ArithmeticError('heat pairing lacks a positive-coefficient certificate')
I0 = s.integrate(r*shear*(zeta*4*f1*f1/r**2-2*Omega*s.diff(f1,r)**2),(r,0,s.oo))
check(I0-s.Rational(1053,512),'changed non-pressure production integral')
check(s.integrate(r*(4*f1*f1/r**2+s.diff(f1,r)**2),(r,0,s.oo))-27,
      'changed horizontal energy divided by pi')

print(json.dumps({
    'status':'all exact residuals zero',
    'changed_profile':str(f1),
    'pressure_resolvent_coefficient':'651/8',
    'signed_heat_primitive':str(C),
    'changed_heat_pressure_pairing':str(J),
    'original_circulation_coefficient':'96/e * integral exp(-4t) h(t) dt < 0',
    'changed_circulation_coefficient_lower_bound':'105/(128 e^3) > 0',
    'changed_enstrophy_coefficient_lower_bound':'1053 pi/128 > 0',
    'scope':'exact initial identities; integral signs and viscous time interval are analytic'
},indent=2))
