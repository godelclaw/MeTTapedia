#!/usr/bin/env python3
"""Exact Gaussian certificates for a mean mode created by two helical parents.

The intermediate pressures and all convection branches are retained.
These checks concern differential identities and the initial cubic jet.
Local evolution and its uniform time window are proved analytically in
papers/ns_symmetry_defect.tex, not certified by this script. Requires Sympy.
"""
import json
from itertools import product
import sympy as s

w, b, a, beta = s.symbols('w b a beta')
I = s.I
radial = w*b
decay = s.exp(-radial)
dx = lambda f: s.diff(f,w)+s.diff(f,b)
dy = lambda f: I*(s.diff(f,w)-s.diff(f,b))
lap = lambda f: 4*s.diff(f,w,b)

def velocity(psi):
    return s.Matrix([dy(psi),-dx(psi),0])

def adv(u,v,n):
    return v.applyfunc(lambda f:u[0]*dx(f)+u[1]*dy(f)+I*2*n*u[2]*f)

def divergence(v,n):
    return dx(v[0])+dy(v[1])+I*2*n*v[2]

def pressure_source(u,v,m,n):
    return s.expand(divergence(adv(u,v,n)+adv(v,u,m),m+n))

def require_zero(expr,label):
    entries=list(expr) if isinstance(expr,s.MatrixBase) else [expr]
    for e in entries:
        q=s.simplify(s.expand(e))
        if q!=0:raise ArithmeticError((label,q))

Apsi=w**2*decay
Bbarpsi=b**4*(1+beta*radial)*decay
A=velocity(Apsi)
Bbar=velocity(Bbarpsi)
FAA=divergence(adv(A,A,1),2)
pAA=-w**4*decay**2
require_zero(-lap(pAA)+16*pAA-FAA,'exact pressure of A with A')
FAB=pressure_source(A,Bbar,1,-1)
polynomial=s.factor(FAB/(b**2*decay**2)).subs(b,a/w).simplify()
terms=s.Poly(polynomial,a)
moment=sum(coef*s.factorial(power[0]+2)/2**(power[0]+3)
           for power,coef in terms.terms())
selected_beta=s.solve(moment,beta)
result={'mixed_pressure_polynomial':str(s.factor(polynomial)),
        'pressure_tail_moment':str(s.factor(moment)),
        'pressure_compatible_beta':[str(v) for v in selected_beta]}
if len(selected_beta)!=1:raise ArithmeticError('expected unique pressure compatibility')
Bbar=Bbar.subs(beta,selected_beta[0])
FAB=FAB.subs(beta,selected_beta[0])
coeff=s.symbols('c0:4')
pAB=b**2*sum(coeff[i]*radial**i for i in range(4))*decay**2
residual=s.Poly(s.expand((-lap(pAB)-FAB)/(b**2*decay**2)),w,b)
sol=s.solve(residual.coeffs(),coeff,dict=True)
result['pressure_polynomial_solution']=[{str(k):str(v) for k,v in q.items()}
                                        for q in sol]
if len(sol)!=1:raise ArithmeticError('no unique polynomial pressure')
pAB=s.simplify(pAB.subs(sol[0]))
require_zero(-lap(pAB)-FAB,'exact mixed zero-axial-frequency pressure')

def grad(p,n):return s.Matrix([dx(p),dy(p),I*2*n*p])
NAA=-adv(A,A,1)-grad(pAA,2)
NAB=-adv(A,Bbar,-1)-adv(Bbar,A,1)-grad(pAB,0)
require_zero(divergence(NAA,2),'transverse quadratic A,A source')
require_zero(divergence(NAB,0),'transverse quadratic A,Bbar source')
# Both branches of the actual cubic Taylor derivative, with every ordered
# convection contribution, before the final pressure projection.
cubic=(-adv(A,NAB,0)-adv(NAB,A,1)
       -adv(Bbar,NAA,2)-adv(NAA,Bbar,-1))
circulation=s.factor((w*(cubic[0]-I*cubic[1])
                       -b*(cubic[0]+I*cubic[1]))/(-2*I))
# The (m,n)=(0,1) circulation is pressure independent, so the outer
# Leray projection makes no change to this component.
expected=(s.Rational(8,5)*radial**2
          *(8*radial**4-110*radial**3+346*radial**2-275*radial+27)*decay**3)
require_zero(circulation-expected,'full cubic circulation coefficient')
require_zero(circulation.subs({w:1,b:1})+s.Rational(32,5)*s.exp(-3),
             'nonzero output at radius one')
require_zero(w*s.diff(circulation,w)-b*s.diff(circulation,b),
             'zero angular index of the circulation output')

# Phase counts also rule out every base and viscous contribution to this
# mode in the second time derivative. A linear derivative preserves labels.
labels={'base':(0,0),'A':(2,1),'Abar':(-2,-1),'B':(4,1),'Bbar':(-4,-1)}
select=lambda names: tuple(sum(labels[name][j] for name in names) for j in range(2))
for degree in [1,2]:
    if any(select(q)==(0,1) for q in product(labels,repeat=degree)):
        raise ArithmeticError('recipient has lower-order parents')
    if any(select(q)[0]==0 and select(q)[1]!=0
           for q in product(labels,repeat=degree)):
        raise ArithmeticError('fast mean occurs below cubic order')
triples=[q for q in product(labels,repeat=3) if select(q)==(0,1)]
if set(triples)!={('A','A','Bbar'),('A','Bbar','A'),('Bbar','A','A')}:
    raise ArithmeticError('missing cubic ancestry')

# Horizontal energies of the real parents, including the angular average.
r=s.symbols('r',positive=True)
energies={}
for m,polynomial_r in [(2,s.Integer(1)),(4,1-s.Rational(2,5)*r*r)]:
    profile=r**m*polynomial_r*s.exp(-r*r)
    mean_sq=(m*m*profile*profile/r**2+s.diff(profile,r)**2)/2
    energies[m]=s.integrate(2*r*mean_sq,(r,0,s.oo))
require_zero(energies[2]-s.Rational(3,4),'quadrupole horizontal energy divided by pi')
require_zero(energies[4]-s.Rational(21,20),'fourth harmonic energy divided by pi')
require_zero(sum(energies.values())-s.Rational(9,5),'total horizontal defect energy')

# Each real parent contributes a factor 1/2; the conjugate output doubles
# the real part. The physical cosine coefficient is therefore C_Gamma/4.
real_cosine_coefficient=circulation/4
require_zero(real_cosine_coefficient.subs({w:1,b:1})
             +s.Rational(8,5)*s.exp(-3),'real-field cubic normalization')

# Physical scaling at the critical relative amplitude epsilon=lambda^(-h).
concentration,h,normalization,nu=s.symbols('concentration h normalization nu',positive=True)
mu=concentration**(1-2*h)
amplitude=concentration**(1+2*h)/s.sqrt(normalization)
epsilon=concentration**(-h)
eta=nu*concentration/amplitude
require_zero(amplitude**2*epsilon**6/(concentration**2*mu)
             -1/(normalization*concentration),'recipient physical kinetic-energy scaling')
require_zero(amplitude**2*epsilon**6/mu-concentration/normalization,
             'recipient physical enstrophy scaling')
require_zero(amplitude**2*eta*epsilon**6/mu
             -nu*concentration**(1-2*h)/s.sqrt(normalization),
             'recipient integrated viscous-cost scaling')
require_zero(amplitude*epsilon**2/concentration-1/s.sqrt(normalization),
             'bounded critical fluctuation-history scaling')
require_zero(concentration**(-3+2*h)*amplitude*concentration**2*epsilon**3
             -concentration**h/s.sqrt(normalization),
             'normalized mean-curvature loss at critical amplitude')
result.update(status='all exact residuals zero',
              pressure_AA=str(pAA),pressure_ABbar=str(pAB),
              mixed_circulation_second_derivative=str(circulation),
              radial_form=str(s.factor(circulation.subs(b,a/w))),
              real_cosine_coefficient_at_radius_one=str(
                  s.simplify(real_cosine_coefficient.subs({w:1,b:1}))),
              cubic_parent_triples=triples,
              horizontal_energies_divided_by_pi={str(k):str(v) for k,v in energies.items()},
              critical_amplitude_scaling='kinetic lambda^-1; enstrophy lambda; mean curvature lambda^h',
              scope='exact pressure and cubic-jet identities; evolution estimates are analytic')
print(json.dumps(result,indent=2))
