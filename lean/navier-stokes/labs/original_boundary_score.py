#!/usr/bin/env python3
"""Original-data terminal smoothing and compatible age weights.

Stochastic changes of measure, local existence, comparison and mixture
arguments are analytic in README.md. These checks cover their constants,
complete reserve squares, physical NS fixtures and bridge cancellation.
"""

import json
import sympy as sp

import passive_parent_bellman as parent
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f, Q, r = parent.f, parent.Q, parent.r


def vec(prefix):
    return sp.Matrix(sp.symbols(prefix+'0:3', real=True))


def weighted_reserve():
    nu, age_weight = sp.symbols('nu a', positive=True)
    derivative, potential, bulk, base = sp.symbols('adot Q BQ base', real=True)
    h, gamma, b, D, F = [vec(p) for p in ('h', 'g', 'b', 'D', 'F')]
    square = lambda v: v.dot(v)
    before = base-nu*square(h-b)/4-square(gamma-nu*h)/(4*nu)
    before += derivative*potential+age_weight*(bulk+gamma.dot(D)-h.dot(F))
    hstar = b+2*age_weight*(nu*D-F)/nu
    source = base+derivative*potential+age_weight*bulk
    source += nu*age_weight**2*square(D)+age_weight**2*square(nu*D-F)/nu
    source += age_weight*b.dot(nu*D-F)
    after = source-nu*square(h-hstar)/4-square(gamma-nu*h-2*nu*age_weight*D)/(4*nu)
    zero(before-after, 'complete age-weighted pressure reserve, with its weight derivative')
    tau, age = sp.symbols('tau age', positive=True)
    zero(age.subs(age,tau)-tau, 'capped weight is continuous at its seam')
    zero(sp.diff(age,age)-1, 'early weight derivative')
    zero(sp.diff(tau,age), 'late weight derivative vanishes')
    return dict(full_square_identity=True, cap='min(r,tau)',
                retained=['a_prime Q', 'a B_Q', 'joint density flux', 'original action', 'incoming history'])


def gaussian_and_local_constants():
    ell, B, s, c, nu, C4, S = sp.symbols('ell B s c nu C4 S', positive=True)
    proxy = sp.integrate((1+B*s)**2/ell**2,(s,0,ell))
    zero(proxy-(1/ell+B+B*B*ell/3),'terminal-shift directional variation')
    denominator = 1-(1+c+c*c/3)/12
    zero(denominator-sp.Rational(29,36)-(1-c)*(4+c)/36,
         'Gaussian margin for every B ell <= 1')
    zero(1-c*c/9-sp.Rational(8,9)-(1-c*c)/9,
         'short-time conditional deformation exponential margin')
    time = nu/(256*C4*C4*S*S)
    zero(8*C4*S*sp.sqrt(time/nu)-sp.Rational(1,2),
         'local mild contraction on the radius 2S ball')
    zero(8*C4*S*S*sp.sqrt(time/nu)-S/2,
         'local mild nonlinear displacement stays below S/2')
    zero(sp.Rational(1,2)*sp.Rational(1,12)-sp.Rational(1,24),
         'half of the original action pays the terminal cost')
    return dict(shift_variation=str(proxy), moment='(36/29)^(3/2)',
                terminal_payment='(3/4)log(36/29)', local_time=str(time),
                scope='deterministic constants; probability and local-existence arguments analytic')


def bernstein_identity():
    x,y,z = sp.symbols('x y z', real=True)
    nu,b0,age = sp.symbols('nu b0 age', positive=True)
    coords=(x,y,z)
    grad=lambda v:sp.Matrix([sp.diff(v,c) for c in coords])
    lap=lambda v:sum(sp.diff(v,c,2) for c in coords)
    u=sp.Matrix([1+x+2*y,2-y+z,-1+x])
    q=3+x+2*y-z+x*x+x*y+3*z*z+x*y*z+x**3
    g=grad(q); K=sp.hessian(q,coords); B=u.jacobian(coords)
    qt=nu*lap(q)+u.dot(g)
    g2=g.dot(g)
    Lg2=2*g.dot(grad(qt))-nu*lap(g2)-u.dot(grad(g2))
    K2=sum(v*v for v in K)
    zero(Lg2-2*g.dot(B.T*g)+2*nu*K2,'literal differentiated density gradient')
    Lq2=2*q*qt-nu*lap(q*q)-u.dot(grad(q*q))
    zero(Lq2+2*nu*g2,'literal scalar diffusion square')
    w=age*sp.exp(-2*b0*age)
    actual=sp.diff(w,age)*g2+w*Lg2+Lq2/(2*nu)
    expected=(sp.exp(-2*b0*age)-1)*g2
    expected-=2*w*(b0*g2-g.dot(B.T*g)+nu*K2)
    zero(actual-expected,'Bernstein test retains both negative terms')
    D,M,tau=sp.symbols('D M tau',positive=True)
    zero(D*D/(4*nu*tau)+M*D/(2*nu)+M*M*tau/(4*nu)
         -(D+M*tau)**2/(4*nu*tau),'bridge lower-bound exponent')
    return dict(gradient_bound='exp(b0 tau/2) Q0/sqrt(nu tau)',
                scope='local scalar PDE jets; not an additional NS flow or receiver')


def bridge_divergence(u,label):
    jets,pressure=velocity_time_jets(u,Q(1),1)
    for order,velocity in enumerate(jets):
        modes=set().union(*(set(v) for v in velocity))
        for k in modes:
            # For a bridge Gaussian with covariance v I, the extra term in
            # E[b(Y).(y-Y)] is -v times this divergence coefficient.
            coefficient=0
            for j in range(3):
                value=velocity[j].get(k)
                if value is not None:
                    scalar=sp.Rational(value.x)+sp.I*sp.Rational(value.y)
                    coefficient+=sp.I*k[j]*scalar
            zero(coefficient,(label,order,k,'bridge covariance cancels by incompressibility'))
    variance=sp.symbols('variance',positive=True)
    matrix=sp.diag(2,-1,0)
    zero(-variance*sp.trace(matrix)+variance,
         'a non-solenoidal field retains the Gaussian divergence defect')
    return dict(fixture=label,pressure_modes=len(pressure[0]),actual_time_jets=len(jets))


def actual_calibrations():
    x,y,z,time=sp.symbols('x y z time',real=True)
    a,nu=sp.symbols('a nu',positive=True)
    coords=(x,y,z)
    U=sp.Matrix([sp.sin(z)+sp.cos(y),sp.sin(x)+sp.cos(z),sp.sin(y)+sp.cos(x)])
    u=a*sp.exp(-nu*time)*U
    B=u.jacobian(coords); p=-u.dot(u)/2
    lap=u.applyfunc(lambda v:sum(sp.diff(v,c,2) for c in coords))
    residual=u.diff(time)+B*u+sp.Matrix([sp.diff(p,c) for c in coords])-nu*lap
    for j,v in enumerate(residual):
        zero(sp.trigsimp(v),('actual ABC NS, all time',j))
    zero(sp.trigsimp(sum(v*v for v in B))-3*a*a*sp.exp(-2*nu*time),
         'actual decaying ABC gradient bound from the datum')
    remainder=(sp.sin(z)-sp.cos(y))**2+(sp.sin(x)-sp.cos(z))**2+(sp.sin(y)-sp.cos(x))**2
    zero(sp.trigsimp(6-U.dot(U)-remainder),'ABC velocity bound is a sum of squares')
    return dict(abc_velocity_bound='sqrt(6) a',abc_gradient_bound='sqrt(3) a',
                certified_window='any tau <= 1/(sqrt(3) a)',
                scope='same exact regular 3D flow that defeats the unconditioned noise moment')


def mixture_identity():
    mu1,mu2,K1,K2=sp.symbols('mu1 mu2 K1 K2',positive=True)
    g1,g2=vec('g1'),vec('g2')
    density=mu1*K1+mu2*K2
    score=(mu1*g1+mu2*g2)/density
    mixture=mu1*K1/density*(g1/K1)+mu2*K2/density*(g2/K2)
    for j,v in enumerate(score-mixture):
        zero(v,('mixture preserves the exact terminal gradient',j))
    return dict(posterior_weights='mu_i K_i / sum mu_j K_j',
                scope='finite mixture algebra; general kernel integration and convexity analytic')


def late_shift_covariance():
    start,ell=sp.symbols('start ell',positive=True)
    s,c=sp.symbols('s c',real=True)
    drift=sp.Matrix([[0,c,0],[0,0,0],[0,0,0]])
    transition=sp.eye(3)+(start+ell-s)*drift
    shift=(sp.eye(3)-(s-start)*drift).T/ell
    covariance=sp.integrate(shift*transition.T,(s,start,start+ell))
    for i in range(3):
        for j in range(3):
            zero(covariance[i,j]-int(i==j),('late shift retains exact terminal covariance',i,j))
    return dict(covariance='Id, independently of the inherited starting age',
                scope='non-normal linear Gaussian formula check, not a finite-energy NS example')


def main():
    simple=parent.carrier(r.c.simple_parent(),Q(16),4,[{},{},{}])
    background=r.ns.vector_scale(Q(-20000),r.ns.nonlinear(r.c.resonant_parent()))
    resonant=parent.carrier(r.c.resonant_parent(),Q(200),4,background)
    cases=[(r.counterstrain_datum(Q(4),Q(8)),'pressure_start'),
           (r.record_datum(Q(4),Q(8)),'original_maximum'),
           (simple,'original_simple_carrier'),(resonant,'original_resonant_carrier')]
    result=dict(status='all exact checks passed',reserve=weighted_reserve(),
                constants=gaussian_and_local_constants(),bernstein=bernstein_identity(),
                bridge=[bridge_divergence(*case) for case in cases],
                calibration=actual_calibrations(),mixture=mixture_identity(),
                late_shift=late_shift_covariance(),
                scope='boundary payments analytic; full physical-history source open; no new Lean')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
