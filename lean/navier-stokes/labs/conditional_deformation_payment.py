#!/usr/bin/env python3
"""Conditional deformation projection and original-energy payment.

Weighted elliptic existence, stochastic observation preservation, Nash
smoothing and controlled payments are analytic in README.md. These checks
retain actual NS jets and a nontrivial exact weighted projection.
"""

import json
import sympy as sp

import passive_parent_bellman as parent
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f,Q,r=parent.f,parent.Q,parent.r


def divergence_rows(M):
    return [f.add(*(f.diff(M[i][j],j) for j in range(3))) for i in range(3)]


def physical_divergence(u,label):
    jets,pressure=velocity_time_jets(u,Q(1),1)
    Ht=parent.ph.vector_transport(u,u,Q(1))
    It=[f.add(h,f.scale(-1,v)) for h,v in zip(Ht,jets[1])]
    parent.ph.vectors_equal(It,f.grad(pressure[0]),(label,'actual original pressure generation'))
    for order,(velocity,passive) in enumerate(((u,u),(jets[1],Ht))):
        B=f.jac(velocity)
        transpose=[[B[j][i] for j in range(3)] for i in range(3)]
        parent.ph.vectors_equal(divergence_rows(transpose),[{}, {}, {}],
                                (label,order,'row divergence of transposed physical deformation'))
        BH=f.jac(passive)
        C=[[f.add(BH[i][j],f.scale(-1,transpose[i][j])) for j in range(3)] for i in range(3)]
        parent.ph.vectors_equal(divergence_rows(C),[f.lap(h) for h in passive],
                                (label,order,'pressure and rotation divergence is original passive Laplacian'))
    return dict(fixture=label,pressure_modes=len(pressure[0]),time_jets=2)


def weighted_projection():
    x,y,z=sp.symbols('x y z',real=True)
    coords=(x,y,z)
    u=sp.Matrix([5*sp.sin(y),0,0])
    BT=u.jacobian(coords).T
    q=sp.Rational(64,5)/(5-3*sp.cos(x))**2
    potential=sp.Matrix([0,3*sp.sin(x)*sp.cos(y),0])
    T=potential.jacobian(coords)
    for i in range(3):
        zero(sp.trigsimp(sum(sp.diff(q*(BT[i,j]-T[i,j]),coords[j]) for j in range(3))),
             ('weighted divergence-free residual',i))
        zero(sum(sp.diff(BT[i,j],coords[j]) for j in range(3)),('unweighted transposed divergence',i))
    # Tangent half-angle substitution integrates the entire periodic x circle.
    t=sp.symbols('t',real=True)
    cosine=(1-t*t)/(1+t*t)
    density=sp.Rational(64,5)/(5-3*cosine)**2*2/(1+t*t)
    mass=sp.integrate(density,(t,-sp.oo,sp.oo))/(2*sp.pi)
    first=sp.integrate(cosine*density,(t,-sp.oo,sp.oo))/(2*sp.pi)
    zero(mass-1,'positive receiver has normalized mass one')
    zero(first-sp.Rational(3,5),'receiver first cosine moment')
    rownorm=sum(v*v for v in T)
    ymean=sp.integrate(sp.expand_trig(rownorm),(y,-sp.pi,sp.pi))/(2*sp.pi)
    zero(sp.trigsimp(ymean)-sp.Rational(9,2),'exact nonzero projected norm')
    original_mean=sp.integrate(sum(v*v for v in BT),(y,-sp.pi,sp.pi))/(2*sp.pi)
    zero(original_mean-sp.Rational(25,2),'original weighted and unweighted squared norm')
    cross=sum(BT[i,j]*T[i,j] for i in range(3) for j in range(3))
    cross_mean=sp.integrate(cross,(y,-sp.pi,sp.pi))/(2*sp.pi)
    zero(cross_mean-sp.Rational(15,2)*sp.cos(x),'actual projection cross term')
    zero(sp.Rational(15,2)*first-sp.Rational(9,2),'projection orthogonality retains the exact cross term')
    return dict(receiver='64/[5(5-3cos x)^2]',velocity='(5sin y,0,0)',
                potential='(0,3sin x cos y,0)',projected_norm_sq='9/2',
                original_norm_sq='25/2',
                scope='instantaneous projection fixture with a prescribed smooth receiver; not an actual point kernel')


def constants():
    C,nu,E0,age=sp.symbols('C nu E0 age',positive=True)
    # Fourier splitting leaves half the squared L2 norm above this radius.
    X,m=sp.symbols('X m',positive=True)
    R=(X/(54*m*m))**sp.Rational(1,3)
    zero(27*R**3*m*m-X/2,'Nash low frequency half')
    lower=X*R**2/2
    zero(lower-X**sp.Rational(5,3)/(2*54**sp.Rational(2,3)*m**sp.Rational(4,3)),
         'Nash gradient lower bound')
    Y=54*(sp.Rational(3,2)/(nu*age))**sp.Rational(3,2)
    zero(sp.diff(Y,age)+nu*Y**sp.Rational(5,3)/54**sp.Rational(2,3),
         'Nash differential comparison with its exact constant')
    zero(324-6*54,'kernel prefactor; 3 sqrt(3) < 6')
    L=2+sp.log(4*C)
    zero(2*C*sp.exp(2-L)-sp.Rational(1,2),'uniform mixing threshold')
    z,ell=sp.symbols('z ell',positive=True)
    tail=z*z*sp.exp(-2*(z-ell))/2
    zero(sp.diff(tail,z)-z*(1-z)*sp.exp(-2*(z-ell)),
         'late-age squared weight is decreasing for z>=ell>=2')
    zero(sp.Rational(5,2)**8-1296-sp.Rational(58849,256),
         'exp(1)>5/2 implies log1296<8')
    zero(324*(100+4)/2-16848,'explicit fixed-torus energy allowance')
    zero(sp.Rational(16848,24)-702,'bounded-concentration terminal coefficient')
    # Whole-space transition density bound and the actual dissipation ledger.
    KR=E0*sp.sqrt(age)/(2*nu*(4*sp.pi*nu)**sp.Rational(3,2))
    zero(KR/age/24-E0/(48*nu*(4*sp.pi*nu)**sp.Rational(3,2)*sp.sqrt(age)),
         'whole-space finite-horizon control coefficient')
    a,b=sp.symbols('a b',real=True)
    zero(a*a+b*b-(a+b)**2/2-(a-b)**2/2,'two score contributions and their retained difference')
    theta,alpha=sp.Rational(1,2),sp.Rational(1,24)
    zero(1-2*alpha/theta-sp.Rational(5,6),'Gaussian moment retains the assigned action share')
    zero(1-2*alpha/sp.Rational(1,4)-sp.Rational(2,3),
         'unrestricted reduction pays each term with one quarter of the action')
    zero(alpha/sp.Rational(1,4)-sp.Rational(1,6),
         'remaining exponential acts on the endpoint-conditional mean')
    return dict(torus_kernel_constant=324,torus_variance='<=16848 E0/nu^3',
                torus_control='(3/4)log(6/5)+702 Lrho E0/(nu^3 r)',
                whole_space_variance=str(KR),
                scope='Nash, elliptic and probability inequalities remain analytic')


def main():
    simple=parent.carrier(r.c.simple_parent(),Q(16),4,[{},{},{}])
    background=r.ns.vector_scale(Q(-20000),r.ns.nonlinear(r.c.resonant_parent()))
    resonant=parent.carrier(r.c.resonant_parent(),Q(200),4,background)
    cases=[(r.counterstrain_datum(Q(4),Q(8)),'pressure_start'),
           (r.record_datum(Q(4),Q(8)),'original_maximum'),
           (simple,'original_simple_carrier'),(resonant,'original_resonant_carrier')]
    print(json.dumps(dict(status='all exact checks passed',projection=weighted_projection(),
                         constants=constants(),fixtures=[physical_divergence(*case) for case in cases],
                         scope='actual prefix payments and stochastic preservation analytic; no new Lean certification'),indent=2))


if __name__=='__main__':
    main()
