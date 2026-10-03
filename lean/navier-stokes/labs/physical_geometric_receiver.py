#!/usr/bin/env python3
"""Physical enstrophy receiver and a geometric feedback criterion.

General integration, local existence, passive transport, geometric bounds and
continuation are analytic in README.md. The checker retains complete NS jets,
canonical pressure, and the normalized receiver's mass and reaction.
"""

import json
import sympy as sp

import signed_impulse_geometry as geom
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f,r,Q,pm=geom.f,geom.r,geom.Q,geom.pm


def consumer():
    nu,M,theta,Y,D=sp.symbols('nu M theta Y D',positive=True)
    zero(nu*D+(M+sp.sqrt(theta))**2*Y/nu-2*sp.sqrt(Y*D)*(M+sp.sqrt(theta))
         -(sp.sqrt(nu*D)-(M+sp.sqrt(theta))*sp.sqrt(Y/nu))**2,
         'geometric mass retains half of physical dissipation')
    zero(2*(M*M+theta)-(M+sp.sqrt(theta))**2-(M-sp.sqrt(theta))**2,
         'explicit coefficient for the finite geometric budget')
    q,g,zeta,exponent=sp.symbols('q g zeta exponent',real=True)
    rateY=2*g-2*nu*D
    reserve=(sp.exp(exponent)-1)*Y
    rate=sp.diff(reserve,Y)*rateY-q*sp.diff(reserve,exponent)
    gap=q*Y-(rateY+nu*D)
    zero(rate+2*g-nu*D+sp.exp(exponent)*gap+nu*(sp.exp(exponent)-1)*D,
         'nonnegative reserve with one original geometric allowance')
    # Keep the passive contribution linear when testing feedback absorption.
    d=sp.symbols('d',nonnegative=True)
    zero(theta/nu+nu*d-2*sp.sqrt(theta*d)
         -(sp.sqrt(theta/nu)-sp.sqrt(nu*d))**2,
         'feedback leaves the passive parent uncombined')
    k,T,x=sp.symbols('k T x',positive=True) # k=1-alpha, x=sqrt(int d)
    zero(k*nu*x*x-2*M*sp.sqrt(T)*x+M*M*T/(k*nu)
         -k*nu*(x-M*sp.sqrt(T)/(k*nu))**2,
         'sharp scalar completion for the enstrophy envelope')
    zero(k*nu*x*x/2+2*M*M*T/(k*nu)-2*M*sp.sqrt(T)*x
         -(sp.sqrt(k*nu/2)*x-sp.sqrt(2/(k*nu))*M*sp.sqrt(T))**2,
         'finite normalized-dissipation allowance')
    # The history feedback itself gives a nonnegative logarithmic reserve.
    gap=sp.symbols('gap',nonnegative=True)
    Lprime=2*(M+sp.sqrt(theta))*sp.sqrt(d)-2*nu*d-gap
    Cprime=theta-(1-k)*nu*nu*d
    reserve_prime=Lprime-Cprime/nu-2*M*M/(k*nu)
    theta_square=(sp.sqrt(theta/nu)-sp.sqrt(nu*d))**2
    parent_square=(sp.sqrt(k*nu/2)*sp.sqrt(d)-sp.sqrt(2/(k*nu))*M)**2
    zero(reserve_prime+k*nu*d/2+gap+theta_square+parent_square,
         'complete logarithmic reserve pays actual normalized dissipation')
    B0,L0=sp.symbols('B0 L0',nonnegative=True)
    Qstar=2*(L0+B0/nu+2*M*M*T/(k*nu))/(k*nu)
    zero(k*nu*Qstar/2-(L0+B0/nu+2*M*M*T/(k*nu)),
         'explicit normalized-dissipation constant')
    return dict(geometric='Y_prime+nu D <= 2(M^2+Theta)Y/nu',
        feedback='integral Theta <= alpha nu^2 integral(D/Y)+B0, 0<=alpha<1',
        envelope='Y <= Y0 exp((B0+M^2 T/(1-alpha))/nu)',
        normalized_dissipation='Qstar=2[log(Y0/zeta)+B0/nu+2M^2 T/((1-alpha)nu)]/((1-alpha)nu)',
        scope='conditional physical consumer; neither original-data geometric budget is proved')


def actual_receiver(u0,label):
    nu=Q(1)
    jets,pressures=velocity_time_jets(u0,nu,2)
    u,u1,u2=jets
    w,w1,w2=[f.curl(v) for v in jets]
    B,B1=f.jac(u),f.jac(u1)
    e=f.dot(w,w)
    e1=f.scale(2,f.dot(w,w1))
    e2=f.scale(2,f.add(f.dot(w1,w1),f.dot(w,w2)))
    Z,Z1,Z2=[pm.mean(v) for v in (e,e1,e2)]
    if Z<=0:raise ArithmeticError('Physical receiver fixture needs positive enstrophy')
    zeta=Z;Y=Z+zeta
    rho=f.scale(1/Y,e)
    rho1=f.add(f.scale(1/Y,e1),f.scale(-Z1/(Y*Y),e))
    rho2=f.add(f.scale(1/Y,e2),f.scale(-2*Z1/(Y*Y),e1),
        f.scale(-Z2/(Y*Y)+2*Z1*Z1/(Y**3),e))
    dw=[geom.derivative(w,j) for j in range(3)]
    dw1=[geom.derivative(w1,j) for j in range(3)]
    gradient=f.add(*(f.dot(v,v) for v in dw))
    gradient1=f.scale(2,f.add(*(f.dot(v,v1) for v,v1 in zip(dw,dw1))))
    stretch=f.dot(w,f.matvec(B,w))
    stretch1=f.add(f.dot(w1,f.matvec(B,w)),f.dot(w,f.matvec(B1,w)),f.dot(w,f.matvec(B,w1)))
    source=f.scale(2,f.add(stretch,f.scale(-nu,gradient)))
    source1=f.scale(2,f.add(stretch1,f.scale(-nu,gradient1)))
    f.equal(f.add(e1,f.adv(u,e),f.scale(-nu,f.lap(e))),source,
            (label,'literal physical squared-vorticity source'))
    if pm.mean(source)!=Z1 or pm.mean(source1)!=Z2:
        raise ArithmeticError((label,'whole-flow normalization rate'))
    rate=Z1/Y;rate1=Z2/Y-Z1*Z1/(Y*Y)
    predicted=f.add(f.scale(1/Y,source),f.scale(-rate,rho))
    actual=f.add(rho1,f.adv(u,rho),f.scale(-nu,f.lap(rho)))
    f.equal(actual,predicted,(label,'physical receiver retains reaction and normalization'))
    predicted1=f.add(f.scale(1/Y,source1),f.scale(-Z1/(Y*Y),source),
        f.scale(-rate1,rho),f.scale(-rate,rho1))
    actual1=f.add(rho2,f.adv(u1,rho),f.adv(u,rho1),f.scale(-nu,f.lap(rho1)))
    f.equal(actual1,predicted1,(label,'first evolving receiver identity with full pressure'))
    atom=zeta/Y;atom1=-zeta*Z1/(Y*Y);atom2=-zeta*Z2/(Y*Y)+2*zeta*Z1*Z1/(Y**3)
    if pm.mean(rho)+atom!=1 or pm.mean(rho1)+atom1!=0 or pm.mean(rho2)+atom2!=0:
        raise ArithmeticError((label,'retained atom and physical density fail to preserve total mass'))
    if not predicted:raise ArithmeticError((label,'receiver must not accidentally be passive'))
    # Independent pointwise decomposition of its Fisher and direction costs.
    point=(0,1,0)
    ev=lambda p:r.at(p,point)
    wp=sp.Matrix([ev(p) for p in w]);evalue=wp.dot(wp)
    if evalue<=0:raise ArithmeticError('Fisher fixture needs nonzero vorticity')
    Ysp=sp.Rational(str(Y))
    rawD=0;radial=0;angular=0
    for j,v in enumerate(dw):
        v=sp.Matrix([ev(p) for p in v]);dot=wp.dot(v)
        zero(ev(f.diff(e,j))-2*dot,(label,'literal density gradient'))
        rawD+=v.dot(v)/Ysp
        radial+=dot**2/(evalue*Ysp)
        angular+=(evalue*v.dot(v)-dot**2)/(evalue*Ysp)
    zero(rawD-radial-angular,(label,'normalized dissipation pays concentration and orientation'))
    return dict(fixture=label,pressure_modes=[len(p) for p in pressures],
        initial_enstrophy=str(Z),zeta=str(zeta),receiver_reaction_modes=len(predicted),
        receiver_reaction_at_origin=str(f.evaluate(predicted)),
        initial_fluid_mass=str(pm.mean(rho)),initial_retained_atom=str(atom),
        receiver_identity_derivatives=2,
        scope='complete actual NS jets; no independently selectable density or projected evolution')


def eigenflow_payments():
    nu,k,M,Z0,zeta,t=sp.symbols('nu k M Z0 zeta t',positive=True)
    Z=Z0*sp.exp(-2*nu*k*k*t)
    budget=M*M/(2*nu*k*k)*sp.log((Z0+zeta)/(Z+zeta))
    dissipation=sp.log((Z0+zeta)/(Z+zeta))/(2*nu)
    zero(sp.diff(budget,t)-M*M*Z/(Z+zeta),'entire eigenflow history has a finite geometric payment')
    zero(sp.diff(dissipation,t)-k*k*Z/(Z+zeta),'same normalized diffusion is spent once')
    zero(budget.subs(t,0),'no original expenditure')
    zero(dissipation.subs(t,0),'no original normalized dissipation')
    return dict(geometric_bound='M^2/(2 nu k^2) log((Z0+zeta)/(Z0 exp(-2nu k^2t)+zeta))',
        all_time_bound='M^2/(2nu k^2) log(1+Z0/zeta)',
        normalized_dissipation='log((Z0+zeta)/(Z(t)+zeta))/(2nu)',
        ABC='zero geometric cost, exactly',
        scope='known exact steady-Euler Laplacian eigenflow families; actual original passive H retained')


def main():
    cases=[(r.counterstrain_datum(Q(4),Q(8)),'pressure_start'),
           (r.record_datum(Q(4),Q(8)),'original_maximum')]
    print(json.dumps(dict(status='all exact checks passed',consumer=consumer(),
        receiver=[actual_receiver(*case) for case in cases],eigenflows=eigenflow_payments(),
        scope='analytic sufficient physical-receiver targets and calibrations; arbitrary-data payment OPEN; no new Lean'),indent=2))


if __name__=='__main__':
    main()
