#!/usr/bin/env python3
"""Exact physical covector/HJB identities and their paid spatial mean.

The pressure, drift and covector belong to the same unforced fluid.
Full Fourier jets test interacting data without discarding any outputs;
the shear check is an exact positive-time solution. The analytic control
verification and the remaining derivative-level estimate are in README.md.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
from cyclic_pressure_history import velocity_time_jets
from covector_fluid_bridge import covector_rhs, projection, vector_add, vector_scale
from pressure_impulse_history import vectors_equal
from signed_viscous_pressure import interacting_datum


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(value, label):
    entries = list(value) if isinstance(value, s.MatrixBase) else [value]
    require(all(s.simplify(s.expand_trig(v)) == 0 for v in entries), label)


def half_square(v):
    return f.scale(f.QQ_I(1)/2, f.dot(v, v))


def fourier_case(phase, nu):
    u = vector_scale(phase, interacting_datum())
    U, P = velocity_time_jets(u, nu, 2)
    nuq = f.QQ_I(nu)
    B = f.jac(u)
    # The canonical lift starts with S=0, m=u, with no new fluid force.
    S1 = f.add(half_square(u), f.scale(-1, P[0]))
    S2 = f.add(f.scale(nuq, f.lap(S1)), f.scale(-1, f.adv(u, S1)),
               f.dot(u, U[1]), f.scale(-1, P[1]))
    m1 = vector_add(U[1], vector_scale(-1, f.grad(S1)))
    m2 = vector_add(U[2], vector_scale(-1, f.grad(S2)))
    vectors_equal(m1, covector_rhs(nuq, u, B, u), 'canonical first covector jet')
    expected_m2 = vector_add(covector_rhs(nuq, u, B, m1),
        vector_scale(-1, [f.adv(U[1], a) for a in u]),
        vector_scale(-1, f.matvec(pm.transpose(f.jac(U[1])), u)))
    vectors_equal(m2, expected_m2, 'full evolving covector jet with pressure')
    for m, v in ((m1, U[1]), (m2, U[2])):
        vectors_equal(projection(m), v, 'physical projected evolution')
        vectors_equal(f.curl(m), f.curl(v), 'physical curl retains all outputs')
    f.equal(f.add(S2, f.scale(-nuq, f.lap(S1))),
            f.add(f.dot(u, m1), f.scale(-1, P[1])), 'evolving HJB equation')

    # An arbitrary nonconstant gauge tests the full instantaneous operator,
    # not only its canonical initial value. It is not a reset of that history.
    S = P[0]
    g = f.grad(S)
    m = vector_add(u, vector_scale(-1, g))
    St = f.add(f.scale(nuq, f.lap(S)), f.scale(-1, f.adv(u, S)), S1)
    mt = vector_add(U[1], vector_scale(-1, f.grad(St)))
    vectors_equal(mt, covector_rhs(nuq, u, B, m), 'nonzero gauge covector identity')
    f.equal(f.add(St, f.scale(-nuq, f.lap(S)), half_square(g)),
            f.add(half_square(m), f.scale(-1, P[0])), 'full physical HJB source')
    E = pm.mean(f.dot(u, u))
    d = pm.mean(pm.pair(B, B))
    require(pm.mean(St) == E/2 and pm.mean(S1) == E/2,
            'mean HJB rate equals physical kinetic energy divided by two')
    require(pm.mean(S2) == -nuq.x*d, 'differentiated mean uses actual viscosity')
    require(pm.mean(f.dot(m, m))-pm.mean(f.dot(g, g)) == E,
            'hidden-gradient and control-square mean cancellation')
    source = vector_add(f.matvec(pm.transpose(B),m),vector_scale(-1,f.grad(P[0])))
    gradient_cost = pm.mean(pm.pair(f.jac(g),f.jac(g)))
    require(pm.mean(f.dot(g,f.grad(St))) == pm.mean(f.dot(g,source))-nuq.x*gradient_cost,
            'complete integrated gradient production keeps pressure and diffusion')
    initial_gradient_acceleration = 2*pm.mean(f.dot(f.grad(S1),f.grad(S1)))
    require(initial_gradient_acceleration > 0,
            'nontrivial canonical gradient history despite initially zero gradient')

    # A solenoidal fluid force survives this bridge; it cannot become gauge.
    force = f.curl(u)
    require(any(force) and any(f.curl(force)), 'non-gradient diagnostic force')
    forced_mt = vector_add(U[1], force, vector_scale(-1, f.grad(St)))
    vectors_equal(vector_add(forced_mt, vector_scale(-1, covector_rhs(nuq,u,B,m))),
                  force, 'exact forced defect retained')
    vectors_equal(projection(force), force, 'fluid force survives projection')
    return {'phase':phase, 'nu':str(nu), 'energy':str(E),
            'mean_S_rate':str(E/2), 'mean_S_second_rate':str(-nuq.x*d),
            'initial_gradient_square_second_rate':str(initial_gradient_acceleration),
            'nonzero_gauge_modes':len(S), 'NS_jet_modes':[
                len(set().union(*(component.keys() for component in v))) for v in U],
            'scope':'exact full initial NS jets and gauge operator identities'}


def shear():
    y,t=s.symbols('y t', real=True)
    A,nu=s.symbols('A nu', positive=True)
    a=A*s.exp(-nu*t)
    S=A**2/(8*nu)*(1-s.exp(-2*nu*t)
                     -(s.exp(-2*nu*t)-s.exp(-4*nu*t))*s.cos(2*y))
    u=s.Matrix([a*s.sin(y),0,0])
    g=s.Matrix([0,s.diff(S,y),0])
    m=u-g
    B=s.Matrix([[0,a*s.cos(y),0],[0,0,0],[0,0,0]])
    zero(S.subs(t,0),'canonical shear potential initially zero')
    zero(m.subs(t,0)-u.subs(t,0),'canonical original covector')
    zero(u.diff(t)-nu*u.diff(y,2),'complete unforced shear equation')
    zero(m.diff(t)-nu*m.diff(y,2)+B.T*m,'complete covector shear equation')
    V=m.dot(m)/2
    zero(s.diff(S,t)-nu*s.diff(S,y,2)+g.dot(g)/2-V,'actual all-time HJB')
    # Verify the positive transform without simplifying a nested exponential.
    # (Phi_t-nu Delta Phi)/Phi=-S_t/(2nu)+Delta S/2-|grad S|^2/(4nu).
    transformed=-s.diff(S,t)/(2*nu)+s.diff(S,y,2)/2-g.dot(g)/(4*nu)
    zero(transformed+V/(2*nu),'Cole-Hopf retains the internal potential')
    mean_S=A**2*(1-s.exp(-2*nu*t))/(8*nu)
    zero(s.integrate(S,(y,-s.pi,s.pi))/(2*s.pi)-mean_S,'literal spatial mean')
    zero(s.diff(mean_S,t)-a*a/4,'physical mean action rate')
    return {'potential_S':str(S),'covector_transverse_component':str(s.factor(m[1])),
            'mean_action':str(mean_S),'scope':'exact unforced periodic shear for all t>=0'}


def pressure_sign():
    x,y,t=s.symbols('x y t', real=True)
    A,nu=s.symbols('A nu', positive=True)
    a=A*s.exp(-2*nu*t)
    u=s.Matrix([a*s.sin(x)*s.cos(y),-a*s.cos(x)*s.sin(y),0])
    p=a*a*(s.cos(2*x)+s.cos(2*y))/4
    B=u.jacobian([x,y,s.Symbol('z')])
    zero(u.diff(t)+B*u-nu*(u.diff(x,2)+u.diff(y,2))+
         s.Matrix([s.diff(p,x),s.diff(p,y),0]),'complete Taylor-Green unforced equation')
    V0=(u.dot(u)/2-p).subs(t,0)
    zero(V0.subs({x:0,y:0})+A*A/2,'negative canonical initial HJB source')
    return {'mean_zero_pressure':str(p), 'initial_source_at_origin':'-A**2/2',
            'scope':'raw canonical HJB value is not a nonnegative reserve; time gauge changes this sign'}


def scalar_payment():
    h,E,d,nu=s.symbols('h E d nu', nonnegative=True)
    R=h*E/2
    rate=-s.diff(R,h)-2*nu*d*s.diff(R,E)
    zero(rate+E/2+nu*h*d,'finite-horizon mean action payment')
    q=s.Matrix(s.symbols('q0:3',real=True))
    a=s.Matrix(s.symbols('a0:3',real=True))
    zero(a.dot(q)+a.dot(a)/2+q.dot(q)/2-(a+q).dot(a+q)/2,
         'exact auxiliary-control Bellman square')
    return {'remaining_reserve':'(H-t)*E(t)/2', 'rate':'-E(t)/2-nu*(H-t)*||grad u||_2^2',
            'optimizer':'auxiliary drift -grad S, not the fluid drift',
            'scope':'pays signed spatial-mean HJB action, not its gradients or cubic stretching'}


def main():
    print(json.dumps({'shear':shear(), 'pressure_sign':pressure_sign(),
        'scalar_payment':scalar_payment(),
        'interacting_cases':[fourier_case(phase,nu) for phase in (-1,1)
                             for nu in (Q(1,10),Q(1))],
        'scope':'exact checks; continuous stochastic/control verification remains analytic'},indent=2))


if __name__=='__main__':
    main()
