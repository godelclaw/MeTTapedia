#!/usr/bin/env python3
"""Viscous production of the signed joint geometric observation.

Exact actual cellular flows and a full 3D NS datum test the local diffusion
sign. General parabolic identities, short-interval deductions and integration
of the existing passive-history payment are analytic; see README.md.
"""

import json
import sympy as sp

import signed_impulse_geometry as geometry
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f, r, Q = geometry.f, geometry.r, geometry.Q


def observation(I, w, c, delta, mu=0):
    """Smooth positive branch; callers separately verify its sign."""
    return (-I.cross(w).dot(c))**2/((w.dot(w)+delta)*(c.dot(c)+mu))


def directional_hessian(I, w, c, di, dw, dc, delta, mu=0):
    J = -I.cross(w).dot(c)
    J1 = -(di.cross(w)+I.cross(dw)).dot(c)-I.cross(w).dot(dc)
    J2 = -2*(di.cross(dw).dot(c)+di.cross(w).dot(dc)+I.cross(dw).dot(dc))
    s, d = w.dot(w)+delta, c.dot(c)+mu
    s1, d1 = 2*w.dot(dw), 2*c.dot(dc)
    s2, d2 = 2*dw.dot(dw), 2*dc.dot(dc)
    return ((2*J1*J1+2*J*J2)/(s*d)
            -4*J*J1*(s1/(s*s*d)+d1/(s*d*d))
            -J*J*(s2/(s*s*d)+d2/(s*d*d))
            +2*J*J*(s1*s1/(s*s*s*d)+d1*d1/(s*d*d*d)+s1*d1/(s*s*d*d)))


def chain_square():
    nu, q, eps = sp.symbols('nu q eps', real=True)
    vec = lambda label: sp.Matrix(sp.symbols(label+'0:3', real=True))
    I, b, di, db, kb = [vec(label) for label in ('I', 'b', 'dI', 'db', 'kb')]
    path = -(I+eps*di).dot(b+eps*db+eps**2*kb/2)
    literal = -nu*sp.diff(path**2, eps, 2).subs(eps, 0)
    spatial_q = -di.dot(b)-I.dot(db)
    expected = 2*nu*(-I.dot(b))*I.dot(kb)+4*nu*(-I.dot(b))*di.dot(db)
    expected -= 2*nu*spatial_q**2
    zero(literal-expected, 'literal joint diffusion Hessian')
    zero(4*nu*q*di.dot(db)
         -(2*nu*di.dot(di)+2*nu*q*q*db.dot(db)-2*nu*(di-q*db).dot(di-q*db)),
         'paid impulse-gradient square and retained joint orientation')
    # Pointwise convexification cannot preserve every collinear zero.
    delta, mu = sp.symbols('delta mu', positive=True)
    I = sp.Matrix([-1, 0, 0])
    w1, w2 = sp.Matrix([0, 1, 0]), sp.Matrix([0, 0, 1])
    c1, c2 = w1, 2*w2
    zero(observation(I,w1,c1,delta,mu), 'first aligned zero')
    zero(observation(I,w2,c2,delta,mu), 'second aligned zero')
    middle = observation(I,(w1+w2)/2,(c1+c2)/2,delta,mu)
    zero(middle-1/(16*(delta+sp.Rational(1,2))*(mu+sp.Rational(5,4))),
         'strict convexification gap on joint states')
    return dict(paid_spatial_term='2 nu integral |grad I|^2 <= 4 E0',
                unpaid_orientation='2 nu integral |I|^2 (|b||K_b|+|b|^2|grad b|^2)',
                convexification_gap=str(middle),
                scope='conditional local algebra; actual fields and spatial integration identified analytically')


def cellular_family():
    x, y, z, a, nu, h, delta, mu, eps = sp.symbols(
        'x y z a nu h delta mu eps', positive=True)
    coords = (x,y,z)
    grad = lambda v: sp.Matrix([sp.diff(v,q) for q in coords])
    lap = lambda v: sum(sp.diff(v,q,2) for q in coords)
    curl = lambda v: sp.Matrix([sp.diff(v[2],y)-sp.diff(v[1],z),
        sp.diff(v[0],z)-sp.diff(v[2],x),sp.diff(v[1],x)-sp.diff(v[0],y)])
    u = a*h*sp.Matrix([sp.sin(x)*sp.cos(y),-sp.cos(x)*sp.sin(y),0])
    p = a*a*h*h*(sp.cos(2*x)+sp.cos(2*y))/4
    D = lambda v: -2*nu*h*sp.diff(v,h)+u.dot(grad(v))-nu*lap(v)
    B = u.jacobian(coords)
    w,c = curl(u),curl(curl(u))
    for j in range(3):
        zero(sp.trigsimp(D(u[j])+grad(p)[j]), ('actual unforced cellular PDE',j))
        zero(sp.trigsimp(D(w[j])-(B*w)[j]), ('actual vorticity equation',j))
    Fc = grad(lap(p))-B*c+2*sum((B.diff(q)*u.diff(q) for q in coords),sp.zeros(3,1))
    for j in range(3):
        zero(sp.trigsimp(D(c[j])-Fc[j]), ('actual full curl observer source',j))
    zero(B.trace(), 'cellular incompressibility')
    zero(sp.trigsimp(w.dot(B*w)), 'zero actual stretching for the entire evolution')
    zero(sp.trigsimp(u.cross(w).dot(c)), 'zero full Lamb work for the entire evolution')
    u0,p0=u.subs(h,1),p.subs(h,1)
    H1 = nu*u0.applyfunc(lap)-u0.jacobian(coords)*u0
    u1 = -2*nu*u0
    I1 = (H1-u1).applyfunc(sp.trigsimp)
    for j in range(3):
        zero(sp.trigsimp(I1[j]-grad(p0)[j]), ('original passive pressure impulse',j))
    point={x:sp.pi/4,y:sp.pi/4,z:0}
    fields=[I1,w.subs(h,1),c.subs(h,1)]
    values=[v.subs(point) for v in fields]
    I,w0,c0=values
    zero(-I.cross(w0).dot(c0)-a**4, 'positive actual signed numerator first rate')
    for entry in I1.jacobian(coords).subs(point):
        zero(entry, 'no leading impulse-gradient payment at the receiver')
    hessians=[]
    for q in coords:
        directions=[v.diff(q).subs(point) for v in fields]
        literal=sp.diff(observation(*[v+eps*d for v,d in zip(values,directions)],delta,mu),eps,2).subs(eps,0)
        predicted=directional_hessian(*values,*directions,delta,mu)
        zero(sp.factor(literal-predicted), ('independent literal physical Hessian',q))
        hessians.append(sp.factor(literal))
    coefficient=sp.factor(-sum(hessians))
    raw=sp.factor(coefficient.subs(mu,0))
    expected=2*a**8*(a*a+5*delta)/(a*a+delta)**3
    zero(raw-expected, 'strict positive diffusion source for every a,delta')
    zero(coefficient.subs(delta,a*a)-a**6*(6*a*a+mu)/(2*a*a+mu)**2,
         'positive source survives smooth curl regularization')
    zero(observation(*values,delta)-a**6/(2*(a*a+delta)), 'actual cost first nonzero coefficient')
    # When w=c, the joint direction b is zero throughout every affine
    # spatial variation preserving that equality, including ABC.
    wv=sp.Matrix([1,2,3]); dw=sp.Matrix([2,-1,4]); iv=sp.Matrix([3,2,-1]); di=sp.Matrix([1,-2,3])
    zero(observation(iv+eps*di,wv+eps*dw,wv+eps*dw,delta,mu),
         'joint ABC alignment retains zero cost and zero viscous source')
    return dict(velocity='a exp(-2 nu t) (sin x cos y,-cos x sin y,0)',
                pressure='a^2 exp(-4 nu t) (cos(2x)+cos(2y))/4',
                point='(pi/4,pi/4,0)', signed_numerator_first_rate='a^4',
                cost_leading='a^6 t^2/(2(a^2+delta))',
                viscous_leading='2 nu a^8(a^2+5delta)t^2/(a^2+delta)^3 > 0',
                regularized_coefficient=str(coefficient),
                impulse_gradient='O(t^2); any finite constant times its square contributes only O(t^4)',
                scope='actual entire smooth solution; pressure impulse and short-time signs use the analytic passive PDE')


def three_dimensional_fixture():
    u=r.counterstrain_datum(Q(4),Q(8))
    jets,pressures=velocity_time_jets(u,Q(1),1)
    p=pressures[0]
    f.equal(p,f.green(f.trace(f.matmul(f.jac(u),f.jac(u)))), 'independent full canonical pressure')
    H1=geometry.ph.vector_transport(u,u,Q(1))
    I1=geometry.add(H1,geometry.scale(-1,jets[1]))
    geometry.ph.vectors_equal(I1,f.grad(p),'actual original impulse, no independent source')
    fields=[I1,f.curl(u),f.curl(f.curl(u))]
    point=(0,2,1)
    ev=lambda v:sp.Matrix([r.at(p,point) for p in v])
    values=[ev(v) for v in fields]
    J=sp.simplify(-values[0].cross(values[1]).dot(values[2]))
    zero(J-7424,'positive 3D numerator rate')
    hessians=[]
    eps=sp.symbols('eps',real=True)
    for j in range(3):
        directions=[ev(geometry.derivative(v,j)) for v in fields]
        literal=sp.diff(observation(*[v+eps*d for v,d in zip(values,directions)],sp.Integer(1)),eps,2).subs(eps,0)
        predicted=directional_hessian(*values,*directions,sp.Integer(1))
        zero(sp.simplify(literal-predicted),('full 3D physical Hessian',j))
        hessians.append(literal)
    result=sp.simplify(-sum(hessians))
    zero(result-sp.Rational(42181805312,8214057),'positive 3D viscous production coefficient')
    return dict(point='(0,pi/2,pi/4)',delta=1,signed_numerator_rate=str(J),
                viscous_coefficient=str(result), pressure_modes=len(p),
                scope='actual full unforced 3D datum; analytic local existence supplies the nonzero time interval')


def main():
    print(json.dumps(dict(status='all exact checks passed',joint_square=chain_square(),
        cellular=cellular_family(),three_dimensional=three_dimensional_fixture(),
        scope='local viscous monotonicity refuted; full-datum history allowance remains open; no new Lean'),indent=2))


if __name__=='__main__':
    main()
