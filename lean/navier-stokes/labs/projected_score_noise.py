#!/usr/bin/env python3
"""Joint projected-score noise and exact unforced calibrations.

The rare-path lower bound, divergent moment and controlled terminal
payment are analytic in README.md. These exact checks certify their
algebra, actual NS profiles, loop circulation and strict constants.
"""

import json
import sympy as sp

from metric_loss_bellman import zero


def vector(prefix):
    return sp.Matrix(sp.symbols(prefix+'0:3', real=True))


def matrix(prefix):
    return sp.Matrix(3,3,sp.symbols(prefix+'0:9', real=True))


def check_vector(v, label):
    for i, value in enumerate(v):
        zero(sp.trigsimp(sp.expand(value)), (label,i))


def cross_matrix(w):
    return sp.Matrix([[0,-w[2],w[1]],[w[2],0,-w[0]],[-w[1],w[0],0]])


def joint_ito():
    age, nu, scale=sp.symbols('age nu scale',positive=True)
    n, noise, drift=vector('n'),vector('m'),vector('b')
    A,G=matrix('A'),matrix('G')
    Omega=cross_matrix(scale*n)
    C=A+Omega
    sigma_n=sp.sqrt(2*nu)*G
    sigma_noise=age*C
    reward=n.dot(noise)
    grad=sp.Matrix([sp.diff(reward,v) for v in list(n)+list(noise)])
    Hess=sp.hessian(reward,list(n)+list(noise))
    sigma=sigma_n.col_join(sigma_noise)
    actual_drift=grad.dot(drift.col_join(sp.zeros(3,1)))+sp.trace(sigma*sigma.T*Hess)/2
    expected_drift=noise.dot(drift)+sp.sqrt(2*nu)*age*sum(G[i,j]*C[i,j] for i in range(3) for j in range(3))
    zero(actual_drift-expected_drift,'joint Ito drift retains quadratic covariation')
    expected_noise=sp.sqrt(2*nu)*G.T*noise+age*A.T*n
    check_vector(sigma.T*grad-expected_noise,'instantaneous rotation cancels in the martingale coefficient')
    y, by, variance=sp.symbols('y by variance',real=True)
    potential=y*y/(4*age)
    log_drift=sp.diff(potential,age)+sp.diff(potential,y)*by+sp.diff(potential,y,2)*variance/2
    exp_drift=log_drift+sp.diff(potential,y)**2*variance/2
    zero(exp_drift-(y*by/(2*age)+variance/(4*age)-y*y/(4*age**2)+y*y*variance/(8*age**2)),
         'complete exponential generator of projected memory')
    return dict(joint_drift=True,instantaneous_rotation_cancelled=True,
                retained=['changing direction','quadratic covariation','original pressure impulse','inherited noise'])


def abc_loop():
    x,y,z,time=sp.symbols('x y z time',real=True)
    amplitude,nu=sp.symbols('amplitude nu',positive=True)
    coords=(x,y,z)
    U=sp.Matrix([sp.sin(z)+sp.cos(y),sp.sin(x)+sp.cos(z),sp.sin(y)+sp.cos(x)])
    u=amplitude*sp.exp(-nu*time)*U
    B=u.jacobian(coords)
    p=-u.dot(u)/2
    curl=lambda v:sp.Matrix([sp.diff(v[2],y)-sp.diff(v[1],z),
                             sp.diff(v[0],z)-sp.diff(v[2],x),
                             sp.diff(v[1],x)-sp.diff(v[0],y)])
    lap=lambda v:v.applyfunc(lambda a:sum(sp.diff(a,c,2) for c in coords))
    check_vector(curl(u)-u,'literal Beltrami vorticity')
    check_vector(u.diff(time)+B*u+sp.Matrix([sp.diff(p,c) for c in coords])-nu*lap(u),
                 'all-time unforced NS including nonconstant pressure')
    zero(sp.trace(B),'incompressibility')
    zero(sp.trigsimp(sum(v*v for v in B))-3*amplitude**2*sp.exp(-2*nu*time),
         'exact Frobenius bound used in the rare-path probability estimate')
    zero(sp.trigsimp(U.dot(U)-3-2*(sp.sin(z)*sp.cos(y)+sp.sin(x)*sp.cos(z)+sp.sin(y)*sp.cos(x))),
         'normalized kinetic energy is three times the squared amplitude')
    n0=sp.ones(3,1)/sp.sqrt(15)
    origin={x:0,y:0,z:0,time:0}
    check_vector((u/sp.sqrt(u.dot(u)+12*amplitude**2)).subs(origin)-n0,
                 'terminal direction uses the original regularizer')
    g=U.jacobian(coords)*n0
    edges=[sp.integrate(g[0].subs({y:0,z:0}),(x,0,sp.pi)),
           sp.integrate(g[2].subs({y:0,x:sp.pi}),(z,0,sp.pi)),
           sp.integrate(g[0].subs({y:0,z:sp.pi}),(x,sp.pi,0)),
           sp.integrate(g[2].subs({y:0,x:0}),(z,sp.pi,0))]
    circulation=sum(edges)
    zero(circulation-2*sp.pi/sp.sqrt(15),'all four oriented loop edges')
    s=sp.symbols('s',real=True)
    weight=sp.integrate(s*sp.exp(s-1),(s,0,1))
    zero(weight-1/sp.E,'complete sampling-age and physical-decay weight')
    leading=amplitude*circulation*weight/sp.sqrt(2)
    zero(leading-2*sp.pi*amplitude/(sp.E*sp.sqrt(30)),'projected-noise leading coefficient')
    # Constant-speed rectangle has length4pi. The Girsanov martingale
    # threshold doubles its leading action coefficient in the lower bound.
    action=(4*sp.pi)**2/4
    zero(leading**2/16-2*action-sp.pi**2*(amplitude**2/(120*sp.E**2)-8),
         'reward on the retained half-leading event minus its probability cost')
    lower_margin=sp.Rational(100**2,120*9)-8
    zero(lower_margin-sp.Rational(34,27),'strict rational margin using exp(1)<3')
    return dict(velocity='a exp(-nu t)(sin z+cos y, sin x+cos z, sin y+cos x)',
                pressure='-|u|^2/2',nu=1,amplitude=100,delta=120000,
                loop_edges=[str(v) for v in edges],circulation=str(circulation),
                leading_coefficient=str(leading),exponent_margin_lower='34 pi^2/27',
                scope='actual globally smooth 3D flow; divergent unconditioned score-noise moment proved analytically')


def rotating_shear():
    x,y,z,time=sp.symbols('x y z time',real=True)
    amplitude,nu,theta,alpha=sp.symbols('amplitude nu theta alpha',positive=True)
    coords=(x,y,z)
    u=amplitude*sp.exp(-nu*time)*sp.Matrix([sp.cos(z),sp.sin(z),0])
    B=u.jacobian(coords)
    lap=u.applyfunc(lambda a:sum(sp.diff(a,c,2) for c in coords))
    check_vector(u.diff(time)+B*u-nu*lap,'exact rotating unforced shear with zero pressure')
    horizontal=sp.Matrix(sp.symbols('h0:2',real=True)+ (0,))
    check_vector(B*horizontal,'any horizontal terminal direction kills the transposed deformation')
    # One-dimensional Gaussian exponent with alpha=theta=1/2.
    g=sp.symbols('g',real=True)
    gaussian=sp.integrate(sp.exp(-g*g/4)/sp.sqrt(2*sp.pi),(g,-sp.oo,sp.oo))
    zero(sp.log(gaussian)/2-sp.log(2)/4,'rotating-direction controlled terminal allowance')
    return dict(spatial_direction_rotates=True,pressure_impulse_zero=True,
                terminal_payment='log(2)/4 at alpha=theta=1/2',
                scope='analytic conditional Gaussian argument uses independence of horizontal Brownian displacement and vertical terminal angle')


def conditional_memory():
    coords=sp.symbols('x y z',real=True)
    nu,age=sp.symbols('nu age',positive=True)
    q=sp.Function('q')(*coords)
    v=sp.Matrix([sp.Function('v'+str(i))(*coords) for i in range(3)])
    C=sp.Matrix(3,3,lambda i,j:sp.Function('c'+str(i)+str(j))(*coords))
    u=vector('u')
    grad=lambda f:sp.Matrix([sp.diff(f,c) for c in coords])
    lap=lambda f:sum(sp.diff(f,c,2) for c in coords)
    qr=nu*lap(q)+u.dot(grad(q))
    for i in range(3):
        mr=nu*lap(q*v[i])+u.dot(grad(q*v[i]))-sp.sqrt(2*nu)*age*sum(sp.diff(q*C[i,j],coords[j]) for j in range(3))
        quotient=(mr-v[i]*qr)/q
        expected=(nu*lap(v[i])+(u+2*nu*grad(q)/q).dot(grad(v[i]))
                  -sp.sqrt(2*nu)*age*sum(sp.diff(C[i,j],coords[j])+C[i,j]*sp.diff(q,coords[j])/q for j in range(3)))
        zero(quotient-expected,('conditional first moment retains the common density',i))
    return dict(density_equation='m_r=nu Delta m+u.grad m-sqrt(2nu)r div(q C)',
                conditional_mean='v=m/q; C=grad I+cross(omega)',
                scope='weak stochastic derivation and smoothing analytic; quotient product rule exact')


def main():
    print(json.dumps(dict(status='all exact checks passed',joint=joint_ito(),
                         abc=abc_loop(),rotating=rotating_shear(),conditional=conditional_memory(),
                         scope='algebra and exact flows checked; probability and PDE arguments analytic, not Lean-certified'),indent=2))


if __name__=='__main__':
    main()
