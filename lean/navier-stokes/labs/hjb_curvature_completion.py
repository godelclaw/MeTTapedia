#!/usr/bin/env python3
"""Physical HJB curvature completion and a positive-viscosity shear test.

Exact full NS jets verify the pressure cancellation and its retained source.
An exact coherent limit and explicit Brownian-moment error bounds test a
fixed-coefficient Bellman candidate on actual unforced shear histories.
The stochastic estimates are analytic in README.md, not numerical samples.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
from cyclic_pressure_history import velocity_time_jets
from covector_fluid_bridge import vector_add, vector_scale
from pressure_impulse_history import matrix_transport
from signed_viscous_pressure import interacting_datum


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(value, label):
    entries=list(value) if isinstance(value,s.MatrixBase) else [value]
    require(all(s.simplify(s.expand_trig(v))==0 for v in entries),label)


def curvature_source(m,u):
    return [[f.add(*(f.mul(m[k],f.diff(f.diff(u[k],i),j))
                    for k in range(3))) for j in range(3)] for i in range(3)]


def matrix_rate(nu,u,B,A):
    return pm.matrix_add(matrix_transport(u,A,nu),
        pm.matrix_scale(-1,f.matmul(pm.transpose(B),A)),
        pm.matrix_scale(-1,f.matmul(A,B)))


def actual_jets(phase):
    nu=f.QQ_I(1)/10
    u=vector_scale(phase,interacting_datum())
    U,P=velocity_time_jets(u,Q(1,10),2)
    B,B1=f.jac(u),f.jac(U[1])
    A1=matrix_rate(nu,u,B,B)
    A2=pm.matrix_add(matrix_rate(nu,u,B,A1),
        pm.matrix_scale(-1,pm.matrix_adv(U[1],B)),
        pm.matrix_scale(-1,f.matmul(pm.transpose(B1),B)),
        pm.matrix_scale(-1,f.matmul(B,B1)))
    S1=f.add(f.scale(f.QQ_I(1)/2,f.dot(u,u)),f.scale(-1,P[0]))
    S2=f.add(f.scale(nu,f.lap(S1)),f.scale(-1,f.adv(u,S1)),
             f.dot(u,U[1]),f.scale(-1,P[1]))
    m1=vector_add(U[1],vector_scale(-1,f.grad(S1)))
    K1=pm.matrix_add(A1,pm.matrix_scale(-1,B1),f.hess(S1))
    K2=pm.matrix_add(A2,pm.matrix_scale(-1,f.jac(U[2])),f.hess(S2))
    f.same_matrices(K1,curvature_source(u,u),'initial physical curvature source')
    expected=pm.matrix_add(matrix_rate(nu,u,B,K1),
                           curvature_source(m1,u),curvature_source(u,U[1]))
    f.same_matrices(K2,expected,'complete evolving source retains every parent')
    f.same_matrices(K1,pm.transpose(K1),'symmetric first curvature jet')
    f.same_matrices(K2,pm.transpose(K2),'symmetric second curvature jet')
    require(pm.mean(pm.pair(K1,K1))>0,'nontrivial curvature source')
    return {'phase':phase,'nu':'1/10',
            'source_square':str(pm.mean(pm.pair(K1,K1))),
            'scope':'complete initial NS jets, not a closed mode system'}


def shear_pde():
    y,t=s.symbols('y t',real=True)
    a,nu=s.symbols('a nu',positive=True)
    q=s.exp(-nu*t)
    S=a*a/(8*nu)*(1-q*q-(q*q-q**4)*s.cos(2*y))
    u=s.Matrix([a*q*s.sin(y),0,0])
    m=u-s.Matrix([0,s.diff(S,y),0])
    B=s.zeros(3); B[0,1]=a*q*s.cos(y)
    A=s.zeros(3); A[0,1]=B[0,1]
    A[1,1]=-a*a/(4*nu)*(1-q*q+(q*q-q**4)*s.cos(2*y))
    gradm=s.zeros(3)
    for i in range(3): gradm[i,1]=s.diff(m[i],y)
    K=A-gradm
    expected=s.zeros(3); expected[1,1]=-2*S
    zero(K-expected,'literal original-packet minus covector-gradient curvature')
    zero(A.diff(t)-nu*A.diff(y,2)+B.T*A+A*B,'full original packet equation')
    source=s.zeros(3); source[1,1]=m[0]*s.diff(u[0],y,2)
    zero(K.diff(t)-nu*K.diff(y,2)+B.T*K+K*B-source,'full pressure-free curvature equation')
    zero(source[1,1]+a*a*q*q*s.sin(y)**2,'nonzero retained parent-Hessian source')
    omega=s.Matrix([0,0,-a*q*s.cos(y)])
    zero((omega.T*B*omega)[0],'identically zero physical cubic stretching')
    diss=s.integrate(omega.diff(y).dot(omega.diff(y)),(y,-s.pi,s.pi))/(2*s.pi)
    zero(diss-a*a*q*q/2,'literal physical vorticity dissipation')
    zero(s.diff(a*a*q*q/4,t)+nu*diss,'exact signed renewal cost primitive')
    return {'curvature_K_yy':str(s.factor(K[1,1])),
            'source_yy':'-a**2*exp(-2*nu*t)*sin(y)**2',
            'physical_cubic_stretching':'0','scope':'exact all-time unforced viscous shear'}


def joint_metric_limit():
    y,tau=s.symbols('y tau',real=True)
    b=tau*s.cos(y)
    F=s.Matrix([[1,-b,0],[0,1,0],[0,0,1]])
    G=F.T*F; H=G.inv()
    B=s.zeros(3); B[0,1]=s.cos(y)
    A=F.T*B*F
    K=s.zeros(3); K[1,1]=-tau*s.sin(y)**2
    pair=lambda T:s.trace(H*T*H*T.T)
    zero(F.det()-1,'volume preservation')
    zero(pair(A)-s.cos(y)**2,'paid original tensor norm in coherent limit')
    zero(pair(K)-tau*tau*s.sin(y)**4,'curvature energy in the same joint metric')
    zero(s.integrate(pair(A),(y,-s.pi,s.pi))/(2*s.pi)-s.Rational(1,2),
         'integrated original norm')
    zero(s.integrate(pair(K),(y,-s.pi,s.pi))/(2*s.pi)-3*tau*tau/8,
         'integrated curvature energy')
    return {'Q_A_over_a_squared':'1/2', 'Q_K_over_a_squared':'3*tau**2/8',
            'scope':'coherent limit; positive viscosity justified by explicit error bounds'}


def error_bounds():
    b,c=s.symbols('b c',real=True)
    F=lambda z:s.Matrix([[1,-z,0],[0,1,0],[0,0,1]])
    G=lambda z:F(z).T*F(z)
    zero(F(b).inv().T*s.Matrix([0,0,1])-s.Matrix([0,0,1]),
         'every actual shear frame preserves the physical curl direction')
    delta=G(b)-G(c)
    zero(6*(b-c)**2-s.trace(delta.T*delta)-(b-c)**2*(4-(b+c)**2),
         'matrix Lipschitz bound for |b|,|c|<=1')
    require(9**2*24==1944,'inverse joint-metric perturbation constant')
    require(9*4*3+2*1944==3996 and 3996<=4000,'original tensor cost error')
    require(9*2*2+1944==1980 and 1980<=2000,'curvature cost error')
    a,nu,h,beta=s.symbols('a nu h beta',positive=True)
    decay=s.exp(-2*nu/a)
    paid=(beta*(h-1/a)*a*a*decay/4-beta*h*a*a/4-a*a*(1-decay)/4)/(a*a)
    zero(paid+(beta*h+1)*(1-decay)/4+beta*decay/(4*a),
         'exact physical dissipation and mean-action credit')
    # The analytic bounds use epsilon=nu/a<=1 at tau=1. For alpha>0,
    # beta>=0, the normalized Bellman defect is at least
    # 3alpha/8-(4000+2000alpha)sqrt(nu/a)-L/a.
    alpha,beta,nu,h=map(Q,(1,1,1,1))
    amplitude=Q(10**10)
    L=beta*(h*nu/2+Q(1,4))+nu/2
    lower=3*alpha/8-(4000+2000*alpha)*Q(1,10**5)-L/amplitude
    require(lower>Q(1,8),'strict positive-viscosity signed-budget defect')
    return {'epsilon':'nu/a','uniform_errors':{'joint_metric':24,'inverse_joint_metric':1944,
            'Q_A_over_a_squared':4000,'Q_K_over_a_squared':2000},
            'example':{'alpha':str(alpha),'beta':str(beta),'nu':str(nu),'H':str(h),
                       'a':str(amplitude),'t':'1/10000000000',
                       'normalized_defect_lower_bound':str(lower)},
            'scope':'exact bound constants; Brownian and inverse-matrix inequalities proved analytically'}


def main():
    print(json.dumps({'shear':shear_pde(),'joint_metric':joint_metric_limit(),
        'positive_viscosity_bounds':error_bounds(),
        'actual_3d_jets':[actual_jets(p) for p in (-1,1)],
        'candidate':'Q_A+alpha Q_K+beta(H-t)E/2, alpha>0, beta>=0 fixed',
        'verdict':'fails the signed renewal supersolution inequality; no general full-datum budget is refuted'},indent=2))


if __name__=='__main__':
    main()
