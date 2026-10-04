#!/usr/bin/env python3
"""Convex joint velocity/pressure entropy on actual NS prefixes.

Checks the full local source identities, entropy algebra, sharp diffusion
fixture, original-energy coarse payment and continuation exponents. The
operator estimates and PDE consequences are analytic in README.md. This
is not a Lean certificate or a proof of the remaining history payment.
"""
import hashlib
import json
from pathlib import Path
import sympy as s
from rotational_curl_reserve import require, zero


def actual_sources():
    t,nu=s.symbols('t nu',real=True)
    x=s.symbols('x0:3',real=True)
    coordinates=(t,)+x
    u=s.Matrix([s.Function('u'+str(i))(*coordinates) for i in range(3)])
    q=s.Function('q')(*coordinates)
    grad=lambda f:s.Matrix([s.diff(f,a) for a in x])
    lap=lambda f:sum(s.diff(f,a,2) for a in x)
    operator=lambda f:s.diff(f,t)+u.dot(grad(f))-nu*lap(f)
    for i in range(3):
        zero(operator(s.diff(q,x[i]))-s.diff(operator(q),x[i])
             +sum(s.diff(u[j],x[i])*s.diff(q,x[j]) for j in range(3)),
             'material gradient commutator retains every deformation component')
        for j in range(3):
            zero(operator(u[i]*u[j])-u[i]*operator(u[j])-u[j]*operator(u[i])
                 +2*nu*grad(u[i]).dot(grad(u[j])),
                 'complete stress product law retains viscous production')
    return {
      'q':'int_0^(L^2) exp(s Delta)p ds',
      'beta':'grad q, all three components',
      'S_q':'Q_L[-u tensor grad p-grad p tensor u-2nu G]+[u.grad,Q_L](u tensor u)',
      'S_beta':'grad S_q-(grad u)^T grad q',
      'G_ij':'sum_k (partial_k u_i)(partial_k u_j)',
      'Q_L':'(-Delta)^(-1)(I-exp(L^2 Delta)) partial_i partial_j(-Delta)^(-1)',
      'retained':'Viscous stress production -2nu G remains in the source; positivity of the explicit diffusion block does not pay it.'}


def joint_diffusion():
    z=s.Matrix(s.symbols('z0:6',real=True))
    r=s.sqrt(z.dot(z))
    H=s.hessian(r**3,list(z))
    require(all(s.simplify(v)==0 for v in H-3*r*s.eye(6)-3*z*z.T/r),
            'full six-component cubic Hessian')
    N=s.zeros(6)
    for i in range(3):N[i,i+3]=1
    require(N*N==s.zeros(6),'cross diffusion is nilpotent of order two')
    # A scalar block attains the universal half-diffusion constant.
    u,y,du,dy=s.symbols('u y du dy',real=True)
    zz=s.Matrix([u,y]);dd=s.Matrix([du,dy]);rr=s.sqrt(u*u+y*y)
    HH=s.hessian(rr**3,(u,y));AA=s.Matrix([[1,1/s.sqrt(2)],[0,1]])
    M=s.simplify((HH*AA+AA.T*HH)/2-HH/2)
    zero(M[0,0]-3*(2*u*u+y*y)/(2*rr),'positive first principal minor')
    zero(M.det()-9*y*y*(4*u*u+3*y*y)/(8*(u*u+y*y)),
         'nonnegative determinant of half-diffusion remainder')
    zero((dd.T*M*dd)[0].subs({u:1,y:0,du:1,dy:-s.sqrt(2)}),
         'sharp half-diffusion fixture')
    # The scalar-gradient Sobolev consumer uses B <= A below.
    A,B=s.symbols('A B',nonnegative=True)
    zero(s.Rational(9,8)*(A+B)-s.Rational(9,4)*B-s.Rational(9,8)*(A-B),
         'gradient of |z|^(3/2) is controlled by the cubic Hessian')
    return {
      'variables':'y=sqrt(2) beta/nu; z=(u,y); J=int |z|^3',
      'diffusion':'D=nu sum_j int (partial_j z)^T H_z (I+N/sqrt(2)) partial_j z',
      'bound':'D >= (nu/2) sum_j int (partial_j z)^T H_z partial_j z >= (4nu/3) int |grad |z|^(3/2)|^2',
      'matrix_argument':'For B^2=0, split a vector orthogonally over ker B and its complement: |<v,Bv>| <= ||B|| |v|^2/2. Apply to H_z^(1/2) N H_z^(-1/2), whose norm is at most sqrt(2).',
      'source_pairing':'F_gen=(3sqrt(2)/nu) int |z| y.S_beta',
      'balance':'J_prime+D=W_low+F_gen; W_low=-3 int |z| u.grad p_low',
      'scope':'Actual pressure observations satisfy the block system. The source is not independently prescribed; the remaining payment is open.'}


def actual_calibration():
    x,y,z,t=s.symbols('x y z t',real=True)
    nu,L=s.symbols('nu L',positive=True)
    xyz=(x,y,z)
    lap=lambda f:sum(s.diff(f,a,2) for a in xyz)
    grad=lambda f:s.Matrix([s.diff(f,a) for a in xyz])
    u=s.exp(-2*nu*t)*s.Matrix([s.sin(x)*s.cos(y),-s.cos(x)*s.sin(y),0])
    p=s.exp(-4*nu*t)*(s.cos(2*x)+s.cos(2*y))/4
    operator=lambda f:s.diff(f,t)+u.dot(grad(f))-nu*lap(f)
    require(all(s.trigsimp(operator(u[i])+s.diff(p,xyz[i]))==0 for i in range(3)),
            'actual unforced periodic calibration')
    q=(1-s.exp(-4*L*L))*p/4; beta=grad(q)
    low=s.exp(-4*L*L)*p
    require(all(s.trigsimp(operator(u[i])-lap(beta[i])+s.diff(low,xyz[i]))==0
                for i in range(3)), 'actual pressure observation has the claimed diffusion transfer')
    require(all(s.trigsimp(operator(beta[i])-u.dot(grad(beta[i])))==0 for i in range(3)),
            'actual material pressure source retained in the calibration')
    X,Y=s.symbols('X Y',positive=True)
    phi=(X+Y)**s.Rational(3,2)
    zero(-4*nu*X*s.diff(phi,X)-8*nu*Y*s.diff(phi,Y)
         +6*nu*s.sqrt(X+Y)*(X+2*Y), 'complete convex entropy decays on the actual calibration')
    return {'flow':'exp(-2nu t)(sin x cos y,-cos x sin y,0)',
            'pressure':'exp(-4nu t)(cos(2x)+cos(2y))/4',
            'all_time_entropy':'integrand_prime=-6nu sqrt(X+Y)(X+2Y)<=0, X=|u|^2,Y=2|beta|^2/nu^2',
            'scope':'Exact actual-flow calibration; not a bound on arbitrary generated-pressure histories.'}


def energy_payment():
    # ||u||_(12/5) <= ||u||_2^(3/4) ||u||_6^(1/4).
    zero(s.Rational(5,12)-s.Rational(3,4)/2-s.Rational(1,4)/6,
         'interpolation exponent for the pressure stress')
    E,H,nu,CS,ML=s.symbols('E H nu CS ML',positive=True)
    a=s.Rational(9,2)*ML*E**2
    b=3*ML*CS**s.Rational(3,2)*E**s.Rational(5,2)/nu**2
    allowance=s.simplify(a*H+b*s.sqrt(H*E/(2*nu)))
    expected=3*ML*E*(s.Rational(3,2)*E*H
                      +CS**s.Rational(3,2)*E**2/nu**2*s.sqrt(H/(2*nu)))
    zero(allowance-expected,'same finite original-data allowance')
    # s=H-t, energy'= -2nu Z. Let root=sqrt(s E/(2nu)).
    h,Z=s.symbols('h Z',positive=True)
    root=s.sqrt(h*E/(2*nu))
    rate=-s.diff(root,h)-2*nu*Z*s.diff(root,E)
    zero(-rate-s.sqrt(Z)
         -(s.sqrt(E/(2*nu))-s.sqrt(h*Z))**2/(2*root),
         'complete energy-clock derivative pays sqrt(enstrophy)')
    return {
      'beta_norm':'||beta||2^2 <= C_S^(3/2) E(t)^(3/2) Z(t)^(1/2), uniform in fixed L',
      'proof':'Dual Sobolev and the exact tensor-to-vector pressure multiplier, then interpolation. All current velocity components and stress cross terms remain.',
      'coarse_cost':'|W_low|<=a+b sqrt(Z), a=(9/2) M_L E0^2, b=3 M_L C_S^(3/2) E0^(5/2)/nu^2',
      'reserve':'B_low(t)=a(H-t)+b sqrt((H-t)E(t)/(2nu)) >=0',
      'payment':'B_low_prime+|W_low|<=0 almost everywhere; extend endpoints by continuity',
      'allowance':str(allowance),
      'whole_space_kernel':'M_L=(4pi)^(-3/2)L^(-4)',
      'periodic_kernel':'M_L=sum_(k !=0) |k| exp(-L^2 |k|^2), for normalized period-2pi volume',
      'zero_energy':'u=0 and every cost/reserve is zero',
      'seams':'The same E(t), pressure state and remaining original horizon are inherited; no new allowance is issued.'}


def continuation_and_limits():
    zero(s.Rational(7,18)-s.Rational(2,3)/2-s.Rational(1,3)/6,
         'gradient interpolation for the order-one consumer')
    a,nu,d=s.symbols('a nu d',positive=True)
    maximum=s.simplify((a*d**s.Rational(2,3)-nu*d/2).subs(d,(4*a/(3*nu))**3))
    zero(maximum-16*a**3/(27*nu**2),'explicit enstrophy Young constant')
    c=s.symbols('c',positive=True)
    # Under amplitude c and Euler time tau=c*t, pressure scales like c^2.
    zero(c**2*c**2*c**3-c**7,'leading regenerated pressure degree')
    return {
      'OPEN':'int_0^T [F_gen-D/2] <= K_gen(u0,nu,H,L) for EVERY available same-datum prefix T<=H',
      'consequence':'J(T)+(1/2)int_0^T D <= A0=J(0)+B_low(0)+K_gen',
      'whole_space':'int_0^T ||u||9^3 <= (3 C_S/(2nu)) A0',
      'periodic':'int_0^T ||u||9^3 <= C_I [3/(2nu)+H] A0; C_I is the inhomogeneous Sobolev constant',
      'enstrophy':'Z_prime+nu||Delta u||2^2 <= [32 sqrt(C_S)/(27nu^2)] ||u||9^3 Z',
      'continuation':'Gronwall gives one datum-only order-one bound if the OPEN source allowance is proved; the existing continuation consumer then applies.',
      'adverse_horizontal_variant':'For z=(u_h,sqrt(2) grad_h q/nu), the existing Gaussian certificate gives positive initial nonlinear pressure production at large amplitude. It refutes automatic monotonicity of that projected variant.',
      'distinction':'The full three-component pressure norm has a different coefficient; the horizontal sign is not asserted for it. No integrated source payment or regularity theorem is proved.'}


if __name__=='__main__':
    result={'sources':actual_sources(),'diffusion':joint_diffusion(),
            'calibration':actual_calibration(),'payment':energy_payment(),'consumer':continuation_and_limits(),
            'status':'All exact checks passed; operator estimates and PDE consequences remain analytic.',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result,indent=2),flush=True)
