#!/usr/bin/env python3
"""Exact joint covariance reserve identities and all-time shear calibration.

The compensated-compactness estimate and physical interval transfer in
README.md are analytic arguments, not certified by these finite fixtures.
"""
import json
import sympy as sy

import covariance_velocity_defect as c
s, f, j, Q = c.s, c.f, c.j, c.Q


def rate_checks(u, F, Sigma, nu, theta, beta):
    B=f.jac(u)
    K=c.tadd(*(f.matmul([[f.diff(a,k) for a in row] for row in F],
                      c.transpose([[f.diff(a,k) for a in row] for row in F])) for k in range(3)))
    div=j.tensor_div(Sigma)
    chi=f.scale(-1,f.green(f.trace(f.jac(div))))
    gradchi=f.grad(chi)
    j.vector_equal(gradchi,s.vector_add(div,s.vector_scale(-1,j.project(div))),'chi potential')
    C=s.vector_add(u,s.vector_scale(nu,j.project(div)))
    ut=s.vector_add(s.vector_scale(-nu,s.minus_laplacian(u)),s.nonlinear(u))
    Sigmat=c.tadd(j.tensor_scale(nu,c.tlap(Sigma)),c.deformation(u,Sigma),j.tensor_scale(2*nu,K))
    Ct=s.vector_add(ut,s.vector_scale(nu,j.project(j.tensor_div(Sigmat))))
    q=s.vector_add(C,s.vector_scale(-theta,u))
    qt=s.vector_add(Ct,s.vector_scale(-theta,ut))
    H=c.tadd(f.matmul(B,Sigma),[[f.mul(chi,a) for a in row] for row in c.transpose(B)],j.tensor_scale(2*nu,K))
    innerT=lambda A,Z:sum(s.inner(a,z) for a,z in zip(A,Z))
    Qgrad=f.jac(q)
    direct=s.inner(q,qt)+beta*s.inner(u,ut)
    rhs=-nu*innerT(Qgrad,Qgrad)-beta*nu*innerT(B,B)-nu*innerT(Qgrad,H)
    s.require(direct==rhs,'full positive quadratic rate')
    completed=c.tadd(Qgrad,j.tensor_scale(Q(1,2),H))
    s.require(direct+nu*innerT(completed,completed)+beta*nu*innerT(B,B)==nu*innerT(H,H)/4,'square')
    adv=c.vadv(u,q)
    qeq=s.vector_add(s.vector_scale(-nu,s.minus_laplacian(q)),j.project(s.vector_add(s.vector_scale(-1,adv),s.vector_scale(nu,j.tensor_div(H)))))
    j.vector_equal(qt,qeq,'stress PDE all derivatives')
    # The pressure test is a div--curl product with exactly zero mean.
    pressure_test=f.trace(f.matmul(B,Qgrad))
    s.require(pressure_test.get(f.ORIGIN,0)==0,'pressure test has zero mean')
    pressure_work=innerT(Qgrad,[[f.mul(chi,a) for a in row] for row in c.transpose(B)])
    paired=-innerT(Sigma,f.hess(f.green(pressure_test)))
    s.require(pressure_work==paired,'adjoint pressure pairing retains only covariance amplitude')
    # Mean-frame gradient energy: differentiate its ACTUAL equation.
    Ft=c.tadd(j.tensor_scale(nu,c.tlap(F)),j.tensor_scale(-1,c.tadv(u,F)),f.matmul(B,F))
    EF_rate=-innerT(c.tlap(F),Ft)
    transport=innerT(c.tlap(F),c.tadv(u,F))
    source=-innerT(c.tlap(F),f.matmul(B,F))
    s.require(EF_rate == -nu*innerT(c.tlap(F),c.tlap(F))+transport+source,
              'mean-frame Dirichlet balance includes transport and deformation')
    return {'rate':str(direct), 'frame_gradient_energy_rate':str(EF_rate),
            'pressure_work':str(pressure_work),'stress_squared':str(innerT(H,H)),'potential_squared':str(s.inner([chi,{},{}],[chi,{},{}]))}


def ordered_checks():
    v1=c.simple_parent()
    cx,cy,cz=(c.mode(tuple(int(i==k) for i in range(3)),1) for k in range(3))
    v2=[{},f.mul(cx,cz),f.scale(-1,f.mul(cx,cy))]
    S1,S2=j.tensor(v1,v1),j.tensor(v2,v2)
    u=s.vector_add(s.nonlinear(v1),s.nonlinear(v2))
    weighted=lambda scalar,T:[[f.mul(scalar,a) for a in row] for row in T]
    S12=c.tadd(S1,S2,weighted(S1[0][0],S2))
    S21=c.tadd(S1,S2,weighted(S2[2][2],S1))
    return [rate_checks(u,c.matrix_identity(),S,Q(1),Q(1),Q(1)) for S in (S12,S21)]


def shear_checks():
    t,y=sy.symbols('t y',real=True)
    nu,amplitude,lam=sy.symbols('nu amplitude lam',positive=True)
    z=sy.symbols('z',positive=True) # z=exp(-nu*t)
    rt=lambda a:sy.diff(a,t)-nu*z*sy.diff(a,z)
    zero=lambda a,label:j.zero(sy.trigsimp(sy.expand(a)),label)
    u=sy.Matrix([amplitude*z*sy.sin(y),0,0])
    B=sy.zeros(3);B[0,1]=sy.diff(u[0],y)
    b=amplitude*t*z*sy.cos(y)
    h0=amplitude**2/(4*nu**2)*(1-(1+2*nu*t)*z**2)
    h2=amplitude**2/(4*nu**2)*((2*nu*t-1)*z**2+z**4)
    h=h0+h2*sy.cos(2*y)
    F=sy.eye(3);F[0,1]=b
    M=sy.diag(1+(1+lam)*h,1+lam,1)
    M[0,1]=M[1,0]=(1+lam)*b
    for A,source in [(F,B*F),(M,B*M+M*B.T)]:
        defect=A.applyfunc(rt)-nu*A.diff(y,2)-source
        for value in defect:zero(value,'full shear moment PDE')
    omega=sy.Matrix([0,0,-sy.diff(u[0],y)])
    for value in M*omega-omega:zero(value,'shear frame conversion is exactly one in the vorticity direction')
    Sigma=M-F*F.T
    div=Sigma[:,1].diff(y)
    C=u+nu*div
    for value in C-(1-lam*nu*t)*u:zero(value,'actual evolving shear discrepancy')
    K=F.diff(y)*F.diff(y).T
    for value in K[:,1].diff(y):zero(value,'mean-frame work has zero divergence in this shear')
    zero(rt(h-b*b)-nu*sy.diff(h-b*b,y,2)-2*nu*sy.diff(b,y)**2,
         'shear covariance positivity has a nonnegative diffusion source')
    theta,beta,ss=sy.symbols('theta beta ss',real=True)
    zz=1-theta-lam*ss
    # Divide by the positive factor ||u(0)||^2 exp(-2ss).
    derivative=-zz**2-lam*zz-beta
    zero(derivative+(zz+lam/2)**2+beta-lam**2/4,
         'sharp memory-dependent quadratic weight')
    at=sy.Rational(1,2)+(1-theta)/lam
    zero((zz+lam/2).subs(ss,at),'interior time of largest normalized reserve growth')
    x,Y,Z,A,a=sy.symbols('x Y Z A a',real=True)
    gamma=72*A*A; bb=a*a+16*gamma*A*A+1
    upper=-x*x-bb*Y*Y-gamma*Z*Z+a*x*Y+6*A*x*Z+4*gamma*A*Y*Z
    squares=(x/2-a*Y)**2+(x/2-6*A*Z)**2+gamma*(Z/2-4*A*Y)**2
    zero(-upper-(x*x/2+Y*Y+gamma*Z*Z/4)-squares,
         'complete three-way diffusion absorption with explicit coefficients')
    L,Ldot,U2,Q2,G2,bcap=sy.symbols('L Ldot U2 Q2 G2 bcap',positive=True)
    normalized=(Q2+U2)/(2*L**2)+bcap*U2/2+108*nu**2*G2/L
    zero(sy.diff(normalized,L)*Ldot+Ldot*(Q2+U2)/L**3
         +108*nu**2*Ldot*G2/L**2,'nondecreasing memory normalization has favorable derivative')
    zero((72*(3*L))/4/L**2-54/L,'normalized frame diffusion coefficient')
    return {'normalized_memory_weight_derivative':'-Lprime*(||q||^2+||u||^2)/L^3-108*nu^2*Lprime*||grad F||^2/L^2',
            'shear_C':'(1-lambda*nu*t) u',
            'sharp_shear_weight':'beta >= lambda^2/4 when theta <= 1+lambda/2',
            'fixed_weight_growth_time':'nu*t=1/2+(1-theta)/lambda',
            'complete_payment_gamma':'72 A^2',
            'complete_payment_beta':'a^2+1152 A^4+1',
            'all_moment_PDEs_and_absorption_squares':True}


def main():
    v=c.simple_parent()
    u=s.vector_add(s.nonlinear(v),s.vector_scale(Q(1,3),v))
    e3=[{},{},{f.ORIGIN:f.QQ_I(1)}]
    F=c.tadd(c.matrix_identity(),j.tensor_scale(Q(1,4),j.tensor(v,e3)))
    general=rate_checks(u,F,j.tensor(v,v),Q(2,3),Q(3,2),Q(2))
    released=[]
    for name,v in [('simple',c.simple_parent()),('resonant',c.resonant_parent()),
                   ('adverse',c.release.horizontal_seed())]:
        u=s.nonlinear(v)
        released.append(dict(label=name,**rate_checks(u,c.matrix_identity(),j.tensor(v,v),
                                                     Q(1),Q(1),Q(1))))
    alpha=Q(10000);v=c.resonant_parent()
    growing=rate_checks(s.vector_scale(-alpha,s.nonlinear(v)),c.matrix_identity(),
                        j.tensor_scale(alpha,j.tensor(v,v)),Q(1),Q(1),Q(1))
    print(json.dumps(dict(status='all exact checks passed',general=general,released=released,
                         growing_background=growing,ordered_histories=ordered_checks(),
                         shear=shear_checks(),
                         scope='exact finite PDE fixtures and shear formulas; norm estimates and original-parent realization analytic'),indent=2))


if __name__=='__main__':
    main()
