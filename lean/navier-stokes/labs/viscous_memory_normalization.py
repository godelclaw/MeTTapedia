#!/usr/bin/env python3
"""A geometric-mean memory normalization and its local shape payment.

Generic matrix jets and complete unforced shear histories check the
determinant chain rule, auxiliary drift and coercive normalization.
The README gives the analytic conditional continuation argument. No
uniform bound on the remaining nonlinear history source is proved.
"""
import json
import sympy as s
import pressure_history_source as f
import strain_cycle_diffusion as d
import pressure_core_envelope as envelope


def heat(field,q):
    return {k:a*q**sum(z*z for z in k) for k,a in field.items()}


def check_generic_matrix():
    a=s.symbols('a1:4',positive=True);nu=s.symbols('nu',positive=True)
    def symmetric(prefix):
        z=s.symbols(prefix+'0:6',real=True)
        return s.Matrix([[z[0],z[3],z[4]],[z[3],z[1],z[5]],[z[4],z[5],z[2]]])
    H=s.diag(*a);E=symmetric('e');L=symmetric('l');G=symmetric('g')
    inv=H.inv();x,t=s.symbols('x t',real=True);det=H.det()
    polynomial=(H+x*E+x*x*L/2).det()
    det_x=s.diff(polynomial,x).subs(x,0)
    det_xx=s.diff(polynomial,x,2).subs(x,0)
    det_t=s.diff((H+t*(nu*L+2*nu*G)).det(),t).subs(t,0)
    # h=det(H/eta)^(1/3); eta is constant and drops out of Dh/h.
    direct=det_t/(3*det)-nu*det_xx/(3*det)+2*nu*det_x**2/(9*det**2)
    metric=s.trace(inv*E*inv*E)
    shape=metric-s.trace(inv*E)**2/3
    production=2*nu*s.trace(inv*G)/3+nu*shape/3
    d.zero(direct-production,'full noncommuting determinant parabolic chain rule')
    ratios=[E[i,i]/a[i] for i in range(3)]
    sos=sum((ratios[i]-ratios[j])**2/3+2*E[i,j]**2/(a[i]*a[j])
            for i in range(3) for j in range(i+1,3))
    d.zero(shape-sos,'relative-eigenvalue and orientation shape cost')

    gl=s.Matrix(s.symbols('L1:4',real=True));gp=s.Matrix(s.symbols('P1:4',real=True))
    Dl,Dp,kappa=s.symbols('Dl Dp kappa',real=True)
    transformed=Dl-Dp-kappa-2*nu*gp.dot(gl-gp)-nu*(gl-gp).dot(gl-gp)
    d.zero(transformed-(Dl-nu*gl.dot(gl)-kappa-(Dp-nu*gp.dot(gp))),
           'exact drift correction for the normalized logarithm')


def check_actual_shear(q,phase):
    nu=f.QQ_I(1)/5;ns=s.Rational(1,5);eta=s.Integer(1)
    u0=[f.scale(3,f.add(d.sin((0,1,0)),f.scale(phase,d.cos((0,1,0))))),
        {},d.cos((0,2,0))]
    u=[heat(a,q) for a in u0];ut=[f.scale(nu,f.lap(a)) for a in u]
    T0=f.tensor(u0,u0);T=f.tensor(u,u);heated=[[heat(a,q) for a in row] for row in T0]
    C=[[f.add(heated[i][j],f.scale(-1,T[i][j])) for j in range(3)] for i in range(3)]
    Ct=[[f.add(f.scale(nu,f.lap(heated[i][j])),
              f.scale(-1,f.mul(ut[i],u[j])),f.scale(-1,f.mul(u[i],ut[j])))
         for j in range(3)] for i in range(3)]
    for a in u:f.equal(f.adv(u,a),{},'complete shear advection vanishes')
    f.equal(f.tensor_pressure(T),{},'complete shear fluid pressure')
    f.equal(f.tensor_pressure(C),{},'complete shear memory pressure')
    B=f.jac(u);G=f.matmul(B,[list(row) for row in zip(*B)])
    c=d.matval(C);ct=d.matval(Ct);g=d.matval(G)
    H=eta*s.eye(3)+c;inv=H.inv();det=H.det()
    if det<eta**3 or det>(s.trace(H)/3)**3:
        raise ArithmeticError('geometric mean lower and mass upper bounds')
    Cj=[d.matval([[f.diff(a,j) for a in row] for row in C]) for j in range(3)]
    F=sum(s.trace(inv*a*inv*a) for a in Cj)
    trace_gradient=sum(s.trace(inv*a)**2 for a in Cj)
    shape=s.factor(F-trace_gradient/3)
    if shape<0:raise ArithmeticError('positive shape cost')
    source=s.factor(2*ns*s.trace(inv*g)/3)
    paid=s.factor(source+ns*shape/3)
    e=s.symbols('e',real=True)
    det_t=s.diff((H+e*ct).det(),e).subs(e,0)
    determinant=(d.jetmat(C)+eta*s.eye(3)).det()
    det_lap=d.lapval(determinant);det_grad=d.gradval(determinant)
    direct=s.factor(det_t/(3*det)-ns*det_lap/(3*det)
                    +2*ns*det_grad.dot(det_grad)/(9*det**2))
    d.zero(direct-paid,'actual all-time shear determinant production')

    # The complete pressure/core envelope in this shear class is a
    # convex increasing function of r=|omega|^4. Its parabolic production
    # is nonpositive, so the transformed quotient has the additional
    # nonnegative subtraction paid above.
    w=f.curl(u);W=f.dot(w,w);r=f.mul(W,W)
    wt=f.curl(ut);rt=f.scale(4,f.mul(W,f.dot(w,wt)))
    rr=d.ev(r);Dr=d.ev(f.add(rt,f.scale(-nu,f.lap(r))))
    gr=s.Matrix([d.ev(f.diff(r,j)) for j in range(3)])
    a0=s.Rational(1399,1995);b0=s.Rational(4,105)
    root=s.sqrt(b0*b0*rr*rr+1)
    theta=(1-b0*rr/root)/2
    Y=1+a0*rr+(-b0*rr+root)/2
    DY=(a0-b0*theta)*Dr-ns*b0*b0*gr.dot(gr)/(2*root**3)
    if Dr>0 or a0-b0*theta<=0 or Y<=0:
        raise ArithmeticError('actual complete shear envelope sign')
    normalized=s.factor(DY/Y-paid)
    if normalized>0:raise ArithmeticError('normalized shear subsolution')
    return {'heat_parameter':str(q),'phase':phase,'geometric_mean_cubed':str(det/eta**3),
            'shape_metric':str(shape),'source_payment':str(source),
            'complete_local_payment':str(paid),
            'normalized_parabolic_production_nonpositive':True,
            'scope':'complete exact unforced shear histories; no arbitrary-flow bound'}


def check_continuation_exponents():
    nu,A,z=s.symbols('nu A z',positive=True)
    optimum=(3*A/(4*nu))**s.Rational(8,5)
    value=A*z**s.Rational(3,8)-nu*z/2
    d.zero(s.diff(value,z).subs(z,optimum),'enstrophy Young optimizer')
    constant=s.Rational(5,8)*(s.Rational(3,4)/nu)**s.Rational(3,5)*A**s.Rational(8,5)
    d.zero(value.subs(z,optimum)-constant,'enstrophy absorption coefficient')
    # A=C_* (integral |omega|^4)^(1/4) E_omega^(5/8).
    if s.Rational(1,4)*s.Rational(8,5)!=s.Rational(2,5):
        raise ArithmeticError('fourth-moment exponent')
    if s.Rational(5,8)*s.Rational(8,5)!=1:
        raise ArithmeticError('linear enstrophy coefficient')


def check_nonlinear_initial_production():
    # Full three-dimensional NS initial data, made stationary at the
    # receiver by a constant velocity shift. The normalized candidate
    # is not automatically a parabolic subsolution on arbitrary data.
    nu=f.QQ_I(1)/1000;ns=s.Rational(1,1000)
    u=[f.add(a,f.scale(-sum(a.values(),f.ZERO),d.ONE)) for a in f.fixture()]
    result=envelope.actual(u,nu,s.Integer(1))
    B=f.jac(u);G=f.matmul(B,[list(row) for row in zip(*B)])
    C1=[[f.scale(2*nu,a) for a in row] for row in G]
    P1=d.matval(f.hess(f.tensor_pressure(C1)))
    w=s.Matrix([d.ev(a) for a in f.curl(u)])
    pressure_rate=result['DP']-2*w.dot(P1*w)
    payment=2*ns*s.trace(d.matval(G))/3
    gap=result['gap']
    if gap==0:raise ArithmeticError('nonzero gap needed for the rational switch bound')
    Yupper=s.Rational(3,2)+result['core']+max(gap,0)
    lower=min(pressure_rate,result['DC'])
    lower-=ns*result['gradgap'].dot(result['gradgap'])/(2*abs(gap)**3)
    lower-=payment*Yupper
    certificate=s.floor(lower)
    if certificate<=0:raise ArithmeticError('strict positive normalized parabolic production')
    return {'viscosity':'1/1000','initial_memory':'0',
            'local_geometric_payment':str(payment),
            'normalized_production_numerator_lower_integer':int(certificate),
            'scope':'full actual initial NS tangent; positive parabolic production '
                    'is not temporal growth or failure of a finite history allowance'}


if __name__=='__main__':
    check_generic_matrix();check_continuation_exponents()
    print(json.dumps({'status':'all exact checks passed',
                      'shear_histories':[check_actual_shear(q,phase)
                          for q in (f.QQ_I(1),f.QQ_I(1)/2,f.QQ_I(3)/4) for phase in (0,1)],
                      'nonlinear_initial_production':check_nonlinear_initial_production(),
                      'scope':'local geometric-mean normalization and conditional continuation; '
                              'the remaining controlled-history estimate is open'},indent=2))
