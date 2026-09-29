#!/usr/bin/env python3
"""Initial unforced pressure transfer and an aligned joint reserve.

A compact axisymmetric meridional background strains two radial swirl
packets. The calculation retains both carried swirl motion and the
meridional pressure reaction, including the finite background cutoff.
An aligned central core gives a pressure/strain/vorticity feedback law
at the initial time of actual local whole-space NS solutions.

The polynomial reserve is an all-time certificate for the stated scalar
rates with explicit defects. Its identification with NS is only initial;
the shape is not invariant. The spatial chain rule and planar reduction
are checked separately. No arbitrary-data regularity bound is asserted.
Requires NumPy, SciPy and SymPy. Derivation and scope: labs/README.md.
"""
import json
import numpy as np
import sympy as s
from numpy.polynomial.legendre import leggauss
from scipy.special import expit


def zero(expr,label):
    value=s.factor(s.together(expr))
    if value != 0:
        value=s.simplify(value)
    if value != 0:
        raise AssertionError((label,value))


x,y,z=s.symbols('x y z',real=True)
I,K,L=s.symbols('I K L',positive=True)
a=s.symbols('a',real=True)
r=s.sqrt(x*x+y*y+z*z)
P2=(3*z*z/r**2-1)/2
p=-s.Rational(2,3)*I*P2/r**3
q=-s.Rational(2,9)*I/r+(-I/(9*r)+K/(15*r**3))*P2
lap=lambda f: sum(s.diff(f,t,2) for t in (x,y,z))
zero(-lap(q)-p,'exterior biharmonic potential')
axis={x:0,y:0,z:L}
H=s.hessian(p,(x,y,z)).subs(axis)
Q=s.hessian(s.diff(q,z,2),(x,y,z)).subs(axis)
S=a*s.diag(1,1,-2)
swirl_rate=-S*H-H*S-2*a*H+6*a*Q
reaction_rate=6*a*Q
full_rate=swirl_rate+reaction_rate
moment=K/(I*L**2)
zero(swirl_rate[2,2]-a*(8-18*moment)*H[2,2],'carried swirl axial rate')
zero(reaction_rate[2,2]-a*(6-18*moment)*H[2,2],'meridional back-reaction rate')
zero(full_rate[2,2]-a*(14-36*moment)*H[2,2],'full coupled axial rate')
zero(full_rate[0,0]-a*(20-36*moment)*H[0,0],'full transverse rate')
zero(s.trace(full_rate)-12*a*H[0,0],'pressure-excess trace production')

# The swirl pressure source s_w=-(1/rho) partial_rho W^2 follows a
# different dilation weight from its velocity. Here rho is cylindrical.
rho,zz=s.symbols('rho zz',positive=True)
F=s.Function('F')(rho,zz)
A=lambda f: -a*rho*s.diff(f,rho)+2*a*zz*s.diff(f,zz)
sw=-s.diff(F,rho)/rho
zero(-s.diff(A(F)-2*a*F,rho)/rho-(A(sw)-4*a*sw),
     'swirl source dilation law')
pp=s.Function('p')(x,y,z)
Ac=lambda f: -a*x*s.diff(f,x)-a*y*s.diff(f,y)+2*a*z*s.diff(f,z)
zero(-lap(Ac(pp)-2*a*pp)-(Ac(-lap(pp))-4*a*(-lap(pp))-6*a*s.diff(pp,z,2)),
     'Newtonian dilation commutator')

# A compact axisymmetric meridional background comes from the potential
# A_theta=-a z rho chi(sqrt(rho^2+z^2)). It agrees with Sx where chi=1.
ss=s.sqrt(rho*rho+zz*zz)
chi=s.Function('chi')(ss)
vr=a*rho*(chi+zz*s.diff(chi,zz))
vz=-a*zz*(2*chi+rho*s.diff(chi,rho))
zero(s.diff(vr,rho)+vr/rho+s.diff(vz,zz),'compact strain incompressibility')

# Angular projection of the compact background's pressure source.
# c=chi, d=r chi', e=r^2 chi''. The quadratic derivative terms cancel
# after radial integration by parts, leaving a profile-independent core.
mu,c,d,e=s.symbols('mu c d e',real=True)
rh=s.sqrt(1-mu*mu)
br=c+d+mu*mu*(1-mu*mu)*(e-d)
bp=c+mu*mu*d
bz=-2*c-(1+mu*mu)*d-mu*mu*(1-mu*mu)*(e-d)
brz=rh*(3*mu*d+mu**3*(e-d))
bzr=-mu*(4*rh*d+rh**3*(e-d))
source=br**2+bp**2+bz**2+2*brz*bzr
angular=s.integrate(s.expand(s.legendre(2,mu)*source),(mu,-1,1))
zero(angular-s.Rational(8,105)*(18*c*d+3*c*e+2*d*d-d*e),
     'compact strain pressure angular projection')
Achi=s.symbols('Achi',real=True)
zero(-2+s.Rational(8,105)*(18*(-s.Rational(1,2))+
       3*(s.Rational(1,2)-Achi)+2*Achi+Achi)+s.Rational(18,7),
     'compact strain axial pressure coefficient')

# For the finite cutoff correction only exterior harmonic degrees 2 and 4
# can contribute to the central pressure Hessian. Higher degrees vanish.
angular_feedback={}
for ell in (2,4,6,8):
    ext=s.legendre(ell,z/r)/r**(ell+1)
    hext=s.hessian(ext,(x,y,z)).subs({x:rh,y:0,z:mu}).applyfunc(s.simplify)
    contraction=br*hext[0,0]+bp*hext[1,1]+bz*hext[2,2]+(brz+bzr)*hext[0,2]
    angular_feedback[ell]=s.factor(s.integrate(s.expand(-2*s.legendre(2,mu)*contraction),(mu,-1,1)))
zero(angular_feedback[2]-s.Rational(32,35)*(4*d-e),'degree-two cutoff cancellation')
zero(angular_feedback[4]-s.Rational(32,7)*(d-e),'degree-four cutoff response')
zero(angular_feedback[6],'degree-six cutoff response')
zero(angular_feedback[8],'degree-eight cutoff response')

# Signed joint reserve for the leading aligned feedback system. The
# physical initial derivatives match this system with an explicit
# finite-width/cutoff correction; invariance for later NS times is open.
w,sigma,h,gamma,fs,fw,fh=s.symbols('w sigma h gamma fs fw fh',real=True)
reserve=w**5*(2090*sigma**2+154*w**14+665*h)
sigma_rate=-s.Rational(5,14)*sigma**2-s.Rational(1,10)*w**14+h+fs
w_rate=sigma*w/7+fw
h_rate=-7*sigma*h-gamma*h+fh
production=s.diff(reserve,sigma)*sigma_rate+s.diff(reserve,w)*w_rate+s.diff(reserve,h)*h_rate
defect=4180*w**5*sigma*fs+(10450*w**4*sigma**2+2926*w**18+3325*w**4*h)*fw+665*w**5*fh
zero(production+665*gamma*w**5*h-defect,'coercive joint reserve with all rate defects')
zero(49*h*w**48*w_rate+w**49*h_rate+gamma*h*w**49-
     49*h*w**48*fw-w**49*fh,'reciprocal pressure and vorticity history')

# This earlier actual unforced mixed-parent example has h'=23 gamma at
# sigma=0, h=7/4. It grows the observed reserve despite positive h.
# A parent-sensitive defect allowance remains necessary.
zero(production.subs({sigma:0,h:s.Rational(7,4),fw:0,fs:0,
                     fh:s.Rational(99,4)*gamma})-15295*gamma*w**5,
     'actual unequal-parent initial reserve production')

# Full parabolic chain rule, keeping the root-amplitude correction.
# For D=partial_t+u.grad-nu Delta and Omega=w^7>0,
# D w=sigma*w/7+6nu*|grad w|^2/w-(nu/7)w|grad xi|^2.
dw,ds,dh=s.symbols('dw ds dh',real=True)
direction=s.Matrix([dw,ds,dh])
gradient=s.Matrix([s.diff(reserve,v) for v in (w,sigma,h)])
second=(direction.T*s.hessian(reserve,(w,sigma,h))*direction)[0]
gradient_work=((20900*w**3*sigma**2-35112*w**17+6650*w**3*h)*dw**2-
    41800*w**4*sigma*dw*ds-6650*w**4*dw*dh-4180*w**5*ds**2)
zero(6*s.diff(reserve,w)*dw**2/w-second-gradient_work,
     'parabolic reserve gradient work')
shifted=(125400*w**3*sigma**2-5852*w**17+39900*w**3*h)*dw**2-4180*w**5*ds**2
zero(gradient_work+10*dw*gradient.dot(direction)/w-shifted,
     'complete gradient drift correction')
stationary={w:1,sigma:0,h:1,dw:1,ds:0,dh:-s.Rational(6251,665)}
zero(gradient.dot(direction).subs(stationary),'stationary scalar spatial jet')
zero(gradient_work.subs(stationary)-34048,'positive scalar diffusion work')

# These are genuine planar-flow correlations: the directional pressure
# and strain vanish, h=Omega^2/10, D h=-nu|grad Omega|^2/5.
# They pay the mixed gradients exactly and recover convex-power decay.
physical_pressure=s.symbols('physical_pressure',real=True)
zero(reserve.subs(h,-physical_pressure-s.Rational(9,14)*sigma**2+w**14/10)-
     w**5*(s.Rational(3325,2)*sigma**2+s.Rational(441,2)*w**14-665*physical_pressure),
     'physical directional pressure form')
zero(reserve.subs({sigma:0,h:w**14/10})-s.Rational(441,2)*w**19,
     'planar physical vorticity power')
planar_work=gradient_work.subs({sigma:0,h:w**14/10,ds:0,dh:s.Rational(7,5)*w**13*dw})
planar_work+=665*w**5*(-s.Rational(49,5)*w**12*dw**2)
zero(planar_work+50274*w**17*dw**2,'planar correlated diffusion balance')

# Initially the remote pressure excess equals the instantaneous expression
# -p_directional-(9/14)sigma^2+Omega^2/10. Their derivatives need not agree.
# Keep the reference flow's own pressure derivative as an independent
# finite quantity; it does not depend on the amplitude of remote packets.
reference_rate,kappa,delta=s.symbols('reference_rate kappa delta',real=True)
initial_sigma_rate=-(s.Rational(5,14))*sigma**2-w**14/10+h
remote_rate=(-7*sigma-gamma+(18*kappa-delta/2)*sigma)*h
input_rate=(remote_rate-reference_rate-s.Rational(9,7)*sigma*initial_sigma_rate+
    s.Rational(1,5)*sigma*w**14)
expected_mismatch=(-reference_rate+s.Rational(45,98)*sigma**3+
    s.Rational(23,70)*sigma*w**14-s.Rational(9,7)*sigma*h)
zero(input_rate-remote_rate-expected_mismatch,'initial pressure-summary derivative mismatch')
instantaneous_production=(s.diff(reserve,w)*sigma*w/7+
    s.diff(reserve,sigma)*initial_sigma_rate+s.diff(reserve,h)*input_rate)
zero(s.diff(instantaneous_production,h).subs(sigma,-2*a)-
     665*w**5*(s.Rational(18,7)*a-gamma-36*a*kappa+a*delta),
     'instantaneous pressure-input reserve growth coefficient')


def radial_grid(radius,n):
    nodes,w=leggauss(n)
    rr=radius*(nodes+1)/2
    rw=radius*w/2
    mu=nodes[None,:]
    sr=rr[:,None]
    cyl=sr*np.sqrt(1-mu*mu)
    axial=sr*mu
    weights=2*np.pi*rw[:,None]*sr**2*w[None,:]
    return cyl,axial,weights,rr,rw


def profile(rad,radius):
    den=radius**2-rad**2
    logder=-2*rad*radius**2/den**2
    logsecond=-2*radius**2/den**2-8*rad**2*radius**2/den**3
    value=np.exp(-rad**2/den)
    return value,value*logder,value*(logder**2+logsecond)


def packet_response(n,radius=.4,L=2.):
    cyl,local_z,weight,rr,rw=radial_grid(radius,n)
    chi,dchi,ddchi=profile(rr,radius)
    I=np.sum(rw*rr**4*chi**2)
    K=np.sum(rw*rr**6*chi**2)
    G=np.sum(rw*rr**4*dchi**2)
    gamma_over_nu=2*G/I
    W=cyl*chi[:,None]
    Wr=chi[:,None]+cyl**2*dchi[:,None]/rr[:,None]
    Wz=cyl*local_z*dchi[:,None]/rr[:,None]
    zz=local_z+L
    Wt=-cyl*Wr+2*zz*Wz-W   # a=1, keeping centre translation.
    Wheat=cyl*(ddchi+4*dchi/rr)[:,None]
    sep2=cyl*cyl+zz*zz
    kernel=3*(1-5*zz*zz/sep2)/(4*np.pi*sep2**2.5)
    measured=np.sum(weight*kernel*2*W*Wt)
    measured_heat=np.sum(weight*kernel*2*W*Wheat)
    H=-8*I/L**5
    predicted=(8-18*K/(I*L*L))*H
    error=abs(measured-predicted)/abs(predicted)
    heat_error=abs(measured_heat+gamma_over_nu*H)/abs(gamma_over_nu*H)
    if not np.all(np.isfinite([error,heat_error])) or (n>=64 and max(error,heat_error)>1e-7):
        raise AssertionError(('packet stress derivative',n,error,heat_error))
    return {'order':n,'moment_ratio':K/(I*L*L),'gamma_over_nu':gamma_over_nu,
            'carried_relative_error':error,'heat_relative_error':heat_error,
            'carried_coefficient':measured/H,
            'reaction_coefficient':6-18*K/(I*L*L),
            'full_coefficient':14-36*K/(I*L*L),'I':I,'K':K}


def exterior_hessian(cyl,z,I):
    r2=cyl*cyl+z*z
    dist=np.sqrt(r2)
    normal=np.stack([cyl/dist,np.zeros_like(cyl),z/dist],axis=-1)
    axis=np.array([0.,0.,1.])
    cos=normal[...,2]
    nn=normal[..., :,None]*normal[...,None,:]
    na=normal[..., :,None]*axis+axis[:,None]*normal[...,None,:]
    aa=axis[:,None]*axis
    angular=105*cos[...,None,None]**2*nn-15*(nn+cos[...,None,None]**2*np.eye(3)+
                   2*cos[...,None,None]*na)+3*(np.eye(3)+2*aa)
    # E=8pi I/3, so -E/(8pi)=-I/3.
    return -I*angular/(3*dist[...,None,None]**5)


def compact_background_gradient(cyl,z,RB):
    rad=np.sqrt(cyl*cyl+z*z)
    t=rad/RB-1
    cutoff=np.zeros_like(t)
    first=np.zeros_like(t)
    second=np.zeros_like(t)
    inside=t<=0
    cutoff[inside]=1
    transition=(t>0)&(t<1)
    tt=t[transition]
    logit=-1/tt+1/(1-tt)
    sigmoid=expit(logit)
    lp=1/tt**2+1/(1-tt)**2
    lpp=-2/tt**3+2/(1-tt)**3
    cutoff[transition]=expit(-logit)
    first[transition]=-sigmoid*(1-sigmoid)*lp/RB
    second[transition]=-sigmoid*(1-sigmoid)*((1-2*sigmoid)*lp**2+lpp)/RB**2
    # v_r=rho (chi+z^2 chi'/r), v_z=-z(2chi+rho^2 chi'/r), a=1.
    g=first/rad
    gr=(second/rad-first/rad**2)
    rr=cutoff+z*z*g+cyl*cyl*g+cyl*cyl*z*z*gr/rad
    phiphi=cutoff+z*z*g
    zz=-2*cutoff-cyl*cyl*g-2*z*z*g-cyl*cyl*z*z*gr/rad
    rz=cyl*(3*z*g+z**3*gr/rad)
    zr=-z*(4*cyl*g+cyl**3*gr/rad)
    return rr,phiphi,zz,rz,zr


def cutoff_error(n,RB,L=2.):
    nodes,w=leggauss(n)
    mu=nodes[None,:]
    total=0.
    # Two radial panels: the smooth transition and the exterior tail.
    # The second uses r=2RB/t and covers infinity without truncation.
    for tail in (False,True):
        t=(nodes+1)/2
        if tail:
            rr=2*RB/t
            rw=RB*w/t**2
        else:
            rr=RB*(1+t)
            rw=RB*w/2
        sr=rr[:,None]
        cyl=sr*np.sqrt(1-mu*mu)
        z=sr*mu
        P=exterior_hessian(cyl,z-L,1.)+exterior_hessian(cyl,z+L,1.)
        br,bphi,bz,brz,bzr=compact_background_gradient(cyl,z,RB)
        source=-2*((br-1)*P[...,0,0]+(bphi-1)*P[...,1,1]+
                   (bz+2)*P[...,2,2]+(brz+bzr)*P[...,0,2])
        kernel=(3*mu*mu-1)/(4*np.pi*sr**3)
        weight=2*np.pi*rw[:,None]*sr**2*w[None,:]
        total+=np.sum(weight*kernel*source)
    H_pair=-16/L**5
    tt=(nodes+1)/2
    logit=-1/tt+1/(1-tt)
    sigmoid=expit(logit)
    neg_derivative=sigmoid*(1-sigmoid)*(1/tt**2+1/(1-tt)**2)/RB
    cutoff_moment=np.sum(RB*w/2*neg_derivative/(RB*(1+tt))**7)
    exact_ratio=(80/7)*L**7*cutoff_moment
    relative=abs(total/H_pair-exact_ratio)/abs(exact_ratio)
    if not np.isfinite(relative) or relative>1e-7:
        raise AssertionError(('finite cutoff correction',RB,relative))
    return {'order':n,'background_radius':RB,'error_over_initial_axial_pressure':total/H_pair,
            'exact_correction_ratio':exact_ratio,'relative_error':relative}


def core_pressure_check(n):
    nodes,w=leggauss(n)
    RB=3.
    rr=RB*(1+(nodes+1)/2)
    rw=RB*w/2
    mu=nodes[None,:]
    sr=rr[:,None]
    cyl=sr*np.sqrt(1-mu*mu)
    zz=sr*mu
    br,bp,bz,brz,bzr=compact_background_gradient(cyl,zz,RB)
    source=br*br+bp*bp+bz*bz+2*brz*bzr
    value=-2+np.sum(rw[:,None]*w[None,:]*(3*mu*mu-1)/(2*sr)*source)
    error=abs(value+18/7)
    if not np.isfinite(error) or error>1e-8:
        raise AssertionError(('core pressure',error))
    return {'axial_pressure_over_a_squared':value,'absolute_error':error}


if __name__=='__main__':
    print(json.dumps({'status':'exact checks passed',
      'scope':'initial physical derivative; affine comparison plus finite-support correction',
      'packet_checks':[packet_response(n) for n in (32,64)],
      'finite_background':[cutoff_error(64,RB) for RB in (8.,16.,32.)],
      'background_core_pressure':core_pressure_check(64)},indent=2))
