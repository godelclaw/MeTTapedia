#!/usr/bin/env python3
"""Exact initial swirl-pressure identities, with an independent quadrature.

The physical rate is an initial-time statement. The interval certificate
needs an explicit geometry defect; no arbitrary-flow bound is asserted.
See the labs README for the analytic derivation and formal scope.
"""
import json
import numpy as np
import sympy as s
from numpy.polynomial.legendre import leggauss


def zero(expr, label):
    value=s.factor(s.together(expr))
    if value != 0:
        value=s.simplify(value)
    if value != 0:
        raise AssertionError((label,value))


def matrix_zero(matrix,label):
    for i,entry in enumerate(matrix):
        zero(entry,(label,i))


r=s.symbols('r',positive=True)
chi=s.Function('chi')(r)
J=s.Function('J')(r)
f=2*J/r**5
subs={s.diff(J,r,2):4*r**3*chi+r**4*s.diff(chi,r),s.diff(J,r):r**4*chi}
zero((s.diff(f,r,2)+6*s.diff(f,r)/r).subs(subs)-2*s.diff(chi,r)/r,
     'quadrupole radial pressure feedback equation')
b, gamma, beta=s.symbols('b gamma beta',real=True)
h11,h22,h12,h13,h23=s.symbols('h11 h22 h12 h13 h23',real=True)
H=s.Matrix([[h11,h12,h13],[h12,h22,h23],[h13,h23,-h11-h22]])
R=s.Matrix([[0,-1,0],[1,0,0],[0,0,0]])
x,y,z=s.symbols('x y z',real=True)
X=s.Matrix([x,y,z])
phi=(X.T*H*X)[0]/2
rotation=sum((R*X)[i]*s.diff(phi,q) for i,q in enumerate((x,y,z)))
matrix_zero(s.hessian(rotation,(x,y,z))-(H*R-R*H),'rotation of pressure Hessian')
rate=-gamma*H+beta*(H*R-R*H)
zero(2*s.trace(H*rate)+2*gamma*s.trace(H*H),'pressure size decays; commutator is free')
zero(s.trace(H*(H*R-R*H)),'signed rotation cancellation')

# For a radial swirl, its self-advection and own pressure contribute zero
# to the nonlinear pressure-source derivative, pointwise. This leaves
# precisely the Hessians of the other disjoint packets in the quadrature.
g,gp=s.symbols('g gp',real=True)
axis=s.Matrix([0,0,1])
spin=R*X
B=g*R+gp*spin*X.T  # gp stands for chi'(r)/r.
a0,a1,a2,a3=s.symbols('a0 a1 a2 a3',real=True)
self_hessian=(a0*s.eye(3)+a1*X*X.T+
              a2*(axis*X.T+X*axis.T)+a3*axis*axis.T)
zero(s.trace(B*self_hessian),'axisymmetric self-pressure source cancellation')
advection_gradient=g*g*R*R+2*g*gp*(R*R*X)*X.T
zero(s.trace(B*advection_gradient),'self-advection source cancellation')
zero(s.trace(B*H)-gp*(X.T*H*spin)[0],'cross-pressure source contraction')

# The radial heat operator gives the dissipation factor gamma by integration
# by parts. Smooth compact support removes the endpoint terms.
zero(s.diff(r**4*chi*s.diff(chi,r),r)-r**4*s.diff(chi,r)**2-
     r**4*chi*(s.diff(chi,r,2)+4*s.diff(chi,r)/r),
     'radial swirl heat dissipation identity')

# Coherent radial swirls leave their class at once: in a constant-profile
# core the nonlinear tangent has a nonzero meridional component.
Pcore=b*b*s.diag(s.Rational(4,5),s.Rational(4,5),s.Rational(2,5))
meridional=b*b*s.diag(s.Rational(1,5),s.Rational(1,5),s.Rational(-2,5))
matrix_zero(-b*b*R*R-Pcore-meridional,'initial meridional core feedback')

# An external pressure can cancel that initial core tangent, but viscosity
# immediately changes the required pressure. The matching Hessian commutes
# with the core rotation, so the first pressure-excess rate is -gamma H.
Hbalance=meridional
matrix_zero(-b*b*R*R-Pcore-Hbalance,'balanced initial core tangent')
matrix_zero(Hbalance*R-R*Hbalance,'balanced pressure has no rotation rate')

# Every trace-free diagonal target is a positive combination of I-3 n n^T.
c,a,h1,h2=s.symbols('c a h1 h2',real=True)
eigenvalues=[h1,h2,-h1-h2]
energies=[(a-v)/(3*c) for v in eigenvalues]
response=s.zeros(3)
for i,e in enumerate(energies):
    n=s.eye(3)[:,i]
    response += c*e*(s.eye(3)-3*n*n.T)
matrix_zero(response-s.diag(*eigenvalues),'positive pressure cone reconstruction')
zero(sum(energies)-a/c,'pressure cone total energy')

# Different packet widths invalidate damping of the combined observed
# pressure. Each parent's response shrinks, but a cancellation disappears.
T1=s.diag(-2,1,1)
T2=s.diag(1,-2,1)
mixed_H=T1+T2/4
mixed_heat_rate=-gamma*T1-25*gamma*T2  # rates gamma and 100*gamma.
zero(s.trace(mixed_H*mixed_H)-s.Rational(39,8),'unequal-width pressure norm')
zero(2*s.trace(mixed_H*mixed_heat_rate)-s.Rational(129,2)*gamma,
     'unequal-width viscosity increases combined pressure norm')
zero(2*s.trace(mixed_H*(mixed_heat_rate+beta*(mixed_H*R-R*mixed_H)))-
     s.Rational(129,2)*gamma,'core rotation does not change unequal-width growth')

# Rotate the unequal-width example so its dangerous direction is the
# core vorticity axis. The core is a plateau, so the relevant initial
# Laplacians vanish: the external pressure is harmonic throughout it.
# These are actual initial jets, not a spatially homogeneous closure.
Tz=s.diag(1,1,-2)
Tx=s.diag(-2,1,1)
danger_H=Tz+Tx/4
P=Pcore+danger_H
P1=-gamma*Tz-25*gamma*Tx+s.Rational(2,5)*b*(danger_H*R-R*danger_H)
B0=b*R
B1=-B0*B0-P
B2=-B1*B0-B0*B1-P1
omega0=2*b*axis
omega2=B1*omega0
omega3=B2*omega0+B0*omega2
M2=2*B1
M3=B2+B2.T+B0*M2+M2*B0.T
zero(2*omega0.dot(omega3)-(omega0.T*M3*omega0)[0],
     'metric vorticity third derivative still cancels')
zero(2*omega0.dot(omega3)-184*b*b*gamma,
     'physical vorticity squared third derivative from disappearing cancellation')
zero((2*omega0.dot(omega2)).subs(b,1)-s.Rational(54,5),
     'at unit core amplitude the second derivative is positive as well')


def cross_matrix(axis):
    x,y,z=axis
    return np.array([[0.,-z,y],[z,0.,-x],[-y,x,0.]])


def exterior_hessian(points,centre,axis,energy):
    sep=points-centre
    radius=np.linalg.norm(sep,axis=-1)
    normal=sep/radius[...,None]
    cos=np.sum(normal*axis,axis=-1)
    nn=normal[..., :,None]*normal[...,None,:]
    na=normal[..., :,None]*axis[None,:]+axis[:,None]*normal[...,None,:]
    aa=axis[:,None]*axis[None,:]
    I=np.eye(3)
    angular=105*cos[...,None,None]**2*nn-15*(nn+cos[...,None,None]**2*I+2*cos[...,None,None]*na)+3*(I+2*aa)
    return -energy*angular/(8*np.pi*radius[...,None,None]**5)


def grid(radius,count):
    nodes,w=leggauss(count)
    rho=radius*(nodes+1)/2
    radial_weight=radius*w/2
    mu=nodes[None,:,None]
    phi=2*np.pi*np.arange(2*count)[None,None,:]/(2*count)
    rr=rho[:,None,None]
    xx=rr*np.sqrt(1-mu**2)*np.cos(phi)
    yy=rr*np.sqrt(1-mu**2)*np.sin(phi)
    zz=np.broadcast_to(rr*mu,xx.shape)
    local=np.stack([xx,yy,zz],axis=-1).reshape(-1,3)
    weights=np.broadcast_to(radial_weight[:,None,None]*w[None,:,None]*rr**2*(2*np.pi/(2*count)),xx.shape).reshape(-1)
    return local,weights,rho,radial_weight


def profile(rr,radius,amplitude):
    q=rr/radius
    value=amplitude*np.exp(-q*q/(1-q*q))
    derivative=value*(-2*rr*radius**2/(radius**2-rr**2)**2)
    return value,derivative


def experiment(count,unequal_widths=False):
    # The same C-infinity radial shape is used for all remote packets.
    # Axis reversal in each antipodal pair makes the remote velocity even.
    Q=np.array([[1,2,2],[2,1,-2],[-2,2,-1]],dtype=float)/3
    if np.linalg.norm(Q.T@Q-np.eye(3))>1e-14:
        raise AssertionError('orthogonal packet axes')
    core_b=.9
    distance=2.5
    remote_radius=.35
    packets=[(np.zeros(3),np.array([0.,0.,1.]),.7,core_b)]
    for i,amp in enumerate((.8,1.2,1.6)):
        axis=Q[:,i]
        radius=remote_radius*(1+.3*i) if unequal_widths else remote_radius
        for sign in (-1.,1.):
            packets.append((sign*distance*axis,sign*axis,radius,amp))
    evaluated=[]
    for centre,axis,radius,amp in packets:
        local,weight,rad,radweight=grid(radius,count)
        v,dv=profile(rad,radius,amp)
        energy=(8*np.pi/3)*np.sum(radweight*rad**4*v*v)
        gamma_over_nu=2*np.sum(radweight*rad**4*dv*dv)/np.sum(radweight*rad**4*v*v)
        evaluated.append((centre,axis,radius,amp,local,weight,energy,gamma_over_nu))
    Hremote=sum((exterior_hessian(np.zeros((1,3)),c,n,E)[0]
                 for c,n,rad,amp,loc,w,E,g in evaluated[1:]),np.zeros((3,3)))
    outputs=[]
    for index,(centre,axis,radius,amp,local,weight,energy,gam) in enumerate(evaluated):
        points=centre+local
        other_pressure=sum((exterior_hessian(points,c,n,E)
                            for j,(c,n,rad,a,loc,w,E,g) in enumerate(evaluated) if j!=index),
                           np.zeros((len(points),3,3)))
        rr=np.linalg.norm(local,axis=-1)
        chi,deriv=profile(rr,radius,amp)
        spin=np.cross(axis,local)
        # The skew part of grad u has zero trace against a symmetric Hessian.
        source=-2*(deriv/rr)*np.einsum('ni,nij,nj->n',local,other_pressure,spin)
        observer_radius=np.linalg.norm(points,axis=-1)
        observer_normal=points/observer_radius[:,None]
        newton2=(3*observer_normal[:,:,None]*observer_normal[:,None,:]-np.eye(3))/(4*np.pi*observer_radius[:,None,None]**3)
        outputs.append(np.sum(weight[:,None,None]*source[:,None,None]*newton2,axis=0))
    total=sum(outputs,np.zeros((3,3)))
    expected=(2*core_b/5)*(Hremote@cross_matrix(np.array([0.,0.,1.]))-cross_matrix(np.array([0.,0.,1.]))@Hremote)
    error=np.linalg.norm(total-expected)/np.linalg.norm(expected)
    remote=np.linalg.norm(sum(outputs[1:],np.zeros((3,3))))/np.linalg.norm(expected)
    gamma_values=[item[-1] for item in evaluated[1:]]
    if not unequal_widths and max(gamma_values)-min(gamma_values)>1e-10:
        raise AssertionError('common viscous decay rate')
    if remote>1e-10:
        raise AssertionError(('remote parity cancellation failed',remote))
    if count>=40 and error>1e-7:
        raise AssertionError(('pressure history quadrature failed',count,error,total,expected))
    return {'resolution':count,'unequal_widths':unequal_widths,
            'relative_commutator_error':error,
            'relative_remote_nonlinear_remainder':remote,
            'gamma_over_nu':gamma_values,
            'remote_pressure_eigenvalues':np.linalg.eigvalsh(Hremote).tolist(),
            'relative_trace_error':abs(np.trace(total))/np.linalg.norm(expected)}


if __name__ == '__main__':
    print(json.dumps({'status':'exact checks passed',
     'physical_claim':'initial pressure-excess rate; radial packet geometry is not invariant',
     'interval_claim':'conditional matrix reserve; the actual geometry-defect cost remains open',
     'quadrature_kind':'numerical cross-check, not a proof',
     'unequal_width_exact_production':'129 gamma / 2 > 0 for gamma > 0',
     'plateau_directional_ratio_third_derivative':'184 b^2 gamma / (4 b^2 + eta)',
     'quadrature':[experiment(n) for n in (24,40)]+[experiment(40,True)]},indent=2))
