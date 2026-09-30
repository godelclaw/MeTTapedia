#!/usr/bin/env python3
"""Quadrature of the complete joint receiver on explicit planar NS data.

The phase variables are (phi=n*x,y); physical x derivatives and Helmholtz
symbols retain n. All initial polynomial NS outputs are resolved. The
nonpolynomial receiver is approximated by phase-grid quadrature, with
independent grids. This is a spatial diagnostic, not a time evolution or
a continuum enclosure. The selector threshold b=1 is not the route's
above-initial-supremum choice.
"""

import json
import numpy as np
from cellular_parent_history import Prefix


def dot(A,B): return np.einsum('...ij,...ij->...',A,B)
def vecdot(a,b): return np.einsum('...i,...i->...',a,b)
def sym(A): return (A+np.swapaxes(A,-1,-2))/2

def curl(B):
    return np.stack((B[...,2,1]-B[...,1,2],B[...,0,2]-B[...,2,0],B[...,1,0]-B[...,0,1]),axis=-1)

def cadjoint(v):
    A=np.zeros(v.shape[:-1]+(3,3),dtype=v.dtype)
    A[...,0,1]=-v[...,2];A[...,1,0]=v[...,2]
    A[...,0,2]=v[...,1];A[...,2,0]=-v[...,1]
    A[...,1,2]=-v[...,0];A[...,2,1]=v[...,0]
    return A

def outer(v,w): return np.einsum('...i,...j->...ij',v,w)
def mv(A,v): return np.einsum('...ij,...j->...i',A,v)
def sm(c,A): return c[...,None,None]*A


def slots(B,P):
    S=sym(B);w=curl(B);W=vecdot(w,w);Sw=mv(S,w);V=vecdot(w,Sw)
    Qs=dot(S,S);Z=vecdot(Sw,Sw);r=dot(B,B);q=np.sqrt(1+dot(P,P));Q=r+q
    gW=2*cadjoint(w)
    gV=outer(w,w)+2*cadjoint(Sw)
    gT=sm(2*V/(W+1),gV)-sm(V*V/(W+1)**2,gW)
    gZ=2*sym(outer(Sw,w))+2*cadjoint(mv(S,Sw))
    p0=5*V*V/(W+1)+(63/95)*W*W-2*vecdot(w,mv(P,w))
    c0=5*V*V/(W+1)+(4/7)*Z+(10/21)*Qs*W+(44/95)*W*W
    pB=5*gT+sm((126/95)*W,gW)-4*cadjoint(mv(P,w))
    cB=5*gT+(4/7)*gZ+(10/21)*(sm(2*W,S)+sm(Qs,gW))+sm((88/95)*W,gW)
    A=p0+48*Q*Q;C=c0+48*Q*Q;rho=np.sqrt(A*A+C*C)
    TB=sm(A/rho,pB+sm(192*Q,B))+sm(C/rho,cB+sm(192*Q,B))
    TP=sm(96*Q*(A+C)/(rho*q),P)-sm(2*A/rho,outer(w,w))
    Psi=1+rho;Phi=Psi+dot(P,P)
    a=1-1/Phi**2
    beta=2*(1-1/Phi)
    return Phi,sm(a,TB),sm(a,TP+2*P),sm(a,TP),Q,a,beta,TB,TP


class Grid:
    def __init__(self,n,N):
        self.n=n;self.N=N
        f=np.fft.fftfreq(n)*n
        self.K=np.zeros((n,n,3));self.K[...,0]=N*f[:,None];self.K[...,1]=f[None,:]
        k2=np.sum(self.K**2,axis=-1)
        self.inv=np.divide(1,k2,out=np.zeros_like(k2),where=k2!=0)
        t=np.arange(n)*2*np.pi/n
        self.phi=t[:,None];self.y=t[None,:]
    def fft(self,v):return np.fft.fftn(v,axes=(0,1))
    def ifft(self,v):return np.fft.ifftn(v,axes=(0,1)).real
    def deriv(self,v,j):
        ext=(None,)*(v.ndim-2)
        return self.ifft(self.fft(v)*(1j*self.K[...,j])[(...,)+ext])
    def lap(self,v):
        ext=(None,)*(v.ndim-2)
        return self.ifft(self.fft(v)*(-np.sum(self.K**2,axis=-1))[(...,)+ext])
    def jac(self,u):return np.stack([self.deriv(u,j) for j in range(3)],axis=-1)
    def observe(self,T):
        th=self.fft(T);kh=self.K
        ph=-np.einsum('...i,...j,...ij->...',kh,kh,th)*self.inv
        return self.ifft(-sm(ph,outer(kh,kh)))
    def negative_grad(self,v):
        vh=self.fft(v)
        return self.ifft(-self.K*np.einsum('...i,...i->...',self.K,vh)[...,None]*self.inv[...,None])


def check(n,N,nu=.1):
    g=Grid(n,N)
    u=np.zeros((n,n,3));u[...,0]=N*np.sin(g.y);u[...,1]=np.sin(g.phi)/N**2
    B=g.jac(u)
    p=2*np.cos(g.y)*np.cos(g.phi)/(N*N+1)
    P=g.jac(np.stack([g.deriv(p,j) for j in range(3)],axis=-1))
    G=B@np.swapaxes(B,-1,-2)
    directP=g.observe(outer(u,u))
    if np.max(abs(directP-P))>1e-9:
        raise ArithmeticError('canonical pressure mismatch')
    Phi,M,Nt,Nh,Q,a,beta,TB,TP=slots(B,P)
    native=np.zeros((n,n));divM=np.zeros((n,n,3));divN=np.zeros((n,n,3));rawN=0;weightedN=0;weightedM=0
    step=1e-20
    for j in range(3):
        E=g.deriv(B,j);L=g.deriv(P,j)
        dPsi,ddPsi=Prefix.observable(B,P,(E,L))
        dPhi=dPsi+2*dot(P,L)
        J=nu*2*dPhi*dPhi/Phi**3
        native+=a*nu*(ddPsi+2*dot(L,L))+J
        vals=slots(B+1j*step*E,P+1j*step*L)
        dM=vals[1].imag/step;dN=vals[2].imag/step
        divM+=dM[..., :,j];divN+=dN[..., :,j]
        rawN+=nu*np.mean(dot(dN,dN))
        weightedN+=nu*np.mean(np.sqrt(1+dot(P,P))/Q*dot(dN,dN))
        weightedM+=nu*np.mean(dot(dM,dM)/Q)
    V=g.negative_grad(divN)
    ell=-2*mv(np.swapaxes(B,-1,-2),V)
    Lambda=-divM+ell
    norm=nu*np.mean(vecdot(Lambda,Lambda)/Q)
    ut=-mv(B,u)-np.stack([g.deriv(p,j) for j in range(3)],axis=-1)+nu*g.lap(u)
    Bt=g.jac(ut)
    Pt=g.observe(outer(u,ut)+outer(ut,u))
    Ct=2*nu*G
    Ph_t=Pt+g.observe(Ct)
    actual_dPsi,_=Prefix.observable(B,P,(Bt,Ph_t))
    phi_t=actual_dPsi+2*dot(P,Pt)
    F_t=a*phi_t-beta*np.trace(Ct,axis1=-2,axis2=-1)/3
    Lambda_C=g.observe(Nh)-sm(beta/3,np.broadcast_to(np.eye(3),(n,n,3,3)))
    velocitywork=np.mean(vecdot(Lambda,ut))
    memorywork=np.mean(dot(Lambda_C,Ct))
    direct=np.mean(F_t)
    nonlinear_ut=-mv(B,u)-np.stack([g.deriv(p,j) for j in range(3)],axis=-1)
    nonlinear_ph_t=g.observe(outer(u,nonlinear_ut)+outer(nonlinear_ut,u))
    npdot,_=Prefix.observable(B,P,(g.jac(nonlinear_ut),nonlinear_ph_t))
    nonlinear_work=np.mean(a*(npdot+2*dot(P,nonlinear_ph_t)))
    cap=-np.mean(beta*np.trace(Ct,axis1=-2,axis2=-1)/3)
    if np.min(native)<-2e-12*max(1,np.max(native)):
        raise ArithmeticError('negative completed diffusion')
    # Scale the work check by the physical work and diffusion. The much
    # larger unpaid norm would hide an error in this identity.
    scale=max(1,abs(direct),abs(velocitywork),abs(memorywork),np.mean(native))
    return dict(grid=n,parent_frequency=N,norm_cost=norm,native=float(np.mean(native)),
                ratio=float(norm/np.mean(native)),norm_over_N6=float(norm/N**6),
                native_over_N4=float(np.mean(native)/N**4),
                M_cost_ratio=float(weightedM/np.mean(native)),
                raw_N_gradient_ratio=float(rawN/np.mean(native)),
                weighted_N_gradient_ratio=float(weightedN/np.mean(native)),
                nonlinear_work=float(nonlinear_work),capacity_work=float(cap),
                full_initial_mass_derivative=float(direct),
                full_cotangent_mass_derivative=float(velocitywork+memorywork),
                mass_identity_relative_error=float(abs(direct-velocitywork-memorywork)/scale),
                signed_balance_relative_error=float(abs(direct+np.mean(native)-cap)/scale),
                memory_pressure_source_max=float(np.max(abs(g.observe(Ct)))))


def diagnose():
    cases=[check(grid,n) for grid in (128,256) for n in (4,8,16,32,64)]
    coarse={row['parent_frequency']:row for row in cases if row['grid']==128}
    comparisons=[]
    for row in cases:
        if row['grid']!=256:
            continue
        old=coarse[row['parent_frequency']]
        residuals={name:abs(row[name]-old[name])/max(1,abs(row[name]))
                   for name in ('norm_cost','native','ratio','weighted_N_gradient_ratio')}
        if max(residuals.values())>2e-6:
            raise ArithmeticError('independent phase quadratures do not agree')
        if row['M_cost_ratio']>15000 or row['weighted_N_gradient_ratio']>3500:
            raise ArithmeticError('local complete-slot payment mismatch')
        if max(row['mass_identity_relative_error'],row['signed_balance_relative_error'])>1e-8:
            raise ArithmeticError('full velocity/memory chain rule mismatch')
        if abs(row['nonlinear_work'])>1e-10*max(1,row['native']):
            raise ArithmeticError('exact nonlinear phase cancellation mismatch')
        comparisons.append({'parent_frequency':row['parent_frequency'],
                            'relative_quadrature_changes':residuals})
    theta=48+63/95
    core=48+1399/1995
    gamma=np.hypot(theta,core)
    kappa=(theta+core)/gamma
    t=np.arange(512)*2*np.pi/512
    c=np.cos(t)[None,:];sp=np.sin(t)[:,None];cp=np.cos(t)[:,None]
    q=np.sqrt(1+4*c*c*cp*cp)
    limit_cost=.1*(384*kappa)**2*np.mean(c**6*sp**2/q**6)
    limit_native=.1*np.mean(12*gamma*c*c*(1-c*c)+384*kappa*c**4*sp**2/q**3)
    return {'cases':cases,'independent_quadratures':comparisons,
            'analytic_limit_quadrature':{'cost_over_n6':float(limit_cost),
                'native_over_n4':float(limit_native),
                'ratio_over_n2':float(limit_cost/limit_native)},
            'scope':'spatial continuum-PDE diagnostic; no time-history estimate or continuum enclosure'}


if __name__=='__main__':
    print(json.dumps(diagnose(),indent=2))
