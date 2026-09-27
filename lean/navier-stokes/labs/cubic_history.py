#!/usr/bin/env python3
"""Numerical signed history of a cubic Euler amplitude variation.

The first-order parents A=(2,1), Bbar=(-4,-1), their quadratic descendants
AA=(4,2), ABbar=(-2,0), and the cubic recipient C=(0,1) all evolve. Labels
are (angular index, axial index), with axial wave number twice the index.
The base is the stationary inviscid Gaussian column. This is the exact
ancestry of C at cubic order in the continuum amplitude expansion.

Horizontal Fourier Galerkin discretization uses a periodic square and
strict two-thirds dealiasing; axial labels are retained exactly. The square
only approximates rotational symmetry. RK4 advances the fields and the
signed discounted forcing and residual integrals at the same stages.

The rational radial test is the one in generated_mode_coupling.py. Its
operator residual is included explicitly; it is not assumed to be an exact
eigenfunction. The initial jet is checked against the full independently
computed polynomial source in mixed_helical_parent.py.

This is a numerical diagnostic, not a validated PDE enclosure, not a full
nonlinear Navier--Stokes evolution, and not a finite-energy R3 background.
Requires NumPy and SciPy. See README.md for refinement data and limitations.
"""
import argparse,json,time
import numpy as np
from scipy.fft import fftn,ifftn
from scipy.special import eval_genlaguerre

def cross(a,b):
    return np.stack([a[...,1,:,:]*b[...,2,:,:]-a[...,2,:,:]*b[...,1,:,:],
                     a[...,2,:,:]*b[...,0,:,:]-a[...,0,:,:]*b[...,2,:,:],
                     a[...,0,:,:]*b[...,1,:,:]-a[...,1,:,:]*b[...,0,:,:]],axis=-3)

class Probe:
    def __init__(self,n,box):
        self.n=n;self.box=box
        x=(np.arange(n)/n-.5)*box
        self.x,self.y=np.meshgrid(x,x,indexing='ij')
        r2=self.x*self.x+self.y*self.y;E=np.exp(-r2);w=self.x+1j*self.y
        kh=2*np.pi*np.fft.fftfreq(n,box/n)
        kx,ky=np.meshgrid(kh,kh,indexing='ij')
        self.mask=(np.abs(kx)<2*np.pi*n/(3*box))&(np.abs(ky)<2*np.pi*n/(3*box))
        labels=[2,-2,4,0,2]
        self.k=np.array([np.array([kx,ky,np.full_like(kx,k)]) for k in labels])
        ks=(self.k*self.k).sum(axis=1)
        self.inv=np.divide(1,ks,out=np.zeros_like(ks),where=ks>0)
        self.area=box**2/n**4/(2*np.pi)
        def curl_potential(p):
            q=self.fft(p)*self.mask
            return np.array([1j*ky*q,-1j*kx*q,np.zeros_like(q)])
        self.vhat=curl_potential(E)
        self.v=self.ifft(self.vhat)
        kbase=np.array([kx,ky,np.zeros_like(kx)])
        self.wv=self.ifft(1j*cross(kbase,self.vhat))
        self.initial=np.zeros((5,3,n,n),complex)
        self.initial[0]=curl_potential(w*w*E)
        self.initial[1]=curl_potential(np.conj(w)**4*(1-.4*r2)*E)
        poly=8*r2**4+136*r2**3-262*r2**2+27*r2+18
        Q4=8*r2**4-110*r2**3+346*r2**2-275*r2+27
        raw=np.array([8j/5*self.x*poly*E**3-8/5*self.y*r2*Q4*E**3,
                      8j/5*self.y*poly*E**3+8/5*self.x*r2*Q4*E**3,
                      -32/5*r2**3*(6*r2**2-25*r2+20)*E**3])
        self.jet=self.project_one(self.fft(raw),4)
        coeff=np.array([129288,-103710,405,2339,11058,4912,3067,42,
                        -645,-1238,-1012,-844,-499,-285,-77,28,
                        104,123,128,110,91,65,46,25,14,0,-3,-13,-8,-18,-6,-19])/100000
        L=np.array([eval_genlaguerre(j,1,2*r2) for j in range(33)])
        P=np.einsum('j,jxy->xy',coeff,L[:32])
        AP=np.zeros_like(P)
        for j,c in enumerate(coeff):
            AP+=c*(j+2)*L[j]+c*(j+1)/2*L[j+1]
            if j: AP+=c*(j+1)/2*L[j-1]
        self.mu=.105;self.gamma=np.sqrt(self.mu)
        f_over_r=E*P;Af_over_r=E*AP
        Phi=16*(1-r2)*E**2
        R_over_r=-Phi*f_over_r-self.mu*Af_over_r
        self.testhat=self.fft(np.array([
            self.gamma*Af_over_r*self.x-4*E*f_over_r*self.y,
            self.gamma*Af_over_r*self.y+4*E*f_over_r*self.x,
            np.zeros_like(P)]))
        self.residualhat=self.fft(np.array([R_over_r*self.x,R_over_r*self.y,np.zeros_like(P)]))
        self.high=(np.abs(kx)>.8*2*np.pi*n/(3*box))|(np.abs(ky)>.8*2*np.pi*n/(3*box))

    @staticmethod
    def fft(v):return fftn(v,axes=(-2,-1),workers=1)
    @staticmethod
    def ifft(v):return ifftn(v,axes=(-2,-1),workers=1)
    def project(self,v):
        return self.mask*(v-self.k*(self.inv*(self.k*v).sum(axis=1))[:,None])
    def project_one(self,v,i):
        return self.mask*(v-self.k[i]*(self.inv[i]*(self.k[i]*v).sum(axis=0)))
    def pair(self,test,v):return self.area*np.sum(np.conj(test)*v)
    def norm(self,v):return float(np.sqrt(self.area*np.sum(np.abs(v)**2)))
    def rhs(self,u):
        v=self.ifft(u);om=self.ifft(1j*cross(self.k,u))
        raw=cross(self.v,om)+cross(v,self.wv)
        raw[2]+=cross(v[0],om[0])
        raw[3]+=cross(v[0],om[1])+cross(v[1],om[0])
        forcing=(cross(v[0],om[3])+cross(v[3],om[0])
                 +cross(v[1],om[2])+cross(v[2],om[1]))
        raw[4]+=forcing
        out=self.project(self.fft(raw))
        fh=self.project_one(self.fft(forcing),4)
        J=self.pair(self.testhat,fh)
        R=self.pair(self.residualhat,u[4])
        q=self.pair(self.testhat,u[4])
        defect=self.pair(self.testhat,out[4])-self.gamma*q-J-R
        return out,J,R,defect
    def step(self,u,t,h):
        a=self.rhs(u);b=self.rhs(u+h*a[0]/2)
        c=self.rhs(u+h*b[0]/2);d=self.rhs(u+h*c[0])
        du=h*(a[0]+2*b[0]+2*c[0]+d[0])/6
        fac=[np.exp(-self.gamma*t),np.exp(-self.gamma*(t+h/2)),
             np.exp(-self.gamma*(t+h/2)),np.exp(-self.gamma*(t+h))]
        integrals=[h*sum(w*e*z[j] for w,e,z in zip([1,2,2,1],fac,[a,b,c,d]))/6
                   for j in [1,2]]
        return u+du,np.array(integrals),max(abs(z[3]) for z in [a,b,c,d])
    def initial_jet_check(self):
        d=self.rhs(self.initial)[0]
        # Differentiate the cubic source at zero. Only the two quadratic
        # descendants contribute, because both begin at zero.
        v=self.ifft(self.initial);om=self.ifft(1j*cross(self.k,self.initial))
        dv=self.ifft(d);dom=self.ifft(1j*cross(self.k,d))
        raw=(cross(v[0],dom[3])+cross(dv[3],om[0])
             +cross(v[1],dom[2])+cross(dv[2],om[1]))
        actual=self.project_one(self.fft(raw),4)
        return {'initial_jet_relative_error':self.norm(actual-self.jet)/self.norm(self.jet),
                'real_test_of_exact_jet':float(self.pair(self.testhat,self.jet).real),
                'source_divergence':float(np.max(np.abs((self.k*actual[None]).sum(axis=1))[4]))}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--n',type=int,default=192);p.add_argument('--box',type=float,default=14.)
    p.add_argument('--step',type=float,default=.005);p.add_argument('--time',type=float,default=1.)
    a=p.parse_args()
    if a.n < 32 or any(not np.isfinite(v) or v <= 0 for v in [a.box,a.step,a.time]):
        p.error('n must be at least 32; box, step and time must be finite and positive')
    count=max(1,int(np.ceil(a.time/a.step)))
    a.step=a.time/count
    model=Probe(a.n,a.box)
    print(json.dumps({'configuration':vars(a),'checks':model.initial_jet_check()}),flush=True)
    u=model.initial.copy();integrals=np.zeros(2,complex);t=0.;defect=0.;started=time.monotonic()
    for j in range(count):
        u,d,err=model.step(u,t,a.step);t+=a.step;integrals+=d;defect=max(defect,err)
        if (j+1)%max(1,count//10)==0 or j+1==count:
            q=model.pair(model.testhat,u[4]);discount=np.exp(-model.gamma*t)*q
            print(json.dumps({'time':t,'recipient_norm':model.norm(u[4]),
                'q_real':float(q.real),'q_imag':float(q.imag),
                'discounted_forcing_real':float(integrals[0].real),
                'discounted_forcing_imag':float(integrals[0].imag),
                'discounted_residual_real':float(integrals[1].real),
                'discounted_residual_imag':float(integrals[1].imag),
                'field_norms':[model.norm(v) for v in u],
                'field_high_frequency_fractions':[float(np.sum(np.abs(v[...,model.high])**2)/np.sum(np.abs(v)**2)) for v in u],
                'duhamel_ledger_error':float(abs(discount-integrals.sum())),
                'max_instantaneous_ledger_defect':float(defect),
                'high_frequency_fraction':float(np.sum(np.abs(u[...,model.high])**2)/np.sum(np.abs(u)**2)),
                'max_divergence':float(np.max(np.abs((model.k*u).sum(axis=1)))),
                'wall_seconds':time.monotonic()-started}),flush=True)

if __name__=='__main__':main()
