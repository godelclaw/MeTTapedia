#!/usr/bin/env python3
"""Full nonlinear viscous Fourier--Galerkin history diagnostic.

Periodic horizontal square and axial period pi. This is an unforced
Galerkin evolution, not a rigorous continuum enclosure or a whole-space
finite-energy construction. No mean or parent is held fixed.
Optional frequency-tail ledgers filter only the recipient of the complete
nonlinearity. Their running maxima are sampled at integration steps; they
are not upper bounds for all intermediate times or omitted frequencies.
"""
import argparse
import json
import time

import numpy as np
from scipy.fft import fftn, ifftn
from scipy.special import j1

if __package__:
    from .cubic_history import Probe
else:
    from cubic_history import Probe


def cross(a,b):
    return np.stack([a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],
                     a[0]*b[1]-a[1]*b[0]])


class FullFlow:
    def __init__(self,n,nz,box,epsilon,viscosity,tail_cutoffs=()):
        self.n=n;self.nz=nz;self.box=box;self.epsilon=epsilon;self.viscosity=viscosity
        x=(np.arange(n)/n-.5)*box
        xx,yy=np.meshgrid(x,x,indexing='ij')
        r2=xx*xx+yy*yy;w=xx+1j*yy;E=np.exp(-r2)
        phase=np.exp(2j*np.pi*np.arange(nz)/nz)
        potential=E[...,None]+epsilon*np.real(
            ((w*w+w**4*(1-.4*r2))*E)[...,None]*phase)
        kh=2*np.pi*np.fft.fftfreq(n,box/n)
        kz=2*np.fft.fftfreq(nz,1/nz)
        self.k=np.array(np.meshgrid(kh,kh,kz,indexing='ij'))
        self.ksq=(self.k*self.k).sum(axis=0)
        self.tail_cutoffs=np.asarray(tail_cutoffs,dtype=float)
        if (self.tail_cutoffs.ndim != 1 or np.any(~np.isfinite(self.tail_cutoffs))
                or np.any(self.tail_cutoffs < 0) or np.any(np.diff(self.tail_cutoffs) <= 0)):
            raise ValueError('tail cutoffs must be finite, nonnegative and strictly increasing')
        self.tail_bins=(np.searchsorted(self.tail_cutoffs**2,self.ksq,side='right')
                        if len(self.tail_cutoffs) else None)
        self.inv=np.divide(1,self.ksq,out=np.zeros_like(self.ksq),where=self.ksq>0)
        self.mask=((np.abs(self.k[0])<2*np.pi*n/(3*box))
                   &(np.abs(self.k[1])<2*np.pi*n/(3*box))
                   &(np.abs(self.k[2])<2*nz/3))
        self.high=((np.abs(self.k[0])>.8*2*np.pi*n/(3*box))
                   |(np.abs(self.k[1])>.8*2*np.pi*n/(3*box))
                   |(np.abs(self.k[2])>.8*2*nz/3))
        psi=self.fft(potential)*self.mask
        self.initial=np.array([1j*self.k[1]*psi,-1j*self.k[0]*psi,np.zeros_like(psi)])
        # Norm squared: horizontal integral / (2*pi), averaged over axial period pi.
        self.area=box*box/(n**4*nz**2*2*np.pi)
        kx,ky=np.meshgrid(kh,kh,indexing='ij');rad=np.hypot(kx,ky)
        kernel=np.divide(j1(rad),rad,out=np.full_like(rad,.5),where=rad>0)
        self.circle_kernel=1j*kernel*np.exp(.5j*box*(kx+ky))/n**2
        self.kx=kx;self.ky=ky
        self.cubic=Probe(n,box)

    @staticmethod
    def fft(v):return fftn(v,axes=(-3,-2,-1),workers=1)
    @staticmethod
    def ifft(v):return ifftn(v,axes=(-3,-2,-1),workers=1)
    def project(self,v):return self.mask*(v-self.k*(self.inv*(self.k*v).sum(axis=0)))
    def energies(self,u):
        density=np.sum(np.abs(u)**2,axis=0)
        return np.array([.5*self.area*np.sum(density),
                         .5*self.area*np.sum(self.ksq*density)])
    def tail_sums(self,density):
        if self.tail_bins is None:return np.empty(0)
        bins=np.bincount(self.tail_bins.ravel(),weights=density.ravel(),
                         minlength=len(self.tail_cutoffs)+1)
        return np.cumsum(bins[::-1])[::-1][1:]
    def tail_enstrophy(self,u):
        return self.tail_sums(.5*self.area*self.ksq*np.sum(np.abs(u)**2,axis=0))
    def rhs(self,u):
        v=self.ifft(u);omega=self.ifft(1j*cross(self.k,u))
        source=self.project(self.fft(cross(v,omega)))
        density=np.sum(np.abs(u)**2,axis=0)
        energy_loss=self.viscosity*self.area*np.sum(self.ksq*density)
        enstrophy_loss=self.viscosity*self.area*np.sum(self.ksq**2*density)
        production=self.area*np.real(np.sum(self.ksq*np.conj(u)*source))
        kinetic_work=self.area*np.real(np.vdot(u,source))
        rates=np.array([energy_loss,production,enstrophy_loss])
        if len(self.tail_cutoffs):
            # Only the recipient is filtered; all nonlinear inputs remain present.
            p=self.area*self.ksq*np.real(np.sum(np.conj(u)*source,axis=0))
            d=self.viscosity*self.area*self.ksq**2*density
            rates=np.concatenate([rates,self.tail_sums(p),self.tail_sums(d)])
        return source-self.viscosity*self.ksq*u,rates,kinetic_work
    def step(self,u,dt):
        a=self.rhs(u);b=self.rhs(u+.5*dt*a[0]);c=self.rhs(u+.5*dt*b[0]);d=self.rhs(u+dt*c[0])
        unew=u+dt*(a[0]+2*b[0]+2*c[0]+d[0])/6
        integrals=dt*(a[1]+2*b[1]+2*c[1]+d[1])/6
        return unew,integrals,max(abs(v[2]) for v in [a,b,c,d])
    def diagnostics(self,u):
        density=np.sum(np.abs(u)**2,axis=0)
        q=self.cubic.pair(self.cubic.testhat,u[...,1]/self.nz)*8/self.epsilon**3
        circle_coef=np.sum(self.circle_kernel[...,None]*
            (-self.ky[...,None]*u[0]+self.kx[...,None]*u[1]),axis=(0,1))
        circle=ifftn(circle_coef,workers=1)
        v=self.ifft(u)
        return {
            'cubic_scaled_q_real':float(q.real),'cubic_scaled_q_imag':float(q.imag),
            'circulation_r1_z0':float(circle[0].real),
            'circulation_r1_max_z':float(np.max(circle.real)),
            'circulation_r1_min_z':float(np.min(circle.real)),
            'velocity_high_frequency_fraction':float(np.sum(density[self.high])/np.sum(density)),
            'enstrophy_high_frequency_fraction':float(np.sum((self.ksq*density)[self.high])/np.sum(self.ksq*density)),
            'palinstrophy_high_frequency_fraction':float(np.sum((self.ksq**2*density)[self.high])/np.sum(self.ksq**2*density)),
            'directional_palinstrophy_high_fractions':[
                float(np.sum((self.ksq**2*density)[np.abs(self.k[j])>.8*limit])/np.sum(self.ksq**2*density))
                for j,limit in enumerate([2*np.pi*self.n/(3*self.box),2*np.pi*self.n/(3*self.box),2*self.nz/3])],
            'divergence_l2':float(np.sqrt(self.area*np.sum(np.abs((self.k*u).sum(axis=0))**2))),
            'max_reality_error':float(np.max(np.abs(v.imag))),
            'max_velocity':float(np.max(np.sqrt(np.sum(np.abs(v)**2,axis=0))))}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--n',type=int,default=128)
    parser.add_argument('--nz',type=int,default=24)
    parser.add_argument('--box',type=float,default=14.)
    parser.add_argument('--epsilon',type=float,default=.1)
    parser.add_argument('--viscosity',type=float,default=.001)
    parser.add_argument('--step',type=float,default=.005)
    parser.add_argument('--time',type=float,default=3.)
    parser.add_argument('--tail-cutoffs',nargs='+',type=float,default=[],
                        help='increasing nonnegative physical wave-number cutoffs')
    args=parser.parse_args()
    if (args.n < 8 or args.nz < 8 or args.box <= 0 or args.epsilon <= 0
            or args.viscosity < 0 or args.step <= 0 or args.time <= 0):
        parser.error('positive sizes, amplitude and time parameters, and nonnegative viscosity required')
    model=FullFlow(args.n,args.nz,args.box,args.epsilon,args.viscosity,args.tail_cutoffs)
    count=int(np.ceil(args.time/args.step));dt=args.time/count
    if dt*args.viscosity*np.max(model.ksq[model.mask])>2:
        raise ValueError('explicit viscous step is too large')
    u=model.initial.copy();initial_energy=model.energies(u)
    initial_tails=model.tail_enstrophy(u);nt=len(args.tail_cutoffs)
    integrals=np.zeros(3+2*nt);tail_peak=np.zeros(nt);work_error=0.
    print(json.dumps({'configuration':vars(args),'initial_energy':initial_energy.tolist(),
                      'initial_tail_enstrophy':initial_tails.tolist(),
                      'initial_diagnostics':model.diagnostics(u)}),flush=True)
    start=time.monotonic()
    for j in range(count):
        u,di,dw=model.step(u,dt);integrals+=di;work_error=max(work_error,dw)
        tail_p=integrals[3:3+nt];tail_d=integrals[3+nt:]
        tail_peak=np.maximum(tail_peak,tail_p-.5*tail_d)
        if (j+1)%max(1,count//10)==0 or j+1==count:
            en=model.energies(u);diagnostics=model.diagnostics(u)
            tails=model.tail_enstrophy(u)
            tail_info=[dict(cutoff=float(k),enstrophy=float(y),
                signed_production_integral=float(p),dissipation_integral=float(d),
                half_dissipation_excess=float(p-.5*d),
                sampled_running_half_dissipation_excess=float(peak),
                ledger_error=float(y-y0-p+d))
                for k,y,y0,p,d,peak in zip(args.tail_cutoffs,tails,initial_tails,
                                          tail_p,tail_d,tail_peak)]
            print(json.dumps({'time':(j+1)*dt,'kinetic_energy':float(en[0]),
                'enstrophy':float(en[1]),'signed_production_integral':float(integrals[1]),
                'enstrophy_dissipation_integral':float(integrals[2]),
                'kinetic_ledger_error':float(en[0]-initial_energy[0]+integrals[0]),
                'enstrophy_ledger_error':float(en[1]-initial_energy[1]-integrals[1]+integrals[2]),
                'max_nonlinear_kinetic_work':float(work_error),
                'tails':tail_info,
                'wall_seconds':time.monotonic()-start,**diagnostics}),flush=True)


if __name__=='__main__':main()
