#!/usr/bin/env python3
"""Complete viscous amplitude expansion through degree three.

This is the Taylor hierarchy of the Fourier Galerkin Navier--Stokes ODE
about its evolving zero-amplitude solution. It uses the same Gaussian
parents, periodic square, axial period pi and normalization as full_history.
The full solver's axial cutoff must retain indices -3 through 3, as it does
for nz>=12.
Every axial sector through degree three and every ordered partition are
retained. Only nonnegative axial indices are stored; negative indices are
the conjugates in physical horizontal coordinates. No parent or mean is
held fixed, and every pressure projection and viscous term is retained.

Coefficients multiply epsilon^j, without factorial. K2 and Y2 include the
pairing of the base with the order-two mean, as well as the order-one
squares. They are coefficients, not positive norms of a solution. Their
signed identities K2'=-2 nu Y2 and Y2'=P2-D2 are checked by the output
ledgers. In particular D2 is a Taylor coefficient and need not be positive.

The diagnostic q uses the fixed radial test from cubic_history; it is not
an eigenmode identity for the evolving viscous base. For amplitude epsilon,
the cubic prediction of full_history's scaled q is q_cubic+q_linear/epsilon^2.
The linear term is retained to expose the square's angular-symmetry error.

The optional full-RHS check extracts coefficients from seven complex-
amplitude evaluations of the full 3D Galerkin RHS, independently of the
axial-sector recursion. Numerical agreement does not certify continuum
errors. This hierarchy is neither the full nonlinear flow nor a regularity
estimate. Requires NumPy and SciPy.
"""
import argparse,json,time
import numpy as np
from scipy.fft import fftn,ifftn
if __package__:
    from .cubic_history import Probe,cross
else:
    from cubic_history import Probe,cross

class Hierarchy:
    keys=[(0,0),(1,1),(2,0),(2,2),(3,1),(3,3)]
    def __init__(self,n,box,nu):
        self.n=n;self.box=box;self.nu=nu;self.probe=Probe(n,box)
        self.area=box**2/n**4/(2*np.pi)
        kh=2*np.pi*np.fft.fftfreq(n,box/n)
        kx,ky=np.meshgrid(kh,kh,indexing='ij')
        self.k=np.array([np.array([kx,ky,np.full_like(kx,2*phase)]) for order,phase in self.keys])
        self.ksq=(self.k*self.k).sum(axis=1)
        self.inv=np.divide(1,self.ksq,out=np.zeros_like(self.ksq),where=self.ksq>0)
        labels=np.fft.fftfreq(n,1/n);a,b=np.meshgrid(labels,labels,indexing='ij')
        self.mask=(np.abs(a)<n/3)&(np.abs(b)<n/3)
        self.high=(np.abs(a)>.8*n/3)|(np.abs(b)>.8*n/3)
        self.initial=np.zeros((len(self.keys),3,n,n),complex)
        self.initial[0]=self.probe.vhat
        reverse=(-np.arange(n))%n
        self.initial[1]=.5*(self.probe.initial[0]+np.conj(self.probe.initial[1][:,reverse][:,:,reverse]))
        self.signed_keys=self.keys+[(j,-n) for j,n in self.keys if n]
        self.partitions={}
        for j,n in self.keys:
            self.partitions[(j,n)]=[(left,(j-left[0],n-left[1])) for left in self.signed_keys
                                     if (j-left[0],n-left[1]) in self.signed_keys]
    @staticmethod
    def fft(v):return fftn(v,axes=(-2,-1),workers=1)
    @staticmethod
    def ifft(v):return ifftn(v,axes=(-2,-1),workers=1)
    def project(self,v):
        return self.mask*(v-self.k*(self.inv*(self.k*v).sum(axis=1))[:,None])
    def values(self,u):
        a=self.ifft(u);b=self.ifft(1j*cross(self.k,u));v={};w={}
        for key,z,c in zip(self.keys,a,b):
            v[key]=z;w[key]=c
            if key[1]:v[(key[0],-key[1])]=np.conj(z);w[(key[0],-key[1])]=np.conj(c)
        return v,w
    def source(self,u):
        v,w=self.values(u);raw=np.zeros_like(u)
        for j,key in enumerate(self.keys):
            for left,right in self.partitions[key]:raw[j]+=cross(v[left],w[right])
        return self.project(self.fft(raw))
    def coefficients(self,u):
        k0=.5*self.area*np.sum(np.abs(u[0])**2)
        y0=.5*self.area*np.sum(self.ksq[0]*np.abs(u[0])**2)
        k2=self.area*np.real(np.vdot(u[0],u[2])+np.vdot(u[1],u[1]))
        y2=self.area*np.real(np.sum(self.ksq[0]*np.conj(u[0])*u[2])+
                                  np.sum(self.ksq[1]*np.abs(u[1])**2))
        return np.array([k0,y0,k2,y2],float)
    def rhs(self,u):
        source=self.source(u)
        dy=source-self.nu*self.ksq[:,None]*u
        coeff=self.coefficients(u)
        production_second=self.area*np.real(
            np.sum(self.ksq[0]*(np.conj(source[0])*u[2]+np.conj(u[0])*source[2]))
            +2*np.sum(self.ksq[1]*np.conj(u[1])*source[1]))
        dissipation_second=2*self.nu*self.area*np.real(
            np.sum(self.ksq[0]**2*np.conj(u[0])*u[2])
            +np.sum(self.ksq[1]**2*np.abs(u[1])**2))
        return dy,np.array([2*self.nu*coeff[1],2*self.nu*coeff[3],
                            production_second,dissipation_second])
    def step(self,u,dt):
        a=self.rhs(u);b=self.rhs(u+.5*dt*a[0]);c=self.rhs(u+.5*dt*b[0]);d=self.rhs(u+dt*c[0])
        return u+dt*(a[0]+2*b[0]+2*c[0]+d[0])/6,dt*(a[1]+2*b[1]+2*c[1]+d[1])/6
    def checks(self):
        u=self.initial;d=self.rhs(u)[0]
        v,w=self.values(u);dv,dw=self.values(d);raw=np.zeros_like(u)
        for i,key in enumerate(self.keys):
            for left,right in self.partitions[key]:
                raw[i]+=cross(dv[left],w[right])+cross(v[left],dw[right])
        second=self.project(self.fft(raw))-self.nu*self.ksq[:,None]*d
        value=8*self.probe.pair(self.probe.testhat,second[4])
        exact=self.probe.pair(self.probe.testhat,self.probe.jet)
        return {'initial_energy_coefficients':self.coefficients(u).tolist(),
                'axisymmetric_cubic_second_jet_difference':float(abs(value-exact)),
                'axisymmetric_cubic_second_jet':[float(value.real),float(value.imag)],
                'independent_cubic_second_jet':[float(exact.real),float(exact.imag)]}
    def full_rhs_check(self):
        if __package__:
            from .full_history import FullFlow
        else:
            from full_history import FullFlow
        n=self.n;nz=16
        full=FullFlow(n,nz,self.box,.1,self.nu)
        step=min(.1,.1/max(1.,self.nu*np.max(self.ksq[:,self.mask])))
        u=self.step(self.initial,step)[0]
        actual=self.rhs(u)[0]
        reverse=(-np.arange(n))%n
        def assemble(coefficients,z):
            field=np.zeros((3,n,n,nz),complex)
            for v,(degree,phase) in zip(coefficients,self.keys):
                field[...,phase]+=nz*z**degree*v
                if phase:
                    field[...,-phase]+=nz*z**degree*np.conj(v[:,reverse][:,:,reverse])
            return field
        initial_error=np.max(np.abs(assemble(self.initial,.1)-full.initial))
        points=7;radius=.5;extracted=np.zeros_like(actual)
        for j in range(points):
            z=radius*np.exp(2j*np.pi*j/points)
            rhs=full.rhs(assemble(u,z))[0]
            for k,(degree,phase) in enumerate(self.keys):
                extracted[k]+=rhs[...,phase]/nz*np.exp(-2j*np.pi*j*degree/points)/(points*radius**degree)
        return {'keys':self.keys,
                'max_initial_datum_difference':float(initial_error),
                'relative_errors':[float(np.linalg.norm(a-b)/max(np.linalg.norm(a),1e-12))
                                   for a,b in zip(actual,extracted)],
                'max_absolute_coefficient_error':float(np.max(np.abs(actual-extracted)))}
    def diagnostics(self,u):
        c=self.coefficients(u)
        q3=8*self.probe.pair(self.probe.testhat,u[4])
        q1=8*self.probe.pair(self.probe.testhat,u[1])
        densities=np.sum(np.abs(u)**2,axis=1)
        return {'kinetic_base':float(c[0]),'enstrophy_base':float(c[1]),
                'kinetic_second':float(c[2]),'enstrophy_second':float(c[3]),
                'q_cubic_real':float(q3.real),'q_cubic_imag':float(q3.imag),
                'q_linear_real':float(q1.real),'q_linear_imag':float(q1.imag),
                'field_norms':[float(np.sqrt(self.area*np.sum(d))) for d in densities],
                'field_high_velocity_fractions':[float(np.sum(d[self.high])/np.sum(d)) if np.sum(d) else 0.
                                                  for d in densities],
                'max_divergence_l2':float(np.sqrt(self.area*np.max(np.sum(np.abs((self.k*u).sum(axis=1))**2,axis=(1,2)))))}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--n',type=int,default=192);p.add_argument('--box',type=float,default=14.)
    p.add_argument('--viscosity',type=float,default=.001);p.add_argument('--time',type=float,default=6.)
    p.add_argument('--step',type=float,default=.005);p.add_argument('--check-only',action='store_true')
    p.add_argument('--check-full-rhs',action='store_true')
    a=p.parse_args()
    if a.n<32 or any(not np.isfinite(v) or v<=0 for v in [a.box,a.time,a.step]):
        p.error('n>=32 and finite positive box, time and step required')
    if not np.isfinite(a.viscosity) or a.viscosity<0:
        p.error('finite nonnegative viscosity required')
    m=Hierarchy(a.n,a.box,a.viscosity)
    checks=m.checks()
    if a.check_full_rhs:checks['full_rhs_coefficient_extraction']=m.full_rhs_check()
    print(json.dumps({'configuration':vars(a),'stored_sectors':m.keys,'checks':checks}),flush=True)
    if a.check_only:return
    count=int(np.ceil(a.time/a.step));dt=a.time/count
    if dt*a.viscosity*np.max(m.ksq[:,m.mask])>2:raise ValueError('explicit viscous timestep')
    u=m.initial.copy();initial=m.coefficients(u);integral=np.zeros(4);started=time.monotonic()
    for j in range(count):
        u,di=m.step(u,dt);integral+=di
        if (j+1)%max(1,count//20)==0 or j+1==count:
            info=m.diagnostics(u)
            info.update(time=(j+1)*dt,kinetic_base_ledger=info['kinetic_base']-initial[0]+integral[0],
                        kinetic_second_ledger=info['kinetic_second']-initial[2]+integral[1],
                        integrated_production_second=float(integral[2]),
                        integrated_dissipation_second=float(integral[3]),
                        enstrophy_second_ledger=info['enstrophy_second']-initial[3]-integral[2]+integral[3],
                        wall_seconds=time.monotonic()-started)
            print(json.dumps(info),flush=True)

if __name__=='__main__':main()
