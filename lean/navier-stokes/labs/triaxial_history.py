#!/usr/bin/env python3
"""Full viscous Galerkin history from a three-component Gaussian curl.

The whole-space seed is V=curl((0,x*z,2*x*y)*exp(-|x|^2)). With
E=(13/8)*(pi/2)^(3/2), its squared gradient and second-derivative norms
are 9*E and 99*E, while integral omega.S.omega=(32/27)*(pi/3)^(3/2).
The exact polynomial checker is reynolds_stress.py.

Periodize A*V(kappa*x) on the pi-periodic cube, A=kappa^(3/2)/sqrt(E),
and apply the strict two-thirds Galerkin truncation. The default rescaled
box length is 14; the program checks the initial Fourier moments against
the whole-space values. This is a numerical normalization check, not a
certified bound on the periodization or truncation error.

All reported energies use physical volume integrals: K=||u||_2^2/2,
Y=||grad u||_2^2/2 and D=nu*||grad^2 u||_2^2. Time and step arguments use
s=A*kappa*t; physical time is reported separately. A listed cutoff k means
physical angular wave number k*kappa. Physical viscosity is unchanged.

The equation and RK4 step are inherited from full_history. No part of the
velocity is frozen. Tail production uses all inputs. Tail self-stretching
instead uses the filtered velocity in every factor, via Betchov's identity.
Selected self-stretching integrals use the same RK stages as the field;
the remaining low-input work is their difference from full tail production.
Prefix maxima are sampled at steps, not upper bounds between steps.

This is a finite Galerkin diagnostic, not a continuum error enclosure or
an arbitrary-data budget. Requires NumPy and SciPy.
"""
import argparse,json,time
import numpy as np
if __package__:
 from .full_history import FullFlow,cross
else:
 from full_history import FullFlow,cross

def self_stretching(m,u,cuts):
 kx,ky,kz=m.k;answer=[]
 for cutoff in cuts:
  v=u*(m.ksq>=cutoff**2)
  aa,bb,dd,ee,ff=m.ifft(1j*np.array([kx*v[0],ky*v[1],
   .5*(kx*v[1]+ky*v[0]),.5*(kx*v[2]+kz*v[0]),.5*(ky*v[2]+kz*v[1])])).real
  cc=-aa-bb
  determinant=aa*bb*cc+2*dd*ee*ff-aa*ff**2-bb*ee**2-cc*dd**2
  answer.append(-4*m.area*(m.n*m.n*m.nz)*float(np.sum(determinant)))
 return np.array(answer)

class SelfFlow(FullFlow):
 def __init__(self,n,nu,cuts,self_cuts):
  super().__init__(n,n,np.pi,.1,nu,cuts)
  self.self_cutoffs=np.array(self_cuts)
 def rhs(self,u):
  velocity,rates,work=super().rhs(u)
  if len(self.self_cutoffs):rates=np.concatenate([rates,self_stretching(self,u,self.self_cutoffs)])
  return velocity,rates,work

def model(n,kappa,nu,self_cuts=()):
 cuts=kappa*np.array([0.,1.,2.,3.,4.,6.,8.])
 m=SelfFlow(n,nu,cuts,kappa*np.array(self_cuts))
 # Convert horizontal/(2*pi), axial-average norms to physical volume integrals.
 m.area*=2*np.pi**2
 Ebase=13/8*(np.pi/2)**1.5
 amplitude=kappa**1.5/np.sqrt(Ebase)
 q=m.k/kappa
 potential=-.25*np.pi**1.5*np.exp(-np.sum(q*q,axis=0)/4)*np.array(
  [np.zeros_like(q[0]),q[2]*q[0],2*q[0]*q[1]])
 labels=np.rint(np.fft.fftfreq(n,1/n)).astype(int)
 ii,jj,kk=np.meshgrid(labels,labels,labels,indexing='ij')
 phase=np.where((ii+jj+kk)%2==0,1.,-1.)
 m.initial=1j*cross(q,potential)*(n**3*amplitude/(kappa*np.pi)**3)*phase*m.mask
 return m,amplitude

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--n',type=int,default=96);p.add_argument('--kappa',type=float,default=14/np.pi)
 p.add_argument('--viscosity',type=float,default=.001);p.add_argument('--time',type=float,default=1.)
 p.add_argument('--step',type=float,default=.005);p.add_argument('--check-only',action='store_true')
 p.add_argument('--self-cutoffs',nargs='+',type=float,default=[])
 a=p.parse_args()
 if a.n<32 or any(not np.isfinite(v) or v<=0 for v in [a.kappa,a.time,a.step]):p.error('positive finite scales and n>=32 required')
 if not np.isfinite(a.viscosity) or a.viscosity<0:p.error('nonnegative finite viscosity required')
 if len(set(a.self_cutoffs))!=len(a.self_cutoffs) or any(k not in [0,1,2,3,4,6,8] for k in a.self_cutoffs):p.error('self cutoffs must be distinct and selected from 0,1,2,3,4,6,8')
 m,A=model(a.n,a.kappa,a.viscosity,a.self_cutoffs);u=m.initial.copy()
 _,rates,work=m.rhs(u);energy=m.energies(u)
 expected=np.array([.5,4.5*a.kappa**2,32/27*(np.pi/3)**1.5*A**3,99*a.viscosity*a.kappa**4])
 actual=np.array([energy[0],energy[1],rates[1],rates[2]])
 errors=np.abs(actual-expected)/np.maximum(np.abs(expected),1e-30)
 if np.max(errors)>1e-8:raise ArithmeticError('Gaussian normalization or resolution')
 ss=self_stretching(m,u,m.tail_cutoffs)
 if abs(ss[0]-rates[1])>1e-8*abs(rates[1]):raise ArithmeticError('Betchov crosscheck')
 nt=len(m.tail_cutoffs);initial_tails=m.tail_enstrophy(u)
 print(json.dumps({'configuration':vars(a),'physical_amplitude':A,'time_factor':A*a.kappa,
  'effective_viscosity':a.viscosity*a.kappa/A,'initial_energy':energy.tolist(),
  'initial_tail_enstrophy':initial_tails.tolist(),
  'analytic_check':{'actual_K_Y_P_D':actual.tolist(),'expected_K_Y_P_D':expected.tolist(),
   'relative_errors':errors.tolist(),'kinetic_work':work},
  'initial_self_tails':[dict(normalized_cutoff=float(k/a.kappa),production=float(p),
   self_stretching=float(s),dissipation=float(d))
   for k,p,s,d in zip(m.tail_cutoffs,rates[3:3+nt],ss,rates[3+nt:3+2*nt])]}),flush=True)
 if a.check_only:return
 count=int(np.ceil(a.time/a.step));ds=a.time/count;dt=ds/(A*a.kappa)
 if dt*a.viscosity*np.max(m.ksq[m.mask])>2:raise ValueError('viscous timestep')
 integrals=np.zeros(3+2*nt+len(a.self_cutoffs));peak=np.zeros(nt)
 self_indices=np.array([[0,1,2,3,4,6,8].index(k) for k in a.self_cutoffs],dtype=int)
 self_peak=np.zeros(len(a.self_cutoffs));started=time.monotonic()
 for j in range(count):
  u,di,dw=m.step(u,dt);integrals+=di;work=max(work,dw)
  tp=integrals[3:3+nt];td=integrals[3+nt:3+2*nt];peak=np.maximum(peak,tp-.5*td)
  self_integrals=integrals[3+2*nt:]
  self_peak=np.maximum(self_peak,self_integrals-.5*td[self_indices])
  if (j+1)%max(1,count//20)==0 or j+1==count:
   en=m.energies(u);ys=m.tail_enstrophy(u);selfp=self_stretching(m,u,m.tail_cutoffs)
   _,rr,_=m.rhs(u);density=np.sum(np.abs(u)**2,axis=0)
   print(json.dumps({'time':(j+1)*ds,'physical_time':(j+1)*dt,'energy':en.tolist(),
    'integrated_production':float(integrals[1]),'integrated_dissipation':float(integrals[2]),
    'kinetic_ledger':float(en[0]-energy[0]+integrals[0]),
    'enstrophy_ledger':float(en[1]-energy[1]-integrals[1]+integrals[2]),
    'tails':[dict(normalized_cutoff=float(k/a.kappa),enstrophy=float(y),
     integrated_production=float(p),integrated_dissipation=float(d),
     half_excess=float(p-.5*d),sampled_prefix_max=float(mx),ledger=float(y-y0-p+d),
     self_stretching=float(s),instantaneous_dissipation=float(drate))
     for k,y,y0,p,d,mx,s,drate in zip(m.tail_cutoffs,ys,initial_tails,tp,td,peak,selfp,rr[3+nt:3+2*nt])],
    'integrated_self_tails':[dict(normalized_cutoff=k,production=float(p),dissipation=float(d),
     low_input_remainder=float(full-p),half_excess=float(p-.5*d),sampled_prefix_max=float(mx))
     for k,p,d,full,mx in zip(a.self_cutoffs,self_integrals,td[self_indices],tp[self_indices],self_peak)],
    'high_palinstrophy_fraction':float(np.sum((m.ksq**2*density)[m.high])/np.sum(m.ksq**2*density)),
    'max_nonlinear_kinetic_work':float(work),'wall_seconds':time.monotonic()-started}),flush=True)

if __name__=='__main__':main()
