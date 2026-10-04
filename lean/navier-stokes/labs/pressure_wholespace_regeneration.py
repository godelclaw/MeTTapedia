#!/usr/bin/env python3
"""Whole-space pressure regeneration: exact identities and numerical core.

Canonical pressure and its induced Euler-direction derivative are finite
Gaussian mixtures. Exact checks verify the heat formulas and the constants
in an analytic spatial-tail bound. Compact-core quadrature is floating-point;
this file does not certify the continuum sign or a physical time interval.
"""
import argparse, functools, hashlib, json, math, time
from pathlib import Path
import numpy as np
import sympy as s
from scipy.special import gamma, gammainc, roots_legendre
from integrated_swirl_pressure import gaussian_pair, r as rg, z as zg
from rotational_curl_reserve import require, zero

r,z,t=s.symbols('r z t',real=True)
def definitions(b2=8):
    R=r*r+z*z
    b=s.sqrt(b2)
    G=s.Matrix([[-4*r*r*z*z+2*r*r+2*z*z-1,-b*z,-4*r*z**3+6*r*z],
       [-2*b*r*r*z+b*z,2*z*z-1,-2*b*r*z*z+b*r],
       [4*r**3*z-8*r*z,0,4*r*r*z*z-2*r*r-4*z*z+2]])
    source=s.expand(s.trace(G*G))
    H2=(3*z*z-R)/2
    H4=(35*z**4-30*R*z*z+3*R**2)/8
    ppoly=-(8*R**2+2*R*b2+32*R+b2-14)/60-H2*(4*R+b2+19)/42+H4*s.Rational(8,35)
    weights={2:-2*s.Rational(b2-5,3),4:-32*s.Rational(b2-9,35)}
    def pressure_contract(f,a):
        rr=s.diff(f,r,2)-4*a*r*s.diff(f,r)+(4*a*a*r*r-2*a)*f
        zz=s.diff(f,z,2)-4*a*z*s.diff(f,z)+(4*a*a*z*z-2*a)*f
        rz=s.diff(f,r,z)-2*a*(z*s.diff(f,r)+r*s.diff(f,z))+4*a*a*r*z*f
        tt=s.diff(f,r)/r-2*a*f
        return s.expand(G[0,0]*rr+G[1,1]*tt+G[2,2]*zz+(G[0,2]+G[2,0])*rz)
    conv=40*b2*r*r*z**4-20*b2*r*r*z*z+8*b2*z**4-4*b2*z*z-32*r**6+160*r**4*z**4+56*r**4+160*r*r*z**6-528*r*r*z**4+120*r*r*z*z-12*r*r+288*z**6-528*z**4+216*z*z-12
    local=s.expand(conv-2*pressure_contract(ppoly,s.Integer(2)))
    mixture=s.expand(sum(-weights[l]*t**(2*l)*pressure_contract(H,2*t*t)/2 for l,H in [(2,H2),(4,H4)]))
    return source,local,mixture

@functools.lru_cache(None)
def transform(i,j):
    """Heat of r^(2i) z^(2j) e^(-alpha R), then radial derivative/r.

    Output (radial power, axial power, half v power, alpha power, coefficient).
    v=(1+4alpha*time)^(-1/2). Includes the factor 1/(2alpha) from time.
    """
    out={}
    def add(key,c):out[key]=out.get(key,0)+c
    for k in range(i+1):
        for m in range(j+1):
            base=s.binomial(i,k)**2*s.factorial(k)*s.binomial(2*j,2*m)*s.factorial2(2*m-1)/2**m
            n=k+m; ip=i-k; jp=j-m
            for h in range(n+1):
                c=base*(-1)**h*s.binomial(n,h)
                vp=2*(ip+jp)+h
                if ip:add((ip-1,jp,vp,-n-1),c*ip)
                add((ip,jp,vp+1,-n),-c)
    return [(key,c) for key,c in out.items() if c]

class HeatGradient:
    def __init__(self, poly):
        grouped={}
        for (ir,iz),co in s.Poly(poly,r,z).terms():
            require(ir%2==iz%2==0, 'Even source polynomial')
            for (ip,jp,vp,ap),f in transform(ir//2,iz//2):
                key=(ip,jp,vp,ap)
                grouped[key]=grouped.get(key,0)+co*f
        self.terms=[(key,s.lambdify(t,s.factor(co),'numpy')) for key,co in grouped.items() if co!=0]
        self.maxv=max(key[2] for key,f in self.terms)
    def evaluate(self,r2,z2,alpha,parameter=0,L=1):
        radius2=r2+z2
        a=alpha*radius2
        vl=1/math.sqrt(1+4*alpha*L*L)
        moments={}
        for k in range(self.maxv+1):
            sh=k+.5
            # integral v^(2k) exp(-a*v^2), at upper limits 1 and vl.
            I=gamma(sh)*gammainc(sh,a)/(2*a**sh)
            Il=gamma(sh)*gammainc(sh,a*vl*vl)/(2*a**sh)
            moments[k]=(I,Il)
        J={k:L*L*moments[k][1]+(moments[k-1][0]-moments[k-1][1]-moments[k][0]+moments[k][1])/(4*alpha) for k in range(1,self.maxv+1)}
        out=np.zeros_like(radius2)
        for (ip,jp,vp,ap),f in self.terms:
            require(vp>=1, 'Gradient makes every heat moment integrable')
            out+=f(parameter)*alpha**ap*r2**ip*z2**jp*J[vp]
        return np.sqrt(r2)*out

def run(nrad=80,nang=64,nmix=40,Rmax=12,b2=8,L=1,kappa=1e-4):
    start=time.time()
    source,local,mixture=definitions(b2)
    fields=[HeatGradient(p) for p in [source,local,mixture]]
    # Composite radial quadrature resolves the core and a much larger tail.
    edges=[0,.5,1,2,4,8]
    if Rmax>8:edges.append(Rmax)
    else:edges=[x for x in edges if x<Rmax]+[Rmax]
    rn,rw=roots_legendre(nrad)
    radii=np.concatenate([(a+b)/2+(b-a)*rn/2 for a,b in zip(edges[:-1],edges[1:])])
    wr=np.concatenate([(b-a)*rw/2 for a,b in zip(edges[:-1],edges[1:])])
    mu,wm=roots_legendre(nang)
    mu=(mu+1)/2;wm=wm/2
    rho=radii[:,None]; mu=mu[None,:]
    r2=rho*rho*(1-mu*mu);z2=rho*rho*mu*mu
    beta=fields[0].evaluate(r2,z2,2,L=L)
    bt=fields[1].evaluate(r2,z2,3,L=L)
    mn,mw=roots_legendre(nmix);mn=(mn+1)/2;mw=mw/2
    for x,w in zip(mn,mw):bt+=w*fields[2].evaluate(r2,z2,1+2*x*x,x,L)
    H=1+kappa*r2*np.exp(-rho*rho)
    ur=-np.sqrt(r2)*(1-2*z2)*np.exp(-rho*rho)
    uz=2*np.sqrt(z2)*(1-r2)*np.exp(-rho*rho)
    Hr=2*kappa*np.sqrt(r2)*(1-r2)*np.exp(-rho*rho)
    Hz=-2*kappa*r2*np.sqrt(z2)*np.exp(-rho*rho)
    Ht=-ur*Hr-uz*Hz
    weight=4*np.pi*wr[:,None]*wm[None,:]*rho*rho
    f=3*abs(beta)*beta*bt/H**1.5
    h=-1.5*abs(beta)**3*Ht/H**2.5
    return dict(b2=b2,L=L,kappa=kappa,nrad=nrad,nang=nang,nmix=nmix,Rmax=Rmax,
        B=float(np.sum(weight*abs(beta)**3/H**1.5)), B_E=float(np.sum(weight*(f+h))),
        pressure_part=float(np.sum(weight*f)),density_part=float(np.sum(weight*h)),
        last_shell=float(np.sum((weight*(f+h))[radii>8])),max_beta=float(np.max(abs(beta))),
        expression_terms=[len(f.terms) for f in fields],elapsed=time.time()-start,
        scope='Floating-point compact-core quadrature. The analytic tail bound is checked separately for b2=8, L=1, kappa=1e-4 and Rmax>=64; core quadrature is not enclosed.')

def lap(f):return s.diff(f,r,2)+s.diff(f,r)/r+s.diff(f,z,2)
def matrix(u):return s.Matrix([[s.diff(u[0],r),-u[1]/r,s.diff(u[0],z)],[s.diff(u[1],r),u[0]/r,s.diff(u[1],z)],[s.diff(u[2],r),0,s.diff(u[2],z)]])
def exact_checks():
 R=r*r+z*z;g=s.exp(-R);b=s.sqrt(8)
 u=s.Matrix([-r*(1-2*z*z)*g,b*r*z*g,2*z*(1-r*r)*g])
 G=matrix(u)
 source,local,mix=definitions()
 zero(s.diff(u[0],r)+u[0]/r+s.diff(u[2],z),'solenoidal datum')
 zero(s.trace(G*G)-source*g*g,'complete pressure source')
 H2=(3*z*z-R)/2;H4=(35*z**4-30*R*z*z+3*R*R)/8
 poly=-(8*R*R+48*R-6)/60-H2*(4*R+27)/42+8*H4/35
 weights={2:s.Integer(-2),4:s.Rational(32,35)}
 zero(-lap(poly*g*g)-(source-sum(weights[l]*H for l,H in [(2,H2),(4,H4)]))*g*g,'canonical pressure polynomial remainder')
 for l,H in [(2,H2),(4,H4)]:
  zero(lap(H),'solid harmonic')
  zero(-lap(H*t**(2*l)*s.exp(-2*t*t*R))/4-H*s.diff(t**(2*l+3)*s.exp(-2*t*t*R),t),'inverse Gaussian pressure as compact mixture')
 adv=s.Matrix([u[0]*s.diff(u[0],r)+u[2]*s.diff(u[0],z)-u[1]**2/r,u[0]*s.diff(u[1],r)+u[2]*s.diff(u[1],z)+u[0]*u[1]/r,u[0]*s.diff(u[2],r)+u[2]*s.diff(u[2],z)])
 def hessian(p):return s.Matrix([[s.diff(p,r,2),0,s.diff(p,r,z)],[0,s.diff(p,r)/r,0],[s.diff(p,r,z),0,s.diff(p,z,2)]])
 zero((-2*s.trace(G*(matrix(adv)+hessian(poly*g*g))))/g**3-local,'full local Euler pressure-time source')
 angle,radial=s.symbols('angle radial',real=True)
 for expression,bound in [(source,4),(local,6),(mix,6)]:
  angular=s.expand(sum(co*radial**(i+j)*(1-angle*angle)**(i//2)*angle**j for (i,j),co in s.Poly(expression,r,z).terms()))
  require(s.degree(angular,angle)<=bound,'No angular component is discarded')
 ptail=sum(weights[l]*H*t**(2*l)/4 for l,H in [(2,H2),(4,H4)])*s.exp(-2*t*t*R)
 zero(-2*s.trace(G*hessian(ptail))/s.exp(-(1+2*t*t)*R)-mix,'full pressure return in the mixture source')
 a,v=s.symbols('a v',positive=True)
 indices=set()
 for p in [source,local,mix]:
  for (ir,iz),co in s.Poly(p,r,z).terms():
   require(ir%2==iz%2==0,'even Gaussian polynomial')
   indices.add((ir//2,iz//2))
 for i,j in sorted(indices):
  P=0
  for k in range(i+1):
   for h in range(j+1):
    P+=s.binomial(i,k)**2*s.factorial(k)*s.binomial(2*j,2*h)*s.factorial2(2*h-1)/2**h/a**(k+h)*(1-v*v)**(k+h)*r**(2*i-2*k)*z**(2*j-2*h)*v**(4*(i+j-k-h))
  P=s.expand(P)
  zero(P.subs(v,1)-r**(2*i)*z**(2*j),'initial heat polynomial')
  zero(lap(P)-4*a*v*v*(r*s.diff(P,r)+z*s.diff(P,z))+2*a*v**3*s.diff(P,v),'complete heat PDE after Gaussian factor')
  gradient=sum(co*r**(2*ip)*z**(2*jp)*v**(2*vp)*a**ap for (ip,jp,vp,ap),co in transform(i,j))
  zero(gradient-(s.diff(P,r)/r-2*a*v*v*P)/(2*a),'radial gradient and heat-time change of variable')
 def pair(p,rate):return gaussian_pair(p.subs({r:rg,z:zg}),s.Integer(rate),True)
 E=pair(s.cancel(u.dot(u)/g**2),2)
 Z=pair(s.cancel(s.trace(G.T*G)/g**2),2)
 A=pair(s.cancel(adv.dot(adv)/g**4),4)
 zero(E-15*s.sqrt(2)*s.pi**s.Rational(3,2)/32,'energy')
 zero(Z-119*s.sqrt(2)*s.pi**s.Rational(3,2)/32,'gradient energy')
 zero(A-1385*s.pi**s.Rational(3,2)/8192,'complete convection energy')
 # pi^(3/2)<28/5 and sqrt(2)<10/7 imply E<4,Z<30,A<1.
 require(s.Rational(22,7)**3<s.Rational(28,5)**2 and 2<s.Rational(10,7)**2,'rational radical bounds')
 require(15*s.Rational(10,7)*s.Rational(28,5)/32<4,'energy below four')
 require(119*s.Rational(10,7)*s.Rational(28,5)/32<30,'gradient energy below thirty')
 require(1385*s.Rational(28,5)/8192<1,'Leray tangent L2 bound')
 def sup_bound(p):
  return sum(abs(co)*s.factorial((i+j)//2)/2**((i+j)//2) for (i,j),co in s.Poly(p,r,z).terms())
 Gpoly=s.expand(s.cancel(s.trace(G.T*G)/g**2))
 require(sup_bound(source)==80 and sup_bound(Gpoly)==262,'global source and gradient bounds')
 require(262<17**2 and 12*17+83<300 and 80+s.Rational(30,12)<83,'full tangent pointwise bound')
 y=s.symbols('y',nonnegative=True)
 majorant=144*(1+y+y*y/2+y**3/6)-8*y*(1+y)**2
 require(all(c>=0 for c in s.Poly(majorant,y).all_coeffs()),'Gaussian polynomial envelope')
 velocity_poly=s.cancel(u.dot(u)/g**2)
 density_gradient_poly=4*r*r*(1-r*r)**2+4*r**4*z*z
 for f in [velocity_poly,density_gradient_poly]:
  require(all(co>=0 for co in s.Poly(s.expand(8*R*(1+R)**2-f),r,z).coeffs()),'Velocity and density gradient obey the envelope')
 require(s.Rational(144,10000)<1,'density material derivative below one')
 # Tensor heat-gradient kernel: integrate its two radial majorants.
 tau,rho=s.symbols('tau rho',positive=True)
 I=lambda n: s.gamma(n+s.Rational(1,2))*4**(n+s.Rational(1,2))/(4*s.pi)**s.Rational(3,2)/rho**(2*n+1)
 zero(rho**3*I(3)/8+rho*I(2)-27/(4*s.pi*rho**4),'far tensor kernel bound')
 zero(rho**3*I(2)/8+rho*I(1)-7/(8*s.pi*rho**2),'near tensor kernel bound')
 zero((8*s.pi)**2*7/(8*s.pi)*27/(4*s.pi)-378,'integrable tensor kernel norm')
 require(378<20**2,'kernel L1 bound below twenty')
 require(s.Rational(2880*s.factorial(6)*4**6,64**8)<1,'Gaussian velocity tail remainder')
 require(s.Rational(144000*s.factorial(10)*8**10,64**16)<1,'Gaussian stress-variation tail remainder')
 bound=2*s.Rational(22,7)*145**3/s.Integer(64)**9
 require(bound<s.Rational(11,10**10),'complete regeneration tail below 1.1e-9')
 return dict(E=str(E),Z=str(Z),convection_L2_squared=str(A),heat_monomials=len(indices),
  pressure_degrees=[0,2,4],pressure_time_degrees=[0,2,4,6],
  tail_bound=str(bound),tail_bound_float=float(bound),
  scope='Exact symbolic identities and rational inequalities; their whole-space PDE and integral interpretation is analytic, not Lean-certified. Compact-core quadrature remains numerical.')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--nrad',type=int,default=32)
    p.add_argument('--nang',type=int,default=80)
    p.add_argument('--nmix',type=int,default=32)
    p.add_argument('--Rmax',type=float,default=64)
    p.add_argument('--b2',type=int,choices=(5,8),default=8)
    p.add_argument('--check-only',action='store_true')
    args=p.parse_args()
    if min(args.nrad,args.nang,args.nmix)<1 or args.Rmax<=0:
        p.error('Positive quadrature orders and radius required')
    output={'exact_checks':exact_checks()}
    if not args.check_only:
        parameters=vars(args).copy()
        parameters.pop('check_only')
        output['quadrature']=run(**parameters)
    output['source_sha256']={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        for name in (Path(__file__).name,'integrated_swirl_pressure.py','rotational_curl_reserve.py')}
    print(json.dumps(output,indent=2),flush=True)
