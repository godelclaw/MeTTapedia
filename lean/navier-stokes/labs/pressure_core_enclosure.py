#!/usr/bin/env python3
"""Validated compact-core sign for the fixed whole-space pressure response.

Uses python-flint 0.9.0 (Arb/Acb balls), exact Gaussian-mixture identities,
Cauchy bounds for every inner Gauss rule and radial Taylor remainder, and
outer interval integration. The absolute value is never differentiated.
The analytic tail bound is imported from pressure_wholespace_regeneration.
This is a validated numerical certificate with an analytic interpretation,
not a Lean certificate or an arbitrary-history regularity theorem.
"""
import argparse
import functools
import hashlib
import json
import math
import time
from pathlib import Path
import sympy as s
import flint
from flint import arb, acb, acb_series, ctx
import pressure_wholespace_regeneration as wg
from rotational_curl_reserve import require, zero

PRECISION = 256
ORDER = 24
MIXTURE_PANELS = 8
MIXTURE_ORDER = 16
RADIAL_SLABS = 256
RADIAL_SUBDIVISIONS = 16
ANGULAR_SUBDIVISIONS = 256
ctx.prec = PRECISION

def rat(x):
 x=s.Rational(x);return acb(int(x.p))/int(x.q)

def polynomial(expr):
 p=s.Poly(expr,wg.t)
 if any(k[0]%2 for k,c in p.terms()):raise ValueError('odd parameter')
 return [rat(p.nth(2*i)) for i in range(p.degree()//2+1)] if expr else [acb(0)]
def horner(cs,x):
 out=acb(0)
 for c in reversed(cs):out=out*x+c
 return out

class Coefficients:
 def __init__(self,poly,rate=None):
  self.rate=rate
  groups={}
  alpha=s.Integer(rate) if rate else 1+2*wg.t**2
  for (ir,iz),co in s.Poly(poly,wg.r,wg.z).terms():
   for (ip,jp,vp,ap),factor in wg.transform(ir//2,iz//2):
    for h in range(ip+1):
     key=(jp+h,ip+jp,vp)
     groups[key]=groups.get(key,0)+co*factor*(-1)**h*s.binomial(ip,h)*alpha**ap
  self.terms=[]
  for (d,n,k),c in groups.items():
   c=s.cancel(c)
   if c:
    num,den=s.fraction(c)
    power=int(s.degree(den,wg.t)//2)
    constant=s.simplify(den/(1+2*wg.t**2)**power)
    if constant.free_symbols:raise ValueError('unfactored denominator')
    self.terms.append((d,n,k,polynomial(num),rat(constant),power))
  self.degree=max(key[0] for key in groups if s.cancel(groups[key]))
  self.maxk=max(k for d,n,k,_,_,_ in self.terms)
 def evaluate(self,rho,parameter=acb(0),simple=False):
  """Direct ball evaluation for checking the radial Taylor representation."""
  alpha=acb(self.rate) if self.rate else 1+2*parameter**2
  S=rho*rho;a=alpha*S
  vl=(1+4*alpha).sqrt(analytic=True)**-1
  # Entire hypergeometric representation avoids artificial cuts at a=0.
  def moment(k,v):
   sh=acb(2*k+1)/2
   return v**(2*k+1)*(-a*v*v).hypgeom_1f1(sh,sh+1)/(2*k+1)
  if simple or a.contains(0) or a.abs_lower()<arb(1)/10:
   I=[moment(k,acb(1)) for k in range(self.maxk+1)]
   Il=[moment(k,vl) for k in range(self.maxk+1)]
  else:
   I=[moment(0,acb(1))];Il=[moment(0,vl)]
   ex=(-a).exp();exl=(-a*vl*vl).exp()
   for k in range(self.maxk):
    I.append(((2*k+1)*I[k]-ex)/(2*a))
    Il.append(((2*k+1)*Il[k]-vl**(2*k+1)*exl)/(2*a))
  J=[None]+[Il[k]+(I[k-1]-Il[k-1]-I[k]+Il[k])/(4*alpha) for k in range(1,self.maxk+1)]
  result=[acb(0) for _ in range(self.degree+1)]
  q=parameter*parameter
  for d,n,k,num,den,power in self.terms:
   c=horner(num,q)/(den*(1+2*q)**power)
   result[d]+=c*S**n*J[k]
  return result

 def majorant(self,rho,parameter=acb(0)):
  """Analytic absolute majorants, including complex Cauchy rectangles."""
  alpha=acb(self.rate) if self.rate else 1+2*parameter**2
  am=alpha.abs_lower(); dm=(1+4*alpha).abs_lower()
  if not am>0 or not dm>0:raise ValueError('coefficient pole not excluded')
  S=rho*rho; vm=dm.rsqrt(); rmag=rho.abs_upper()
  amin=alpha.real.lower()
  if amin>0:
   # Re[a/(1+4a)] >= Re(a)/(1+4Re(a)); Im = Im(a)/|1+4a|^2.
   lo=amin/(1+4*amin); hi=arb(1)/4
   real_bound=arb((lo+hi)/2,((hi-lo)/2).upper())
   imag_bound=alpha.imag.abs_upper()/(1+4*amin)**2
   quotient=acb(real_bound,arb(0,imag_bound.upper()))
  else:
   quotient=alpha/(1+4*alpha)
  args=[alpha*S,quotient*S]
  def integral_bound(k,v,arg):
   lower=arg.real.lower()
   expbound=arb(1) if lower>=0 else (-lower).exp()
   simple=v**(2*k+1)*expbound/(2*k+1)
   if lower>0:
    decay=v**(2*k+1)*(arb(2*k+1)/2).gamma()/(2*lower.sqrt()**(2*k+1))
    return simple if simple<decay else decay
   return simple
  I=[integral_bound(k,arb(1),args[0]) for k in range(self.maxk+1)]
  Il=[integral_bound(k,vm,args[1]) for k in range(self.maxk+1)]
  J=[None]+[Il[k]+(I[k-1]+Il[k-1]+I[k]+Il[k])/(4*am) for k in range(1,self.maxk+1)]
  result=[arb(0) for _ in range(self.degree+1)]
  q=parameter*parameter
  for d,n,k,num,den,power in self.terms:
   c=horner(num,q).abs_upper()/(den.abs_lower()*am**power)
   result[d]+=c*rmag**(2*n)*J[k]
  return result

@functools.lru_cache(None)
def gauss(n):
 return [arb.legendre_p_root(n,k,weight=True) for k in range(n)]

def widen(z,error):
 return z+acb(arb(0,error),arb(0,error))

def moments(alpha,S,maxk):
 a=alpha*S;vl=(1+4*alpha).sqrt(analytic=True)**-1
 def moment(k,v):
  sh=acb(2*k+1)/2
  return v**(2*k+1)*(-a*v*v).hypgeom_1f1(sh,sh+1)/(2*k+1)
 if a.abs_lower()<4:
  I=[moment(k,acb(1)) for k in range(maxk+1)]
  Il=[moment(k,vl) for k in range(maxk+1)]
 else:
  I=[moment(0,acb(1))];Il=[moment(0,vl)]
  ex=(-a).exp();exl=(-a*vl*vl).exp()
  for k in range(maxk):
   I.append(((2*k+1)*I[k]-ex)/(2*a))
   Il.append(((2*k+1)*Il[k]-vl**(2*k+1)*exl)/(2*a))
 return [None]+[Il[k]+(I[k-1]-Il[k-1]-I[k]+Il[k])/(4*alpha) for k in range(1,maxk+1)]

def coefficient_series(field,center,order,parameter=acb(0)):
 # In S=rho^2, d^j J_k/dS^j=(-alpha)^j J_(k+j). Composition retains
 # the dependence shared by every occurrence of rho before enclosure.
 ctx.cap=order+1
 alpha=acb(field.rate) if field.rate else 1+2*parameter**2
 S=acb_series([center,1])**2
 ds=S-center**2
 J=moments(alpha,center**2,field.maxk+order)
 series={k:acb_series([(-alpha)**j*J[k+j]/math.factorial(j) for j in range(order+1)])(ds) for k in range(1,field.maxk+1)}
 powers={n:S**n for d,n,k,_,_,_ in field.terms}
 result=[acb_series([]) for _ in range(field.degree+1)]
 q=parameter**2
 for d,n,k,num,den,power in field.terms:
  c=horner(num,q)/(den*(1+2*q)**power)
  result[d]+=c*powers[n]*series[k]
 return result

class TaylorModel:
 def __init__(self,model,left,right,order=ORDER,nmix=MIXTURE_ORDER,panels=MIXTURE_PANELS):
  self.center=(left+right)/2;self.width=right-left
  self.order=order;self.radius=4*self.width
  point=acb(self.center)
  P=coefficient_series(model.p,point,order)
  Q=coefficient_series(model.e,point,order)
  # Bound each mixture Taylor coefficient's quadrature error by Cauchy.
  cr=self.width
  rho_disk=acb(arb(self.center,cr),arb(0,cr))
  tw=arb(1)/panels;eta=2*tw
  factor=tw*(tw/eta)**(2*nmix)/((2*nmix+1)*math.comb(2*nmix,nmix)**2)
  errors=[arb(0) for _ in Q]
  for panel in range(panels):
   c=tw*(2*panel+1)/2
   tau_domain=acb(arb(c,(tw/2+eta).upper()),arb(0,eta))
   M=model.m.majorant(rho_disk,tau_domain)
   for j,bound in enumerate(M):errors[j]+=factor*bound
   for x,w in gauss(nmix):
    vals=coefficient_series(model.m,point,order,acb(c+tw*x/2))
    for j,v in enumerate(vals):Q[j]+=tw*w*v/2
  self.P=[[p[j].real for j in range(order+1)] for p in P]
  self.Q=[[widen(q[j],errors[d]/cr**j).real for j in range(order+1)] for d,q in enumerate(Q)]
  # Cauchy majorants for radial Taylor truncation, uniform over the slab.
  rho_domain=acb(arb(self.center,self.radius),arb(0,self.radius))
  self.Pmax=model.p.majorant(rho_domain)
  self.Qmax=model.e.majorant(rho_domain)
  for panel in range(panels):
   c=tw*(2*panel+1)/2
   M=model.m.majorant(rho_domain,acb(arb(c,(tw/2).upper())))
   for j,v in enumerate(M):self.Qmax[j]+=tw*v
  # The 5/8 margin also covers outward rounding of the real cell balls.
  ratio=(self.width*arb(5)/8)/self.radius
  self.Perr=[v*ratio**(order+1)/(1-ratio) for v in self.Pmax]
  self.Qerr=[v*ratio**(order+1)/(1-ratio) for v in self.Qmax]
 def radial(self,rho):
  x=rho-self.center
  if not x.abs_upper()<=self.width*arb(5)/8:raise ValueError("outside Taylor remainder domain")
  def evaluate(cs,errors):
   vals=[]
   for c,err in zip(cs,errors):
    v=arb(0)
    for a in reversed(c):v=v*x+a
    vals.append(v+arb(0,err.upper()))
   return vals
  return evaluate(self.P,self.Perr),evaluate(self.Q,self.Qerr)

class Model:
 def __init__(self):
  source,local,mix=wg.definitions()
  self.p=Coefficients(source,2)
  self.e=Coefficients(local,3)
  self.m=Coefficients(mix)

def real_horner(cs,x):
 v=arb(0)
 for c in reversed(cs):v=v*x+c
 return v

def primitive(x):return (3*x.asin()+x*(1-x*x).sqrt()*(5-2*x*x))/8

def angles(n):
 out=[]
 for j in range(n):
  a=arb(j)/n;b=arb(j+1)/n
  mu=arb((a+b)/2,((b-a)/2).upper())
  weight=4*arb.pi()*(primitive(b)-primitive(a))
  if not weight>0:raise ValueError('angular measure not positive')
  out.append((mu**2,weight))
 return out

def exact_checks():
 results=wg.exact_checks()
 r,z,k=wg.r,wg.z,s.symbols('k',real=True)
 g=s.exp(-r*r-z*z)
 ur=-r*(1-2*z*z)*g; uz=2*z*(1-r*r)*g; H=1+k*r*r*g
 zero(-ur*s.diff(H,r)-uz*s.diff(H,z)-2*k*r*r*(1-r*r)*g*g,
      'complete Euler-direction density time derivative')
 x=s.symbols('x',positive=True)
 primitive=(3*s.asin(x)+x*s.sqrt(1-x*x)*(5-2*x*x))/8
 zero(s.diff(primitive,x)-(1-x*x)**s.Rational(3,2),
      'exact positive angular integration measure')
 n=MIXTURE_ORDER
 require(s.factorial(n)**4/s.factorial(2*n)**2 == 1/s.binomial(2*n,n)**2,
         'Gauss error after the Cauchy derivative bound')
 # The complex tau rectangle has |Im(tau)|<=1/4, so Re(alpha)>=7/8.
 require(1-2*s.Rational(1,4)**2==s.Rational(7,8),
         'mixture square-root branch and coefficient poles excluded')
 return results

def enclosure(value):
 return {'lower':str(value.lower()),'upper':str(value.upper())}

def run(progress=False):
 start=time.time();model=Model();angs=angles(ANGULAR_SUBDIVISIONS)
 I=arb(0);A=arb(0);B=arb(0);cells=0;rows=[]
 # Fixed dyadic cells cover [0,64] x [0,1] exactly.
 for slab in range(RADIAL_SLABS):
  left=arb(slab)/4;right=arb(slab+1)/4
  field=TaylorModel(model,left,right)
  for ri in range(RADIAL_SUBDIVISIONS):
   a=left+arb(ri)/(4*RADIAL_SUBDIVISIONS)
   b=left+arb(ri+1)/(4*RADIAL_SUBDIVISIONS)
   rho=arb((a+b)/2,((b-a)/2).upper())
   P,Q=field.radial(rho)
   radial_weight=(b**6-a**6)/6
   for mu2,w in angs:
    pv=real_horner(P,mu2);qv=real_horner(Q,mu2);ap=abs(pv)
    measure=radial_weight*w
    I+=3*ap*pv*qv*measure
    A+=3*pv**2*abs(qv)*measure
    B+=ap**3*measure
    cells+=1
  if slab%32==31:
   rows.append({'radius':(slab+1)//4,'unweighted':enclosure(I)})
   if progress:
    print(json.dumps({'radius':(slab+1)//4,'elapsed':time.time()-start}),flush=True)
 # H-1<=kappa and |H_E|<=2kappa. Both weights retain their full error.
 density_error=(arb(3)*A.upper()/2+3*B.upper())/10000
 core=I+arb(0,density_error.upper())
 tail=2*(arb(22)/7)*145**3/arb(64)**9
 whole=core+arb(0,tail.upper())
 require(core>arb(1)/100000,'compact core greater than 1e-5')
 require(whole>arb(2)/100000,'whole-space coefficient greater than 2e-5')
 require(whole>arb(213)/10**7 and whole<arb(404)/10**7,
         'reported outward rational enclosure')
 return {
  'parameters':{'precision_bits':PRECISION,'radial_Taylor_order':ORDER,
   'mixture_panels':MIXTURE_PANELS,'mixture_Gauss_order':MIXTURE_ORDER,
   'radial_slabs':RADIAL_SLABS,'radial_subdivisions_per_slab':RADIAL_SUBDIVISIONS,
   'angular_subdivisions':ANGULAR_SUBDIVISIONS,'outer_cells':cells,
   'radius':64,'b_squared':8,'L':1,'kappa':'1/10000','positive_floor':1},
  'unweighted_regeneration':enclosure(I),
  'absolute_regeneration_majorant':enclosure(A),
  'unweighted_stock_majorant':enclosure(B),
  'density_weight_error':str(density_error.upper()),
  'core':enclosure(core),'analytic_tail_bound':str(tail.upper()),
  'whole_space':enclosure(whole),
  'verified_core_lower_bound':'1/100000',
  'verified_whole_space_lower_bound':'1/50000',
  'outward_rational_enclosure':['213/10000000','404/10000000'],
  'radial_checkpoints':rows,'elapsed_seconds':time.time()-start,
  'scope':'Validated initial nonlinear pressure-regeneration coefficient. '
   'Together with analytic homogeneity this refutes universal instantaneous '
   'monotonicity of the specified completed stock. It is not Lean-certified '
   'and does not refute a full-datum integrated allowance or regularity.'}

if __name__=='__main__':
 parser=argparse.ArgumentParser()
 parser.add_argument('--check-only',action='store_true')
 parser.add_argument('--progress',action='store_true')
 args=parser.parse_args()
 output={'exact_checks':exact_checks(),'python_flint_version':flint.__version__}
 if not args.check_only:output['certificate']=run(args.progress)
 names=(Path(__file__).name,'pressure_wholespace_regeneration.py',
        'integrated_swirl_pressure.py','rotational_curl_reserve.py')
 output['source_sha256']={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() for name in names}
 print(json.dumps(output,indent=2),flush=True)
