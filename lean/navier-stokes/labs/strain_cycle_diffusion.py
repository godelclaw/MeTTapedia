#!/usr/bin/env python3
"""Exact diffusion and pressure coupling for complete periodic NS tangents.

All Fourier coefficients lie in QQ(i)[M,nu]. Products retain every output
mode, and the pressure and pressure-time Hessians come from the same
unforced velocity. These are exact initial-time identities, not a closed
Galerkin trajectory or an arbitrary-flow continuation bound.

The accompanying README identifies the spatial-jet obstruction, a
vorticity reweighting that cancels its quartic diffusion cost, and an
orientation change showing why positivity remains a separate obligation.
Requires SymPy and the neighboring exact Fourier and resource modules.
"""
import json
import sympy as s
import pressure_history_source as f
import strain_cycle_reserve as cycle
import transverse_strain_history as transverse

M, NU, POWER = s.symbols('M nu p',real=True)
RING=f.QQ_I.poly_ring(M,NU)
MM,NN=RING.gens
SPACE=s.symbols('x y z',real=True)
ORIGIN=dict.fromkeys(SPACE,0)

def zero(q,label):
    q=s.factor(q)
    if q!=0: raise ArithmeticError((label,q))

def sin(k): return {k:-f.II/2,tuple(-x for x in k):f.II/2}
def cos(k): return {k:f.QQ_I(1)/2,tuple(-x for x in k):f.QQ_I(1)/2}
AXES=[tuple(1 if j==i else 0 for j in range(3)) for i in range(3)]
SINES=list(map(sin,AXES));COSINES=list(map(cos,AXES))
ONE={f.ORIGIN:f.QQ_I(1)}

def base():
    sx,sy,sz=SINES
    return [f.add(f.scale(-2,sy),sz),f.scale(2,sx),sx]

def fixture(amplitude):
    sy,sz=SINES[1:];cy,cz=COSINES[1:]
    packet=[{},f.scale(-2,f.mul(f.add(ONE,f.scale(-1,cy)),cz)),f.scale(2,f.mul(sy,sz))]
    return [f.add(a,f.scale(amplitude,b)) for a,b in zip(base(),packet)]

def ev(q):
    value=s.expand(RING.to_sympy(RING.convert(sum(q.values(),f.ZERO))))
    zero(s.im(value),'real-valued Fourier observation')
    return value
def matval(m):return s.Matrix([[ev(q) for q in row] for row in m])
def jet(q):
    return (ev(q)+sum(ev(f.diff(q,j))*SPACE[j] for j in range(3))
            +sum(ev(f.diff(f.diff(q,j),k))*SPACE[j]*SPACE[k]/2
                 for j in range(3) for k in range(3)))
def jetmat(m):return s.Matrix([[jet(q) for q in row] for row in m])
def val(q):return s.factor(q.subs(ORIGIN))
def lapval(q):return s.factor(sum(val(s.diff(q,j,2)) for j in SPACE))
def gradval(q):return s.Matrix([val(s.diff(q,j)) for j in SPACE])

def analyze(u,viscosity,compute_j=True):
    b=f.jac(u);omega=f.curl(u)
    f.equal(f.trace(b),{},'solenoidal datum')
    for q in u:zero(ev(q),'stationary initial receiver')
    source=f.trace(f.matmul(b,b))
    if source.get(f.ORIGIN,f.ZERO):raise ArithmeticError('pressure source mean')
    p=f.green(source);P=f.hess(p)
    ut=[f.add(f.scale(viscosity,f.lap(u[i])),f.scale(-1,f.adv(u,u[i])),
              f.scale(-1,f.diff(p,i))) for i in range(3)]
    f.equal(f.trace(f.jac(ut)),{},'solenoidal full NS tangent')
    bt=f.jac(ut)
    pressure_time_source=f.add(f.trace(f.matmul(bt,b)),f.trace(f.matmul(b,bt)))
    if pressure_time_source.get(f.ORIGIN,f.ZERO):
        raise ArithmeticError('pressure-time source mean')
    pt=f.green(pressure_time_source)
    Pt=matval(f.hess(pt));wt=s.Matrix([ev(q) for q in f.curl(ut)])
    B=jetmat(b);S=(B+B.T)/2;w=s.Matrix([jet(q) for q in omega]);pp=jetmat(P)
    S0=S.subs(ORIGIN);w0=w.subs(ORIGIN);P0=pp.subs(ORIGIN)
    St=(matval(bt)+matval(bt).T)/2
    W=w.dot(w);V=w.dot(S*w);N=w.dot(pp*w)
    pi=N/W;sig=V/W
    W0=val(W);V0=val(V);pi0=val(pi);sigma0=val(sig)
    Wt=2*w0.dot(wt)
    Vt=2*wt.dot(S0*w0)+w0.dot(St*w0)
    Nt=2*wt.dot(P0*w0)+w0.dot(Pt*w0)
    Ltpi=s.factor((Nt-pi0*Wt)/W0)
    Ltsigma=s.factor((Vt-sigma0*Wt)/W0)
    # This bracket is the instantaneous physical-pressure substitution
    # in the earlier joint reserve. The exponent p is kept free.
    F=s.Rational(3325,2)*sig**2+s.Rational(441,2)*W-665*pi
    LtF=3325*sigma0*Ltsigma+s.Rational(441,2)*Wt-665*Ltpi
    a=POWER/2
    LtR=s.factor(LtF+a*Wt/W0*val(F))
    DeltaR=s.factor(lapval(F)+a*val(F)/W0*lapval(W)
                    +2*a/W0*gradval(W).dot(gradval(F))
                    +a*(a-1)*val(F)/W0**2*gradval(W).dot(gradval(W)))
    nu=RING.to_sympy(RING.convert(viscosity))
    result={'strain':S0,'vorticity':w0,'pressure':P0,'pressure_rate':Pt,'W':W0,'F':val(F),
            'gradW':gradval(W),'gradF':gradval(F),
            'DW':s.factor(Wt-nu*lapval(W)),
            'Dsigma_squared':s.factor(2*sigma0*Ltsigma-nu*lapval(sig*sig)),
            'Dpi':s.factor(Ltpi-nu*lapval(pi)),
            'scaled_material_rate':LtR,'scaled_parabolic_rate':s.factor(LtR-nu*DeltaR),
            'new_quartic_value':s.factor(W0*val(F)*s.Rational(2,665)),
            'new_quartic_rate':s.factor((LtR-nu*DeltaR).subs(POWER,2)*W0*s.Rational(2,665))}

    # Independently derive the complete pressure-coupled quartic equation.
    # D means dt + u.grad - nu*Delta, with the actual pressure time derivative.
    Dp=f.add(pt,f.adv(u,p),f.scale(-viscosity,f.lap(p)))
    curvature=[[f.dot(f.grad(p),[f.diff(f.diff(u[k],i),j) for k in range(3)])
                for j in range(3)] for i in range(3)]
    incoming=w0.dot((matval(f.hess(Dp))-matval(curvature))*w0)
    A=C=Gamma=s.Integer(0)
    for j in range(3):
        dw=w.diff(SPACE[j]).subs(ORIGIN)
        ds=S.diff(SPACE[j]).subs(ORIGIN)
        dp=pp.diff(SPACE[j]).subs(ORIGIN)
        A+=dw.dot(dw)
        C+=4*dw.dot(ds*w0)+2*dw.dot(S0*dw)
        Gamma+=dw.dot(P0*dw)+2*dw.dot(dp*w0)
    G=(w0.dot(S0*S0*w0)-V0*V0/W0)/W0
    expected=(10*sigma0*(W0*G-val(N))+s.Rational(252,95)*W0*V0-2*incoming
              +nu*(-10*sigma0*C+10*sigma0*sigma0*A
                    -10*W0*gradval(sig).dot(gradval(sig))-s.Rational(252,95)*W0*A
                    -s.Rational(126,95)*gradval(W).dot(gradval(W))+4*Gamma))
    zero(result['new_quartic_rate']-expected,'complete quartic physical equation')
    if compute_j:
        J=cycle.polynomial(*cycle.moment_values(S,w))
        Jr=cycle.invariant_rate(cycle.moment_values(S0,w0),cycle.moment_tangent(S0,w0,St,wt))
        result.update(J=val(J),gradJ=gradval(J),lapJ=lapval(J),
                      materialJ=Jr,parabolicJ=s.factor(Jr-nu*lapval(J)))
    return result

def check_family():
    u=fixture(MM)
    r=analyze(u,NN)
    zero(RING.to_sympy(RING.convert(f.dot(u,u)[f.ORIGIN]))-5-4*M*M,
         'normalized kinetic energy')
    for entry in r['strain']-s.Matrix([[0,0,1],[0,0,0],[1,0,0]]):zero(entry,'central strain')
    for entry in r['vorticity']-s.Matrix([0,0,4]):zero(entry,'central vorticity')
    expected=s.diag(3,4+s.Rational(4,5)*M*M,-1-s.Rational(4,5)*M*M)
    for entry in r['pressure']-expected:zero(entry,'full pressure matrix')
    for name in ('gradW','gradF','gradJ'):
        for entry in r[name]:zero(entry,name)
    zero(r['J']-s.Rational(2776,95),'resource value')
    zero(r['materialJ']+s.Rational(16656,95)*NU,'material resource rate')
    zero(r['parabolicJ']-s.Rational(686256,1805)*NU*M*M,'parabolic resource rate')
    zero(r['F']-4193-532*M*M,'joint bracket')
    zero(r['DW']+8*NU*M*M,'actual vorticity-square parabolic slot')
    zero(r['Dsigma_squared']+10*NU*M*M,'actual directional-strain-square slot')
    zero(r['Dpi']-s.Rational(2,5)*NU*M*M*(11-M*M),'actual directional-pressure slot')
    target=NU*M*M*((266-133*POWER)*M*M-21315-s.Rational(4193,4)*POWER)
    zero(r['scaled_parabolic_rate']-target,'full parameterized exponent profile')
    zero(r['new_quartic_rate']+s.Rational(107024,95)*NU*M*M,'corrected quartic sign')
    return {k:str(v) for k,v in r.items()}

def check_permuted_family():
    # Rotate the surrounding packet while holding the observed core fixed.
    # This preserves incompressibility and the initial core S and omega.
    # Since the packet has no x dependence/component, swapping y,z agrees
    # with the proper rotation (x,y,z) -> (-x,z,y) on this packet.
    packet=[f.add(a,f.scale(-1,b)) for a,b in zip(fixture(1),base())]
    perm=(0,2,1)
    rotated=[{}, {}, {}]
    for i in range(3):
        for k,coefficient in packet[i].items():
            ell=[0,0,0]
            for j in range(3):ell[perm[j]]=k[j]
            rotated[perm[i]][tuple(ell)]=coefficient
    u=[f.add(a,f.scale(MM,b)) for a,b in zip(base(),rotated)]
    r=analyze(u,NN,False)
    zero(r['new_quartic_value']-s.Rational(32,95)*(599-76*M*M),
         'rotated packet changes the pressure-reserve sign')
    zero(r['new_quartic_rate']+s.Rational(116752,95)*NU*M*M,
         'rotated packet retains favorable diffusion in this test')
    if not r['new_quartic_value'].subs(M,3)<0:
        raise ArithmeticError('rotated counterexample must have negative reserve')
    return {k:str(v) for k,v in r.items()}


def check_general_fixture():
    # A Galilean shift places the receiver at rest without altering its
    # strain, vorticity or pressure. It does not remove material transport.
    u=[f.add(q,f.scale(-RING.from_sympy(ev(q)),ONE)) for q in f.fixture()]
    r=analyze(u,NN,False)
    if not r['new_quartic_value']>0:
        raise ArithmeticError('general fixture must start with positive quartic value')
    if not r['new_quartic_rate'].subs(NU,s.Rational(1,100))>0:
        raise ArithmeticError('general fixture must have positive parabolic production')
    return {'quartic_value':str(r['new_quartic_value']),
            'quartic_parabolic_rate':str(r['new_quartic_rate'])}


def check_core_coercivity():
    sigma,d,e,z1,z2=s.symbols('sigma d e z1 z2',real=True)
    amplitude=s.symbols('Omega',positive=True)
    strain=s.Matrix([[-sigma/2+d,e,z1],[e,-sigma/2-d,z2],[z1,z2,sigma]])
    omega=s.Matrix([0,0,amplitude])
    W=omega.dot(omega);V=omega.dot(strain*omega)
    pressure=transverse.reference_pressure(strain,omega)
    reserve=5*V*V/W+s.Rational(63,95)*W*W-2*omega.dot(pressure*omega)
    lower=(W*(s.Rational(44,7)*sigma*sigma+s.Rational(20,21)*(d*d+e*e)
              +s.Rational(32,21)*(z1*z1+z2*z2))+s.Rational(44,95)*W*W)
    zero(reserve-lower,'coercive core and directional pressure defect')


if __name__=='__main__':
    check_core_coercivity()
    print(json.dumps({'status':'all symbolic checks passed',
                      'family':check_family(), 'rotated_packet':check_permuted_family(),
                      'general_fixture':check_general_fixture(),
                      'scope':'actual unforced initial jets; no arbitrary-history bound'},indent=2))
