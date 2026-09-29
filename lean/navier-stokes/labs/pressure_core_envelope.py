#!/usr/bin/env python3
"""Exact physical branches of a coercive pressure/core envelope.

All Fourier products retain every output. Pressure and its time derivative
are solved from the same actual unforced NS datum, with no Galerkin closure.
The scalar switch and a complete heat-shear class are checked independently.
The general fixture has strictly positive envelope production: this file
certifies no arbitrary-history bound. See README.md for the analytic scope.
"""
import json
import sympy as s
import strain_cycle_diffusion as d
import pressure_history_source as f

ETA=s.symbols('eta',positive=True)
X=d.SPACE
zero=d.zero

def actual(u,viscosity,eta=ETA):
    b=f.jac(u);w_fourier=f.curl(u)
    f.equal(f.trace(b),{},'solenoidal datum')
    for q in u:zero(d.ev(q),'stationary receiver')
    source=f.trace(f.matmul(b,b))
    if source.get(f.ORIGIN,f.ZERO):raise ArithmeticError('pressure source mean')
    p=f.green(source);P=f.hess(p)
    ut=[f.add(f.scale(viscosity,f.lap(u[i])),f.scale(-1,f.adv(u,u[i])),
              f.scale(-1,f.diff(p,i))) for i in range(3)]
    bt=f.jac(ut)
    f.equal(f.trace(bt),{},'solenoidal full NS tangent')
    pts=f.add(f.trace(f.matmul(bt,b)),f.trace(f.matmul(b,bt)))
    if pts.get(f.ORIGIN,f.ZERO):raise ArithmeticError('pressure-time source mean')
    pt=f.green(pts)
    B=d.jetmat(b);S=(B+B.T)/2
    w=s.Matrix([d.jet(q) for q in w_fourier]);pp=d.jetmat(P)
    S0=S.subs(d.ORIGIN);w0=w.subs(d.ORIGIN);P0=pp.subs(d.ORIGIN)
    St=(d.matval(bt)+d.matval(bt).T)/2
    wt=s.Matrix([d.ev(q) for q in f.curl(ut)])
    Pt=d.matval(f.hess(pt))
    nu=d.RING.to_sympy(d.RING.convert(viscosity))
    W=w.dot(w);V=w.dot(S*w);Q=s.trace(S*S);Z=(S*w).dot(S*w);N=w.dot(pp*w)
    W0,V0,Q0,Z0,N0=map(d.val,(W,V,Q,Z,N))
    Wt=2*w0.dot(wt);Vt=2*wt.dot(S0*w0)+w0.dot(St*w0)
    Qt=2*s.trace(S0*St);Zt=2*(S0*w0).dot(St*w0+S0*wt)
    Nt=2*wt.dot(P0*w0)+w0.dot(Pt*w0)
    DW,DV,DQ,DZ,DN=[s.factor(t-nu*d.lapval(q))
                    for q,t in zip((W,V,Q,Z,N),(Wt,Vt,Qt,Zt,Nt))]
    A=C=KS=GAM=Zcross=Zgrad=s.Integer(0)
    for j in X:
        dw=w.diff(j).subs(d.ORIGIN);ds=S.diff(j).subs(d.ORIGIN)
        dp=pp.diff(j).subs(d.ORIGIN)
        A+=dw.dot(dw);KS+=s.trace(ds*ds)
        C+=4*dw.dot(ds*w0)+2*dw.dot(S0*dw)
        GAM+=dw.dot(P0*dw)+2*dw.dot(dp*w0)
        Zcross+=(S0*w0).dot(ds*dw)
        da=ds*w0+S0*dw;Zgrad+=da.dot(da)
    zero(DW-(2*V0-2*nu*A),'DW')
    zero(DV-(Z0-N0-nu*C),'DV')
    zero(DQ-(-2*s.trace(S0**3)-V0/2-2*s.trace(S0*P0)-2*nu*KS),'DQ')
    zero(DZ-(-2*(S0*w0).dot(P0*w0)-4*nu*Zcross-2*nu*Zgrad),'DZ')
    Dp=f.add(pt,f.adv(u,p),f.scale(-viscosity,f.lap(p)))
    H=[[f.dot(f.grad(p),[f.diff(f.diff(u[k],i),j) for k in range(3)])
        for j in range(3)] for i in range(3)]
    Xi=w0.dot((d.matval(f.hess(Dp))-d.matval(H))*w0)
    zero(DN-(Xi-2*nu*GAM),'DN')
    r=V0/(W0+eta);T=V*V/(W+eta)
    Tt=2*r*Vt-r*r*Wt
    DT=s.factor(Tt-nu*d.lapval(T))
    gv=d.gradval(V)-r*d.gradval(W)
    zero(DT-(2*r*DV-r*r*DW-2*nu/(W0+eta)*gv.dot(gv)),'perspective diffusion')
    DWW=2*W0*DW-2*nu*d.gradval(W).dot(d.gradval(W))
    DQW=Q0*DW+W0*DQ-2*nu*d.gradval(Q).dot(d.gradval(W))
    pressure=5*T+s.Rational(63,95)*W*W-2*N
    core=5*T+s.Rational(4,7)*Z+s.Rational(10,21)*Q*W+s.Rational(44,95)*W*W
    pressure_t=5*Tt+s.Rational(126,95)*W0*Wt-2*Nt
    core_t=5*Tt+s.Rational(4,7)*Zt+s.Rational(10,21)*(Qt*W0+Q0*Wt)+s.Rational(88,95)*W0*Wt
    DP=s.factor(pressure_t-nu*d.lapval(pressure))
    DC=s.factor(core_t-nu*d.lapval(core))
    zero(DP-(5*DT+s.Rational(63,95)*DWW-2*DN),'pressure branch')
    zero(DC-(5*DT+s.Rational(4,7)*DZ+s.Rational(10,21)*DQW+s.Rational(44,95)*DWW),'core branch')
    gap=pressure-core;g=d.val(gap);gradgap=d.gradval(gap)
    theta=(1+g/s.sqrt(g*g+1))/2
    curvature=1/(2*(g*g+1)**s.Rational(3,2))
    Y=1+d.val(core)+(g+s.sqrt(g*g+1))/2
    DY=theta*DP+(1-theta)*DC-nu*curvature*gradgap.dot(gradgap)
    zero(g-(-2*N0-s.Rational(4,7)*Z0-s.Rational(10,21)*Q0*W0+W0*W0/5),
         'switch is independent of the denominator regularizer')
    return {'W':W0,'Q':Q0,'V':V0,'Z':Z0,'N':N0,
            'pressure':d.val(pressure),'core':d.val(core),'gap':g,
            'gradgap':gradgap,'DP':DP,'DC':DC,'Y':Y,'DY':DY}

def rotated():
    packet=[f.add(a,f.scale(-1,b)) for a,b in zip(d.fixture(1),d.base())]
    perm=(0,2,1);out=[{},{},{}]
    for i in range(3):
        for k,c in packet[i].items():
            ell=[0,0,0]
            for j in range(3):ell[perm[j]]=k[j]
            out[perm[i]][tuple(ell)]=c
    return [f.add(a,f.scale(d.MM,b)) for a,b in zip(d.base(),out)]


def check_switch():
    """Differentiate the smooth envelope independently of the rate formula."""
    a,b,at,bt,al,bl,nu=s.symbols('a b at bt al bl nu',real=True)
    delta=s.symbols('delta',positive=True)
    av=s.Matrix(s.symbols('a1:4',real=True));bv=s.Matrix(s.symbols('b1:4',real=True))
    t=s.symbols('t',real=True);x=s.Matrix(X)
    aa=a+at*t+av.dot(x)+al*X[0]**2/2
    bb=b+bt*t+bv.dot(x)+bl*X[0]**2/2
    gg=aa-bb;expr=1+bb+(gg+s.sqrt(gg*gg+delta*delta))/2
    sub={**d.ORIGIN,t:0}
    direct=s.diff(expr,t).subs(sub)-nu*sum(s.diff(expr,z,2).subs(sub) for z in X)
    root=s.sqrt((a-b)**2+delta*delta)
    theta=(1+(a-b)/root)/2;curvature=delta*delta/(2*root**3)
    expected=theta*(at-nu*al)+(1-theta)*(bt-nu*bl)-nu*curvature*(av-bv).dot(av-bv)
    zero(direct-expected,'full scalar parabolic switch identity')


def check_heat_shear():
    """For u=(U(y,t),0,V(y,t)), the unforced PDE is the heat equation."""
    a,b,r=s.symbols('a b r',real=True)
    B=s.Matrix([[0,a,0],[0,0,0],[0,b,0]])
    S=(B+B.T)/2;w=s.Matrix([b,0,-a])
    W=w.dot(w);Q=s.trace(S*S);V=w.dot(S*w);Z=(S*w).dot(S*w)
    zero(Q-W/2,'heat shear Q');zero(V,'heat shear V');zero(Z,'heat shear Z')
    zero(s.Rational(10,21)*Q*W+s.Rational(44,95)*W*W
         -s.Rational(1399,1995)*W*W,'heat shear core coefficient')
    zero(s.Rational(63,95)-s.Rational(1399,1995)+s.Rational(4,105),
         'heat shear pressure/core gap')
    # Y(r)=1+a0*r+h(-d0*r), r=W^2. Its slope is at least
    # a0-d0=63/95, and its second derivative is d0^2*h'' >=0.
    # D r=-4 nu W sum|partial_j omega|^2-2 nu |grad W|^2 <=0.
    a0=s.Rational(1399,1995);d0=s.Rational(4,105)
    zero(a0-d0-s.Rational(63,95),'strictly positive shear slope lower bound')
    return {'profile':'1+(1399/1995)r+h_delta(-(4/105)r), r=|omega|^4',
            'slope_lower':'63/95','parabolic_production':'nonpositive for nu>=0',
            'scope':'complete heat-shear histories; no vortex stretching'}


def check_fixtures():
    fixtures={'base_packet':d.fixture(d.MM),'rotated_packet':rotated(),
              'zero_vorticity':[d.SINES[1],d.SINES[0],f.add(d.COSINES[0],f.scale(-1,d.ONE))],
              'general':[f.add(q,f.scale(-d.RING.from_sympy(d.ev(q)),d.ONE)) for q in f.fixture()]}
    results={}
    for name,u in fixtures.items():
        r=actual(u,d.NN,ETA if name!='general' else s.Integer(1))
        if name in ('base_packet','rotated_packet'):
            alpha,beta=(1939,107024) if name=='base_packet' else (2547,116752)
            zero(r['DP']+16*d.M*d.M*d.NU*(alpha*ETA+beta)/(95*(ETA+16)),name+' pressure rate')
            zero(r['DC']+256*d.M*d.M*d.NU*(139*ETA+6974)/(95*(ETA+16)),name+' core rate')
            for q in r['gradgap']:zero(q,name+' switch gradient')
        elif name=='zero_vorticity':
            zero(r['W'],'vorticity zero');zero(r['Y']-s.Rational(3,2),'finite reserve at zero')
            zero(r['DP']+4*d.NU,'pressure rate at zero')
            zero(r['DC']+s.Rational(64,21)*d.NU,'core rate at zero')
            zero(r['DY']+s.Rational(74,21)*d.NU,'envelope rate at zero')
        else:
            # A rational lower certificate for positive production, with no
            # floating-point sign decision. Both weights lie in [0,1], and
            # sqrt(g^2+1)>=|g| bounds the favorable switching subtraction.
            nu=s.Rational(1,100);g=r['gap']
            if g==0:raise ArithmeticError('general fixture needs nonzero switch gap')
            lower=min(r['DP'].subs(d.NU,nu),r['DC'].subs(d.NU,nu))
            lower-=nu*r['gradgap'].dot(r['gradgap'])/(2*abs(g)**3)
            if not lower>0:raise ArithmeticError('positive production certificate failed')
            r['positive_rate_lower_at_nu_1_over_100']=lower
        results[name]={k:str(v) for k,v in r.items()}
    return results


if __name__=='__main__':
    check_switch()
    print(json.dumps({'status':'all exact checks passed','fixtures':check_fixtures(),
                      'heat_shear':check_heat_shear(),
                      'scope':'actual initial NS derivatives and a complete shear class; '
                              'no arbitrary-flow history bound'},indent=2))
