#!/usr/bin/env python3
"""Exact production of the pressure/core reserve after a pressure split.

Every NS product and canonical pressure-time mode is retained. A fixed
Fourier pressure split tests the corrected identity; it is not a spatial
separation cutoff. The companion analysis gives the actual fixed-radius
payment of the direct distant-pressure reaction. Nearby parent pressure
and gradient histories remain unpaid. Positive initial production does
not establish a singularity or disprove a history allowance.
"""
import json
import sympy as s
import pressure_history_source as f
import strain_cycle_diffusion as d
import synchronous_pressure_history as sync

def check_young():
    v,W,eta,z,w,q=s.symbols('v W eta z w q',real=True)
    k=s.Rational(9,4);b=s.Rational(4,7);c=s.Rational(10,21)
    # v here is |V|; all denominators are positive in application.
    d.zero(k*5*v*v/(W+eta)+5*W/k-10*v*W/(W+eta)
           -5*((k*v-W)**2+W*eta)/(k*(W+eta)), 'perspective Young certificate')
    d.zero(k*b*z*z+b*w*w/k-2*b*z*w-b*(k*z-w)**2/k,
           'vector Young certificate')
    d.zero(k*c*q*q*w*w+c*w*w/k-2*c*q*w*w-c*w*w*(k*q-1)**2/k,
           'matrix Young certificate')
    d.zero((5+b+c)*s.Rational(3,4)/k-s.Rational(127,63),'remaining coefficient')

def check_fluid_split(split,nu):
    u=f.fixture();u=[f.add(a,{f.ORIGIN:-sync.raw(a)}) for a in u]
    v=sync.physical(u,nu)
    b,p,w=v['B'],v['p'],v['w']
    # Translation-invariant Fourier split is used to check identities,
    # not to stand in for a spatially separated pressure estimate.
    def filt(poly):
        if split=='none':return {}
        if split=='all':return poly
        return {k:a/(1+sum(i*i for i in k)) for k,a in poly.items()}
    pf=filt(p);pft=filt(v['pt'])
    pn=f.add(p,f.scale(-1,pf));pnt=f.add(v['pt'],f.scale(-1,pft))
    # Check the parent source and transport commutator coefficient by
    # coefficient, using the FULL physical pressure in D(u tensor u).
    def observed_operator(tensor):
        source=f.add(*(f.diff(f.diff(tensor[i][j],i),j)
                       for i in range(3) for j in range(3)))
        scalar=f.green(source)
        return f.hess(f.add(scalar,f.scale(-1,filt(scalar))))
    stress=[[f.mul(u[i],u[j]) for j in range(3)] for i in range(3)]
    gp=f.grad(p)
    stress_rate=[[f.add(f.scale(-1,f.mul(gp[i],u[j])),f.scale(-1,f.mul(u[i],gp[j])),
                    *(f.scale(-2*nu,f.mul(f.diff(u[i],k),f.diff(u[j],k))) for k in range(3)))
                  for j in range(3)] for i in range(3)]
    observed=observed_operator(stress);source=observed_operator(stress_rate)
    transport=observed_operator([[f.adv(u,a) for a in row] for row in stress])
    pn_hess=f.hess(pn);pnt_hess=f.hess(pnt)
    for i in range(3):
        for j in range(3):
            f.equal(observed[i][j],pn_hess[i][j],'stress pressure identification')
            direct=f.add(pnt_hess[i][j],f.adv(u,pn_hess[i][j]),f.scale(-nu,f.lap(pn_hess[i][j])))
            expected=f.add(source[i][j],f.adv(u,pn_hess[i][j]),f.scale(-1,transport[i][j]))
            f.equal(direct,expected,'actual parent pressure and transport commutator')
    B=d.jetmat(b);S=(B+B.T)/2
    om=s.Matrix([d.jet(a) for a in w]);Pn=d.jetmat(f.hess(pn));F=d.jetmat(f.hess(pf))
    at=lambda a:a.subs(d.ORIGIN)
    S0,w0,P0,F0=map(at,(S,om,Pn,F))
    St=d.matval(v['Bt']);St=(St+St.T)/2
    wt=s.Matrix([sync.ev(a) for a in v['wt']]);Pnt=d.matval(f.hess(pnt))
    W=om.dot(om);V=om.dot(S*om);Q=s.trace(S*S);Z=(S*om).dot(S*om);N=om.dot(Pn*om)
    W0,V0,Q0,Z0,N0=map(d.val,(W,V,Q,Z,N))
    Wt=2*w0.dot(wt);Vt=2*wt.dot(S0*w0)+w0.dot(St*w0)
    Qt=2*s.trace(S0*St);Zt=2*(S0*w0).dot(St*w0+S0*wt)
    Nt=2*wt.dot(P0*w0)+w0.dot(Pnt*w0)
    nv=s.Rational(nu.x);D=lambda value,time:s.factor(time-nv*d.lapval(value))
    DW,DV,DQ,DZ,DN=[D(a,t) for a,t in zip((W,V,Q,Z,N),(Wt,Vt,Qt,Zt,Nt))]
    ag=cg=sg=zg=zc=gam=s.Integer(0)
    for x in d.SPACE:
        dw=om.diff(x).subs(d.ORIGIN);ds=S.diff(x).subs(d.ORIGIN);dp=Pn.diff(x).subs(d.ORIGIN)
        ag+=dw.dot(dw);cg+=4*dw.dot(ds*w0)+2*dw.dot(S0*dw)
        sg+=s.trace(ds*ds);zc+=(S0*w0).dot(ds*dw)
        dz=ds*w0+S0*dw;zg+=dz.dot(dz)
        gam+=dw.dot(P0*dw)+2*dw.dot(dp*w0)
    d.zero(DW-(2*V0-2*nv*ag),'actual vorticity production')
    Dpn=Pnt-nv*s.Matrix([[d.lapval(Pn[i,j]) for j in range(3)] for i in range(3)])
    d.zero(DN-(2*(S0*w0).dot(P0*w0)+w0.dot(Dpn*w0)-2*nv*gam),'actual corrected DN')
    n=w0.dot(F0*w0);z=(S0*w0).dot(F0*w0);q=s.trace(S0*F0)
    near_dv=Z0-N0-nv*cg
    near_dq=-2*s.trace(S0**3)-V0/2-2*s.trace(S0*P0)-2*nv*sg
    near_dz=-2*(S0*w0).dot(P0*w0)-4*nv*zc-2*nv*zg
    d.zero(DV-(near_dv-n),'actual strain pressure split DV')
    d.zero(DQ-(near_dq-2*q),'actual strain pressure split DQ')
    d.zero(DZ-(near_dz-2*z),'actual strain pressure split DZ')
    r=V0/(W0+1);T=V*V/(W+1);Tt=2*r*Vt-r*r*Wt
    pbranch=5*T+s.Rational(63,95)*W*W-2*N
    core=5*T+s.Rational(4,7)*Z+s.Rational(10,21)*Q*W+s.Rational(44,95)*W*W
    pbt=5*Tt+s.Rational(126,95)*W0*Wt-2*Nt
    ct=5*Tt+s.Rational(4,7)*Zt+s.Rational(10,21)*(Qt*W0+Q0*Wt)+s.Rational(88,95)*W0*Wt
    DP=D(pbranch,pbt);DC=D(core,ct)
    gap=pbranch-core;g=d.val(gap);gg=d.gradval(gap)
    root=s.sqrt(g*g+1);theta=(1+g/root)/2;curvature=1/(2*root**3)
    Y=1+d.val(core)+(g+root)/2
    DY=theta*DP+(1-theta)*DC-nv*curvature*gg.dot(gg)
    residual=(10*r*near_dv-5*r*r*DW-10*nv/(W0+1)*(d.gradval(V)-r*d.gradval(W)).dot(d.gradval(V)-r*d.gradval(W))
        +(1-theta)*(s.Rational(4,7)*near_dz+s.Rational(10,21)*(Q0*DW+W0*near_dq-2*nv*d.gradval(Q).dot(d.gradval(W))))
        +(s.Rational(44,95)+theta/5)*(2*W0*DW-2*nv*d.gradval(W).dot(d.gradval(W)))
        -2*theta*DN-nv*curvature*gg.dot(gg))
    reaction=-10*r*n-(1-theta)*(s.Rational(8,7)*z+s.Rational(20,21)*W0*q)
    d.zero(DY-residual-reaction,'complete corrected reserve production')
    # Each absolute contraction obeys the actual matrix Cauchy bounds.
    f2=s.trace(F0.T*F0)
    if not (n*n<=W0*W0*f2 and z*z<=Z0*W0*f2 and q*q<=Q0*f2):
        raise ArithmeticError('matrix contraction certificate')
    # Display the proven uniform coefficient; no floating-point sign test.
    k=s.Rational(9,4)
    # Rational lower bound on the complete signed production, if positive.
    if not g:raise ArithmeticError('nonzero switch gap required for sign certificate')
    lower=min(DP,DC)-nv*gg.dot(gg)/(2*abs(g)**3)
    if not lower>0:raise ArithmeticError('positive actual production certificate')
    return {'W':str(W0),'N_observed':str(N0),'far_contractions':list(map(str,(n,z,q))),
            'Y_decimal':str(s.N(Y,12)),'DY_decimal':str(s.N(DY,12)),
            'reaction_over_Y_decimal':str(s.N(reaction/Y,12)),
            'bound_decimal':str(s.N(k*s.sqrt(f2),12)),
            'strict_positive_lower':str(lower),
            'scope':'exact actual initial NS identities and positive-rate certificate; displayed decimals are illustrative'}

if __name__=='__main__':
    check_young()
    print(json.dumps({'status':'all exact checks passed',
                      'nu':'1/100',
                      'fixtures':{k:check_fluid_split(k,f.QQ_I(1)/100) for k in ('none','all','smooth')},
                      'scope':'Fourier observation splits; no spatial-cutoff or arbitrary-history certificate'},indent=2))
