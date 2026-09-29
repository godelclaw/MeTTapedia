#!/usr/bin/env python3
"""Exact shared-diffusion pressure histories on actual NS tangents.

A finite pressure-observation kernel retains every product mode in the
fluid and its actual tangent. Parent integration reproduces the full
initial pressure pairing and its parabolic rate. This is an observation
of the PDE, not a closed Fourier evolution. The companion analysis gives
the general smooth-kernel identity and its stochastic interpretation.
Neither mixed-gradient monotonicity nor a full continuation bound follows.
"""
import json
import sympy as s
import pressure_history_source as f
import strain_cycle_diffusion as d

def raw(a,corner=(0,0,0)):
    return sum((f.II**(sum(k[j]*corner[j] for j in range(3))%4)*v
                for k,v in a.items()),f.ZERO)
def ev(a,corner=(0,0,0)):
    v=raw(a,corner)
    if v.y:raise ArithmeticError('nonreal physical observation')
    return s.Rational(v.x.numerator,v.x.denominator)
def shift(a,k):return {tuple(q[i]+k[i] for i in range(3)):v for q,v in a.items()}
def inner(a,b):return sum((x*y for x,y in zip(a,b)),f.ZERO)
def linear(k,u):return f.add(*(f.scale(k[i],u[i]) for i in range(3)))
def checkzero(x,label):
    if x:raise ArithmeticError((label,str(x)))

def check_weighted_product():
    """Independent product differentiation, one noise coordinate at a time."""
    a,b,c,at,bt,ct,ax,by,cx,axx,byy,cxx,U,V,nu,k,control=s.symbols(
        'a b c at bt ct ax by cx axx byy cxx U V nu k control',real=True)
    A=a*c;At=at*c+a*ct
    Ax=ax*c+a*cx+s.I*k*A
    Axx=axx*c+2*ax*cx+a*cxx+2*s.I*k*(ax*c+a*cx)-k*k*A
    By=by-s.I*k*b;Byy=byy-2*s.I*k*by-k*k*b
    direct=-(At*b+A*bt)-U*Ax*b-V*A*By+nu*(Axx*b+2*Ax*By+A*Byy)
    pair=(-at-U*ax+nu*axx)*b+a*(-bt-V*by+nu*byy)+s.I*k*(V-U)*a*b+2*nu*ax*by
    expected=c*pair+(-ct-U*cx+nu*cxx)*a*b+2*nu*cx*(ax*b+a*by)
    d.zero(direct-expected,'full normalized weight product rule')
    d.zero(control*(Ax*b+A*By)-control*(c*(ax*b+a*by)+cx*a*b),
           'a common auxiliary drift does not differentiate the kernel')
    d.zero(2*nu*(b*b*ax*ax+a*a*by*by+4*a*b*ax*by)
           -3*nu*(b*ax+a*by)**2+nu*(b*ax-a*by)**2,
           'signed correlated-gradient squares')

def check_heat_signs():
    """Both signs occur in actual pressure-free unforced heat shears."""
    x,y,t,nu=s.symbols('x y t nu',real=True)
    U=s.exp(-nu*t)*(s.cos(y)+s.sin(y))
    rates={}
    for sign in (-1,1):
        # u=(U(z2,t),0,V(z2,t)); curl(u)_1=partial_2 V.
        V=s.exp(-nu*t)*(s.sin(x)+sign*s.cos(x))
        omega=s.diff(V,x);F=omega**2*U**2
        rate=(-s.diff(F,t)+nu*(s.diff(F,x,2)+2*s.diff(F,x,y)+s.diff(F,y,2)))
        rate=s.factor(rate.subs({x:0,y:0,t:0}))
        target=(-4 if sign==1 else 12)*nu
        d.zero(rate-target,'actual heat-shear shared-gradient rate')
        rates[str(sign)]=str(rate)
    return {'rates':rates,'scope':'one local component of a two-point observation; '
            'both full flows have zero pressure and no vortex stretching'}

def physical(u,nu):
    B=f.jac(u);w=f.curl(u)
    f.equal(f.trace(B),{},'solenoidal datum')
    p=f.green(f.trace(f.matmul(B,B)))
    ut=[f.add(f.scale(nu,f.lap(u[i])),f.scale(-1,f.adv(u,u[i])),
              f.scale(-1,f.diff(p,i))) for i in range(3)]
    Bt=f.jac(ut)
    f.equal(f.trace(Bt),{},'solenoidal actual tangent')
    pt=f.green(f.scale(2,f.trace(f.matmul(B,Bt))))
    return dict(u=u,B=B,w=w,p=p,ut=ut,wt=f.curl(ut),Bt=Bt,pt=pt)

def reserve_weight(v,nu):
    """Actual c=2 h'(pressure-core)/Y; keep its complete time and space jets."""
    u,B,w,p=v['u'],v['B'],v['w'],v['p']
    ss=d.jetmat(B);ss=(ss+ss.T)/2
    om=s.Matrix([d.jet(a) for a in w]);pp=d.jetmat(f.hess(p))
    S0=ss.subs(d.ORIGIN);w0=om.subs(d.ORIGIN);P0=pp.subs(d.ORIGIN)
    St=d.matval(v['Bt']);St=(St+St.T)/2
    wt=s.Matrix([ev(a) for a in v['wt']]);Pt=d.matval(f.hess(v['pt']))
    W=om.dot(om);V=om.dot(ss*om);Q=s.trace(ss*ss);Z=(ss*om).dot(ss*om);N=om.dot(pp*om)
    W0,V0,Q0,Z0,N0=map(d.val,(W,V,Q,Z,N))
    Wt=2*w0.dot(wt);Vt=2*wt.dot(S0*w0)+w0.dot(St*w0)
    Qt=2*s.trace(S0*St);Zt=2*(S0*w0).dot(St*w0+S0*wt)
    Nt=2*wt.dot(P0*w0)+w0.dot(Pt*w0)
    T=V*V/(W+1);Tt=2*V0*Vt/(W0+1)-V0**2*Wt/(W0+1)**2
    P=5*T+s.Rational(63,95)*W*W-2*N
    C=5*T+s.Rational(4,7)*Z+s.Rational(10,21)*Q*W+s.Rational(44,95)*W*W
    Pt=5*Tt+s.Rational(126,95)*W0*Wt-2*Nt
    Ct=5*Tt+s.Rational(4,7)*Zt+s.Rational(10,21)*(Qt*W0+Q0*Wt)+s.Rational(88,95)*W0*Wt
    a,b=s.symbols('a b',real=True)
    root=s.sqrt((a-b)**2+1);Y=1+b+(a-b+root)/2
    c=(1+(a-b)/root)/Y
    subs={a:d.val(P),b:d.val(C)}
    ca=s.diff(c,a).subs(subs);cb=s.diff(c,b).subs(subs)
    caa=s.diff(c,a,2).subs(subs);cab=s.diff(c,a,b).subs(subs);cbb=s.diff(c,b,2).subs(subs)
    gp=d.gradval(P);gc=d.gradval(C)
    cv=c.subs(subs);ct=ca*Pt+cb*Ct
    cg=ca*gp+cb*gc
    cl=ca*d.lapval(P)+cb*d.lapval(C)+caa*gp.dot(gp)+2*cab*gp.dot(gc)+cbb*gc.dot(gc)
    # The receiver is stationary in this fixture, but the parent is not.
    for x in u:checkzero(raw(x),'stationary receiver')
    return {'value':cv,'time':ct,'grad':cg,'lap':cl,'D':ct-s.Rational(nu.x)*cl,
            'W':W0,'Y':Y.subs(subs)}

def run(nu):
    u=f.fixture()
    u=[f.add(a,{f.ORIGIN:-raw(a)}) for a in u]
    v=physical(u,nu)
    w,p,ut,wt=v['w'],v['p'],v['ut'],v['wt']
    bw=f.matvec(v['B'],w);gp=f.grad(p)
    force=w;forced_w=f.curl(force)
    f.equal(f.trace(f.jac(force)),{},'solenoidal diagnostic force')
    x=(0,0,0);y=(0,0,1)
    ux=[raw(a,x) for a in u];uy=[raw(a,y) for a in u]
    modes=sorted(set(p)|set(v['pt']))
    points={'joint_generator':f.ZERO,'receiver':f.ZERO,'parent':f.ZERO,'relative':f.ZERO,'mixed':f.ZERO,
            'noise_independent':f.ZERO,'noise_shared':f.ZERO,'response':f.ZERO,
            'physical_force_increment':f.ZERO}
    integrated={};integrated_rate={}
    common_grad=[f.ZERO]*3
    for k in modes:
        kk=sum(a*a for a in k)
        if not kk:continue
        kw=linear(k,w);kv=linear(k,u)
        a=f.mul(kw,kw);b=f.mul(kv,kv)
        at=f.scale(2,f.mul(kw,linear(k,wt)));bt=f.scale(2,f.mul(kv,linear(k,ut)))
        A=shift(a,k);B=shift(b,tuple(-i for i in k))
        At=shift(at,k);Bt=shift(bt,tuple(-i for i in k))
        av,bv=raw(A,x),raw(B,y)
        ga=[raw(q,x) for q in f.grad(A)];gb=[raw(q,y) for q in f.grad(B)]
        la,lb=raw(f.lap(A),x),raw(f.lap(B),y)
        direct=-(raw(At,x)*bv+av*raw(Bt,y))-inner(ux,ga)*bv-av*inner(uy,gb)
        independent=nu*(la*bv+av*lb)
        shared=independent+2*nu*inner(ga,gb)
        direct+=shared
        phase=f.II**(sum(k[j]*(x[j]-y[j]) for j in range(3))%4)
        aq,bq=raw(a,x),raw(b,y)
        da=[raw(q,x) for q in f.grad(a)];db=[raw(q,y) for q in f.grad(b)]
        ka=raw(kw,x);kb=raw(kv,y)
        dwa=[raw(q,x) for q in f.grad(kw)];dub=[raw(q,y) for q in f.grad(kv)]
        receiver=(-2*ka*raw(linear(k,bw),x)+2*nu*inner(dwa,dwa))*bq
        parent=aq*(2*kb*raw(linear(k,gp),y)+2*nu*inner(dub,dub))
        relative=f.II*sum(k[j]*(uy[j]-ux[j]) for j in range(3))*aq*bq
        mixed=2*nu*inner(da,db)
        expected=phase*(receiver+parent+relative+mixed)
        checkzero(direct-expected,('two-point generator',k))
        # A body force changes the field equations themselves. A common
        # auxiliary sampling drift only adds a common spatial derivative.
        extra_at=shift(f.scale(2,f.mul(kw,linear(k,forced_w))),k)
        extra_bt=shift(f.scale(2,f.mul(kv,linear(k,force))),tuple(-i for i in k))
        extra=-(raw(extra_at,x)*bv+av*raw(extra_bt,y))
        expected_extra=phase*(-2*ka*raw(linear(k,forced_w),x)*bq
                              -2*aq*kb*raw(linear(k,force),y))
        checkzero(extra-expected_extra,('actual body-force entry',k))
        # Phase derivatives disappear from the SHARED noise, including first-order terms.
        expected_noise=phase*nu*(raw(f.lap(a),x)*bq+aq*raw(f.lap(b),y)+2*inner(da,db))
        checkzero(shared-expected_noise,('kernel noise cancellation',k))
        for label,term in [('joint_generator',direct),('receiver',phase*receiver),('parent',phase*parent),
                           ('relative',phase*relative),('mixed',phase*mixed),
                           ('noise_independent',independent),('noise_shared',shared),('response',av*bv),
                           ('physical_force_increment',extra)]:
            points[label]+=term/kk
        for j in range(3):common_grad[j]+=(ga[j]*bv+av*gb[j])/kk
        bmean=B.get(f.ORIGIN,f.ZERO)
        N=f.scale(bmean/kk,A)
        integrated=f.add(integrated,N)
        # Incompressibility removes parent advection after the parent integral;
        # periodic derivatives remove parent diffusion and cross derivatives.
        checkzero(f.adv(u,B).get(f.ORIGIN,f.ZERO),'parent transport integral')
        for q in f.grad(B):checkzero(q.get(f.ORIGIN,f.ZERO),'parent derivative integral')
        rate=f.add(f.scale(-bmean/kk,At),f.scale(-Bt.get(f.ORIGIN,f.ZERO)/kk,A),
                   f.scale(-bmean/kk,f.adv(u,A)),f.scale(nu*bmean/kk,f.lap(A)))
        integrated_rate=f.add(integrated_rate,rate)
    pk={k:c for k,c in p.items() if k in modes};ptk={k:c for k,c in v['pt'].items() if k in modes}
    Pk=f.hess(pk);Ptk=f.hess(ptk)
    actual_response=f.dot(w,f.matvec(Pk,w))
    actual_time=f.add(f.scale(2,f.dot(wt,f.matvec(Pk,w))),f.dot(w,f.matvec(Ptk,w)))
    expected_rate=f.add(f.scale(-1,actual_time),f.scale(-1,f.adv(u,actual_response)),f.scale(nu,f.lap(actual_response)))
    f.equal(integrated,actual_response,'parent integration gives actual observed pressure')
    f.equal(integrated_rate,expected_rate,'joint generator gives actual negative D of pressure pairing')
    for value in points.values():
        if value.y:raise ArithmeticError('paired mode observation must be real')
    if not points['relative']:raise ArithmeticError('relative transport must be active')
    if nu and not points['mixed']:raise ArithmeticError('shared gradient must be active')
    if not points['physical_force_increment']:raise ArithmeticError('physical force must be visible')
    result={k:str(v) for k,v in points.items()}
    result['modes']=len(modes)
    # c comes from the complete actual pressure/core reserve, not a supplied observer.
    c=reserve_weight(v,nu)
    f0=s.Rational(points['response'].x);lf=s.Rational(points['joint_generator'].x)
    cross=sum(c['grad'][j]*s.Rational(common_grad[j].x) for j in range(3))
    weighted=c['value']*lf-c['D']*f0+2*s.Rational(nu.x)*cross
    result['actual_weight']={name:str(s.N(expr,16)) for name,expr in
        [('c',c['value']),('cW',c['value']*c['W']),('generator',weighted),
         ('weight_rate',-c['D']*f0),('weight_cross',2*s.Rational(nu.x)*cross)]}
    # Values are printed for orientation only; the identities above use exact arithmetic.
    result['actual_weight']['display']='decimal evaluations only; no sign certificate claimed'
    return result

if __name__=='__main__':
    check_weighted_product()
    print(json.dumps({'status':'all exact checks passed',
                      'nu_zero':run(f.QQ_I(0)),'nu_2_over_7':run(f.QQ_I(2)/7),
                      'heat_shears':check_heat_signs()},indent=2))
