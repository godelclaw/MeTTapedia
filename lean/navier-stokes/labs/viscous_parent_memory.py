#!/usr/bin/env python3
"""A pressure-driven heat defect and its retained viscous tensor source.

The complete periodic NS tangent is used on a two-wave solenoidal datum.
The parabolic viscosity contribution is distinguished from temporal heat
decay. A retained quadratic-variation tensor cancels the identified
pressure source; its later nearby pressure action is not bounded here.
All convolutions retain every mode. Requires SymPy and neighboring labs.
"""
import json
import sympy as s
import pressure_history_source as f
import strain_cycle_diffusion as d
import pressure_core_envelope as envelope

def datum(n):
    first=d.sin((n,0,0));second=d.sin((n,n,0))
    return [second,f.add(f.scale(2,first),f.scale(-1,second)),
            f.add(first,f.scale(-1,second))]

def check_frequency(n):
    u=datum(n);B=f.jac(u);w=f.curl(u)
    p=f.green(f.trace(f.matmul(B,B)));P=f.hess(p)
    expected_p=f.add(f.scale(f.QQ_I(2)/5,d.cos((2*n,n,0))),f.scale(2,d.cos((0,n,0))))
    f.equal(p,expected_p,'complete canonical pressure')
    f.equal(f.trace(B),{},'solenoidal two-wave datum')
    energy=sum(f.mul(a,a).get(f.ORIGIN,f.ZERO) for a in u)
    if energy!=f.QQ_I(4):raise ArithmeticError('frequency-independent normalized energy')
    S=[[f.scale(f.QQ_I(1)/2,f.add(B[i][j],B[j][i])) for j in range(3)] for i in range(3)]
    for field in [q for row in S for q in row]+w+[q for row in P for q in row]:
        for derivative in f.grad(field):d.zero(d.ev(derivative),'zero receiver first gradient')
    r=envelope.actual(u,d.NN,s.Integer(1))
    for key,expected in [('W',n*n),('Q',s.Rational(9,2)*n*n),('V',n**3),
                         ('Z',2*n**4),('N',-s.Rational(8,5)*n**4),('gap',s.Rational(4,35)*n**4)]:
        d.zero(r[key]-expected,('actual family moment',key))
    theta=(1+r['gap']/s.sqrt(r['gap']**2+1))/2
    heat=s.diff(r['DY'],d.NU)
    d.zero(heat-s.Rational(32,5)*theta*n**6,'positive complete parabolic heat defect')
    d.zero(s.diff(r['DC'],d.NU),'core heat defect vanishes')
    for q in r['gradgap']:d.zero(q,'zero switch gradient')

    # Differentiate pressure using u_t=Delta u, separately from the full
    # nonlinear NS tangent. This is the viscosity coefficient (nu=1).
    uh=[f.lap(a) for a in u];Bh=f.jac(uh)
    ph=f.green(f.add(f.trace(f.matmul(Bh,B)),f.trace(f.matmul(B,Bh))))
    Ph=f.hess(ph)
    heatP=[[f.add(Ph[i][j],f.scale(-1,f.lap(P[i][j]))) for j in range(3)] for i in range(3)]
    target=n**4*s.Matrix([[-s.Rational(16,5),-s.Rational(8,5),0],
                         [-s.Rational(8,5),s.Rational(16,5),0],[0,0,0]])
    for entry in d.matval(heatP)-target:d.zero(entry,'actual pressure heat defect')

    # C(0)=0 and C_t(0)=2 sum_j partial_j u tensor partial_j u.
    # The full tensor pressure of this source cancels the defect above.
    Ct=[[f.scale(2,f.add(*(f.mul(B[i][j],B[k][j]) for j in range(3))))
         for k in range(3)] for i in range(3)]
    pressure_Ct=f.hess(f.tensor_pressure(Ct))
    f.same_matrices(heatP,[[f.scale(-1,a) for a in row] for row in pressure_Ct],
                    'retained viscous tensor cancels the pressure source')
    w0=s.Matrix([d.ev(a) for a in w])
    correction=-2*theta*w0.dot(d.matval(pressure_Ct)*w0)
    d.zero(heat+correction,'corrected initial reserve heat defect is zero')

    # Temporal heat derivatives need not share the sign of the parabolic
    # defect. Compute both branch temporal rates directly at the receiver.
    S0=d.matval(S);Sh=(d.matval(Bh)+d.matval(Bh).T)/2
    wh=s.Matrix([d.ev(a) for a in f.curl(uh)]);P0=d.matval(P);Ph0=d.matval(Ph)
    W,V,Q,Z,N=(r[k] for k in ('W','V','Q','Z','N'))
    Wt=2*w0.dot(wh);Vt=2*wh.dot(S0*w0)+w0.dot(Sh*w0)
    Qt=2*s.trace(S0*Sh);Zt=2*(S0*w0).dot(Sh*w0+S0*wh)
    Nt=2*wh.dot(P0*w0)+w0.dot(Ph0*w0)
    ratio=V/(W+1);Tt=2*ratio*Vt-ratio**2*Wt
    pressure_t=5*Tt+s.Rational(126,95)*W*Wt-2*Nt
    core_t=5*Tt+s.Rational(4,7)*Zt+s.Rational(10,21)*(Qt*W+Q*Wt)+s.Rational(88,95)*W*Wt
    if not (pressure_t<0 and core_t<0):raise ArithmeticError('temporal heat decay certificate')
    return {'frequency':n,'normalized_energy':'4','gap':str(r['gap']),
            'heat_defect':str(s.factor(heat)),
            'normalized_heat_defect_decimal':str(s.N(heat/r['Y'],12)),
            'temporal_heat_branch_rates':list(map(str,(pressure_t,core_t))),
            'retained_tensor_heat_defect':'0',
            'scope':'exact initial identities; decimal only illustrates size'}

def check_parameter_algebra():
    n=s.symbols('n',positive=True)
    W=n*n;Q=s.Rational(9,2)*n*n;V=n**3;Z=2*n**4;N=-s.Rational(8,5)*n**4
    pressure=5*V*V/(W+1)+s.Rational(63,95)*W*W-2*N
    core=5*V*V/(W+1)+s.Rational(4,7)*Z+s.Rational(10,21)*Q*W+s.Rational(44,95)*W*W
    d.zero(pressure-core-s.Rational(4,35)*n**4,'all-frequency switch gap')
    d.zero(pressure-(5*n**6/(n*n+1)+s.Rational(367,95)*n**4),'pressure upper-bound form')

def check_memory_jets():
    """Two actual time derivatives from C(0)=0, with all parents retained.

    This uses the nonsymmetric, genuinely three-dimensional fixture of
    the pressure-history lab. It checks the coupled differential identity
    and conservation of the mean trace, not an arbitrary-time estimate.
    """
    nu=f.QQ_I(1)/5
    u=f.fixture();B=f.jac(u);T=f.tensor(u,u)
    p=f.tensor_pressure(T);gp=f.grad(p)
    ut=[f.add(f.scale(nu,f.lap(a)),f.scale(-1,f.adv(u,a)),f.scale(-1,gp[i]))
        for i,a in enumerate(u)]
    Bt=f.jac(ut)
    Tt=[[f.add(f.mul(ut[i],u[j]),f.mul(u[i],ut[j])) for j in range(3)] for i in range(3)]
    pt=f.tensor_pressure(Tt);gpt=f.grad(pt)
    utt=[f.add(f.scale(nu,f.lap(ut[i])),f.scale(-1,f.adv(ut,u[i])),
               f.scale(-1,f.adv(u,ut[i])),f.scale(-1,gpt[i])) for i in range(3)]
    f.equal(f.trace(B),{},'initial incompressibility')
    f.equal(f.trace(Bt),{},'first tangent incompressibility')
    f.equal(f.trace(f.jac(utt)),{},'second tangent incompressibility')
    G=[[f.add(*(f.mul(B[i][k],B[j][k]) for k in range(3)))
        for j in range(3)] for i in range(3)]
    Gt=[[f.add(*(f.add(f.mul(Bt[i][k],B[j][k]),f.mul(B[i][k],Bt[j][k]))
                  for k in range(3))) for j in range(3)] for i in range(3)]
    C1=[[f.scale(2*nu,q) for q in row] for row in G]
    C2=[[f.add(f.scale(nu,f.lap(C1[i][j])),f.scale(-1,f.adv(u,C1[i][j])),
               f.scale(2*nu,Gt[i][j])) for j in range(3)] for i in range(3)]
    A1=[[f.add(Tt[i][j],C1[i][j]) for j in range(3)] for i in range(3)]
    A2=[[f.add(f.mul(utt[i],u[j]),f.scale(2,f.mul(ut[i],ut[j])),
               f.mul(u[i],utt[j]),C2[i][j]) for j in range(3)] for i in range(3)]
    source=[[f.scale(-1,f.add(f.mul(gp[i],u[j]),f.mul(u[i],gp[j])))
             for j in range(3)] for i in range(3)]
    source_t=[[f.scale(-1,f.add(f.mul(gpt[i],u[j]),f.mul(gp[i],ut[j]),
                   f.mul(ut[i],gp[j]),f.mul(u[i],gpt[j])))
               for j in range(3)] for i in range(3)]
    DA=[[f.add(A1[i][j],f.adv(u,T[i][j]),f.scale(-nu,f.lap(T[i][j])))
         for j in range(3)] for i in range(3)]
    DAt=[[f.add(A2[i][j],f.adv(ut,T[i][j]),f.adv(u,A1[i][j]),
                f.scale(-nu,f.lap(A1[i][j]))) for j in range(3)] for i in range(3)]
    f.same_matrices(DA,source,'augmented stress retains exactly the pressure work')
    f.same_matrices(DAt,source_t,'time derivative retains all pressure and memory parents')
    for label,m in [('first',A1),('second',A2)]:
        if f.trace(m).get(f.ORIGIN,f.ZERO):raise ArithmeticError((label,'total trace conservation'))
    mean_C1=f.trace(C1).get(f.ORIGIN,f.ZERO)
    mean_Tt=f.trace(Tt).get(f.ORIGIN,f.ZERO)
    if mean_C1+mean_Tt or not mean_C1.x>0 or mean_C1.y:
        raise ArithmeticError('initial kinetic loss is retained as positive memory mass')

    # The full Hessian operator commutes with the Laplacian, but not with
    # transport. Check its commutator after the physical augmentation.
    P=f.hess(p);P1=f.hess(f.tensor_pressure(A1))
    KPsource=f.hess(f.tensor_pressure(source))
    transportT=[[f.adv(u,T[i][j]) for j in range(3)] for i in range(3)]
    KPtransport=f.hess(f.tensor_pressure(transportT))
    DPstar=[[f.add(P1[i][j],f.adv(u,P[i][j]),f.scale(-nu,f.lap(P[i][j])))
             for j in range(3)] for i in range(3)]
    expected=[[f.add(KPsource[i][j],f.adv(u,P[i][j]),f.scale(-1,KPtransport[i][j]))
               for j in range(3)] for i in range(3)]
    f.same_matrices(DPstar,expected,'complete corrected pressure and transport commutator')
    return {'initial_memory':'0','viscosity':'1/5',
            'initial_memory_mass_rate':str(mean_C1),
            'total_trace_first_and_second_rates':['0','0'],
            'scope':'full three-dimensional NS time jets; no all-time coercive estimate'}

if __name__=='__main__':
    check_parameter_algebra()
    print(json.dumps({'status':'all exact checks passed',
                      'frequencies':[check_frequency(n) for n in (1,2,3)],
                      'physical_memory_jets':check_memory_jets(),
                      'scope':'scalar heat-subsolution obstruction and initial memory repair; '
                              'no arbitrary-history bound'},indent=2))
