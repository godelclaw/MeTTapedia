#!/usr/bin/env python3
"""A nonnegative memory reserve and its geometric dissipation.

Exact checks use complete unforced viscous shear histories, including a
rotating memory eigendirection. The general smooth-prefix argument is in
README.md. Its spatial integral does not bound arbitrary receivers or
the nearby pressure-Hessian action of the memory.
"""
import json
import sympy as s
import pressure_history_source as f
import strain_cycle_diffusion as d


def heat(field, q):
    return {k: a*q**sum(z*z for z in k) for k,a in field.items()}


def check_shear(q, phase):
    """q=exp(-nu*t) gives an actual positive-time unforced shear."""
    nu=f.QQ_I(1)/5;eta=s.Integer(1)
    u0=[f.scale(3,f.add(d.sin((0,1,0)),f.scale(phase,d.cos((0,1,0))))),
        {},d.cos((0,2,0))]
    u=[heat(a,q) for a in u0];ut=[f.scale(nu,f.lap(a)) for a in u]
    T0=f.tensor(u0,u0);T=f.tensor(u,u)
    H0=[[heat(a,q) for a in row] for row in T0]
    C=[[f.add(H0[i][j],f.scale(-1,T[i][j])) for j in range(3)] for i in range(3)]
    Ct=[[f.add(f.scale(nu,f.lap(H0[i][j])),
               f.scale(-1,f.mul(ut[i],u[j])),f.scale(-1,f.mul(u[i],ut[j])))
         for j in range(3)] for i in range(3)]
    B=f.jac(u)
    f.equal(f.trace(B),{},'incompressible heat shear')
    f.equal(f.tensor_pressure(T),{},'complete physical pressure is zero')
    f.equal(f.tensor_pressure(C),{},'retained memory generates no pressure in this class')
    for a in u:f.equal(f.adv(u,a),{},'complete NS advection is zero')
    G=f.matmul(B,[list(row) for row in zip(*B)])
    DC=[[f.add(Ct[i][j],f.adv(u,C[i][j]),f.scale(-nu,f.lap(C[i][j])))
         for j in range(3)] for i in range(3)]
    f.same_matrices(DC,[[f.scale(2*nu,a) for a in row] for row in G],
                    'actual nonzero-memory source equation')

    c=d.matval(C);ct=d.matval(Ct);g=d.matval(G)
    h=c+eta*s.eye(3);inv=h.inv();det=h.det();nu_s=s.Rational(1,5)
    if any(c[i,i]<0 for i in range(3)) or c[0,0]*c[2,2]-c[0,2]**2<0:
        raise ArithmeticError('positive memory matrix')
    if det<=0:raise ArithmeticError('positive regularized determinant')
    dc=[d.matval([[f.diff(a,j) for a in row] for row in C]) for j in range(3)]
    lapc=d.matval([[f.lap(a) for a in row] for row in C])
    fisher=sum(s.trace(inv*a*inv*a) for a in dc)
    source=2*nu_s*eta*s.trace(inv*g)
    gradient=nu_s*eta*fisher

    # Differentiate the determinant polynomial independently of the
    # inverse-matrix formula used in the proposed dissipation.
    eps=s.symbols('eps',real=True)
    det_t=s.diff((h+eps*ct).det(),eps).subs(eps,0)
    det_jet=(d.jetmat(C)+eta*s.eye(3)).det()
    det_lap=d.lapval(det_jet);det_grad=d.gradval(det_jet)
    entropy_t=s.trace(ct)-eta*det_t/det
    entropy_lap=s.trace(lapc)-eta*(det_lap/det-det_grad.dot(det_grad)/det**2)
    velocity=s.Matrix([d.ev(a) for a in u]);velocity_t=s.Matrix([d.ev(a) for a in ut])
    energy_rate=2*velocity.dot(velocity_t)-nu_s*d.ev(f.lap(f.dot(u,u)))
    reserve_rate=s.factor(energy_rate+entropy_t-nu_s*entropy_lap)
    d.zero(reserve_rate+source+gradient,'complete physical entropy-reserve identity')
    if source<0 or gradient<0:raise ArithmeticError('nonnegative entropy production')
    mean0=f.dot(u0,u0).get(f.ORIGIN,f.ZERO)
    mean=f.dot(u,u).get(f.ORIGIN,f.ZERO)
    memory_mean=f.trace(C).get(f.ORIGIN,f.ZERO)
    if mean+memory_mean!=mean0:raise ArithmeticError('full kinetic-plus-memory mass')

    # The nontrivial eigenspace is the xz plane. This formula separates
    # spatial turning from turning due to the positive source 2nu G.
    gap_sq=(c[0,0]-c[2,2])**2+4*c[0,2]**2
    turning=source_turn=angle_drift=pair_cost=s.Integer(0);separated=False
    if gap_sq:
        turning=s.factor(((c[0,0]-c[2,2])*dc[1][0,2]
                           -c[0,2]*(dc[1][0,0]-dc[1][2,2]))/gap_sq)
        source_turn=s.factor(2*nu_s*((c[0,0]-c[2,2])*g[0,2]
                                   -c[0,2]*(g[0,0]-g[2,2]))/gap_sq)
        pair_cost=2*gap_sq*turning**2/(h[0,0]*h[2,2]-h[0,2]**2)
        if fisher<pair_cost:raise ArithmeticError('orientation part of matrix gradient cost')
        separated=bool(9*gap_sq>=(2*eta+c[0,0]+c[2,2])**2)
        if separated and (fisher<turning**2 or eta*abs(source_turn)>source):
            raise ArithmeticError('separated-eigenvalue turning payments')
        angle_t=((c[0,0]-c[2,2])*ct[0,2]-c[0,2]*(ct[0,0]-ct[2,2]))/gap_sq
        gap_sq_y=2*(c[0,0]-c[2,2])*(dc[1][0,0]-dc[1][2,2])+8*c[0,2]*dc[1][0,2]
        angle_yy=((c[0,0]-c[2,2])*lapc[0,2]-c[0,2]*(lapc[0,0]-lapc[2,2]))/gap_sq
        angle_yy-=turning*gap_sq_y/gap_sq
        angle_drift=s.factor(angle_t-nu_s*angle_yy)
        drift_sq=2*angle_drift**2+8*nu_s**2*turning**4
        drift_bound=3*source/eta+48*nu_s*fisher
        if separated and (drift_sq>drift_bound**2 or 4*nu_s*turning**2>4*nu_s*fisher):
            raise ArithmeticError('complete stochastic projector drift and noise costs')
    if not phase:
        d.zero(fisher-pair_cost,'all memory gradient cost is orientation at this receiver')
    return {'heat_parameter':str(q),'phase':phase,'initial_mean_energy':str(mean0),
            'memory_mass':str(memory_mean),'weighted_source_cost':str(source),
            'matrix_gradient_cost':str(gradient),'reserve_parabolic_rate':str(reserve_rate),
            'spatial_frame_turn':str(turning) if gap_sq else None,
            'source_only_frame_turn':str(source_turn) if gap_sq else None,
            'complete_parabolic_angle_drift':str(angle_drift) if gap_sq else None,
            'regularized_eigenvalue_ratio_at_least_two':separated,
            'scope':'exact samples of a complete unforced shear family; no nearby-pressure bound'}


def check_frame_algebra():
    a,b=s.symbols('a b',positive=True)
    da,db,r=s.symbols('da db r',real=True)
    derivative=s.Matrix([[da,(b-a)*r],[(b-a)*r,db]])
    inverse=s.diag(1/a,1/b)
    d.zero(s.trace(inverse*derivative*inverse*derivative)
           -(da**2/a**2+db**2/b**2+2*(a-b)**2/(a*b)*r**2),
           'exact eigenvalue and frame-gradient decomposition')
    rho=s.symbols('rho',positive=True)
    d.zero((a-b)**2/(a*b)-(rho-1)**2/rho
           -(a-rho*b)*(rho*a-b)/(rho*a*b),'gap-weight lower bound factorization')

    # Full three-dimensional eigenprojector variation, including the
    # quadratic term needed for its actual parabolic generator.
    lam=s.symbols('lam',real=True)
    E=s.Matrix([[s.symbols('E00',real=True),s.symbols('E01',real=True),s.symbols('E02',real=True)],
                [s.symbols('E01',real=True),s.symbols('E11',real=True),s.symbols('E12',real=True)],
                [s.symbols('E02',real=True),s.symbols('E12',real=True),s.symbols('E22',real=True)]])
    C=s.diag(lam,lam-a,lam-b);e=s.Matrix([1,0,0]);v=s.Matrix([0,E[1,0]/a,E[2,0]/b])
    w=s.Matrix([-v.dot(v),2*((E*v)[1]-E[0,0]*v[1])/a,
                2*((E*v)[2]-E[0,0]*v[2])/b])
    P=e*e.T;P1=v*e.T+e*v.T;P2=w*e.T+e*w.T+2*v*v.T
    for label,residual in [
            ('first commutation',C*P1-P1*C+E*P-P*E),
            ('second commutation',C*P2-P2*C+2*(E*P1-P1*E)),
            ('first idempotency',P*P1+P1*P-P1),
            ('second idempotency',P*P2+P2*P+2*P1*P1-P2)]:
        for entry in residual:d.zero(entry,label)
    d.zero(s.trace(P1),'first projector trace');d.zero(s.trace(P2),'second projector trace')


if __name__=='__main__':
    check_frame_algebra()
    results=[check_shear(q,phase) for q in (f.QQ_I(1),f.QQ_I(1)/2,f.QQ_I(3)/4) for phase in (0,1)]
    print(json.dumps({'status':'all exact checks passed','shear_histories':results,
                      'scope':'nonnegative global entropy reserve and geometric costs; '
                              'continuation estimate remains open'},indent=2))
