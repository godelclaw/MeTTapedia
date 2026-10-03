#!/usr/bin/env python3
"""Signed impulse geometry, its physical source and continuation budget.

The continuation estimate adapts the geometric energy method of Chae--Lee;
see README.md. PDE integration, comparison, local histories and the imported
forced obstruction remain analytic. All Fourier products keep every output.
"""

import itertools
import json
import sympy as sp

import passive_parent_bellman as parent
import pressure_impulse_history as ph
import pressure_memory_diffusion as pm
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f, Q, r = parent.f, parent.Q, parent.r


def cross(v, w):
    return [f.add(f.mul(v[1], w[2]), f.scale(-1, f.mul(v[2], w[1]))),
            f.add(f.mul(v[2], w[0]), f.scale(-1, f.mul(v[0], w[2]))),
            f.add(f.mul(v[0], w[1]), f.scale(-1, f.mul(v[1], w[0])))]


def add(*vectors):
    return [f.add(*(v[j] for v in vectors)) for j in range(3)]


def scale(c, v):
    return [f.scale(c, p) for p in v]


def derivative(v, j):
    return [f.diff(p, j) for p in v]


def consumer_squares():
    nu, M, A, Z, D, E, delta = sp.symbols('nu M A Z D E delta', positive=True)
    # These two elementary squares retain the whole-space low-vorticity
    # remainder without integrating a spatially constant regularizer.
    v = sp.sqrt(A*A*Z+4*delta*E)
    h = M*sp.sqrt(Z)
    zero(2*(M*M+A*A)*Z+8*delta*E-(h+v)**2-(h-v)**2,
         'combined parent and signed-impulse coefficient')
    zero(nu*D+(h+v)**2/nu-2*sp.sqrt(D)*(h+v)
         -(sp.sqrt(nu*D)-(h+v)/sp.sqrt(nu))**2,
         'half dissipation retained for physical continuation')
    force_squared=sp.symbols('force_squared',nonnegative=True)
    for value in (sp.sqrt(A*A*Z+delta*E),sp.sqrt(force_squared)):
        zero(nu*D/2+2*value**2/nu-2*sp.sqrt(D)*value
             -(sp.sqrt(nu*D/2)-sp.sqrt(2/nu)*value)**2,
             'forced comparison allocates half nu D to each source')
    q, F, z, g, diss, tau, exponent = sp.symbols('q F Z g diss tau exponent', real=True)
    Zrate = 2*g-2*nu*diss
    gap = q*z+F-(Zrate+nu*diss)
    reserve = sp.exp(exponent)*(z+F*tau)-z
    rate = sp.diff(reserve,z)*Zrate-sp.diff(reserve,tau)-q*sp.diff(reserve,exponent)
    expected = -sp.exp(exponent)*gap-nu*(sp.exp(exponent)-1)*diss
    expected -= sp.exp(exponent)*q*F*tau
    zero(rate+2*g-nu*diss-expected, 'complete nonnegative reserve rate and its deductions')
    return dict(enstrophy='Z_prime+nu D <= (2/nu)(M^2+A^2)Z+8 delta E0/nu',
                reserve='exp((2/nu)(M^2(T-t)+ell(t)))(Z+F(T-t))-Z',
                allowance='exp((2/nu)(M^2 T+L))(Z0+F T)-Z0+2T|g0|',
                scope='conditional on an original-data bound for integral A^2; not established here')


def actual_history(u0, label, cutoff_squared):
    nu = Q(1)
    jets, pressures = velocity_time_jets(u0, nu, 2)
    u, u1, u2 = jets
    omega = [f.curl(v) for v in jets]
    curls = [f.curl(w) for w in omega]
    B = [f.jac(v) for v in jets]
    H1 = ph.vector_transport(u, u, nu)
    H2 = add(ph.vector_transport(u, H1, nu), scale(-1, [f.adv(u1,p) for p in u]))
    I1 = add(H1, scale(-1,u1))
    I2 = add(H2, scale(-1,u2))
    gp, gp1 = f.grad(pressures[0]), f.grad(pressures[1])
    ph.vectors_equal(I1, gp, (label,'original impulse, actual first pressure source'))
    L1 = cross(I1,omega[0])
    L2 = add(cross(I2,omega[0]),scale(2,cross(I1,omega[1])))
    full_rate1 = add(L2, scale(-1,ph.vector_transport(u,L1,nu)))
    mixed = add(*(cross(derivative(I1,j),derivative(omega[0],j)) for j in range(3)))
    expected_rate1 = add(cross(gp1,omega[0]),cross(gp,omega[1]),
                         cross(I1,f.matvec(B[0],omega[0])),scale(-2*nu,mixed))
    ph.vectors_equal(full_rate1,expected_rate1,(label,'full evolving cross impulse including mixed diffusion'))
    spatial_commutator = add(*(f.matvec([[f.diff(p,j) for p in row] for row in B[0]],
                                       derivative(u,j)) for j in range(3)))
    actual_c = add(curls[1], scale(-1,ph.vector_transport(u,curls[0],nu)))
    expected_c = add(f.grad(f.lap(pressures[0])),scale(-1,f.matvec(B[0],curls[0])),
                     scale(2,spatial_commutator))
    ph.vectors_equal(actual_c,expected_c,(label,'complete derivative of curl omega'))
    stretch = f.dot(omega[0],f.matvec(B[0],omega[0]))
    lamb = f.dot(cross(u,omega[0]),curls[0])
    if pm.mean(stretch)!=pm.mean(lamb):
        raise ArithmeticError((label,'physical integrated stretching equals Lamb observation'))
    stretch1 = f.add(f.dot(omega[1],f.matvec(B[0],omega[0])),
                    f.dot(omega[0],f.matvec(B[1],omega[0])),
                    f.dot(omega[0],f.matvec(B[0],omega[1])))
    lamb1 = f.add(f.dot(cross(u1,omega[0]),curls[0]),
                 f.dot(cross(u,omega[1]),curls[0]),f.dot(cross(u,omega[0]),curls[1]))
    if pm.mean(stretch1)!=pm.mean(lamb1):
        raise ArithmeticError((label,'evolving physical stretching identity with pressure'))
    J1 = f.scale(-1,f.dot(L1,curls[0]))
    J2 = f.scale(-1,f.add(f.dot(L2,curls[0]),f.scale(2,f.dot(L1,curls[1]))))
    # The signed cross observation has a full local evolution, not an
    # independently specified forcing. Its first evolving rate retains
    # changing pressure, changing curl observer and all mixed derivatives.
    J_rate1 = f.add(J2, f.adv(u,J1),f.scale(-nu,f.lap(J1)))
    expected_J_rate1 = f.add(f.scale(-1,f.dot(expected_rate1,curls[0])),
        f.scale(-1,f.dot(cross(gp,omega[0]),curls[1])),
        f.scale(-1,f.dot(L1,actual_c)),
        f.scale(2*nu,f.add(*(f.dot(derivative(L1,j),derivative(curls[0],j)) for j in range(3)))))
    f.equal(J_rate1,expected_J_rate1,(label,'complete evolving signed numerator'))
    project = lambda v: [{k:c for k,c in p.items() if sum(j*j for j in k)<=cutoff_squared} for p in v]
    eta,zeta = project(omega[0]),add(omega[0],scale(-1,project(omega[0])))
    xi = add(project(f.matvec(B[0],omega[0])),scale(-1,f.matvec(B[0],eta)),
             [f.adv(u,p) for p in eta],scale(-1,project([f.adv(u,p) for p in omega[0]])))
    internal1 = cross(I1,xi)
    if not any(internal1):
        raise ArithmeticError((label,'internal cross fixture must be informative'))
    ph.vectors_equal(add(internal1,scale(-1,internal1)),[{},{},{}],
                     (label,'internal cross sources are retained with opposite signs'))
    f.equal(f.dot(L1,L1),f.add(f.dot(cross(I1,eta),cross(I1,eta)),
        f.dot(cross(I1,zeta),cross(I1,zeta)),f.scale(2,f.dot(cross(I1,eta),cross(I1,zeta)))),
        (label,'generated cross impulse retains the joint squared observation'))
    four_terms=f.add(*(f.dot(cross(I1,w),f.curl(v))
                      for w in (eta,zeta) for v in (eta,zeta)))
    f.equal(J1,f.scale(-1,four_terms),(label,'signed observation retains all four parent pairs'))
    sample = None
    if label=='pressure_start':
        for point in itertools.product(range(3),repeat=3):
            value=r.at(J1,point)
            if value.is_positive:
                w=sp.Matrix([r.at(p,point) for p in omega[0]])
                c=sp.Matrix([r.at(p,point) for p in curls[0]])
                if w.dot(w)>0 and c.dot(c)>0:
                    sample=dict(point_in_pi_over_four_units=point,signed_numerator_rate=str(value),
                                omega_squared=str(w.dot(w)),curl_omega_squared=str(c.dot(c)))
                    break
        if sample is None:
            raise ArithmeticError('No informative positive physical creation fixture found')
    return dict(fixture=label,pressure_modes=[len(p) for p in pressures],
                signed_first_rate_modes=len(J1),signed_second_rate_modes=len(J2),
                positive_creation=sample,internal_correction_modes=len(set().union(*(set(p) for p in internal1))),
                scope='full actual initial jets and analytic short histories; no arbitrary-time bound')


def exact_eigenflows():
    x,y,z,t=sp.symbols('x y z t',real=True)
    amp,nu=sp.symbols('A nu',positive=True)
    coords=(x,y,z)
    lap=lambda v:sum(sp.diff(v,c,2) for c in coords)
    grad=lambda p:sp.Matrix([sp.diff(p,c) for c in coords])
    curl=lambda v:sp.Matrix([sp.diff(v[2],y)-sp.diff(v[1],z),
                             sp.diff(v[0],z)-sp.diff(v[2],x),
                             sp.diff(v[1],x)-sp.diff(v[0],y)])
    Uabc=sp.Matrix([sp.sin(z)+sp.cos(y),sp.sin(x)+sp.cos(z),sp.sin(y)+sp.cos(x)])
    Ucell=sp.Matrix([sp.sin(x)*sp.cos(y),-sp.cos(x)*sp.sin(y),0])
    cases=[('ABC',Uabc,-Uabc.dot(Uabc)/2,1),
           ('cellular',Ucell,(sp.cos(2*x)+sp.cos(2*y))/4,2)]
    rows=[]
    for name,U,P,k2 in cases:
        u=amp*sp.exp(-nu*k2*t)*U
        p=amp**2*sp.exp(-2*nu*k2*t)*P
        for j,val in enumerate(u.diff(t)+u.jacobian(coords)*u+grad(p)-nu*u.applyfunc(lap)):
            zero(sp.trigsimp(val),(name,'literal all-time unforced equation',j))
        w=curl(u); c=curl(w)
        for j,val in enumerate(c-k2*u):
            zero(sp.trigsimp(val),(name,'curl observer stays parallel to velocity',j))
        zero(sp.trigsimp(u.cross(w).dot(c)),(name,'full signed Lamb production vanishes pointwise'))
        H=sp.Matrix(sp.symbols('H0:3',real=True))
        zero(sp.trigsimp(-(H-u).cross(w).dot(c)+H.cross(w).dot(c)),
             (name,'impulse observation is paid by original passive magnitude'))
        if name=='ABC':
            zero(sp.trigsimp(H.cross(w).dot(c)), 'ABC signed impulse cost vanishes for every actual H')
        rows.append(dict(flow=name,laplacian_eigenvalue=k2,
                         signed_observer_bound='a_delta = 0' if name=='ABC' else 'a_delta <= M',
                         integral_allowance='0' if name=='ABC' else 'M^2 T',
                         scope='actual entire decaying family; H itself is not replaced by u'))
    part1=sp.Matrix([0,sp.sin(x),sp.cos(x)])
    part2=Uabc-part1
    for part in (part1,part2):
        for v in curl(part)-part:
            zero(sp.trigsimp(v),'fixed ABC Fourier components keep their common eigenvalue')
    gp=grad(-amp**2*Uabc.dot(Uabc)/2)
    j12=-gp.cross(amp*part1).dot(amp*part2)
    j21=-gp.cross(amp*part2).dot(amp*part1)
    zero(sp.trigsimp(j12+j21),'off-diagonal signs cancel before positive part')
    point={x:0,y:sp.pi/2,z:0}
    zero(sp.trigsimp(j12.subs(point))+amp**4,'actual first off-diagonal pressure-history rate')
    zero(sp.trigsimp(j21.subs(point))-amp**4,'actual second off-diagonal pressure-history rate')
    rows.append(dict(flow='ABC joint parent observation',point='(0,pi/2,0)',
                     off_diagonal_first_rates=['-A^4','A^4'],full_signed_cost='identically zero',
                     separate_positive_numerators='A^4 t+O(t^2)>0 for small positive t',
                     scope='actual inherited pressure impulse; no independent parent choices'))
    return rows


def main():
    simple=parent.carrier(r.c.simple_parent(),Q(16),4,[{},{},{}])
    background=r.ns.vector_scale(Q(-20000),r.ns.nonlinear(r.c.resonant_parent()))
    resonant=parent.carrier(r.c.resonant_parent(),Q(200),4,background)
    cases=[(r.counterstrain_datum(Q(4),Q(8)),'pressure_start',1),
           (r.record_datum(Q(4),Q(8)),'original_maximum',1),
           (simple,'original_simple_carrier',10),(resonant,'original_resonant_carrier',3)]
    result=dict(status='all exact checks passed',consumer=consumer_squares(),
                eigenflows=exact_eigenflows(),histories=[actual_history(*case) for case in cases],
                scope='analytic conditional geometric continuation and source identification; full datum-only allowance OPEN')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
