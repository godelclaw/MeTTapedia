#!/usr/bin/env python3
"""Stretching observations modulo gradients and nonpositive work.

Hilbert cone reduction, all-time two-coordinate payment, and continuation
are analytic in README.md. Exact checks retain complete NS pressure jets
and the Reynolds source of the actual coordinate average.
"""

import json
import sympy as sp
import signed_impulse_geometry as g
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f,pm,Q=g.f,g.pm,g.Q
add,scale,cross=g.add,g.scale,g.cross


def harmonic(k,kind='sin'):
    neg=tuple(-j for j in k)
    if kind=='cos':return {k:Q(1)/2,neg:Q(1)/2}
    return {k:-f.II/2,neg:f.II/2}


def planar_velocity(psi,v):
    return [f.diff(psi,1),f.scale(-1,f.diff(psi,0)),v]


def projection(v):
    return add(v,f.grad(f.green(pm.divergence(v))))


def eqv(v,w,label):
    for j in range(3):f.equal(v[j],w[j],(label,j))


def average(v):
    return [{k:a for k,a in p.items() if k[2]==0} for p in v]


def planar_case(vertical):
    psi=f.add(f.mul(harmonic((1,0,0)),harmonic((0,1,0))),
              f.scale(Q(1)/3,harmonic((2,0,0))))
    v=f.add(harmonic((1,0,0)),f.scale(-1,harmonic((2,1,0)))) if vertical else {}
    u=planar_velocity(psi,v)
    jets,pressures=velocity_time_jets(u,Q(1),2)
    for U in jets[:2]:
        if any(k[2] for p in U for k in p):raise ArithmeticError('Two-coordinate class not retained')
    w=f.curl(u);c=f.curl(w);q=w[2]
    chi=f.add(f.scale(-1,f.mul(psi,q)),f.scale(Q(1)/2,f.mul(v,v)))
    R=[f.mul(psi,f.diff(q,0)),f.mul(psi,f.diff(q,1)),f.scale(-1,f.adv(u,v))]
    F=cross(u,w)
    eqv(F,add(f.grad(chi),R),'literal streamfunction cancellation')
    reduced=f.mul(f.adv(u,v),f.lap(v))
    f.equal(f.dot(R,c),reduced,'only vertical-component mixing remains')
    if pm.mean(f.dot(f.grad(chi),c))!=0:raise ArithmeticError('Gradient changes stretching')
    stretching=pm.mean(f.dot(w,f.matvec(f.jac(u),w)))
    if pm.mean(reduced)!=stretching:raise ArithmeticError('Reduced observation loses actual stretching')
    q1=f.curl(jets[1])[2];psi1=f.green(q1);v1=jets[1][2]
    eqv(jets[1],planar_velocity(psi1,v1),'full NS tangent keeps streamfunction representation')
    chi1=f.add(f.scale(-1,f.add(f.mul(psi1,q),f.mul(psi,q1))),f.mul(v,v1))
    R1=[f.add(f.mul(psi1,f.diff(q,j)),f.mul(psi,f.diff(q1,j))) for j in range(2)]
    R1.append(f.scale(-1,f.add(f.adv(jets[1],v),f.adv(u,v1))))
    F1=add(cross(jets[1],w),cross(u,f.curl(jets[1])))
    eqv(F1,add(f.grad(chi1),R1),'first evolving cancellation retains actual pressure')
    Eh=pm.mean(f.add(f.mul(u[0],u[0]),f.mul(u[1],u[1])))
    Zh=pm.mean(f.mul(q,q));Dh=pm.mean(f.dot(f.grad(q),f.grad(q)))
    if 2*pm.mean(f.add(f.mul(u[0],jets[1][0]),f.mul(u[1],jets[1][1])))!=-2*Zh:
        raise ArithmeticError('Horizontal energy payment')
    if 2*pm.mean(f.mul(q,q1))!=-2*Dh:raise ArithmeticError('Horizontal enstrophy payment')
    leray=projection(F)
    f.equal(pm.divergence(leray),{},'literal Leray projection')
    if vertical and stretching<=0:raise ArithmeticError('Vertical mixing must have genuine positive stretching')
    if not vertical:
        f.equal(reduced,{},'all planar nonlinear flows have zero reduced cost')
        if pm.mean(f.dot(leray,leray))<=0 or not f.dot(F,c):
            raise ArithmeticError('Planar calibration must distinguish both larger observations')
    return dict(vertical_component=vertical,pressure_modes=[len(p) for p in pressures],
        horizontal_energy=str(Eh),horizontal_enstrophy=str(Zh),
        raw_signed_observation_modes=len(f.dot(F,c)),leray_lamb_energy=str(pm.mean(f.dot(leray,leray))),
        actual_stretching=str(stretching),reduced_observation_modes=len(reduced),
        scope='full PDE tangent and evolving identity; general all-time payment is analytic')


def three_dimensional_case(u,label):
    jets,pressures=velocity_time_jets(u,Q(1),2)
    u1=jets[1];U=average(u);U1=average(u1);v=add(u,scale(-1,U))
    w=f.curl(u);c=f.curl(w);W=f.curl(U);C=f.curl(W)
    eta=f.curl(v);ce=f.curl(eta)
    psi=f.green(W[2]);V=U[2]
    eqv(U,planar_velocity(psi,V),(label,'actual coordinate average'))
    chi=f.add(f.scale(-1,f.mul(psi,W[2])),f.scale(Q(1)/2,f.mul(V,V)))
    R=[f.mul(psi,f.diff(W[2],j)) for j in range(2)]+[f.scale(-1,f.adv(U,V))]
    N=add(cross(U,eta),cross(v,W),cross(v,eta))
    defect=f.add(f.dot(R,ce),f.dot(N,c))
    actual=f.dot(add(cross(u,w),scale(-1,f.grad(chi))),c)
    expected=f.add(f.mul(f.adv(U,V),f.lap(V)),defect)
    f.equal(actual,expected,(label,'full physical three-dimensional defect'))
    if not defect:raise ArithmeticError((label,'a genuine three-dimensional defect is required'))
    sigma=[[{k:a for k,a in f.mul(v[i],v[j]).items() if k[2]==0} for j in range(3)] for i in range(3)]
    forcing=scale(-1,pm.tensor_divergence(sigma))
    pbar={k:a for k,a in pressures[0].items() if k[2]==0}
    base_rhs=add([f.lap(p) for p in U],scale(-1,[f.adv(U,p) for p in U]),scale(-1,f.grad(pbar)),forcing)
    eqv(U1,base_rhs,(label,'coordinate average retains Reynolds forcing and pressure'))
    if not any(forcing):raise ArithmeticError((label,'hidden parents must feed the average'))
    q=W[2];q1=f.curl(U1)[2];curl_force=f.curl(forcing)[2]
    fullZ=pm.mean(f.dot(w,w));baseZ=pm.mean(pm.pair(f.jac(U),f.jac(U)))
    fluctZ=pm.mean(pm.pair(f.jac(v),f.jac(v)))
    if fullZ!=baseZ+fluctZ:raise ArithmeticError('The full energy pays the actual averaged gradient')
    if pm.mean(f.dot(c,c))!=pm.mean(f.dot(C,C))+pm.mean(f.dot(ce,ce)):
        raise ArithmeticError('Actual normalized diffusion retains orthogonal average and fluctuation')
    if 2*pm.mean(f.dot(u,u1))!=-2*fullZ:raise ArithmeticError('Original full energy law is retained')
    eq=2*pm.mean(f.mul(q,q1))+2*pm.mean(f.dot(f.grad(q),f.grad(q)))
    source=2*pm.mean(f.mul(q,curl_force))
    if eq!=source:raise ArithmeticError((label,'base enstrophy has its actual parent source'))
    horizontal_work=2*pm.mean(f.add(f.mul(U[0],forcing[0]),f.mul(U[1],forcing[1])))
    base_energy_rate=2*pm.mean(f.add(f.mul(U[0],U1[0]),f.mul(U[1],U1[1])))
    base_enstrophy_rate=2*pm.mean(f.mul(q,q1))
    # Pressure annihilation holds through the first evolving full NS equation.
    F=cross(u,w);F1=add(cross(u1,w),cross(u,f.curl(u1)))
    bernoulli=f.add(pressures[0],f.scale(Q(1)/2,f.dot(u,u)))
    bernoulli1=f.add(pressures[1],f.dot(u,u1))
    eqv(F,add(u1,c,f.grad(bernoulli)),(label,'actual projected acceleration identity'))
    eqv(F1,add(jets[2],f.curl(f.curl(u1)),f.grad(bernoulli1)),(label,'evolving projected acceleration'))
    w1=f.curl(u1);B=f.jac(u);B1=f.jac(u1)
    stretch=pm.mean(f.dot(w,f.matvec(B,w)))
    stretch1=pm.mean(f.add(f.dot(w1,f.matvec(B,w)),f.dot(w,f.matvec(B1,w)),f.dot(w,f.matvec(B,w1))))
    if label=='planted_inflow' and (base_energy_rate!=Q(1)/16 or base_enstrophy_rate!=Q(1)/8):
        raise ArithmeticError('Planted internal forcing must actually amplify the base')
    if label.startswith('planted_') and (stretch!=0 or stretch1<=0):
        raise ArithmeticError('Planted eigenmode data must generate positive actual stretching')
    onset=None
    if label.startswith('planted_'):
        eqv(c,scale(2,u),'planted datum starts in one Laplacian eigenspace')
        f.equal(f.dot(F,c),{},'joint cone cost initially vanishes pointwise')
        Z0=pm.mean(f.dot(w,w));D0=pm.mean(f.dot(c,c))
        if Z0!=Q(161)/32 or D0!=Q(161)/16:raise ArithmeticError('Planted exact enstrophy normalization')
        onset=str(stretch1**2/(D0*(2*Z0)))
    return dict(fixture=label,pressure_modes=[len(p) for p in pressures],
        three_dimensional_defect_modes=len(defect),reynolds_force_modes=len(set().union(*(set(p) for p in forcing))),
        horizontal_energy_source=str(horizontal_work),horizontal_enstrophy_source=str(source),
        horizontal_energy_rate=str(base_energy_rate),horizontal_enstrophy_rate=str(base_enstrophy_rate),
        actual_stretching=str(stretch),first_stretching_rate=str(stretch1),
        quotient_cost_onset_lower_coefficient_at_zeta_Z0=onset,
        scope='all hidden Fourier outputs retained; coordinate average is not an autonomous reference')


def planted_feedback(sign):
    p=harmonic((1,0,1));q=harmonic((0,1,-1))
    v=[f.add(p,q),q,f.add(f.scale(-1,p),q)]
    sigma=[[average([f.mul(v[i],v[j]),{},{}])[0] for j in range(3)] for i in range(3)]
    force=scale(-1,pm.tensor_divergence(sigma))
    U=scale(Q(sign)/4,projection([force[0],force[1],{}]))
    if pm.mean(f.dot(U,U))!=Q(1)/64:raise ArithmeticError('Planted base energy')
    return add(U,v)


def logarithmic_parent_reserve():
    nu,k,d,M,theta=sp.symbols('nu k d M theta',positive=True)
    zero(k*nu*d/2+2*M*M/(k*nu)-2*M*sp.sqrt(d)
         -(sp.sqrt(k*nu/2)*sp.sqrt(d)-sp.sqrt(2/(k*nu))*M)**2,
         'parent uses a fixed part of the remaining diffusion')
    delta=k*k/8
    zero(2*delta*nu*nu/(k*nu)-k*nu/4,'logarithmic interpolation spends the declared diffusion')
    Z,Zu,h,ell,b,gap=sp.symbols('Z Zu h ell b gap',nonnegative=True)
    A=96/(k*nu)
    z=h+ell+b
    zprime=A*Zu*(ell+h)-k*nu*d/4-gap
    normalized_rate=zprime-A*Z*z
    remainder=-k*nu*d/4-gap-A*((Z-Zu)*(ell+h)+Z*b)
    zero(normalized_rate-remainder,'full energy pays the internally fed two-coordinate parent')
    E=sp.symbols('E',nonnegative=True)
    zero(sp.diff(48*E/(k*nu*nu),E)*(-2*nu*Z)+A*Z,'actual full kinetic energy integrating factor')
    j=sp.symbols('j',integer=True,positive=True)
    zero((2*j+1)**2-(2*j-1)**2-8*j,'two-dimensional shell count')
    return dict(logarithmic_constant=48,mean='all three components of the actual coordinate average',
        fluctuation_cost='||Q_c((u-average_z u) cross omega)||2^2/(Z+zeta)',
        OPEN='Cw=integral(theta_w-alpha nu^2 D/(Z+zeta))<=Bw(original data,nu,T)',
        ell='log(e+384 zeta/((1-alpha)^2 nu^2))',
        reserve='exp(48 E/((1-alpha)nu^2)) [ell+log((Z+zeta)/zeta)+(Bw-Cw)/nu]',
        rate='R_prime<=-((1-alpha)nu/4) exp(48 E/((1-alpha)nu^2)) D/(Z+zeta)',
        scope='periodic physical consumer; no autonomous-parent hypothesis and no proof of the fluctuation allowance')


def scalar_consumer():
    nu,theta,d,Y,zeta,k=sp.symbols('nu theta d Y zeta k',positive=True)
    gap=sp.symbols('gap',nonnegative=True)
    Lprime=2*sp.sqrt(theta*d)-2*nu*d-gap
    Cprime=theta-(1-k)*nu*nu*d
    zero(Lprime-Cprime/nu+k*nu*d+gap+(sp.sqrt(theta/nu)-sp.sqrt(nu*d))**2,
         'joint quotient reserve retains a fixed share of dissipation')
    E,Z=sp.symbols('E Z',nonnegative=True)
    zero(104*sp.sqrt((E/(2*nu))*(Z/(2*nu)))-52*sp.sqrt(E*Z)/nu,
         'existing lattice constant gives an explicit all-time parent allowance')
    return dict(conditional_reserve='log(Y/zeta)+(B-C)/nu',
        conditional_rate='R_prime+(1-alpha)nu d<=0',
        all_time_two_coordinate_allowance='52 sqrt(E_horizontal0 Z_horizontal0)/nu',
        scope='general quotient/payment arguments are analytic, not new Lean certification')


def main():
    print(json.dumps(dict(status='all exact checks passed',consumer=scalar_consumer(),logarithmic_parent=logarithmic_parent_reserve(),
        planar=[planar_case(False),planar_case(True)],
        full_3d=[three_dimensional_case(g.r.counterstrain_datum(Q(4),Q(8)),'pressure_start'),
                 three_dimensional_case(g.r.record_datum(Q(4),Q(8)),'original_maximum'),
                 three_dimensional_case(planted_feedback(1),'planted_inflow'),
                 three_dimensional_case(planted_feedback(-1),'planted_return')],
        scope='exact physical cancellation and defects; arbitrary-data history bound OPEN'),indent=2))


if __name__=='__main__':
    main()
