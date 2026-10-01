#!/usr/bin/env python3
"""Physical-measure compression weight, axis trace and continuation inputs.

Exact differential and Gaussian checks for actual axisymmetric equations.
Integration, maximum principles, elliptic estimates and continuation remain
analytic. No uniformly funded weight for arbitrary data is constructed.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity, gaussian_coefficient
from circulation_source_reserve import div3, lap3


def lap_minus(f):
    return s.diff(f, r, 2)-s.diff(f, r)/r+s.diff(f, z, 2)


def physical_weight():
    nu = s.symbols('nu', positive=True)
    chi, b, W, Wt, psi, psit = [s.Function(n)(r, z)
                               for n in ('chi', 'b', 'W', 'Wt', 'psi', 'psit')]
    v, a = velocity(chi), -s.diff(chi, z)
    b_rate = nu*lap5(b)-v.dot(grad(b))-2*a*b
    h, diss = b**4, b*b*grad(b).dot(grad(b))
    flux = W*(v*h-nu*grad(h)-s.Matrix([2*nu*h/r, 0]))+nu*h*grad(W)
    defect = Wt+v.dot(grad(W))+nu*lap_minus(W)-8*a*W
    zero(Wt*h+4*W*b**3*b_rate+div3(flux)-h*defect+12*nu*W*diss,
         'complete physical weighted equation before axis integration')
    zero(12*nu*W*diss-3*nu*W*s.diff(b*b,z)**2-12*nu*W*b*b*s.diff(b,r)**2,
         'physical source is paid by the complete weighted diffusion')
    lifted_defect = Wt/r**2+v.dot(grad(W/r**2))+nu*lap5(W/r**2)-6*a*W/r**2
    zero(lifted_defect-defect/r**2,
         'measure conjugation changes both the diffusion adjoint and compression coefficient')
    log_defect = psit+v.dot(grad(psi))+nu*lap_minus(psi)+nu*grad(psi).dot(grad(psi))-8*a
    zero(defect.subs({W:s.exp(psi), Wt:s.exp(psi)*psit}).doit()-s.exp(psi)*log_defect,
         'physical logarithmic compression inequality')
    m, ap, ac, wp, wc, wt, adv, lap = s.symbols('m ap ac wp wc wt adv lap', real=True)
    full_rate = -8*m*wp*wc+wp*(wt+adv+nu*lap)-8*(ap+ac)*wp*wc
    zero(full_rate-wp*(wt+adv+nu*lap-8*ac*wc-8*(m+ap)*wc),
         'paid history factor uses eight in the physical measure')
    return {'adjoint':'Lminus=partial_rr-partial_r/r+partial_zz',
            'balance':'I_prime+12*nu*integral W*b^2*|grad b|^2 dx+4*pi*nu*integral W_axis*b_axis^4 dz=integral b^4*defect dx',
            'defect':'W_t+v.grad W+nu*Lminus(W)-8*a*W',
            'conditional_payment':'W>=1 and defect<=0 give integral_0^t||S||_2^2<=I(0)/(3*nu)',
            'paid_history_factor':'exp(8*M_H-8*integral_0^t||a_paid||_infinity)',
            'scope':'all norms here use physical dx; integrations and uniform original-datum funding are not symbolically certified'}


def axis_trace():
    nu = s.symbols('nu', positive=True)
    c0,c2,c4,b0,b2,w0,w2,w4 = [s.Function(n)(z)
                               for n in ('c0','c2','c4','b0','b2','w0','w2','w4')]
    chi, b, W = c0+c2*r**2+c4*r**4, b0+b2*r**2, w0+w2*r**2+w4*r**4
    v, a = velocity(chi), -s.diff(chi,z)
    h = b**4
    flux = W*(v*h-nu*grad(h)-s.Matrix([2*nu*h/r,0]))+nu*h*grad(W)
    zero(s.limit(-2*s.pi*r*flux[0], r, 0)-4*s.pi*nu*w0*b0**4,
         'outward flux through the shrinking inner cylinder retains its positive limit')
    zero(s.limit(lap_minus(W),r,0)-s.diff(w0,z,2),
         'regular radial curvature cancels from the physical adjoint at the axis')
    zero(s.limit(v[1],r,0)-2*c0,'actual axial drift trace')
    zero(s.limit(v.dot(grad(W))+nu*lap_minus(W)-8*a*W,r,0)
         -(2*c0*s.diff(w0,z)+nu*s.diff(w0,z,2)+8*s.diff(c0,z)*w0),
         'axis trace is the one-dimensional axial-stretching weight equation')
    zero(s.diff(v[1],z).subs(r,0)+2*a.subs(r,0),
         'axis incompressibility turns radial compression into axial expansion')
    # The physical lifted weight is singular; its boundary cannot be erased.
    W5 = W/r**2
    flux5 = W5*(v*h-nu*grad(h))+nu*h*grad(W5)
    zero(s.limit(-2*s.pi*r**3*flux5[0],r,0)-4*s.pi*nu*w0*b0**4,
         'singular conjugated lifted weight has exactly the same axis payment')
    return {'axis_payment':'4*pi*nu*integral W(0,z)*b(0,z)^4 dz',
            'necessary_trace':'w_t+U*w_z+nu*w_zz+4*U_z*w<=0, w>=1, U=u_z(t,0,z)',
            'stochastic_axis':'exp(4*integral U_z)*w along dZ=U dt+sqrt(2*nu)dB is conditionally a local supermartingale',
            'scope':'Taylor coefficients check the boundary for regular even radial fields; stochastic and boundary-limit assertions analytic'}


def sampling_generator():
    nu = s.symbols('nu', positive=True)
    y = s.symbols('y', nonnegative=True)
    f = s.Function('f')(y,z)
    pulled = f.subs(y,r*r)
    zero(lap_minus(pulled)
         -(4*y*s.diff(f,y,2)+s.diff(f,z,2)).subs(y,r*r),
         'squared radius gives a degenerate generator with an absorbing axis')
    a, U = s.symbols('a U', real=True)
    zero(a*r*s.diff(pulled,r)+U*s.diff(pulled,z)
         -(2*a*y*s.diff(f,y)+U*s.diff(f,z)).subs(y,r*r),
         'squared-radius drift keeps the actual meridional fluid')
    py,pz,q1,q2=s.symbols('py pz q1 q2',real=True)
    H=nu*(4*y*py**2+pz**2)
    control=2*s.sqrt(y)*q1*py+q2*pz-(q1*q1+q2*q2)/(4*nu)
    zero(H-control-((q1-4*nu*s.sqrt(y)*py)**2+(q2-2*nu*pz)**2)/(4*nu),
         'controlled sampling keeps the degeneracy at the axis and exact cost')
    return {'squared_radius':'dY=2*a*Y dt+sqrt(8*nu*Y) dB1; dZ=u_z dt+sqrt(2*nu) dB2',
            'axis':'Y=0 is absorbing in radius; axial sampling continues',
            'weight_process':'exp(-8*integral a)*W along this stopped diffusion is a conditional local supermartingale',
            'axis_deformation':'on Y=0, the exponential is J^4 for dJ=U_z*J dt, J(initial)=1',
            'scope':'generator and Hamiltonian checked; stochastic construction, localization and optional stopping analytic; q changes sampling only'}


def axis_pressure():
    nu=s.symbols('nu',positive=True)
    chi,p=[s.Function(n)(r,z) for n in ('chi','p')]
    v=velocity(chi)
    ur,uz=v[0],v[1]
    # The full axial equation is differentiated before taking the axis limit.
    chi0,chi2,chi4=[s.Function(n)(z) for n in ('chi0','chi2','chi4')]
    series=chi0+chi2*r**2+chi4*r**4
    zero((s.diff(uz,z).subs(chi,series).doit()).subs(r,0)+2*(-s.diff(series,z)).subs(r,0),
         'axis axial expansion equals minus twice radial strain')
    q=s.diff(uz,z)
    extra=s.diff(ur,z)*s.diff(uz,r)
    q_rate=s.diff(nu*lap3(uz)-v.dot(grad(uz))-s.diff(p,z),z)
    zero(q_rate+v.dot(grad(q))-nu*lap3(q)+q*q+s.diff(p,z,2)+extra,
         'complete differentiated axial NS equation before restriction')
    zero(extra.subs(chi,series).doit().subs(r,0),
         'differentiated radial advection has no missing axis term')
    # Full pressure Poisson trace at the axis, including swirl rotation.
    aa,bb,pzz=s.symbols('aa bb pzz',real=True)
    G=s.Matrix([[aa,-bb,0],[bb,aa,0],[0,0,-2*aa]])
    zero(s.trace(G*G)-(6*aa**2-2*bb**2),'full axis pressure source')
    prr_value=(-s.trace(G*G)-pzz)/2
    zero(-aa**2+bb**2-prr_value-(2*aa**2+pzz/2),
         'swirl affects radial compression through the complete nonlocal pressure')
    return {'axial_strain':'q=partial_z u_z at r=0 = -2*a_axis',
            'actual_evolution':'q_t+U*q_z=nu*(Delta_3 partial_z u_z)_axis-q^2-p_zz_axis',
            'radial_diffusion':'the full off-axis radial second derivatives remain in Delta_3',
            'scope':'self-expansion has a negative quadratic term; neither pressure curvature nor lateral diffusion has a proved original-datum payment'}


def physical_continuation_inputs():
    nu = s.symbols('nu', positive=True)
    chi, b, eta = [s.Function(n)(r,z) for n in ('chi','b','eta')]
    v, a = velocity(chi), -s.diff(chi,z)
    eta_rate = nu*lap5(eta)-v.dot(grad(eta))+s.diff(b*b,z)
    omega = r*eta
    omega_rate = nu*(lap3(omega)-omega/r**2)-v.dot(grad(omega))+a*omega+r*s.diff(b*b,z)
    zero(r*eta_rate-omega_rate,
         'angular vorticity equation follows from the complete eta equation')
    ut=r*b
    b_rate=nu*lap5(b)-v.dot(grad(b))-2*a*b
    zero(r*b_rate-(nu*(lap3(ut)-ut/r**2)-v.dot(grad(ut))-a*ut),
         'angular velocity has the radial-strain maximum-principle equation')
    flux = v*omega**2/2-nu*grad(omega**2/2)-s.Matrix([0,r*b*b*omega])
    zero(omega*omega_rate+div3(flux)
         +nu*(grad(omega).dot(grad(omega))+omega**2/r**2)
         -a*omega**2+r*b*b*s.diff(omega,z),
         'angular vorticity energy with signed source work and no missing axis flux')
    # Exact dissipation allocation in the integrated source work.
    x, y = s.symbols('x y', real=True)
    zero(nu*x*x/2+y*y/(2*nu)-x*y-(s.sqrt(nu)*x-y/s.sqrt(nu))**2/2,
         'source work absorbed by angular-vorticity diffusion')
    return {'source_budget':'P=I_initial_bound/(3*nu)',
            'eta_bound':'Y=||eta0||_2+sqrt(H*P)',
            'full_radial_strain':'A_H=C_BS*H^(3/4)*(2*nu)^(-1/4)*Y',
            'swirl_slope':'L_H=||b0||_infinity*exp(2*A_H)',
            'swirl_velocity':'D_H=||u_theta0||_infinity*exp(A_H)',
            'angular_vorticity_square':'Q_H=exp(2*A_H)*(||omega_theta0||_2^2+H*L_H^2*||u0||_2^2/nu)',
            'velocity_L6':'U_H=C_S*sqrt(Q_H)+||u0||_2^(1/3)*D_H^(2/3)',
            'enstrophy':'sup_[0,H]||grad u||_2^2<=||grad u0||_2^2*exp(C*nu^(-3)*H*U_H^4)',
            'scope':'analytic implication using maximum principles, elliptic estimates and Sobolev interpolation; initial weight funding is open'}


def gaussian_tests():
    b = s.exp(-r*r-2*z*z)
    chi = z*(1-3*r*r+4*z*z)*b/2
    nu = s.Rational(1,1000)
    B = gaussian_coefficient(b**4,4,1)
    D = gaussian_coefficient(b*b*grad(b).dot(grad(b)),4,1)
    S2 = gaussian_coefficient(s.diff(b*b,z)**2,4,1)
    for value,expected,label in ((B,s.Rational(1,8),'physical quartic stock'),
                                 (D,s.Rational(1,4),'physical quartic diffusion'),
                                 (S2,s.Rational(1,2),'physical source square')):
        zero(value-expected,label)
    axis = s.integrate(b.subs(r,0)**4,(z,-s.oo,s.oo))/s.sqrt(s.pi/8)
    zero(axis-1,'nonzero Gaussian axis trace')
    zero(gaussian_coefficient(4*b**3*lap5(b),4,1)+12*D+2*axis,
         'literal Gaussian viscous rate includes the axis term')
    rates=[]
    for phase in (1,-1):
        v, a = velocity(phase*chi), -s.diff(phase*chi,z)
        compression=gaussian_coefficient(a*b**4,5,1)
        zero(compression+phase*s.Rational(1,25),'physical compression moment on each phase')
        zero(gaussian_coefficient(4*b**3*(-v.dot(grad(b))-2*a*b),5,1)+8*compression,
             'literal physical nonlinear rate')
        rate=-nu*(12*D+2*axis)-8*compression*s.sqrt(s.Rational(4,5))
        require(phase*rate>0,'opposite physical quartic rates persist with positive viscosity')
        rates.append({'phase':phase,'B3_prime_over_K4':str(rate)})
    # Every smooth positive radius-only static weight fails at this point.
    wr0,wr2,wr4=s.symbols('wr0 wr2 wr4',real=True)
    W=wr0+wr2*r*r+wr4*r**4
    v,a=velocity(chi),-s.diff(chi,z)
    arbitrary_nu=s.symbols('arbitrary_nu',positive=True)
    axis_defect=s.limit(v.dot(grad(W))+arbitrary_nu*lap_minus(W)-8*a*W,r,0).subs(z,0)
    zero(axis_defect-4*wr0,'radial shape and viscosity cannot repair static positive axis weight')
    return {'B3_over_K4':str(B),'source_square_over_K4':str(S2),
            'viscosity':str(nu),'phases':rates,'static_radial_axis_defect':'4*W(0)>0',
            'scope':'failure of the sufficient pointwise static-weight inequality, not all integrated reserves or datum-dependent history weights'}


def scaling():
    # NS concentration u_lambda(t,x)=lambda*u(lambda^2*t,lambda*x).
    half=s.Rational(1,2)
    horizon,energy,b_slope,u_swirl,omega_l2_square=map(s.Integer,(-2,-1,2,1,1))
    eta_l2,source_payment=3*half,s.Integer(5)
    zero((horizon+source_payment)/2-eta_l2,'source forcing and eta have the same scaling')
    strain_history=3*horizon/4+eta_l2
    zero(strain_history,'accumulated radial strain is scale invariant')
    zero(horizon+2*b_slope+energy-omega_l2_square,'angular-vorticity source allowance scales correctly')
    u_l6=energy/6+s.Rational(2,3)*u_swirl
    zero(u_l6-omega_l2_square/2,'both velocity L6 contributions have the same scaling')
    zero(horizon+4*u_l6,'continuation exponential is scale invariant')
    return {'physical_quartic_stock_degree':5,'integrated_source_square_degree':5,
            'strain_history_degree':0,'continuation_exponential_degree':0,
            'scope':'dimensional consistency only; no bound on the funding functional'}


if __name__ == '__main__':
    print(json.dumps({'physical_weight':physical_weight(),'axis':axis_trace(),
                      'sampling_generator':sampling_generator(),
                      'axis_pressure':axis_pressure(),
                      'continuation_inputs':physical_continuation_inputs(),
                      'adversarial':gaussian_tests(),'scaling':scaling()},indent=2))
