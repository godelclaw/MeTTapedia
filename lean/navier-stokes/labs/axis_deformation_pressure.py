#!/usr/bin/env python3
"""Actual pressure suppliers for stochastic axial deformation.

Exact Ito-generator algebra and whole-space Gaussian pressure moments.
The initial data are smooth, solenoidal and finite energy. Local solution,
heat-resolvent and stochastic stopping consequences are analytic, not Lean
certificates. Static metric monotonicity is tested, not global regularity.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity
from circulation_source_reserve import div3


def ito_deformation():
    J,V,q,qz,qzz,U,D,pzz,nu=s.symbols('J V q qz qzz U D pzz nu',real=True)
    qt=-U*qz+nu*D-q*q-pzz
    F=-pzz+nu*(D+qzz)
    q_drift=qt+U*qz+nu*qzz
    zero(q_drift-(F-q*q),'forward sampling retains its additional axial diffusion')
    zero(J*q*q+J*q_drift-J*F,'quadratic strain cancels in the acceleration variable V=Jq')
    generator=lambda phi: V*s.diff(phi,J)+J*F*s.diff(phi,V)+nu*J*J*qz*qz*s.diff(phi,V,2)
    zero(generator(V*V)-(2*V*J*F+2*nu*J*J*qz*qz),
         'acceleration square retains positive quadratic variation')
    zero(generator(J*V)-(V*V+J*J*F),'mixed deformation moment')
    ell=s.symbols('ell',positive=True)
    Q=J*J+ell*ell*V*V
    energy=Q*Q
    expected=4*J*V*Q*(1+ell*ell*F)+4*nu*ell*ell*J*J*qz*qz*(J*J+3*ell*ell*V*V)
    zero(generator(energy)-expected,'complete quartic phase-space metric drift')
    zero(9*Q*Q-8*J*J*(J*J+3*ell*ell*V*V)-(J*J-3*ell*ell*V*V)**2,
         'sharp diffusion comparison for the quartic metric')
    zero(Q-2*ell*J*V-(J-ell*V)**2,'one sign of the mixed-term comparison')
    zero(Q+2*ell*J*V-(J+ell*V)**2,'the other sign of the mixed-term comparison')
    alpha,beta,gamma=s.symbols('alpha beta gamma',real=True)
    general=(alpha*J*J+2*beta*J*V+gamma*V*V)**2
    # Here F=1 and q_z=0: the realized initial drift is exactly radial in (J,V).
    eigen_generator=lambda phi: V*s.diff(phi,J)+J*s.diff(phi,V)
    zero((eigen_generator(general)-4*general).subs({J:1,V:1}),
         'every positive quadratic metric squared increases on the realized eigenvector')
    return {'state':'dJ=V dt; dV=J*F dt+sqrt(2nu)*J*q_z dB',
            'F':'-p_zz_axis+nu*((Delta_3 partial_z u_z)_axis+q_zz)',
            'squared_velocity_drift':'2*V*J*F+2*nu*J^2*q_z^2',
            'quartic_drift':'4*J*V*Q*(1+ell^2*F)+4*nu*ell^2*J^2*q_z^2*(J^2+3*ell^2*V^2)',
            'conditional_rate':'k_ell=2*abs(1+ell^2*F)/ell+(9/2)*nu*ell^2*q_z^2',
            'scope':'exact generator algebra; no original-datum funding for this future-dependent rate'}


def far_pressure_payment():
    J,V,pfar=s.symbols('J V pfar',real=True)
    ell=s.symbols('ell',positive=True)
    K=s.symbols('K',nonnegative=True)
    Q=J*J+ell*ell*V*V
    E=Q*Q
    far=-4*ell*ell*J*V*Q*pfar
    # For ell>0, K>=abs(pfar), use either sign certificate according to JV*pfar.
    zero(2*ell*K*E-far-2*ell*Q*(K*Q+2*ell*J*V*pfar),
         'exact far-pressure quartic comparison')
    zero(Q-2*ell*J*V-(J-ell*V)**2,'positive mixed moment bound')
    zero(Q+2*ell*J*V-(J+ell*V)**2,'negative mixed moment bound')
    zero(2*E/ell-4*J*V*Q-2*Q*(J-ell*V)**2/ell,
         'the same clock pays the kinematic part of the quartic drift')
    t,H=s.symbols('t H',real=True)
    c=2/ell+2*ell*K
    factor=s.exp(c*(H-t))
    zero(s.diff(factor,t)+c*factor,'original-horizon clock pays transport and separated pressure')
    nu,qz,Fcore=s.symbols('nu qz Fcore',real=True)
    force=s.symbols('force',real=True)
    full=4*J*V*Q*(1+ell*ell*(Fcore-pfar))+4*nu*ell*ell*J*J*qz*qz*(J*J+3*ell*ell*V*V)
    core=4*ell*ell*J*V*Q*Fcore+4*nu*ell*ell*J*J*qz*qz*(J*J+3*ell*ell*V*V)
    zero(full-core-4*J*V*Q-far,'remaining signed acceleration cost retains all noise')
    zero(s.diff(E,V)*J*force-4*ell*ell*J*V*Q*force,'actual axial body-force derivative entry')
    diagonal=(J*J+V*V)**2
    eigen_drift=V*s.diff(diagonal,J)+J*s.diff(diagonal,V)
    zero((eigen_drift-3*diagonal-diagonal).subs({J:1,V:1}),
         'kinematic and far-pressure clock still leaves positive production in the actual calibration')
    return {'separated_bound':'K_R=6*||u0||_2^2/(pi*R^5), R>0 fixed',
            'quartic_contribution':'L_far(E)=-4*ell^2*J*V*Q*p_zz_far <= 2*ell*K_R*E',
            'paid_factor':'exp((2/ell+2*ell*K_R)*(H-t)), single initial factor exp((2/ell+2*ell*K_R)*H)',
            'retained_near':'F_near=-p_zz_near+nu*(Delta_3 partial_z u_z|axis+q_zz), with actual q_z noise',
            'signed_near_cost':'4*ell^2*J*V*Q*F_near+4*nu*ell^2*J^2*q_z^2*(J^2+3*ell^2*V^2)',
            'external_force_entry':'4*ell^2*J*V*Q*partial_z(f_z)_axis, using the actual pressure',
            'clock_test':'ell=1 and R^5=12*||u0||_2^2/pi give K_R=1/2, c=3; calibrated full clocked drift remains positive',
            'scope':'reuses the prior separated Newtonian pressure bound; full-horizon payment of this contribution only, no restart or core bound'}


def green_origin(polynomial):
    """Integral_0^infinity heat_h[P exp(-2|x|^2)](0) dh in R3.

The two radial dimensions and the one axial dimension have different
Gaussian moments. A rational antiderivative certificate checks each term
after x=sqrt(1+8h), independently of its factorial endpoint formula.
"""
    x=s.symbols('x',positive=True)
    value=0
    for (ir,jz),co in s.Poly(s.expand(polynomial),r,z).terms():
        require(ir%2==0 and jz%2==0,'even radial and axial source polynomial')
        i,j=ir//2,jz//2
        n=i+j
        prefactor=s.Integer(4)**i*s.factorial(i)*s.factorial2(2*j-1)*s.Integer(2)**j
        transformed=prefactor*(x*x-1)**n/(4*s.Integer(8)**n*x**(2*n+2))
        primitive=prefactor/(4*s.Integer(8)**n)*sum(
            s.binomial(n,k)*(-1)**(n-k)*x**(2*k-2*n-1)/s.Integer(2*k-2*n-1)
            for k in range(n+1))
        zero(s.diff(primitive,x)-transformed,'exact rational heat-resolvent primitive')
        # Every monomial in primitive has a strictly negative power of x.
        require(all(2*k-2*n-1<0 for k in range(n+1)),'primitive vanishes at infinity')
        endpoint=-primitive.subs(x,1)
        beta=s.Integer(2)**(i-1)*s.factorial(i)*s.factorial2(2*j-1)*s.factorial(n)*s.factorial(n+1)/s.factorial(2*n+2)
        zero(endpoint-beta,'independent factorial and endpoint pressure moments agree')
        value+=co*endpoint
    return s.factor(value)


def gaussian_pressure():
    A,B,C=s.symbols('A B C',real=True)
    nu=s.symbols('nu',positive=True)
    e=s.exp(-r*r-z*z)
    chi=z*(A/2+C*r**4)*e
    b=B*e
    v=velocity(chi)
    ur,uz=v[0],v[1]
    zero(div3(v),'actual physical incompressibility')
    G=s.Matrix([[s.diff(ur,r),-b,s.diff(ur,z)],
                [b+r*s.diff(b,r),ur/r,r*s.diff(b,z)],
                [s.diff(uz,r),0,s.diff(uz,z)]])
    Gpoly=G.applyfunc(lambda entry:s.cancel(entry/e))
    source_poly=s.expand(s.trace(Gpoly*Gpoly))
    source=source_poly*e**2
    convection=s.Matrix([v.dot(grad(ur))-r*b*b,v.dot(grad(uz))])
    zero(div3(convection)-source,'pressure source equals divergence of full vector convection')
    # -Delta_3 p = tr((grad u)^2), p=(-Delta_3)^-1 source.
    zz_poly=s.diff(source_poly,z,2)-8*z*s.diff(source_poly,z)+(16*z*z-4)*source_poly
    rr_poly=(s.diff(source_poly,r,2)+s.diff(source_poly,r)/r
             -8*r*s.diff(source_poly,r)+(16*r*r-8)*source_poly)/2
    pzz=green_origin(zz_poly)
    pxx=green_origin(rr_poly)
    expected=-s.Rational(9,14)*A*A-s.Rational(104,5005)*A*C+s.Rational(2,5)*B*B-s.Rational(1408,5005)*C*C
    zero(pzz-expected,'canonical whole-space pressure curvature with all parents retained')
    zero(2*pxx+pzz+source_poly.subs({r:0,z:0}),
         'independent pressure Hessian trace matches the actual Poisson equation')
    q=s.diff(uz,z)
    q_axis=s.simplify(q.subs(r,0))
    D=s.diff(q,r,2)+s.diff(q,r)/r+s.diff(q,z,2)
    zero(s.diff(uz,C).subs(r,0),'hidden parent leaves the complete initial axis velocity fixed')
    zero(s.diff(q_axis,C),'hidden parent leaves the complete initial axis strain fixed')
    zero(s.limit(s.diff(D,C),r,0),'hidden parent leaves the full initial axis diffusion fixed')
    F=s.simplify(-pzz+nu*(s.limit(D,r,0)+s.diff(q_axis,z,2)).subs(z,0))
    zero(F-(-expected-20*nu*A),'actual acceleration forcing at the origin')
    # Direct Gaussian energy integral, divided by pi^(3/2).
    energy_poly=s.Poly(s.expand(s.cancel((v.dot(v)+r*r*b*b)/e**2)),r,z)
    E=0
    for (ir,jz),co in energy_poly.terms():
        require(jz%2==0,'even physical energy polynomial')
        E+=2*s.pi*co*s.gamma(s.Rational(ir+2,2))/(2*s.Integer(2)**s.Rational(ir+2,2))*s.gamma(s.Rational(jz+1,2))/s.Integer(2)**s.Rational(jz+1,2)
    E=s.simplify(E/s.pi**s.Rational(3,2))
    zero(E-s.sqrt(2)*(7*A*A+18*A*C+16*B*B+162*C*C)/128,
         'full finite initial energy records the hidden parents')
    calibration={A:1,B:1,C:2,nu:s.Rational(4101,200200)}
    require(calibration[nu]>0,'strictly positive physical viscosity')
    zero(q_axis.subs(calibration).subs(z,0)-1,'initial axial strain is one')
    zero(s.diff(q_axis,z).subs(calibration).subs(z,0),'initial stochastic velocity noise vanishes at origin')
    zero(F.subs(calibration)-1,'actual pressure realizes the expanding phase-space eigenvector')
    zero(pzz.subs(calibration)+s.Rational(14111,10010),'exact calibrated pressure curvature')
    fixed_axis=s.factor(F.subs({A:1,B:1,nu:calibration[nu]}))
    zero(fixed_axis-(1408*C*C+104*C-835)/5005,'hidden parents vary acceleration with fixed axis data')
    # A second simpler member refutes every diagonal metric scale at fixed small nu.
    simple={A:1,B:1,C:0,nu:s.Rational(1,1000)}
    zero(F.subs(simple)-s.Rational(39,175),'positive acceleration in the simpler Gaussian calibration')
    no_swirl={A:1,B:0,C:2,nu:s.Rational(1621,40040)}
    zero(F.subs(no_swirl)-1,'same metric obstruction in the source-free no-swirl class')
    return {'datum':'chi=z*(A/2+C*r^4)*exp(-r^2-z^2), b=B*exp(-r^2-z^2)',
            'velocity':'u_r=-r*chi_z, u_z=2*chi+r*chi_r, u_theta=r*b',
            'canonical_pzz_origin':str(pzz),'physical_F_origin':str(F),
            'initial_energy_over_pi_3_over_2':str(E),
            'fixed_axis':'U0(z)=A*z*exp(-z^2); q0(z)=A*(1-2*z^2)*exp(-z^2), independent of C',
            'fixed_axis_diffusion':'(Delta_3 partial_z u_z)_axis is independent of C',
            'calibration':{'A':1,'B':1,'C':2,'nu':'4101/200200','q':1,'q_z':0,'F':1,
                           'p_zz':'-14111/10010','metric_squared_drift':'4*metric_squared(1,1)>0'},
            'hidden_parent_F':str(fixed_axis),
            'no_swirl_calibration':{'A':1,'B':0,'C':2,'nu':'1621/40040','q':1,'q_z':0,'F':1},
            'scope':'actual unforced initial NS jets; local smooth evolution and short stopped expectation increase analytic; no indefinite renewal claimed'}


def scaling():
    # NS concentration preserves nu. J is dimensionless; V=J*q has degree two.
    q,F,qz,ell=map(s.Integer,(2,4,3,-2))
    zero(2*ell+2*q,'the metric is dimensionless when ell is a time scale')
    zero(2*ell+F,'one plus ell^2 F is dimensionless')
    zero(2*ell+2*qz-q,'the quadratic-variation rate has inverse-time degree')
    return {'J_degree':0,'V_degree':2,'F_degree':4,'ell_degree':-2,
            'scope':'one actual differential counterexample survives physical concentration with its viscosity unchanged'}


def generated_core():
    h=s.symbols('h',nonnegative=True)
    tau=s.symbols('tau',positive=True)
    b=s.exp(-r*r-z*z)
    heat=(1+8*h)**s.Rational(-5,2)*s.exp(-2*(r*r+z*z)/(1+8*h))
    zero(s.diff(heat,h)-lap5(heat),'actual five-dimensional heat resolvent for pure-swirl generation')
    zero(heat.subs(h,0)-b*b,'heat resolvent starts from the actual swirl square')
    # q_1=2*partial_zz*(-L5)^-1(b^2), evaluated on the axis.
    kernel=2*s.diff(heat,z,2).subs(r,0)
    transformed=kernel.subs(h,(1/tau-1)/8)/(8*tau*tau)
    integrand=tau**s.Rational(3,2)*(4*z*z*tau-1)*s.exp(-2*z*z*tau)
    zero(transformed-integrand,'exact source-generated axial strain kernel')
    negative=s.integrate(tau**s.Rational(3,2),(tau,0,s.Rational(1,4)))
    zero(negative-s.Rational(1,80),'upper bound for the negative interval')
    # On [1/2,1], tau^(3/2)>=1/4, 4tau-1>=1, exp(-2tau)>1/9.
    # The exponential bound uses the elementary e<3.
    positive=s.Rational(1,2)*s.Rational(1,4)*s.Rational(1,9)
    lower=positive-negative
    zero(lower-s.Rational(1,720),'strict source-generated expansion lower bound at z=1')
    angle=s.symbols('angle',real=True)
    # N5=|x|^(-3)/(8*pi^2); 2*partial_zz N5 has angular factor 2*(-3+15*cos^2).
    N5=1/(8*s.pi**2*(r*r+z*z)**s.Rational(3,2))
    zero(2*s.diff(N5,z,2)-(-3+15*z*z/(r*r+z*z))/(4*s.pi**2*(r*r+z*z)**s.Rational(5,2)),
         'literal five-dimensional Newtonian Hessian')
    zero((-3+15*angle**2)+3-15*angle**2,'five-dimensional angular lower endpoint')
    zero(12-(-3+15*angle**2)-15*(1-angle**2),'five-dimensional angular upper endpoint')
    # |q_paid_prime| <= 3*sqrt(pi)/(2^(5/2)*rho^5) <3/(2*rho^5), using pi<4.
    rho=s.Integer(5)
    paid_upper=s.Rational(3,2)/rho**5
    residual=lower-paid_upper
    require(residual>0,'positive generation remains after the already paid outside-source component')
    ell,delta,t,J,nu=s.symbols('ell delta t J nu',positive=True)
    qc,Uz=s.Function('qc')(t,z),s.Function('Uz')(t,z)
    L=lambda f:s.diff(f,t)+Uz*s.diff(f,z)+nu*s.diff(f,z,2)+J*qc*s.diff(f,J)
    def initial_jet(expr):
        sub={qc:0,Uz:0,J:1}
        for index,d in enumerate(sorted(expr.atoms(s.Derivative),key=str)):
            nt=d.variables.count(t)
            nz=d.variables.count(z)
            # Preserve all unspecified time/mixed derivatives as free values.
            sub[d]=0 if nt==0 else (delta if d.expr==qc and nt==1 and nz==0
                                    else s.Symbol('jet_'+str(index),real=True))
        return s.simplify(s.expand(expr).xreplace(sub))
    zero(initial_jet(L(J**4)),'zero initial residual deformation rate')
    zero(initial_jet(L(L(J**4)))-4*delta,
         'full time-dependent Ito generator gives positive second moment derivative')
    diagonal=(J*J+ell*ell*(J*qc)**2)**2
    zero(initial_jet(L(L(diagonal)))-4*delta-4*ell*ell*delta*delta,
         'diagonal residual metric retains the full weak Ito second derivative')
    return {'initial_datum':'chi0=0, b0=exp(-r^2-z^2), arbitrary nu>0',
            'full_generation':'q_prime(0,0,z)=integral_0^1 tau^(3/2)*(4*z^2*tau-1)*exp(-2*z^2*tau) d tau',
            'at_z_one_lower':str(lower),'cutoff_radius':str(rho),
            'cutoff':'zero for r<=5 and one for r>=10, between zero and one',
            'outside_generation_upper':str(paid_upper),'residual_generation_lower':str(residual),
            'moment_second_derivative':'d_tt E[J_core^4]|0=4*q_core_prime(0,0,1)>0',
            'scope':'exact resolvent/jet arithmetic; elementary integral bounds and stochastic short-time expansion analytic; finite source prefunding remains possible'}


if __name__=='__main__':
    print(json.dumps({'ito':ito_deformation(),'actual_pressure':gaussian_pressure(),
                      'far_pressure':far_pressure_payment(),'generated_core':generated_core(),
                      'scaling':scaling()},indent=2,default=str))
