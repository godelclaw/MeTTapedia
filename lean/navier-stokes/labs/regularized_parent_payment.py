#!/usr/bin/env python3
"""Exact identities and constants for a paid parent subtraction on actual flows.

The circulation weight has a positive floor. The original finite-mass
stochastic density is retained; its singular quotient is only notation
off the axis. PDE integration and continuation remain analytic.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

from rotational_joint_enstrophy import r, z, grad, lap5
from rotational_curl_reserve import require, zero
from integrated_swirl_pressure import gaussian_pair, integrated_absorption
from axis_deformation_pressure import green_origin


def complete_identity():
    n,b,h,f,uz,pressure = [s.Function(name)(r,z)
                          for name in ('n','b','h','f','uz','pressure')]
    nu,e = s.symbols('nu e',positive=True)
    m = n+f
    v = s.Matrix([-r*m,uz])
    floor = e/r**2
    zero(lap5(floor), 'the added quotient is harmonic off the axis only')
    zero(v.dot(grad(floor))-2*m*floor,
         'the constant physical circulation floor has the correct material rate')
    H = r*r*h+e
    Lminus = lambda a:s.diff(a,r,2)-s.diff(a,r)/r+s.diff(a,z,2)
    zero(r*r*(nu*lap5(h)+2*m*h)+2*r*v[0]*h-nu*Lminus(H),
         'the regular physical weight retains the circulation equation')

    residual = s.diff(pressure,r)/r
    source = f*f-v.dot(grad(f))+nu*lap5(f)
    nr = nu*lap5(n)+n*n-b*b+2*f*n+residual+source
    br = nu*lap5(b)+2*m*b
    hr = nu*lap5(h)+2*m*h
    Q = (n*n+b*b)/h
    rate = 2*n*nr/h+2*b*br/h-(n*n+b*b)*hr/h**2
    squares = sum((s.diff(n,c)-n*s.diff(h,c)/h)**2
                  +(s.diff(b,c)-b*s.diff(h,c)/h)**2 for c in (r,z))
    zero(rate-nu*lap5(Q)-2*f*Q-2*n*(residual+source)/h+2*nu*squares/h,
         'every subtraction reaction, transport and viscous term is retained')
    A,dA,F,Lf,advf,P = s.symbols('A dA F Lf advf P',real=True)
    zero((n+A*F)**2-b*b+P-dA*F-advf+nu*Lf
         -(n*n-b*b+2*A*F*n+(P-dA*F)+(A*F)**2-advf+nu*Lf),
         'actual pressure residual uses the actual energy-tensor anisotropy')
    return dict(weight='H_e=r^2 h+e, e<=H_e<=G+e; h_e=H_e/r^2 for r>0',
                source='S=f^2-v.grad f+nu L5 f',
                local_law='(D_t-nu L5)Q=2fQ+2n(P_res+S)/h_e-(2nu/h_e) relative_squares',
                warning='h_e is not a finite-mass R5 probability density; all axis limits use the regular physical weight H_e.')


def physical_observer():
    H,wr,wt = [s.Function(name)(r,z) for name in ('H','wr','wt')]
    he = H/r**2
    n,b = -wr/r,wt/r
    zero((n*n+b*b)/he-(wr*wr+wt*wt)/H,
         'the physical measurement has no singular division at the axis')
    for quotient,component,sign in ((n,wr,-1),(b,wt,1)):
        for c in (r,z):
            expected = sign/r*(s.diff(component,c)-component*s.diff(H,c)/H
                               +(component/r if c==r else 0))
            zero(s.diff(quotient,c)-quotient*s.diff(he,c)/he-expected,
                 'regular physical relative derivative retains the frame term')
    e,N,h0 = s.symbols('e N h0',positive=True)
    power = (r*r*N/(e+r*r*h0))**s.Rational(3,2)
    zero(s.limit(power,r,0), 'the physical axis stock vanishes')
    zero(s.limit(r*s.diff(power,r),r,0), 'no discarded inner radial boundary flux')
    # Removing the old inverse-density divergence is a physical bound, not
    # a claim that h itself has an original-data positive lower bound.
    q = s.symbols('q',positive=True)
    zero(s.Rational(3,4)/s.sqrt(q)-s.Rational(4,3)*s.diff(q**s.Rational(3,4),q)**2,
         'critical power diffusion has its full physical coefficient')
    height,norm = s.symbols('height norm',positive=True)
    pr,radial_velocity = s.symbols('pr radial_velocity',real=True)
    zero((norm/s.sqrt(height))/(height/r**2)*(pr/r)**2
         -norm*pr*pr/height**s.Rational(3,2),
         'the squared pressure cost is a regular physical-volume integral')
    zero((norm/s.sqrt(height))*(-radial_velocity/r)/(height/r**2)
         +r*norm*radial_velocity/height**s.Rational(3,2),
         'the pressure test weight vanishes cubically at the regular axis')
    # Reuse both exact completed squares from the full pressure calculation.
    # Here the physical axis weight is zero, so no pressure-axis subtraction
    # or additional signed seam term is needed.
    integrated_absorption()
    return dict(stock='R=int [(u_r+r f)^2+u_theta^2]^(3/2)/H_e^(3/2)',
                pressure_work='W_p=-3 int abs(w) w_r partial_r(p_res)/H_e^(3/2), w=(u_r+r f,u_theta)',
                coercivity='u_theta^2 <= (G+e) Q',
                pressure_estimate='W_p<=D/2+(3/nu)V_p, V_p=int abs(w)*p_res^2/H_e^(3/2)<=e^(-3/2)||w||_3||p_res||_3^2',
                axis='Q^(3/2)=O(r^3); physical axis loss is zero, with all volume diffusion retained',
                initial='R(0)<=e^(-3/2)||u0||_3^3 since A(0)=0')


def smooth_profile():
    ell = s.symbols('ell',positive=True)
    U = ell*ell+r*r+z*z
    N = 1/(4*s.pi*s.sqrt(U))
    q0 = s.diff(N,z,2)
    F = s.factor(s.diff(q0,r)/r)
    expected = 3*(ell*ell+r*r-4*z*z)/(4*s.pi*U**s.Rational(7,2))
    zero(F-expected, 'one globally smooth regularization of the actual far parent')
    radial = 15*r*(-ell*ell-r*r+6*z*z)/(4*s.pi*U**s.Rational(9,2))
    axial = 15*z*(-3*ell*ell-3*r*r+4*z*z)/(4*s.pi*U**s.Rational(9,2))
    viscous = 105*ell*ell*(-ell*ell-r*r+8*z*z)/(4*s.pi*U**s.Rational(11,2))
    zero(s.diff(F,r)-radial, 'complete radial profile derivative')
    zero(s.diff(F,z)-axial, 'complete axial profile derivative')
    zero(lap5(F)-viscous, 'smooth subtraction has a nonzero viscous defect')
    # Absolute numerator bounds follow from these nonnegative sums.
    for numerator,bound in ((ell*ell+r*r-4*z*z,4*U),
                            (-ell*ell-r*r+6*z*z,6*U),
                            (-3*ell*ell-3*r*r+4*z*z,4*U),
                            (-ell*ell-r*r+8*z*z,8*U)):
        for sign in (-1,1):
            coefficients=s.Poly(s.expand(bound+sign*numerator),ell,r,z)
            require(all(c>=0 for _,c in coefficients.terms()),
                    'profile numerator bound has nonnegative even coefficients')
            require(all(all(p%2==0 for p in powers) for powers,_ in coefficients.terms()),
                    'the polynomial bound applies for every axial coordinate')
    M = 3/(s.pi*ell**5)
    M1 = 45/(2*s.pi*ell**5)
    # The Cartesian spherical integral of r^3 has angular factor 3*pi^2/4.
    theta=s.symbols('theta',real=True)
    angular=s.integrate(2*s.pi*s.sin(theta)**4,(theta,0,s.pi))
    zero(angular-3*s.pi**2/4, 'physical cylindrical weight in both profile norms')
    # int_0^infty rho^5(ell^2+rho^2)^(-p) d rho
    # = ell^(6-2p)/[(p-1)(p-2)(p-3)] for p>3.
    radial_moment=lambda p:ell**(6-2*p)/((p-1)*(p-2)*(p-3))
    C0=s.simplify((3/s.pi)**6*angular*radial_moment(s.Integer(15)))
    C1=s.simplify((210*ell*ell/s.pi)**3*angular*radial_moment(s.Rational(27,2)))
    zero(C0-729/(2912*s.pi**4*ell**24), 'explicit bound for int r^3 abs(F)^6')
    zero(C1-105840/(23*s.pi*ell**15), 'explicit bound for int r^3 abs(L5 F)^3')
    x=s.symbols('x',positive=True)
    for p in (s.Integer(15),s.Rational(27,2)):
        primitive=(1+x)**(3-p)/(3-p)-2*(1+x)**(2-p)/(2-p)+(1+x)**(1-p)/(1-p)
        zero(s.diff(primitive,x)-x*x*(1+x)**(-p), 'exact radial norm primitive')
        zero(-primitive.subs(x,0)/2-1/((p-1)*(p-2)*(p-3)),
             'radial norm endpoints retain the change-of-variable factor')
    return dict(q0=str(s.factor(q0)),F0=str(F),L5F0=str(viscous),
                M_bound=str(M),radial_gradient_bound=str(M1),C0_bound=str(C0),C1_bound=str(C1),
                scope='This is an observer subtraction; its smoothed potential is not asserted to be a standalone incompressible NS solution.')


def complete_payment():
    x,y,k = s.symbols('x y k',positive=True)
    zero(2*k*x**3+y**3/k**2-3*x*x*y-(k*x-y)**2*(2*k*x+y)/k**2,
         'the complete source work has a positive cubic Young certificate')
    a,b,c = s.symbols('a b c',nonnegative=True)
    difference=9*(a**3+b**3+c**3)-(a+b+c)**3
    certificate=sum((v-w)**2*(4*v+4*w+u) for v,w,u in ((a,b,c),(b,c,a),(c,a,b)))
    zero(difference-certificate, 'all three source channels are paid together')
    t,H,E,nu,e,M,M1,C0,C1,CS = s.symbols('t H E nu e M M1 C0 C1 CS',positive=True)
    # Spatial interpolation and time Holder exponents for the complete actual velocity.
    zero(s.Rational(1,3)-(s.Rational(1,2)/2+s.Rational(1,2)/6),
         'L3 interpolation lies between physical L2 and L6')
    zero(s.Rational(3,4)+s.Rational(1,4)-1, 'energy dissipation pays the time integral')
    K=9/(k*k*e**s.Rational(3,2))*(C0*E**6*H**7/7
        +nu**3*C1*E**3*H**4/4
        +M1**3*CS**s.Rational(3,4)*E**s.Rational(9,2)*H**s.Rational(13,4)/(2*nu)**s.Rational(3,4))
    zero(s.integrate(t**6,(t,0,H))-H**7/7, 'complete squared-parent source history')
    zero(s.integrate(t**3,(t,0,H))-H**4/4, 'complete viscous-defect history')
    zero(E**3*H**3*E**s.Rational(3,4)*H**s.Rational(1,4)*(E/(2*nu))**s.Rational(3,4)
         -E**s.Rational(9,2)*H**s.Rational(13,4)/(2*nu)**s.Rational(3,4),
         'actual fluid advection is paid from the original energy and viscosity')
    clock=s.exp(-s.Rational(3,2)*M*E*t*t-2*k*t)
    zero(s.diff(clock,t)+(3*M*E*t+2*k)*clock, 'one clock pays the full known linear reaction')
    zero(clock.subs(t,0)-1, 'the clock uses the original start')
    return dict(source_allowance=str(K),
                source_bound='int_0^T k^(-2)e^(-3/2) int |rS|^3 <= K_source for every actual prefix T<=H',
                clock=str(clock),
                remaining='int_0^T clock*(W_p-D/2) <= K_pressure(original datum,nu,H,e,ell,k)',
                consumer='B=(R(0)+K_source+K_pressure)/clock(H); int |u_theta|^5 <= (3CS/(2nu))*(G+e)^(5/2)*B^(5/3)',
                limitation='All subtraction-induced source costs are paid. The complete residual pressure history and arbitrary-data regularity remain open.')


def isotropic_tensor_test():
    B=s.symbols('B',real=True)
    exponential=s.exp(-r*r-z*z)
    chi=z*exponential
    ur,uz=-r*s.diff(chi,z),2*chi+r*s.diff(chi,r)
    b=B*z*exponential
    zero(s.diff(ur,r)+ur/r+s.diff(uz,z), 'complete test datum is incompressible')
    normalized=lambda expr:s.simplify(gaussian_pair(s.cancel(expr/exponential**2),
                                      s.Integer(2),True)/s.pi**s.Rational(3,2))
    horizontal=normalized(ur*ur+r*r*b*b)/2
    axial=normalized(uz*uz)
    zero(horizontal-s.sqrt(2)*(B*B+3)/64, 'full horizontal energy retains the swirl')
    zero(axial-s.sqrt(2)/8, 'full axial energy')
    zero((axial-horizontal).subs(B,s.sqrt(5)), 'energy tensor is exactly isotropic at the initial time')
    gradient=s.Matrix([[s.diff(ur,r),-b,s.diff(ur,z)],
                       [b+r*s.diff(b,r),ur/r,r*s.diff(b,z)],
                       [s.diff(uz,r),0,s.diff(uz,z)]])
    polynomial=gradient.applyfunc(lambda x:s.cancel(x/exponential))
    source=s.expand(s.trace(polynomial*polynomial))
    radial_hessian=(s.diff(source,r,2)+s.diff(source,r)/r-8*r*s.diff(source,r)
                    +(16*r*r-8)*source)/2
    P=green_origin(radial_hessian)
    zero(P-2*(B*B-30)/35, 'canonical pressure retains every source component')
    zero(P.subs(B,s.sqrt(5))+s.Rational(10,7), 'pressure curvature survives isotropic total energy')
    # Reverse the entire velocity. Pressure and its energy tensor are unchanged.
    reversed_m=(ur/r).subs({r:0,z:0})
    zero(reversed_m+1, 'reversal changes the retained radial orientation')
    zero(reversed_m*P.subs(B,s.sqrt(5))-s.Rational(10,7),
         'residual pressure production is positive near but off the axis')
    return dict(datum='reverse the full chi=z exp(-rho^2), b=sqrt(5)z exp(-rho^2) datum',
                initial_tensor='Exx=Eyy=Ezz=pi^(3/2)*sqrt(2)/8; delta(0)=A(0)=0',
                axis_pressure='P(0)=-10/7, m(0)=-1, mP=10/7',
                scope='Actual local unforced solutions realize positive residual pressure work on a nearby off-axis region. This is not a sign claim for the whole stock derivative or an integrated-budget refutation.')


if __name__=='__main__':
    output=dict(identity=complete_identity(),observer=physical_observer(),
                profile=smooth_profile(),payment=complete_payment(),
                residual_test=isotropic_tensor_test())
    paths=[Path(__file__)]+[Path(__file__).with_name(name) for name in
            ('rotational_joint_enstrophy.py','rotational_curl_reserve.py',
             'integrated_swirl_pressure.py','axis_deformation_pressure.py',
             'circulation_source_reserve.py')]
    output['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    print(json.dumps(output,indent=2))
