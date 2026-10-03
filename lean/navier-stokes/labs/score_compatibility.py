#!/usr/bin/env python3
"""Joint entropy squares, admissible density gradients and actual score noise.

Stochastic identification, heat kernels, density integration and probability
bounds are analytic in README.md. The checks retain exact NS Fourier data;
linear Gaussian probes are explicitly outside the finite-energy fluid class.
"""

import json
import sympy as sp

import passive_parent_bellman as parent
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f, Q, r = parent.f, parent.Q, parent.r


def vec(prefix):
    return sp.Matrix(sp.symbols(prefix+'0:3', real=True))


def sq(x):
    return x.dot(x)


def combined_squares():
    nu, age = sp.symbols('nu age', positive=True)
    h, gamma, b, D, F = [vec(s) for s in ('h', 'g', 'b', 'D', 'F')]
    hstar = b+2*age*(nu*D-F)/nu
    old = -nu*sq(h-b)/4-sq(gamma-nu*h)/(4*nu)+age*gamma.dot(D)-age*h.dot(F)
    source = nu*age*age*sq(D)+age*age*sq(nu*D-F)/nu+age*b.dot(nu*D-F)
    new = source-nu*sq(h-hstar)/4-sq(gamma-nu*h-2*nu*age*D)/(4*nu)
    zero(old-new, 'joint receiver/relative-entropy squares count the control cost once')
    # Weighted Cauchy inequality for a solenoidal test is analytic, but
    # its completing-square identity is checked before discarding anything.
    e, a = vec('e'), vec('a')
    weight, lam = sp.symbols('weight lam', positive=True)
    zero(weight*sq(e-lam*a/weight)-weight*sq(e)+2*lam*e.dot(a)-lam*lam*sq(a)/weight,
         'weighted solenoidal test retains the complete square')
    return dict(joint_square=True, weighted_projection_square=True)


def shear_circulation():
    y, z, age, nu, alpha = sp.symbols('y z age nu alpha', positive=True)
    m = sp.Function('m')(y)
    ell = sp.Function('ell')(z)
    hy = 2*alpha*nu*age*sp.diff(m, y)*ell
    hz = -2*alpha*nu*age*m*sp.diff(ell, z)
    curl = sp.diff(hz, y)-sp.diff(hy, z)
    zero(curl+4*alpha*nu*age*sp.diff(m,y)*sp.diff(ell,z),
         'formal optimal relative score has nonzero curl')
    m0,m1,l0,l1 = sp.symbols('m0 m1 l0 l1', real=True)
    circulation = 2*alpha*nu*age*((m1-m0)*l0-m1*(l1-l0)-(m1-m0)*l1+m0*(l1-l0))
    zero(circulation+4*alpha*nu*age*(m1-m0)*(l1-l0),
         'entire rectangle circulation, including every edge')
    zero(circulation.subs({m1:0,l0:0})-4*alpha*nu*age*m0*l1,
         'actual shear rectangle gives strictly positive circulation')
    return dict(formal_optimum='h*=2 alpha nu r [ell dm-m dell]',
                circulation='-4 alpha nu r Delta(m) Delta(ell)',
                scope='actual shear m=n_z^2 and ell=(periodic heat score)^2; nonzero at every finite positive sampling age')


def linear_score_check():
    age, nu = sp.symbols('age nu', positive=True)
    s,c = sp.symbols('s c', real=True)
    drift = sp.Matrix([[0,c,0],[0,0,0],[0,0,0]])
    transition = sp.eye(3)+(age-s)*drift
    M = (sp.eye(3)-s*drift).T
    cov = sp.integrate(M*transition.T, (s,0,age))/age
    for i in range(3):
        for j in range(3):
            zero(cov[i,j]-int(i==j), ('terminal-score covariance',i,j))
    wrong = sp.integrate((sp.eye(3)-s*drift)*transition.T, (s,0,age))/age
    if all(sp.simplify(v)==0 for v in wrong-sp.eye(3)):
        raise ArithmeticError('non-normal Gaussian probe must detect the missing transpose')
    C = 2*nu*sp.integrate(transition*transition.T, (s,0,age))
    zero(C.det()-2*nu**3*age**3*(age**2*c*c+12)/3,
         'full Gaussian covariance, including cross-coordinate transfer')
    return dict(covariance_identity=True, omitted_transpose_detected=True,
                scope='linear Gaussian calibration with unbounded drift, not a finite-energy NS example')


def physical_deformation(u, label):
    jets, pressures = velocity_time_jets(u, Q(1), 1)
    B, omega = f.jac(u), f.curl(u)
    ox,oy,oz = omega
    cross = [[{},f.scale(-1,oz),oy],[oz,{},f.scale(-1,ox)],[f.scale(-1,oy),ox,{}]]
    for i in range(3):
        for j in range(3):
            f.equal(f.add(B[i][j],f.scale(-1,B[j][i])),cross[i][j],
                    (label,'vorticity is the skew deformation',i,j))
    Ht = parent.ph.vector_transport(u,u,Q(1))
    It = [f.add(v,f.scale(-1,w)) for v,w in zip(Ht,jets[1])]
    parent.ph.vectors_equal(It,f.grad(pressures[0]),(label,'original impulse starts from actual canonical pressure'))
    # At time zero H=u, I=0. The derivative retains the generated impulse.
    BHt, Bt, At = f.jac(Ht),f.jac(jets[1]),f.jac(It)
    omegadot = f.curl(jets[1])
    x,y,z = omegadot
    crossdot = [[{},f.scale(-1,z),y],[z,{},f.scale(-1,x)],[f.scale(-1,y),x,{}]]
    for i in range(3):
        for j in range(3):
            f.equal(f.add(BHt[i][j],f.scale(-1,Bt[j][i])),f.add(At[i][j],crossdot[i][j]),
                    (label,'pressure-gradient plus rotation after parent generation',i,j))
    return dict(fixture=label, pressure_modes=len(pressures[0]),
                identity='grad H-(grad u)^T=grad I+cross(omega), including its actual first time jet')


def score_payment_constants():
    a,b,c=sp.symbols('a b c', real=True)
    zero(3*(a*a+b*b+c*c)-(a+b+c)**2-((a-b)**2+(a-c)**2+(b-c)**2),
         'three score contributions keep every cross term in the bound')
    x=sp.symbols('x', real=True)
    moment1=sp.integrate(sp.exp(-x*x/4)/sp.sqrt(2*sp.pi),(x,-sp.oo,sp.oo))
    zero(moment1-sp.sqrt(2),'one Gaussian coordinate at the chosen exponent')
    zero(sp.log(moment1**3)/2-sp.Rational(3,4)*sp.log(2),
         'three-dimensional Brownian contribution after Cauchy--Schwarz')
    # eta=1/12, then theta=1/2: terminal coefficient=1/24.
    eta,theta=sp.Rational(1,12),sp.Rational(1,2)
    zero(3*eta-sp.Rational(1,4),'original passive maximum term')
    zero(theta*eta-sp.Rational(1,24),'terminal score coefficient')
    zero(theta*3*eta-sp.Rational(1,8),'paid parent term after control share')
    return dict(uncontrolled='log E exp[(nu r/12)(n.k)^2] <= M^2 r/(4nu)+(3/4)log2+(1/2)log E exp[(n_r.N_r)^2/(4r)]',
                controlled='E_gamma[(nu r/24)(n.k)^2]-(1/2)E_gamma action <= M^2 r/(8nu)+(3/8)log2+(1/4)log E exp[(n_r.N_r)^2/(4r)]',
                remaining_noise='N_r=integral_0^r s[grad I+cross(omega)] dW_s',
                scope='remaining exponential noise moment is not bounded from the datum here')


def entrance_constants():
    age, s, nu, alpha = sp.symbols('age s nu alpha', positive=True)
    zero(sp.integrate(s*s/age,(s,0,age))-age*age/3,
         'Ito isometry gives a vanishing scaled deformation remainder')
    n, z = vec('n'), vec('z')
    polynomial=sp.Poly((n.dot(z))**2,*z)
    gaussian_second_moment=0
    for powers, coefficient in polynomial.terms():
        if any(power % 2 for power in powers):
            continue
        gaussian_second_moment += coefficient
    zero(alpha*gaussian_second_moment/2-alpha*sq(n)/2,
         'three-dimensional Gaussian entrance retains the endpoint direction')
    # Planar NS has a horizontal impulse and vertical vorticity.
    entries=sp.symbols('a0:6',real=True)
    A=sp.Matrix([[entries[0],entries[1],0],[entries[2],entries[3],0],[0,0,0]])
    w=sp.symbols('w',real=True)
    Omega=sp.Matrix([[0,-w,0],[w,0,0],[0,0,0]])
    for value in sp.Matrix([[0,0,1]])*(A+Omega):
        zero(value,'planar terminal direction kills pressure/rotation score noise')
    return dict(entrance='lim J(r) = alpha |n(t,x)|^2/2 <= alpha/2',
                deformation_variance_factor='r^2/3',planar_noise_projection_zero=True,
                scope='actual entrance limit uses analytic conditional projection, Ito estimates and Girsanov; fixed bounded controls only')


def main():
    squares=combined_squares()
    circulation=shear_circulation()
    linear=linear_score_check()
    simple=parent.carrier(r.c.simple_parent(),Q(16),4,[{},{},{}])
    background=r.ns.vector_scale(Q(-20000),r.ns.nonlinear(r.c.resonant_parent()))
    resonant=parent.carrier(r.c.resonant_parent(),Q(200),4,background)
    cases=[(r.counterstrain_datum(Q(4),Q(8)),'pressure_start'),
           (r.record_datum(Q(4),Q(8)),'original_maximum'),
           (simple,'original_simple_carrier'),(resonant,'original_resonant_carrier')]
    fixtures=[physical_deformation(*case) for case in cases]
    payment=score_payment_constants()
    entrance=entrance_constants()
    print(json.dumps(dict(status='all exact checks passed',squares=squares,circulation=circulation,
                         linear_calibration=linear,fixtures=fixtures,payment=payment,entrance=entrance,
                         scope='stochastic identification, Hodge integration and PDE claims analytic; no Lean certification'),indent=2))


if __name__=='__main__':
    main()
