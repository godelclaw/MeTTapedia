#!/usr/bin/env python3
"""Exact identities for convex strain/swirl reaction-cancelling reserves.

The family classification and PDE consequences in README.md are analytic,
not Lean certificates. Pressure is obtained from actual smooth NS data.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

from axis_deformation_pressure import green_origin
from circulation_source_reserve import div3
from integrated_swirl_pressure import source_and_heat, exact_pressure_moment, full_diffusion
from joint_swirl_perspective import actual_pressure_test, joint_identity
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, velocity


def classification():
    x, y = s.symbols('x y', real=True)
    h = s.symbols('h', positive=True)
    g = s.Function('g')(y)
    phi = (x*x+y*y)/g
    zero(2*x*phi-(x*x+y*y)*s.diff(phi, x),
         'the complete normalized reaction vanishes')
    trial = s.Function('phi')(x, y)
    zero(s.diff(trial/(x*x+y*y), x)
         -((x*x+y*y)*s.diff(trial, x)-2*x*trial)/(x*x+y*y)**2,
         'reaction cancellation integrates to one function of the ratio')
    Hess = s.hessian(phi, (x, y))
    zero(Hess[0, 0]-2/g, 'first convexity minor')
    determinant = (4*(g-y*s.diff(g, y))**2/g**4
                   -2*(x*x+y*y)*s.diff(g, y, 2)/g**3)
    zero(Hess.det()-determinant, 'full convexity determinant')
    zero(s.diff(determinant, x, 2)+4*s.diff(g, y, 2)/g**3,
         'convexity for every strain forces concavity of g')

    m, b = s.symbols('m b', real=True)
    F = h*phi.subs({x:m/h, y:b/h}, simultaneous=True)
    variables = (m, b, h)
    zero(sum(v*s.diff(F, v) for v in variables)-F,
         'positive degree-one homogeneity')
    reaction = s.Matrix([m*m-b*b, 2*m*b, 2*m*h])
    zero(s.Matrix([s.diff(F, v) for v in variables]).dot(reaction),
         'unscaled quadratic reaction cancels exactly')
    pullback = s.Matrix([[1, 0, -m/h], [0, 1, -b/h]])
    expected = pullback.T*Hess.subs({x:m/h, y:b/h}, simultaneous=True)*pullback/h
    difference = s.hessian(F, variables)-expected
    for entry in difference:
        zero(entry, 'the perspective Hessian retains all density derivatives')
    return dict(
        domain='h>0, b/h in an open interval I containing 0; all real m',
        hypotheses='F is C2, convex, degree-one homogeneous, positive when (m,b)!=0, and exactly cancels (m^2-b^2,2mb,2mh)',
        family='F=(m^2+b^2)/(h*g(b/h)), g>0 and g concave on I',
        global_ratio_consequence='If I=R, positive concave g is constant; F is a positive multiple of the existing joint perspective.',
        determinant=str(determinant),
        scope='Symbolic identities support the analytic classification, including its separate continuity argument at b=0.')


def physical_diffusion():
    m, b, h = s.symbols('m b h', real=True)
    pressure, nu = s.symbols('P nu', real=True)
    dm, db, dh = s.symbols('dm db dh', real=True)
    y = s.symbols('y', real=True)
    g = s.Function('g')(y)
    ratio = b/h
    gy = lambda f: f.subs(y, ratio)
    H = h*gy(g)
    F = (m*m+b*b)/H
    variables = (m, b, h)
    direction = s.Matrix([dm, db, dh])
    reaction = s.Matrix([m*m-b*b+pressure, 2*m*b, 2*m*h])
    grad_state = lambda f: s.Matrix([s.diff(f, v) for v in variables])
    defect = lambda f: grad_state(f).dot(reaction)-nu*(direction.T*s.hessian(f, variables)*direction)[0]
    dy = (db-ratio*dh)/h
    zero(defect(ratio)-2*nu*dh*dy/h,
         'the physical ratio has the full density-gradient drift')
    zero(defect(H)-2*m*H+nu*h*gy(s.diff(g, y, 2))*dy**2,
         'concave reweighting creates an additional favorable density source')
    dH = grad_state(H).dot(direction)
    squares = (dm-m*dH/H)**2+(db-b*dH/H)**2
    expected = (2*m*pressure/H-2*nu*squares/H
                +nu*h*gy(s.diff(g, y, 2))*(m*m+b*b)*dy**2/H**2)
    zero(defect(F)-expected, 'complete physical parabolic law in every spatial direction')

    q, gradient_squared = s.symbols('q gradient_squared', positive=True)
    zero(s.Rational(3,4)*q**s.Rational(-1,2)*gradient_squared
         -s.Rational(4,3)*s.diff(q**s.Rational(3,4), q)**2*gradient_squared,
         'critical integrated diffusion retains the existing coefficient')
    bounded_g = 2-y*y
    zero(s.diff(bounded_g, y, 2)+2, 'a nonconstant concave bounded-ratio example')
    require(bounded_g.subs(y, s.Rational(1,2)) == s.Rational(7,4),
            'fixed ratio range gives explicit comparable stocks')
    return dict(
        density='H=h*g(y), y=b/h; (D-nu L5)H=2mH-nu*h*g_second(y)*|grad y|^2',
        full_law='(D-nu L5)F=2mP/H-(2nu/H)(|grad m-m grad log H|^2+|grad b-b grad log H|^2)+nu*h*g_second(y)*(m^2+b^2)*|grad y|^2/H^2',
        pressure='2mP/H retains its sign for every admissible g',
        conditional_consumer='R_g=int_R3 F^(3/2); retain full diffusion and the physical axis loss. The same all-prefix signed-pressure allowance gives the JP9 swirl L5 estimate with G replaced by g_max*G.',
        bounded_example='g=2-y^2 on (-1,1), |b/h|<=1/2: Q/2<=F<=4Q/7; the extra diffusion term is nonpositive.',
        limitation='H has additional production, so its mass is not the conserved mass of h.')


def pressure_obstruction():
    previous = actual_pressure_test()
    kappa, g_value = s.symbols('kappa g_value', positive=True)
    P0 = s.Rational(296,715)
    work = 2*P0/(kappa*g_value)
    zero(work-s.Rational(592,715)/(kappa*g_value),
         'the actual pressure fixture defeats the entire convex family')
    e = s.exp(-r*r-z*z)
    chi = z*(1+3*r**4)*e
    ur, uz = velocity(chi)
    m, b, h = -ur/r, e, kappa*(1+r*r+z*z)**-3
    for f in (m, b, h):
        for coordinate in (r, z):
            zero(s.diff(f, coordinate).subs({r:0,z:0}),
                 'every reweighted diffusion square vanishes at the pressure witness')
    a = s.symbols('a', nonnegative=True)
    ratio_profile = s.exp(-a)*(1+a)**3
    zero(s.diff(ratio_profile, a)-s.exp(-a)*(1+a)**2*(2-a),
         'the full physical ratio fits inside any interval containing zero')
    zero(ratio_profile.subs(a, 2)-27*s.exp(-2), 'exact initial ratio maximum')
    return dict(
        reused_canonical_pressure=previous['canonical_P_origin'],
        datum='chi=z(1+3r^4)exp(-R^2), b=exp(-R^2), h0=kappa(1+R^2)^-3',
        origin='m=b=1, h=kappa, all first gradients vanish; P=296/715',
        pressure_work=str(work),
        domain_control='0<b0/h0<=27/(exp(2)*kappa). Choose kappa once so this closed range lies in I; comparison of the common b,h equation retains it.',
        failed_assertion='A universal pointwise bound of 2mP/H by any finite multiple of the full chain-rule diffusion, for every smooth unforced datum.',
        not_refuted='An integrated allowance depending on the full original datum; nonlocal, history-dependent, nonhomogeneous or nonexactly-cancelling reserves.')


def nonconcave_diffusion():
    x, y = s.symbols('x y', real=True)
    phi = (x*x+y*y)/(1+y*y)
    Hess = s.hessian(phi, (x,y)).subs({x:2,y:0})
    require(Hess == s.diag(2,-6), 'positive but nonconcave g creates a negative Hessian direction')
    e = s.exp(-r*r-z*z)
    ur, uz = velocity(2*z*e)
    b = z*e
    m = -ur/r
    h = (1+r*r+z*z)**-3
    zero(div3(s.Matrix([ur,uz])), 'the diffusion fixture is an actual solenoidal datum')
    for f, value in ((m,2),(b,0),(h,1)):
        zero(f.subs({r:0,z:0})-value, 'specified state at the physical origin')
    for f in (m,h):
        for c in (r,z):
            zero(s.diff(f,c).subs({r:0,z:0}), 'no missing first derivative of strain or density')
    zero(s.diff(b,r).subs({r:0,z:0}), 'radial swirl derivative vanishes')
    zero(s.diff(b,z).subs({r:0,z:0})-1, 'the negative Hessian direction is physically realized')
    G = s.Matrix([[s.diff(ur,r),-b,s.diff(ur,z)],
                  [b+r*s.diff(b,r),ur/r,r*s.diff(b,z)],
                  [s.diff(uz,r),0,s.diff(uz,z)]])
    source = s.expand(s.trace(G.applyfunc(lambda f:s.cancel(f/e))**2))
    v = s.Matrix([ur,uz])
    convection = s.Matrix([v.dot(grad(ur))-r*b*b, v.dot(grad(uz))])
    zero(div3(convection)-source*e**2, 'the entire convection supplies the new pressure fixture')
    rr_poly = (s.diff(source,r,2)+s.diff(source,r)/r-8*r*s.diff(source,r)
               +(16*r*r-8)*source)/2
    P0 = s.factor(green_origin(rr_poly))
    zero(P0+s.Rational(34,5), 'exact canonical pressure for the nonconcave fixture')
    R, t = s.symbols('R t', real=True, positive=True)
    source_sphere = -source.subs({r:R*s.sqrt(1-t*t), z:R*t})
    harmonic2 = s.expand(s.Rational(5,2)*s.integrate(s.expand(source_sphere)*(3*t*t-1)/2, (t,-1,1)))
    independent = -source.subs({r:0,z:0})/3+s.integrate(harmonic2*s.exp(-2*R*R)/R, (R,0,s.oo))/5
    zero(P0-independent, 'full canonical pressure includes the Newtonian contact term')
    return dict(
        failed_choice='g(y)=1+y^2 on R; reaction cancellation survives, convexity does not',
        datum='chi=2z exp(-R^2), b=z exp(-R^2), h0=(1+R^2)^-3',
        hessian_at_x_two_y_zero=str(Hess),
        canonical_P_origin=str(P0),
        full_parabolic_defect=f'4P+6nu = {4*P0}+6nu at the origin',
        conclusion='Diffusion contributes positive 6nu on genuine smooth initial data. This statement isolates that contribution and does not assert positive total defect at every viscosity.')


def integrated_family_obstruction():
    m, b, h, eps = s.symbols('m b h eps', real=True)
    g = s.Function('g')
    normalized = (m*m+b*b)/(h*g(eps*b/h))
    base = (m*m+b*b)/(h*g(0))
    zero(normalized.subs(eps,0)-base, 'normalized density scaling approaches the old stock')
    variables = (m,b,h)
    for v in variables:
        zero(s.diff(normalized,v).subs(eps,0)-s.diff(base,v),
             'all normalized reaction and pressure coefficients have the same limit')
        for w in variables:
            zero(s.diff(normalized,v,w).subs(eps,0)-s.diff(base,v,w),
                 'all normalized diffusion coefficients have the same limit')
    _, heat, _ = source_and_heat()
    pressure = exact_pressure_moment(heat,5)
    diffusion = full_diffusion()
    return dict(
        reused_exact_pressure_W=pressure['W'],
        reused_exact_diffusion=diffusion['D_over_nu_pi_three_halves'],
        original_family=diffusion['physical_family'],
        rescaling='h_kappa=kappa*h_star; normalized F_kappa=(1/kappa)*Q_star/g(b/(kappa*h_star))',
        integrated_limit='kappa^(3/2)*R_g_kappa_prime(0) -> g(0)^(-3/2)*(W_star(0)-D_star(0)) > 0',
        quantifier='For every fixed admissible g and every nu>0, the actual datum u0=-A V with A>=100nu and sufficiently large original kappa gives increasing integrated stock on a short interval.',
        justification='The C2 coefficient limit is checked algebraically. Gaussian decay, pressure decay, dominated convergence and the local interval consequence are analytic.',
        limitation='Refutes automatic monotonicity for all permitted initial density normalizations. It does not exclude a specially selected datum-dependent normalization, a different g selected with it, or a positive full-datum allowance.')


if __name__ == '__main__':
    result = dict(physical_equations=joint_identity(),
                  classification=classification(), diffusion=physical_diffusion(),
                  pressure=pressure_obstruction(), nonconcave=nonconcave_diffusion(),
                  integrated=integrated_family_obstruction(),
                  status='Analytic classification and PDE statements with exact symbolic fixtures; arbitrary-history pressure payment remains open. No new Lean certificate.')
    names = [Path(__file__).name, 'joint_swirl_perspective.py',
             'axis_deformation_pressure.py', 'circulation_source_reserve.py',
             'rotational_curl_reserve.py', 'rotational_joint_enstrophy.py',
             'integrated_swirl_pressure.py']
    result['source_sha256'] = {name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                               for name in names}
    print(json.dumps(result, indent=2))
