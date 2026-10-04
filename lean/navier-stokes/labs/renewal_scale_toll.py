#!/usr/bin/env python3
"""Exact seed and scaling checks for actual multiscale no-swirl bursts.

Global no-swirl evolution, finite separated-profile stability and the
nodal circulation payment are analytic arguments in README.md.
"""

import hashlib
import json
from pathlib import Path

import sympy as s


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(value, label):
    require(s.simplify(value) == 0, label)


X = s.symbols('x y z', real=True)
x, y, z = X
P = s.Matrix([x*(1-2*z*z), y*(1-2*z*z), 2*z*(x*x+y*y-1)])


def derivative(poly, j):
    return s.expand(s.diff(poly, X[j])-2*X[j]*poly)


def curl(poly):
    return s.Matrix([derivative(poly[2], 1)-derivative(poly[1], 2),
                     derivative(poly[0], 2)-derivative(poly[2], 0),
                     derivative(poly[1], 0)-derivative(poly[0], 1)])


def gaussian_integral(poly, rate):
    result = s.Integer(0)
    for powers, coefficient in s.Poly(s.expand(poly), *X).terms():
        if any(n % 2 for n in powers):
            continue
        result += coefficient*s.prod(s.gamma(s.Rational(n+1, 2)) /
                                     rate**s.Rational(n+1, 2) for n in powers)
    return s.simplify(result)


def radial_fourier_integral(poly, order):
    result = s.Integer(0)
    for powers, coefficient in s.Poly(s.expand(poly), *X).terms():
        if any(n % 2 for n in powers):
            continue
        degree = sum(powers)
        angle = 2*s.prod(s.gamma(s.Rational(n+1, 2)) for n in powers) / s.gamma(s.Rational(degree+3, 2))
        exponent = s.Rational(degree+order+3, 2)
        radial = 2**(exponent-1)*s.gamma(exponent)
        result += coefficient*angle*radial
    return s.simplify(result)


def seed_checks():
    J = s.Matrix(3, 3, lambda i, j: derivative(P[i], j))
    omega = curl(P)
    lap = s.Matrix([sum(derivative(derivative(a, j), j) for j in range(3)) for a in P])
    zero(s.trace(J), 'Cartesian datum is divergence free')
    zero(x*P[1]-y*P[0], 'Cartesian datum has zero swirl')
    potential = s.Matrix([y*z, -x*z, 0])
    for a in curl(potential)-P:
        zero(a, 'Gaussian vector potential reconstructs the datum')
    resources = dict(E=gaussian_integral(P.dot(P), 2),
                     Z=gaussian_integral(omega.dot(omega), 2),
                     D=gaussian_integral(lap.dot(lap), 2),
                     g=gaussian_integral((omega.T*J*omega)[0], 3))
    expected = dict(E=7*s.sqrt(2)*s.pi**s.Rational(3, 2)/32,
                    Z=63*s.sqrt(2)*s.pi**s.Rational(3, 2)/32,
                    D=693*s.sqrt(2)*s.pi**s.Rational(3, 2)/32,
                    g=32*s.sqrt(3)*s.pi**s.Rational(3, 2)/243)
    for key in expected:
        zero(resources[key]-expected[key], ('Gaussian physical integral', key))
    grad_omega_squared = sum(derivative(a, j)**2 for a in omega for j in range(3))
    zero(gaussian_integral(grad_omega_squared, 2)-resources['D'],
         'full vorticity diffusion equals velocity Laplacian energy after integration')
    # Unitary Fourier transform of exp(-|x|^2) is 2^(-3/2) exp(-|k|^2/4).
    gaussian_hat = 2**s.Rational(-3, 2)*s.exp(-(x*x+y*y+z*z)/4)
    transformed = []
    for component in P:
        value = 0
        for powers, coefficient in s.Poly(component, *X).terms():
            term = gaussian_hat
            for coordinate, count in zip(X, powers):
                term = s.diff(term, coordinate, count)
            value += coefficient*s.I**sum(powers)*term
        transformed.append(s.simplify(value/gaussian_hat))
    target = s.I*z*s.Matrix([-x*z, -y*z, x*x+y*y])/4
    for actual, desired in zip(transformed, target):
        zero(actual-desired, 'complete Gaussian Fourier transform')
    spectral_density = z*z*(x*x+y*y)*(x*x+y*y+z*z)/128
    for key, order in [('E', 0), ('Z', 2), ('D', 4)]:
        zero(radial_fourier_integral(spectral_density, order)-resources[key],
             ('independent Fourier physical integral', key))
    critical = radial_fourier_integral(spectral_density, 1)
    zero(critical-8*s.pi/5, 'homogeneous H^(1/2) squared size')
    r, q = s.symbols('r q', nonnegative=True)
    azimuthal = 2*r*z*(2*r*r+2*z*z-7)*s.exp(-r*r-z*z)
    zero(omega[1].subs({x:r, y:0})*s.exp(-r*r-z*z)-azimuthal,
         'actual azimuthal vorticity, including orientation')
    zero(azimuthal.subs(z, 0), 'reflection plane is a vorticity node')
    zero(s.diff(azimuthal, z).subs(z, 0)-2*r*(2*r*r-7)*s.exp(-r*r),
         'nondegenerate nodal derivative')
    zero(azimuthal.subs({r:s.Rational(1, 2), z:s.Rational(1, 2)})+3*s.exp(-s.Rational(1, 2)),
         'nonzero vorticity observation off the node')
    circulation = (s.integrate(q*(7-2*q)*s.exp(-q), (q, 0, s.Rational(7, 2)))
                   +s.integrate(q*(2*q-7)*s.exp(-q), (q, s.Rational(7, 2), s.oo)))
    zero(circulation-3-22*s.exp(-s.Rational(7, 2)), 'scale-invariant no-swirl circulation stock')
    absolute_linear = (s.integrate((7-2*q)*s.exp(-q), (q, 0, s.Rational(7, 2)))
                       +s.integrate((2*q-7)*s.exp(-q), (q, s.Rational(7, 2), s.oo)))
    axis_loss = 4*absolute_linear
    plane_loss = 2*absolute_linear
    circular_loss = 196*s.exp(-s.Rational(7, 2))
    zero(axis_loss+plane_loss+circular_loss-10*circulation,
         'all initial axis and nodal diffusion losses give exactly ten times the circulation')
    for j in range(3):
        zero(lap[j]+12*P[j]+2*sum(X[k]*derivative(P[j],k) for k in range(3)),
             'independent Gaussian heat tangent for the complete velocity')
    nu = s.symbols('nu', positive=True)
    amplitude = 2*nu*resources['D']/resources['g']
    zero(amplitude**3*resources['g']-nu*amplitude**2*resources['D']-nu*amplitude**2*resources['D'],
         'positive physical enstrophy production at positive viscosity')
    return {**{k:str(v) for k,v in resources.items()}, 'critical_H_half_squared':str(critical),
            'circulation_L1_dr_dz':str(circulation), 'amplitude':str(s.simplify(amplitude)),
            'initial_circulation_derivative':'-10*nu*C(A U)',
            'Cartesian_polynomial':[str(a) for a in P], 'azimuthal_vorticity':str(azimuthal)}


def history_checks():
    t, nu, C = s.symbols('t nu C', positive=True)
    zero(s.Rational(27, 128)-2*t**3+2*t**4
         -(4*t-3)**2*(16*t*t+8*t+3)/128,
         'complete Young remainder for the classical cubic enstrophy-growth bound')
    kappa = 27*C**4/128
    E, Z = s.symbols('E Z', positive=True)
    zero(kappa/(2*nu**4)*(-2*nu*Z)+kappa/nu**3*Z,
         'one original energy reserve pays upward enstrophy variation weighted by its inverse square')
    a, ratio = s.symbols('a ratio', positive=True)
    energy_toll = 2*nu**4/kappa*(1/a-1/(ratio*a))
    time_toll = nu**3/(2*kappa)*(1/a**2-1/(ratio*a)**2)
    zero(energy_toll-2*nu**4*(ratio-1)/(kappa*ratio*a), 'fixed-factor energy toll')
    zero(time_toll-nu**3*(ratio**2-1)/(2*kappa*ratio**2*a*a), 'fixed-factor duration toll')
    # NS similarity: u_lambda=lambda*u(lambda^2 t,lambda*x), at the SAME nu.
    weights = {'E':-1, 'Z':1, 'D':3, 'g':3, 'time':-2, 'omega_infinity':2,
               'circulation_L1_dr_dz':0, 'critical_H_half_squared':0}
    require(weights['E']-weights['time'] == weights['Z'], 'scaled kinetic identity')
    require(weights['Z']-weights['time'] == weights['g'] == weights['D'], 'scaled enstrophy identity')
    require(weights['omega_infinity']+weights['time'] == 0, 'BKM cost is invariant')
    require(weights['D']+weights['time'] == 1, 'integrated viscous enstrophy cost grows with scale')
    # The scale-invariant circulation dissipation is a nodal-line observation.
    A, lam, b = s.symbols('A lam b', positive=True)
    nodal_rate = 2*nu*(A*lam**3/2)*(s.Rational(1, 4)/lam)
    duration = b/(2*lam**2)
    zero(nodal_rate*duration-nu*A*b/8, 'one retained nodal surface pays a scale-independent charge')
    zero(A*lam**2/2*duration-A*b/4, 'one actual observation has scale-independent BKM cost')
    e = s.symbols('e', positive=True)
    zero((b/lam**2)/(A*A*e/(2*lam))**2-4*b/(A**4*e**2),
         'unit-energy normalization retains a common prescribed time horizon')
    epsilon = s.symbols('epsilon', positive=True)
    r = s.symbols('r', positive=True)
    weight = 1/s.sqrt(r*r+epsilon*epsilon)
    radial_lap = s.diff(weight,r,2)+s.diff(weight,r)/r
    zero(radial_lap-(r*r-2*epsilon*epsilon)/(r*r+epsilon*epsilon)**s.Rational(5,2),
         'regularized axis weight diffusion retains the negative core term')
    eta = s.symbols('eta', positive=True)
    omega = s.Matrix(s.symbols('omega0:3', real=True))
    B = s.Matrix(3, 3, s.symbols('b0:9', real=True))
    grad2 = sum(v*v for v in B)
    longitudinal = sum(omega.dot(B[:,j])**2 for j in range(3))
    transverse = sum(omega.cross(B[:,j]).dot(omega.cross(B[:,j])) for j in range(3))
    zero((omega.dot(omega)+eta*eta)*grad2-longitudinal-eta*eta*grad2-transverse,
         'regularized vorticity diffusion retains the full nonnegative directional defect')
    return dict(kappa=str(kappa), energy_toll=str(s.factor(energy_toll)),
                duration_toll=str(s.factor(time_toll)), similarity_weights=weights,
                nodal_charge='nu*A*b/8 per tracked interval',
                general_defect='Fixed positive axis and norm regularizers retain strain, transport and the complete nonnegative vorticity-gradient defect.',
                scope='The inequalities, actual solution intervals, finite-profile approximation and Kato nodal loss remain analytic.')


if __name__ == '__main__':
    print(json.dumps(dict(seed=seed_checks(), history=history_checks(),
                         source_sha256={Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
                         limitation='Finite preloaded bursts in global no-swirl flows; no single infinite cascade, no arbitrary-data regularity theorem.'), indent=2))
