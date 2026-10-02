#!/usr/bin/env python3
"""Exact NS reduction for arbitrarily many approximate cellular pattern cycles.

The symbolic checks verify the full unforced equation, pressure, physical
clock and comparison constants. The annular-coordinate construction and
parabolic comparison are analytic. The optional orbit calculation is a
numerical illustration, not a proof or a Navier--Stokes simulation.
"""

import argparse
import json
import sympy as s
from rotational_curl_reserve import require, zero


def exact_checks():
    x, y, z, t = s.symbols('x y z t', real=True)
    A, nu = s.symbols('A nu', positive=True)
    coords = (x, y, z)
    a = A*s.exp(-nu*t)
    psi = s.cos(x)+s.cos(y)
    v = s.Matrix([s.sin(y), -s.sin(x)])
    w = s.Function('w')(t, x, y)
    u = s.Matrix([a*v[0], a*v[1], A*w])
    pressure = -a*a*s.cos(x)*s.cos(y)
    lap = lambda f: sum(s.diff(f, c, 2) for c in coords)
    conv = u.jacobian(coords)*u
    rhs_defect = u.diff(t)+conv+s.Matrix([s.diff(pressure, c) for c in coords])-nu*u.applyfunc(lap)
    zero(sum(s.diff(u[i], coords[i]) for i in range(3)), 'physical incompressibility')
    zero(s.Matrix(rhs_defect[:2]), 'both full horizontal NS equations with canonical periodic pressure')
    passive = s.diff(w, t)+a*(v[0]*s.diff(w, x)+v[1]*s.diff(w, y))-nu*lap(w)
    zero(rhs_defect[2]-A*passive, 'vertical equation is literal passive advection and diffusion')
    zero(v.dot(s.Matrix([s.diff(psi, x), s.diff(psi, y)])), 'closed streamline level is conserved')
    zero(sum(s.diff(v[i], (x, y)[i]) for i in range(2)), 'cellular parent preserves area')
    gx, gy = s.diff(w, x), s.diff(w, y)
    gradient_square = gx*gx+gy*gy
    vertical_rate = nu*lap(w)-a*(v[0]*gx+v[1]*gy)
    gradient_rate = 2*gx*s.diff(vertical_rate, x)+2*gy*s.diff(vertical_rate, y)
    production = gradient_rate+a*(v[0]*s.diff(gradient_square, x)+v[1]*s.diff(gradient_square, y))-nu*lap(gradient_square)
    expected = -2*a*(s.cos(y)-s.cos(x))*gx*gy-2*nu*(s.diff(w,x,2)**2+2*s.diff(w,x,y)**2+s.diff(w,y,2)**2)
    zero(production-expected, 'complete passive-gradient equation including all diffusion')
    curl = s.Matrix([s.diff(u[2], y), -s.diff(u[2], x), s.diff(u[1], x)-s.diff(u[0], y)])
    zero(curl-s.Matrix([A*gy, -A*gx, -a*(s.cos(x)+s.cos(y))]), 'literal physical vorticity')

    sigma = A*(1-s.exp(-nu*t))/nu
    zero(s.diff(sigma, t)-a, 'parent advection clock')
    zero(A-nu*sigma-a, 'positive decaying parent amplitude on the physical clock')
    tau = s.symbols('tau', nonnegative=True)
    physical_time = -s.log(1-nu*tau/A)/nu
    zero(s.diff(physical_time, tau)-1/(A-nu*tau), 'inverse clock derivative before tau=A/nu')
    zero(s.diff(s.log(A/(A-nu*tau)), tau)-nu/(A-nu*tau), 'exact integrated diffusion on the clock')

    # Flow derivatives: ||Dv||op<=1 and ||D2v||bilinear<=1 for this v.
    # The second variation bound K solves K'=K+exp(2 tau), K(0)=0.
    K = s.exp(tau)*(s.exp(tau)-1)
    zero(s.diff(K, tau)-K-s.exp(2*tau), 'complete second flow variation bound')
    zero(K.subs(tau, 0), 'second flow variation starts at zero')
    theta, alpha = s.symbols('theta alpha', real=True)
    zero(s.trigsimp(s.cos(theta-alpha)-s.cos(theta)-2*s.sin(alpha/2)*s.sin(theta-alpha/2)),
         'separation of the phase states on the central orbit')
    return {
        'domain': '(R/(2pi Z))^3; fixed nu>0; smooth mean-zero velocity and periodic pressure',
        'velocity': 'u=(A exp(-nu t) sin y, -A exp(-nu t) sin x, A w(t,x,y))',
        'pressure': '-A^2 exp(-2nu t) cos x cos y',
        'vertical_equation': 'w_t+A exp(-nu t) v.grad w=nu Delta2 w',
        'clock': 'sigma=A(1-exp(-nu t))/nu; sigma< A/nu; t(sigma)=-log(1-nu sigma/A)/nu',
        'clock_equation': 'w_sigma+v.grad w=[nu/(A-nu sigma)]Delta2 w',
        'streamlines': 'psi=cos x+cos y; every level c in (0,2) around the central cell is closed and regular',
        'annular_seed': 'w0=chi((psi-1)/delta) cos(theta), with v.grad theta=omega(psi)=2pi/P(psi)',
        'periodic_movie': 'Ustar(sigma)=(v,chi((psi-1)/delta) cos(theta-omega(1)sigma))',
        'heat_error': '||w-w_inviscid||infinity<=M_S log(A/(A-nu S))<=2nu S M_S/A if A>=2nu S',
        'M_S': '2(||D2 w0||infinity+||grad w0||infinity) exp(2S) bounds ||Delta(w0 composed with Phi_-sigma)||infinity',
        'full_pattern_error': 'sup_(0<=sigma<=S)||u(t(sigma))/A-Ustar(sigma)||infinity <=sqrt(2)nu S/A+L_omega delta S+2nu S M_S/A',
        'construction': 'first choose S=N P(1), then delta so L_omega delta S<=epsilon/3, then finite A>=max(2nu S,3sqrt(2)nu S/epsilon,6nu S M_S/epsilon)',
        'two_states': 'sample sigma=j P(1)/2: A,B,A,...; ideal states have sup distance 2',
        'three_states': 'sample sigma=j P(1)/3: A,B,C,A,...; ideal pairwise sup distance sqrt(3)',
        'energy': 'with normalized torus volume, E0=(A^2/2)(1+mean(w0^2))<=A^2',
        'gradient_bound': '||grad w(t)||infinity<=||grad w0||infinity exp(sigma(t))<=||grad w0||infinity exp(A/nu), by the analytic parabolic maximum principle',
        'finite_horizon_vorticity': 'integral_0^H ||curl u||infinity<=H A ||grad w0||infinity exp(A/nu)+2A/nu',
        'receiver_reserve': 'E(t)(exp(2a(t)/nu)-1), E=||grad(Aw)||2^2, pays integral_0^T 2|G| for every T, where G=-a integral (cos y-cos x)(Aw)_x(Aw)_y',
        'original_receiver_payment': 'integral_0^T 2|G|<=E(0)(exp(2A/nu)-1); no segment restart',
        'scope': 'any prescribed finite number of approximate whole-pattern cycles; datum varies with count and accuracy; no exact nonconstant recurrence or mutual parent amplification',
        'status': 'algebra checked; global passive evolution, smooth annular coordinates and comparison theorem analytic'
    }


def orbit_illustration():
    import numpy as np
    from scipy.integrate import quad, solve_ivp

    # Removing the square-root endpoint singularity from the quarter period.
    def integrand(h):
        if h == 0:
            return np.sqrt(2.0)
        c = np.sin(h*h)
        return 2*h/np.sqrt(c*(2-c))

    quarter, quadrature_error = quad(integrand, 0, np.sqrt(np.pi/2), epsabs=1e-12, epsrel=1e-12)
    period = 4*quarter
    rhs = lambda _, p: np.array([np.sin(p[1]), -np.sin(p[0])])
    solution = solve_ivp(rhs, (0, 3*period), [np.pi/2, 0],
                         method='DOP853', rtol=2e-12, atol=2e-13, dense_output=True)
    require(solution.success, 'illustrative streamline integration completed')
    times = np.arange(10)*period/3
    points = solution.sol(times).T
    invariant_error = np.max(np.abs(np.cos(points[:, 0])+np.cos(points[:, 1])-1))
    return_error = np.max(np.linalg.norm(points[::3]-points[0], axis=1))
    require(invariant_error < 1e-9 and return_error < 1e-9, 'numerical orbit agrees with its invariant and returns')
    return {'status': 'numerical illustration only; no certified error intervals or fluid simulation',
            'period': float(period), 'quadrature_error_estimate': float(4*quadrature_error),
            'three_ports': points[:3].tolist(), 'nine_transitions': points.tolist(),
            'level_error': float(invariant_error), 'return_error': float(return_error)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orbit', action='store_true', help='also calculate the illustrative closed orbit')
    args = parser.parse_args()
    result = {'exact': exact_checks()}
    if args.orbit:
        result['orbit'] = orbit_illustration()
    print(json.dumps(result, indent=2))
