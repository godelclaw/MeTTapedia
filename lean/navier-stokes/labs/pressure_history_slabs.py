#!/usr/bin/env python3
"""Complete time-polynomial residuals for the retained pressure history.

All spatial outputs and every time coefficient of the shared reference
are retained. Polynomial norm bounds cover a whole time interval in exact
arithmetic. This implementation does NOT yet enclose floating arithmetic;
its output is validation feasibility data, not a continuum certificate.
"""

import argparse
import json
import time
from fractions import Fraction as Q
from math import comb

import numpy as np
from cellular_parent_history import PAIRS
from pressure_history_control import initial_controls, jets, propagate, sample
from pressure_history_residual import complete_operator, enlarge, fft, frequencies, ifft, require
from pressure_prefix_control import evaluate, hermite
from reciprocal_pressure_payment import make_flow


def centered(coefficients):
    """tau=(1+s)/2, so the new polynomial is evaluated for -1<=s<=1."""
    return [sum(comb(j, i)*coefficients[j]/2**j for j in range(i, len(coefficients)))
            for i in range(len(coefficients))]


def power_value(coefficients, x):
    result = np.zeros_like(coefficients[0])
    for a in reversed(coefficients):
        result = result*x+a
    return result


def full_polynomial(coefficients, h, nu):
    """Exact polynomial formulas; coefficient arrays use numerical FFTs.

    Each input coefficient has retained support |k_j|<n/3. The doubled
    grid retains every cubic output. Nothing is projected back to the
    original retained box after forming the physical operator.
    """
    require(len(coefficients) == 6 and h > 0 and nu > 0, 'Shared quintic and positive physical parameters')
    n = coefficients[0].shape[0]
    keep = np.all(abs(frequencies(n)) < n/3, axis=-1)
    require(all(a.shape == (n, n, n, 16) and np.all(a[~keep] == 0) for a in coefficients),
            'Exact retained support of every supplied time coefficient')
    K = frequencies(2*n)
    k2 = np.sum(K*K, axis=-1)
    inv = np.divide(1., k2, out=np.zeros_like(k2), where=k2 > 0)
    padded = [enlarge(a) for a in coefficients]
    # The real view returned by ifft otherwise retains its complex backing
    # array for the lifetime of every coefficient and derivative.
    physical = [ifft(a).copy() for a in padded]
    gradients = [[ifft(1j*K[..., j, None]*a).copy() for j in range(3)] for a in padded]
    advection, pressure = [], []
    for k in range(11):
        adv = np.zeros_like(physical[0])
        for i in range(6):
            j = k-i
            if 0 <= j < 6:
                adv += sum(physical[i][..., d, None]*gradients[j][d] for d in range(3))
        ah = fft(adv)
        gh = -K*inv[..., None]*np.sum(K*ah[..., :3], axis=-1)[..., None]
        pressure.append(gh)
        advection.append(ah)
    del gradients
    gp = [ifft(a).copy() for a in pressure]
    residual = []
    for k in range(16):
        # Residual = time derivative + diffusion - complete nonlinear RHS.
        value = np.zeros_like(padded[0])
        if k < 5:
            value += (2*(k+1)/h)*padded[k+1]
        if k < 6:
            value += nu*k2[..., None]*padded[k]
        if k < 11:
            value += advection[k]
            # This coefficient has no later consumer. Keep the complete
            # output, but release its quadratic temporary before proceeding.
            advection[k] = None
            value[..., :3] += pressure[k]
            value[..., 3:6] -= pressure[k]
        source = np.zeros_like(physical[0])
        for i in range(6):
            j = k-i
            if not 0 <= j < 11:
                continue
            g, fields = gp[j], physical[i]
            for index, (a, b) in enumerate(PAIRS):
                source[..., 6+index] += fields[..., 3+a]*g[..., b]+fields[..., 3+b]*g[..., a]
                source[..., 12+a] += 2*fields[..., 6+index]*g[..., b]
                if a != b:
                    source[..., 12+b] += 2*fields[..., 6+index]*g[..., a]
                else:
                    source[..., 12:15] += fields[..., 6+index, None]*g
            source[..., 15] += 4*np.sum(g*fields[..., 12:15], axis=-1)
        sh = fft(source)
        # Phi is an integrated scalar; only its zero Fourier mode is used.
        value[..., 6:15] -= sh[..., 6:15]
        value[..., 15] = 0
        if k < 5:
            value[0, 0, 0, 15] = (2*(k+1)/h)*padded[k+1][0, 0, 0, 15]
        value[0, 0, 0, 15] -= sh[0, 0, 0, 15]
        residual.append(value)
    return residual, pressure


def residual_norms(residual):
    m = residual[0].shape[0]
    K = frequencies(m)
    k2 = np.sum(K*K, axis=-1)
    weights = np.array([1 if i == j else 2 for i, j in PAIRS])
    def l2(a, weight=1):
        return float(np.sqrt(np.sum(abs(a)**2*weight)/m**6))
    records = [dict(epsilon0=l2(a[..., :3]), epsilon1=l2(a[..., :3], k2[..., None]),
                    rI=l2(a[..., 3:6]), rQ=l2(a[..., 6:12], weights),
                    rT=l2(a[..., 12:15]), rPhi=float(abs(a[0, 0, 0, 15])/m**3))
               for a in residual]
    return {key: sum(row[key] for row in records) for key in records[0]}, records


def squared_norm_polynomials(residual):
    """Retain every signed time correlation, accumulating by spatial plane.

    This changes the floating summation order, not the mathematical Gram
    matrix. As elsewhere in this module, rounding is not enclosed here.
    """
    m = residual[0].shape[0]
    k2 = np.sum(frequencies(m)**2, axis=-1)
    weights = np.array([1 if i == j else 2 for i, j in PAIRS])
    groups = [('epsilon0', slice(0, 3), 1), ('epsilon1', slice(0, 3), k2[..., None]),
              ('rI', slice(3, 6), 1), ('rQ', slice(6, 12), weights),
              ('rT', slice(12, 15), 1)]
    result = {}
    for key, block, weight in groups:
        gram = np.zeros((len(residual), len(residual)))
        for plane in range(m):
            local_weight = weight[plane] if np.ndim(weight) >= 3 else weight
            matrix = np.stack([a[plane, ..., block].reshape(-1) for a in residual])
            weighted = np.stack([(a[plane, ..., block]*local_weight).reshape(-1) for a in residual])
            gram += (matrix.conj() @ weighted.T).real
        gram /= m**6
        result[key] = [sum(gram[i, k-i] for i in range(len(residual)) if 0 <= k-i < len(residual))
                       for k in range(2*len(residual)-1)]
    phi = [a[0, 0, 0, 15]/m**3 for a in residual]
    result['rPhi'] = [float(sum((phi[i].conjugate()*phi[k-i]).real
                               for i in range(len(phi)) if 0 <= k-i < len(phi)))
                      for k in range(2*len(phi)-1)]
    return result


def interval_norm_bounds(polynomials, subdivisions=8):
    """Bernstein bounds on norm SQUARES, preserving their signed cross terms.

    These formulas give complete-interval bounds in exact arithmetic.
    Extended precision reduces conversion loss here; it is not an enclosure.
    """
    require(subdivisions > 0, 'Positive number of time subintervals')
    result = {}
    for key, values in polynomials.items():
        require(all(np.isfinite(v) for v in values), 'Finite squared-norm coefficients')
        d = len(values)-1
        upper = np.longdouble(0)
        for cell in range(subdivisions):
            left = np.longdouble(-1)+np.longdouble(2*cell)/subdivisions
            width = np.longdouble(2)/subdivisions
            powers = [sum(np.longdouble(values[i])*comb(i, j)*left**(i-j)*width**j
                          for i in range(j, d+1)) for j in range(d+1)]
            bernstein = [sum(powers[j]*comb(k, j)/comb(d, j) for j in range(k+1))
                         for k in range(d+1)]
            require(all(np.isfinite(v) for v in bernstein), 'Finite interval conversion')
            upper = max(upper, max(bernstein))
        result[key] = float(np.sqrt(upper))
    return result


def reference_bounds(coefficients, pressure):
    n = coefficients[0].shape[0]
    K = frequencies(n)
    k2 = np.sum(K*K, axis=-1)
    sizes = [np.sqrt(np.sum(abs(a[..., :3])**2, axis=-1))/n**3 for a in coefficients]
    V0 = float(sum(q.sum() for q in sizes))
    first = [float(np.sum(np.sqrt(k2)*q)) for q in sizes]
    second = [float(np.sum(k2*q)) for q in sizes]
    H1 = float(sum(np.sqrt(np.sum(k2*q*q)) for q in sizes))
    Klarge = frequencies(2*n)
    gradients = np.stack([ifft(1j*Klarge[..., j, None]*enlarge(coefficients[0])[..., :3])
                          for j in range(3)], axis=-1)
    strain = (gradients+gradients.swapaxes(-1, -2))/2
    eig = np.linalg.eigvalsh(strain)
    margin = np.sqrt(3)*np.pi*second[0]/(4*n)+sum(first[1:])/2
    Sminus = min(sum(first)/2, float((-eig[..., 0]).max())+margin)
    Splus = min(sum(first)/2, float(eig[..., -1].max())+margin)
    gsizes = [np.sqrt(np.sum(abs(g)**2, axis=-1))/(2*n)**3 for g in pressure]
    kmag = np.sqrt(np.sum(Klarge*Klarge, axis=-1))
    return dict(S=Sminus, Splus=Splus, V0=V0, V1=sum(first), V2=sum(second), D=sum(second),
                reference_H1=H1, G0=float(sum(q.sum() for q in gsizes)),
                G1=float(sum(np.sum(kmag*q) for q in gsizes)),
                G2=float(sum(np.sqrt(np.sum(q*q)) for q in gsizes)))


def exact_checks():
    """Independent scalar time algebra and complete nonzero moment fixtures."""
    import sympy as s
    from pressure_history_residual import exact_fixture

    z = s.symbols('z')
    a = s.symbols('a:6')
    c = [sum(s.Rational(comb(j, i), 2**j)*a[j] for j in range(i, 6)) for i in range(6)]
    require(s.expand(sum(c[i]*z**i for i in range(6))
                     -sum(a[j]*((1+z)/2)**j for j in range(6))) == 0,
            'Exact centered representation of the entire quintic')
    # A deliberately nonphysical moment fixture exercises every tensor slot.
    # Its operator must still agree; physical realizability is a separate premise.
    flow = make_flow(12, .25, .75)
    base = flow.initial.copy()
    base[..., 3:6] = base[..., :3]/4
    for j, (p, q) in enumerate(PAIRS):
        base[..., 6+j] = base[..., (p+q) % 3]/8
        if p == q:
            base[0, 0, 0, 6+j] += 3*flow.n**3
    base[..., 12:15] = base[..., :3]/16
    base[0, 0, 0, 15] = 7*flow.n**3
    scales = [1., .125, -.0625, .03125, -.015625, .0078125]
    roots = np.array([1., 1j, -1., -1j])
    kx = frequencies(flow.n)[..., 0].astype(int)
    coeff = [v*base*roots[(j*kx) % 4][..., None] for j, v in enumerate(scales)]
    residual, pressure = full_polynomial(coeff, .5, .25)
    errors = []
    for z in [-1., -.375, 0., .625, 1.]:
        value = power_value(coeff, z)
        tangent = 4*power_value([(i+1)*coeff[i+1] for i in range(5)], z)
        large = enlarge(value)
        nl, gh = complete_operator(large)
        k2 = np.sum(frequencies(24)**2, axis=-1)
        expected = enlarge(tangent)+.25*k2[..., None]*large-nl
        observed = power_value(residual, z)
        error = float(np.max(abs(expected-observed))/max(1., np.max(abs(expected))))
        require(error < 2e-13, 'Complete time-polynomial residual reconstructs all operator slots')
        require(np.max(abs(power_value(pressure, z)-gh)) < 2e-13*max(1., np.max(abs(gh))),
                'Complete time-polynomial canonical pressure')
        errors.append(error)
    norms, _ = residual_norms(residual)
    polynomials = squared_norm_polynomials(residual)
    interval = interval_norm_bounds(polynomials)
    for z in np.linspace(-1, 1, 9):
        point, _ = residual_norms([power_value(residual, z)])
        require(all(point[k] <= norms[k]*(1+1e-13) for k in norms),
                'The sampled fixture is consistent with its complete polynomial norm bound')
        for key in point:
            square = sum(a*z**j for j, a in enumerate(polynomials[key]))
            require(abs(square-point[key]**2) <= 2e-12*max(1., point[key]**2),
                    'Independent evaluation reconstructs the squared residual norm')
            require(point[key] <= interval[key]*(1+1e-12),
                    'The complete interval bound includes every checked fixture value')
    # A globally regular actual NS shear exposes a three-node blind spot.
    t = s.symbols('t', real=True)
    r = t**2*(1-t)**2*(2*t-1)
    a = s.expand(sum((-1)**j*s.diff(r, t, j) for j in range(6)))
    require(s.expand(s.diff(a, t)+a-r) == 0, 'Complete residual of a quintic shear reference')
    require(a.subs(t, 0) == -386 and a.subs(t, 1) == -142, 'Reference shares the actual original shear')
    require(all(r.subs(t, q) == 0 for q in [0, s.Rational(1, 2), 1]),
            'All three sampled residuals vanish exactly')
    require(all(s.diff(r, t).subs(t, q) == 0 for q in [0, 1]),
            'Both endpoint first/second jets also match the heat equation')
    require(r.subs(t, s.Rational(1, 4)) == -s.Rational(9, 512),
            'The complete physical residual is nonzero between the samples')
    exp_upper = sum(Q(1, s.factorial(j)) for j in range(13))+Q(14, 13*s.factorial(13))
    require(exp_upper < Q(193, 71), 'The actual final amplitude -386/e differs from -142')
    x, y = s.symbols('x y', real=True)
    U = s.Matrix([s.sin(x)*s.cos(y), -s.cos(x)*s.sin(y)])
    p = (s.cos(2*x)+s.cos(2*y))/4
    require(s.simplify(s.diff(U[0], x)+s.diff(U[1], y)) == 0,
            'The second physical fixture is incompressible')
    defect = U.jacobian([x, y])*U+s.Matrix([s.diff(p, x), s.diff(p, y)])
    require(all(s.trigsimp(q) == 0 for q in defect), 'Nonzero canonical pressure cancels cellular transport')
    require(all(s.simplify(s.diff(q, x, 2)+s.diff(q, y, 2)+2*q) == 0 for q in U),
            'At viscosity one half the same amplitude equation is exact NS')
    return dict(status='Exact time change and independent full operator fixtures passed',
                reconstruction_relative_errors=errors, independent_operator=exact_fixture(),
                blind_spot=dict(actual_amplitude='-386 exp(-t)', reference_amplitude=str(a),
                                residual=str(s.expand(r)), sampled_residuals=[0, 0, 0],
                                interior_residual='-9/512 at time1/4',
                                cellular_velocity='a(t) (sin(x) cos(y), -cos(x) sin(y), 0)',
                                cellular_pressure='a(t)^2 (cos(2x)+cos(2y))/4',
                                cellular_viscosity='1/2'),
                scope='Algebra and numerical fixtures; floating arithmetic not enclosed')


def probes(n, nu, dt, h, times, controlled=False):
    require(n >= 12 and n % 2 == 0 and min(nu, dt, h) > 0, 'Positive physical grid and times')
    require(times and min(times) >= h and all(abs(round(t/h)*h-t) < 1e-12 for t in times),
            'Selected positive slab endpoints')
    steps, final = round(h/dt), round(max(times)/h)
    require(steps > 0 and abs(steps*dt-h) < 1e-12, 'Integral time steps per slab')
    flow = make_flow(n, nu, 1.)
    state, start = flow.initial.copy(), time.time()
    first, second = jets(flow, state)
    controls, maximum_phi = initial_controls(), 0.
    yield dict(n=n, nu=nu, dt=dt, h=h, times=times,
               scope='Complete time polynomial, floating coefficient arithmetic not enclosed')
    selected = {round(t/h) for t in times}
    require(not controlled or selected == set(range(1, final+1)),
            'Physical controls must cover every consecutive interval')
    for slab in range(1, final+1):
        initial, f0, j0 = state.copy(), first, second
        for _ in range(steps):
            state, _ = flow.step(state, dt)
        first, second = jets(flow, state)
        if slab not in selected:
            continue
        coeff = hermite(initial, state, f0, first, j0, second, h)
        c = centered(coeff)
        residual, pressure = full_polynomial(c, h, nu)
        bounds, coefficient_norms = residual_norms(residual)
        squared = squared_norm_polynomials(residual)
        del residual
        interval = interval_norm_bounds(squared)
        best = {k: min(bounds[k], interval[k]) for k in bounds}
        row = dict(**best, **reference_bounds(c, pressure))
        del pressure
        sampled = [sample(flow, *evaluate(coeff, t, h)) for t in [0., .5, 1.]] if not controlled else []
        samples = {k: max(v[k] for v in sampled) for k in sampled[0]} if sampled else {}
        off_grid = {key: float(np.sqrt(max(0., max(sum(a*z**i for i, a in enumerate(values))
                                                 for z in [-1/np.sqrt(5), 1/np.sqrt(5)]))))
                    for key, values in squared.items()}
        record = dict(time=slab*h, polynomial=row, samples=samples,
                   norm_ratios={k: best[k]/max(samples[k], 1e-300) for k in bounds} if sampled else {},
                   power_sum_bounds=bounds, bernstein_bounds=interval,
                   interior_probe_norms=off_grid, norm_squared_coefficients=squared,
                   residual_coefficient_norms=coefficient_norms,
                   elapsed=time.time()-start)
        if controlled:
            try:
                controls = propagate(controls, row, h, nu)
            except (ArithmeticError, OverflowError) as ex:
                yield dict(time=slab*h, status='control failed', reason=str(ex),
                           row=row, previous=controls, elapsed=time.time()-start)
                return
            scalar = [float(a[0, 0, 0, 15].real/n**3) for a in coeff]
            phi_upper = max(sum(scalar[j]*comb(k, j)/comb(5, j) for j in range(k+1)) for k in range(6))
            upper = (max(0., phi_upper+controls['e4'])**.25+controls['impulse'])**4
            maximum_phi = max(maximum_phi, upper)
            final_H1 = float(np.sqrt(np.sum(flow.k2[..., None]*abs(state[..., :3])**2))/n**3)
            record.update(control=controls, conditional_phi_bound=upper,
                          reference_phi_slab_upper=phi_upper,
                          phi=float(state[0, 0, 0, 15].real/n**3),
                          final_reference_H1=final_H1, conditional_final_H1=final_H1+controls['Y'],
                          maximum_conditional_phi=maximum_phi)
        yield record
    yield dict(elapsed=time.time()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--probe', action='store_true')
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=40)
    parser.add_argument('--nu', type=float, default=.25)
    parser.add_argument('--dt', type=float, default=1/128)
    parser.add_argument('--h', type=float, default=1/16)
    parser.add_argument('--times', type=float, nargs='+', default=[1/16, 1., 2., 4.])
    parser.add_argument('--final', type=float, default=18.)
    args = parser.parse_args()
    require(not (args.probe and args.prefix), 'Choose selected probes or a complete prefix')
    if args.probe or args.prefix:
        if args.prefix:
            count = round(args.final/args.h)
            require(count > 0 and abs(count*args.h-args.final) < 1e-12, 'Integral prefix intervals')
            args.times = [j*args.h for j in range(1, count+1)]
        for row in probes(args.n, args.nu, args.dt, args.h, args.times, args.prefix):
            print(json.dumps(row), flush=True)
    else:
        print(json.dumps(exact_checks(), indent=2))
