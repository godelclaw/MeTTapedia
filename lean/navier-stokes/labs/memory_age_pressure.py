#!/usr/bin/env python3
"""Retained-memory age splitting and its explicit pressure-cost remainder.

Default checks certify exact finite tensor algebra, constants and an actual
unforced shear's memory equation. Optional diagnostics continue a saved
reciprocal-parent Galerkin prefix while transporting its old memory without
new sources. They preserve the original datum threshold. The scalar
propagator and arbitrary-history recent-memory estimate are analytic/open,
respectively; the diagnostic is not a continuum enclosure.
"""

import argparse
import json
from fractions import Fraction
import numpy as np
import sympy as s
import cellular_parent_history as cellular
import reciprocal_parent_history as reciprocal
import pressure_history_source as f


def exact_checks():
    K, c, V = s.symbols('K c V', real=True)
    gap = (5*K*K+3*c*c-(3*K*K+4*K*c+c*c))*V
    if s.expand(gap-2*(K-c)**2*V) != 0:
        raise ArithmeticError('memory cost must retain every mixed weight')
    nu, eta, eps, E, Q, R = s.symbols('nu eta eps E Q R', positive=True)
    alpha = 60*K*K/(eps*nu*nu*eta)
    native = 240*K*K*Q/nu+3*R
    payment = alpha*E+native/(4*alpha*nu*eta)
    target = 60*K*K*E/(eps*nu*nu*eta)+eps*Q+eps*nu*R/(80*K*K)
    if s.factor(payment-target) != 0:
        raise ArithmeticError('age absorption coefficient')
    alpha_directional = 36*K*K/(eps*nu*nu*eta)
    directional = alpha_directional*E+(144*K*K*Q/nu+R)/(4*alpha_directional*nu*eta)
    directional_target = (36*K*K*E/(eps*nu*nu*eta)+eps*Q+eps*nu*R/(144*K*K))
    if s.factor(directional-directional_target) != 0:
        raise ArithmeticError('directional age payment coefficient')
    nash = 2**s.Rational(5, 3)/(6*s.pi**2)**s.Rational(2, 3)
    constant = (3*nash/2)**s.Rational(3, 2)
    if s.simplify(constant-s.sqrt(3)/s.pi**2) != 0:
        raise ArithmeticError('whole-space drift-independent kernel constant')

    # Distinct positive tensors with noncommuting eigenspaces. The trace
    # bounds are conservative; no simultaneous eigenframe is assumed.
    A = s.Matrix([[1, 2, 0], [0, 1, 1], [1, 0, 1]])
    B = s.Matrix([[2, -1, 1], [1, 0, 2], [0, 1, 1]])
    old, recent = A*A.T, B*B.T
    if old*recent == recent*old:
        raise ArithmeticError('matrix fixture must test noncommutation')
    tensor_checks = []
    for v in (s.Matrix([1, -2, 3]), s.Matrix([3, 0, -1]), s.Matrix([0, 1, 0])):
        capacity = s.eye(3)+old+recent
        vv = v.dot(v)
        weight = s.trace(capacity)*v.dot(capacity*v)
        L, cr = s.trace(old), s.trace(recent)
        fresh_directional = (1+L)*cr*vv+(3*(1+L)+cr)*v.dot(recent*v)
        sharper = 3*(1+L)**2*vv+fresh_directional
        bound = 5*(1+L)**2*vv+3*cr**2*vv
        if not weight <= sharper <= bound:
            raise ArithmeticError('full noncommuting matrix weight comparison')
        tensor_checks.append({'vector': list(map(str, v)), 'weighted_cost': str(weight),
                              'anisotropic_split_majorant': str(sharper),
                              'split_majorant': str(bound)})

    # A genuine periodic unforced shear has heat-decaying velocity and
    # explicitly generated positive memory. Its pressure is zero: this
    # is a memory-equation check, not an active pressure-cost counterexample.
    amp, lam, time, delta, y = s.symbols('A lambda t delta y', positive=True)
    a = nu*lam*lam
    total = amp**2/2*(1-s.exp(-2*a*time)
                      +(s.exp(-2*a*time)-s.exp(-4*a*time))*s.cos(2*lam*y))
    old_shear = amp**2/2*(1-s.exp(-2*a*(time-delta))
                         +(s.exp(-2*a*(time-delta))-s.exp(-4*a*(time-delta)))
                         *s.exp(-4*a*delta)*s.cos(2*lam*y))
    fresh = amp**2/2*(s.exp(-2*a*(time-delta))-s.exp(-2*a*time)
                     +s.exp(-2*a*time)*(1-s.exp(-2*a*delta))*s.cos(2*lam*y))
    source = 2*nu*amp**2*lam**2*s.exp(-2*a*time)*s.cos(lam*y)**2
    residual = s.diff(total, time)-nu*s.diff(total, y, 2)-source
    if s.simplify(s.trigsimp(residual)) != 0:
        raise ArithmeticError('actual positive-viscosity shear memory PDE')
    if s.simplify(total-old_shear-fresh) != 0:
        raise ArithmeticError('actual memory must retain old and new sources')

    # Exact reason a same-cutoff Fourier memory scheme need not preserve
    # positivity. This is an actual unforced heat shear at its initial
    # time, but its projected memory is an auxiliary approximation.
    cosines = [f.add({(0, k, 0): f.QQ_I(Fraction(1, 2))},
                     {(0, -k, 0): f.QQ_I(Fraction(1, 2))}) for k in (1, 2, 3)]
    gradient = f.add(*cosines)
    shear = {k: -f.II*z/k[1] for k, z in gradient.items()}
    f.equal(f.diff(shear, 1), gradient, 'literal gradient of the unforced shear')
    N, p = reciprocal.nonlinear_source([shear, {}, {}])
    f.equal(p, {}, 'actual shear pressure is zero')
    for component in N:
        f.equal(component, {}, 'actual shear nonlinear RHS is zero')
    exact_source = f.mul(gradient, gradient)
    projected = {k: z for k, z in exact_source.items() if abs(k[1]) <= 3}
    expected = f.add({(0, 0, 0): f.QQ_I(Fraction(3, 2))},
                     f.scale(2, cosines[0]), f.scale(Fraction(3, 2), cosines[1]),
                     cosines[2])
    f.equal(projected, expected, 'actual filtered gradient-square source')
    x = s.Rational(1, 10)
    projected_value = s.Rational(3, 2)+2*x+s.Rational(3, 2)*(2*x*x-1)+(4*x**3-3*x)
    true_value = (x+(2*x*x-1)+(4*x**3-3*x))**2
    if projected_value != -s.Rational(33, 500) or not true_value > 0:
        raise ArithmeticError('positive physical source and negative filtered source')
    return {'status': 'all exact checks passed',
            'whole_space_kernel_constant': str(s.sqrt(3)/s.pi**2),
            'matrix_cost_certificate': '2*(K-c)^2*|v|^2',
            'noncommuting_tensors': tensor_checks,
            'single_datum_allowance': '60*K^2*E0/(epsilon*nu^2*eta)',
            'recent_remainder': '(epsilon*nu/(80*K^2))*integral c_recent^2*|v|^2',
            'anisotropic_payment': {
                'single_datum_allowance': '36*K^2*E0/(epsilon*nu^2*eta)',
                'recent_cost': 'K*c_recent*|v|^2+(3K+c_recent)*v.C_recent*v',
                'remainder_coefficient': 'epsilon*nu/(144*K^2)'},
            'shear': {'velocity': '(A*exp(-nu*lambda^2*t)*sin(lambda*y),0,0)',
                      'memory': str(total), 'old_plus_recent': 'exact for t>=delta',
                      'pressure': 'zero; not a receiver-cost obstruction'},
            'filtering_obstruction': {
                'unforced_velocity': '(sum_(k=1)^3 exp(-nu*k^2*t)*sin(k*y)/k,0,0)',
                'initial_source_without_2nu': '(cos(y)+cos(2y)+cos(3y))^2',
                'memory_cutoff': '|k_y|<=3', 'at_cos_y': '1/10',
                'actual_source_value': str(true_value),
                'projected_source_value': str(projected_value),
                'scope': 'positivity fails for truncated auxiliary memory, not physical NS'},
            'scope': 'exact algebra and restricted actual memory; no full history bound'}


class AgeFlow(reciprocal.Flow):
    """Transport six old components alongside the full coupled state.

    The inherited RHS sources only components3--8. Components9--14 have
    advection and viscosity, with no fresh gradient source. Subtracting
    them from the full memory leaves the recent sourced tensor.
    """

    def start(self, state):
        return np.concatenate((state, state[..., 3:9]), axis=-1)


def diagnose(flow, state, time, age, diagnostic_n):
    flow, state = flow.padded(state, diagnostic_n)
    del flow.initial
    flow.ifft = lambda a: reciprocal.Flow.ifft(a).copy()
    physical = flow.ifft(state)
    old = flow.matrix(physical[..., 9:15])
    del physical
    u, B, C, gc = flow.fields(state)
    recent = C-old
    old_eigenvalues = np.linalg.eigvalsh(old)
    recent_eigenvalues = np.linalg.eigvalsh(recent)
    positivity = min(float(old_eigenvalues.min()), float(recent_eigenvalues.min()))
    positivity_tolerance = 1e-12*max(1, float(old_eigenvalues.max()),
                                   float(recent_eigenvalues.max()))
    if positivity < -positivity_tolerance:
        raise ArithmeticError('truncated memory invalidates physical positivity: '
                              f'old_min={old_eigenvalues.min():.9g}, '
                              f'recent_min={recent_eigenvalues.min():.9g}; '
                              'withhold the weighted estimate on this approximation')
    measured_L = float(old_eigenvalues.max())
    H = C+np.eye(3)
    h = np.linalg.det(H)**(1/3)
    invH = np.linalg.inv(H)
    P, _ = flow.observe(np.einsum('...i,...j->...ij', u, u))
    PC, _ = flow.observe(C)
    Ph = P+PC
    dot = cellular.matdot
    Psi = cellular.Prefix.observable(B, Ph)
    Phi = Psi+dot(P, P)
    z = Phi/h
    threshold = flow.threshold+flow.pbound**2
    active = z > threshold
    weight = np.where(active, 1-threshold**2/z**2, 0)
    curvature = np.where(active, 2*threshold**2/z**3, 0)
    divergence = np.zeros_like(u)
    pressure_diffusion = np.zeros_like(h)
    selection_diffusion = np.zeros_like(h)
    for j in range(3):
        dB, dPh = flow.derivative(B, j), flow.derivative(Ph, j)
        dP = flow.derivative(P, j)
        dPsi, _ = cellular.Prefix.observable(B, Ph, (dB, dPh))
        Cj = flow.matrix(gc[j][..., 3:9])
        dh = h*np.trace(invH @ Cj, axis1=-2, axis2=-1)/3
        dz = (dPsi+2*dot(P, dP)-z*dh)/h
        Njet = 2*weight[..., None, None]*dP+2*(curvature*dz)[..., None, None]*P
        divergence += Njet[..., :, j]
        pressure_diffusion += 2*flow.nu*weight*dot(dP, dP)
        selection_diffusion += flow.nu*h*curvature*dz*dz
    divhat = flow.fft(divergence)
    # Actual pressure sign: -Pi_grad(div N), with no Galerkin output mask.
    v = flow.ifft(-flow.K*flow.inv[..., None]*np.sum(flow.K*divhat, axis=-1)[..., None])
    vv = np.sum(v*v, axis=-1)
    cost = np.trace(H, axis1=-2, axis2=-1)*np.einsum('...i,...ij,...j->...', v, H, v)
    cr = np.trace(recent, axis1=-2, axis2=-1)
    remainder = cr*cr*vv
    majorant = 5*(1+measured_L)**2*vv+3*remainder
    if np.min((majorant-cost)/np.maximum(1, majorant)) < -2e-10:
        raise ArithmeticError('actual age-split tensor comparison')
    native_cost = float(np.mean(pressure_diffusion+selection_diffusion))
    receiver_cost = float(flow.nu*np.mean(vv))
    if receiver_cost > 48*native_cost+1e-10:
        raise ArithmeticError('actual native pressure projection payment')
    kernel = 54*max(1, (3/(flow.nu*age))**1.5)
    datum_L = flow.energy0*kernel
    if measured_L > datum_L:
        raise ArithmeticError('measured old memory exceeds conservative analytic age bound')
    traceC = np.trace(C, axis1=-2, axis2=-1)
    energy = np.sum(u*u, axis=-1)
    return {'time': time, 'age': age, 'diagnostic_n': diagnostic_n,
            'datum_fixed_threshold': threshold, 'active_fraction': float(active.mean()),
            'old_minimum_eigenvalue': float(old_eigenvalues.min()),
            'recent_minimum_eigenvalue': float(recent_eigenvalues.min()),
            'old_measured_maximum_eigenvalue': measured_L,
            'old_datum_fixed_analytic_bound': datum_L,
            'energy_memory_balance_error': float(np.mean(energy+traceC)-flow.energy0),
            'old_memory_mass': float(np.mean(np.trace(old, axis1=-2, axis2=-1))),
            'recent_memory_mass': float(np.mean(cr)),
            'receiver_projection_nu_cost': receiver_cost,
            'receiver_native_diffusion_cost': native_cost,
            'full_memory_weighted_pressure_cost': float(np.mean(cost)),
            'recent_squared_trace_pressure_remainder': float(np.mean(remainder)),
            'age_split_majorant_using_measured_old_bound': float(np.mean(majorant)),
            'tensor_comparison_minimum_relative_slack': float(np.min(
                (majorant-cost)/np.maximum(1, majorant))),
            'scope': 'continued Galerkin history and padded spatial diagnostic; '
                     'measured maxima are test values, not proposed a priori constants; '
                     'no continuum enclosure or arbitrary-history remainder bound'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--state', help='saved full reciprocal-parent velocity/memory prefix')
    parser.add_argument('--duration', type=float, default=.1)
    parser.add_argument('--dt', type=float, default=.005)
    parser.add_argument('--diagnostic-n', type=int, default=0)
    parser.add_argument('--output-state', help='optional saved age-decomposed final state')
    args = parser.parse_args()
    if not args.state:
        print(json.dumps(exact_checks(), indent=2))
        return
    if args.duration <= 0 or args.dt <= 0:
        parser.error('positive age and time step required')
    with np.load(args.state, allow_pickle=False) as saved:
        n, nu = int(saved['n']), float(saved['nu'])
        epsilon, phase = Fraction(str(saved['epsilon'])), int(saved['phase'])
        time = float(saved['time'])
        flow = AgeFlow(n, nu, epsilon, phase)
        flow.threshold = float(saved['threshold'])
        state = flow.start(saved['state'])
    steps = int(np.ceil(args.duration/args.dt))
    dt = args.duration/steps
    for j in range(steps):
        state, _ = flow.step(state, dt)
    diagnostic_n = args.diagnostic_n or 2*n
    if diagnostic_n < 2*n or diagnostic_n % 2:
        parser.error('even diagnostic grid at least twice the evolution grid required')
    if args.output_state:
        np.savez_compressed(args.output_state, state=state, n=n, nu=nu, epsilon=str(epsilon),
                            phase=phase, time=time+args.duration, age=args.duration,
                            dt=dt, threshold=flow.threshold)
    print(json.dumps(diagnose(flow, state, time+args.duration, args.duration,
                             diagnostic_n), indent=2))


if __name__ == '__main__':
    main()
