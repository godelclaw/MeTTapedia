#!/usr/bin/env python3
"""Actual canonical pressure square in the joint memory observable.

The default exact checks retain every Fourier output and identify the
additional pressure production and square diffusion. Optional diagnostics
read a saved full velocity/memory Galerkin prefix, without evolving it
again. The added observable is stronger; its arbitrary-history estimate
remains open. The torus has period 2*pi and normalized volume.
"""

import argparse
import json
from fractions import Fraction
import numpy as np
import cellular_parent_history as cellular
import pressure_history_source as f
import pressure_memory_diffusion as pm
import reciprocal_parent_history as reciprocal


def matrix_laplacian(A):
    return [[f.lap(q) for q in row] for row in A]


def exact_check(epsilon, phase, nu):
    """Identify pressure production using the actual full initial NS RHS."""
    u = reciprocal.seed(epsilon, phase)
    N, p = reciprocal.nonlinear_source(u)
    P, B = f.hess(p), f.jac(u)
    G = f.matmul(B, pm.transpose(B))
    viscosity = f.QQ_I(nu)
    ut = [f.add(a, f.scale(viscosity, f.lap(v))) for a, v in zip(N, u)]
    Pt = pm.observe(pm.symmetric_product(u, ut))
    DP = pm.matrix_add(Pt, pm.matrix_adv(u, P),
                       pm.matrix_scale(-viscosity, matrix_laplacian(P)))
    pressure_work = pm.matrix_scale(-1, pm.observe(pm.symmetric_product(u, f.grad(p))))
    commutator = pm.pressure_commutator(u, f.tensor(u, u))
    viscous_source = pm.matrix_scale(-2*viscosity, pm.observe(G))
    formula = pm.matrix_add(pressure_work, commutator, viscous_source)
    for i in range(3):
        for j in range(3):
            f.equal(DP[i][j], formula[i][j], 'actual material pressure evolution')

    square = pm.pair(P, P)
    grad_square = {}
    for j in range(3):
        dP = pm.matrix_diff(P, j)
        grad_square = f.add(grad_square, pm.pair(dP, dP))
    f.equal(f.lap(square), f.add(f.scale(2, grad_square),
                                 f.scale(2, pm.pair(P, matrix_laplacian(P)))),
            'literal pressure-square Laplacian')
    r = pm.pair(B, B)
    pressure_cost, quartic_cost = pm.mean(square), pm.mean(f.mul(r, r))
    if pressure_cost > quartic_cost:
        raise ArithmeticError('canonical initial pressure quartic estimate')

    # The identity is pointwise and accepts arbitrary observers. Use the
    # physical observer increment here and a distinct pressure increment
    # so that cancellation is not hidden by initial zero memory.
    L = pm.matrix_diff(P, 0)
    PP = pm.matrix_diff(P, 1)
    difference = pm.matrix_add(L, pm.matrix_scale(-1, PP))
    slack = f.add(f.scale(Fraction(33, 5), pm.pair(L, L)),
                  f.scale(Fraction(33, 28), pm.pair(PP, PP)),
                  f.scale(-1, pm.pair(difference, difference)))
    gap = pm.matrix_add(pm.matrix_scale(28, L), pm.matrix_scale(5, PP))
    f.equal(slack, f.scale(Fraction(1, 140), pm.pair(gap, gap)),
            'pointwise memory-gradient absorption square')
    components = [2*pm.mean(pm.pair(P, q))
                  for q in (pressure_work, commutator, viscous_source)]
    reaction = 2*pm.mean(pm.pair(P, DP))
    if sum(components) != reaction:
        raise ArithmeticError('additional production must retain every component')
    return {'epsilon': str(epsilon), 'phase': phase, 'nu': str(nu),
            'pressure_square_mass': str(pressure_cost),
            'velocity_gradient_quartic_mass': str(quartic_cost),
            'additional_signed_production': str(reaction),
            'production_pressure_work': str(components[0]),
            'production_transport_commutator': str(components[1]),
            'production_viscous_source': str(components[2]),
            'additional_square_diffusion_mass': str(2*viscosity*pm.mean(grad_square)),
            'scope': 'full exact initial Fourier vector field; no time-history bound'}


def diagnose(flow, state, t, diagnostic_n):
    """Evaluate the augmented physical PDE on a padded Galerkin slice.

    This is not the derivative of the truncated evolution: Galerkin
    residuals are not included in the reported continuum-PDE expression.
    Positivity and independent quadrature remain necessary for interpreting
    numerical excess masses. The absorption theorem itself is pointwise.
    """
    flow, state = flow.padded(state, diagnostic_n)
    del flow.initial
    # Own the real output instead of retaining a complex FFT backing array
    # for every velocity, memory and pressure field in the diagnostic.
    flow.ifft = lambda a: reciprocal.Flow.ifft(a).copy()
    u, B, C, gc = flow.fields(state)
    tensor = np.einsum('...i,...j->...ij', u, u)
    P, p = flow.observe(tensor)
    PC, _ = flow.observe(C)
    Ph = P+PC
    dot = cellular.matdot
    square = dot(P, P)
    Psi = cellular.Prefix.observable(B, Ph)
    Phi = Psi+square
    threshold = flow.threshold+flow.pbound**2
    H = C+np.eye(3)
    minimum_eigenvalue = float(np.min(np.linalg.eigvalsh(C)))
    if minimum_eigenvalue <= -1:
        raise ArithmeticError('capacity matrix loses positive definiteness')
    h = np.linalg.det(H)**(1/3)
    invH = np.linalg.inv(H)
    z = Phi/h
    active = z > threshold
    weight = np.where(active, 1-threshold**2/z**2, 0)
    curvature = np.where(active, 2*threshold**2/z**3, 0)
    capacity_weight = np.where(active, 2*threshold*(1-threshold/z), 0)
    F = np.where(active, (Phi-threshold*h)**2/Phi, 0)
    r = dot(B, B)
    G = B @ np.swapaxes(B, -1, -2)
    Qgeom = (2*flow.nu/3)*np.trace(invH @ G, axis1=-2, axis2=-1)
    observer_grad2 = np.zeros_like(r)
    pressure_grad2 = np.zeros_like(r)
    memory_grad2 = np.zeros_like(r)
    base_diffusion = np.zeros_like(r)
    selection_diffusion = np.zeros_like(r)
    receiver_gradient_cost = np.zeros_like(r)
    receiver_payment = np.zeros_like(r)
    receiver_divergence = np.zeros_like(u)
    # A low Fourier test probes the weak product rule across the active
    # boundary. The receiver is continuous; its derivative need not be.
    # Use a nonzero retained low moment of the actual receiver. An
    # arbitrarily chosen moment can vanish by symmetry and prove nothing.
    receiver00_hat = flow.fft(2*weight*P[..., 0, 0])/flow.n**3
    candidate = np.all(abs(flow.K) <= 4, axis=-1) & (flow.K[..., 0] > 0)
    strongest = np.unravel_index(np.argmax(np.where(candidate, abs(receiver00_hat), 0)),
                                receiver00_hat.shape)
    qtest = flow.K[strongest].copy()
    weak_phase = float(np.angle(receiver00_hat[strongest]))
    weak_amplitude = float(abs(receiver00_hat[strongest]))
    del receiver00_hat, candidate
    grid = np.arange(flow.n)*2*np.pi/flow.n
    test_phase = sum(qtest[j]*grid.reshape(tuple(flow.n if k == j else 1
                                               for k in range(3)))
                     for j in range(3))
    test_phase += weak_phase
    test_sin, test_cos = np.sin(test_phase), np.cos(test_phase)
    weak_moments, weak_scales, weak_left, weak_right = [], [], [], []
    for j in range(3):
        E, L = flow.derivative(B, j), flow.derivative(Ph, j)
        PP, CP = flow.derivative(P, j), flow.derivative(PC, j)
        dPsi, ddPsi = cellular.Prefix.observable(B, Ph, (E, L))
        Cj = flow.matrix(gc[j][..., 3:])
        Hj = invH @ Cj
        dh = h*np.trace(Hj, axis1=-2, axis2=-1)/3
        dz = (dPsi+2*dot(P, PP)-z*dh)/h
        observer_grad2 += dot(L, L)
        pressure_grad2 += dot(PP, PP)
        memory_grad2 += dot(CP, CP)
        base_diffusion += flow.nu*ddPsi
        Jj = flow.nu*h*curvature*dz*dz
        selection_diffusion += Jj
        Njet = (2*weight[..., None, None]*PP
                +2*(curvature*dz)[..., None, None]*P)
        jet_cost = flow.nu*dot(Njet, Njet)
        jet_payment = 8*flow.nu*weight*dot(PP, PP)+16*Jj
        if np.min((jet_payment-jet_cost)/np.maximum(1, jet_payment)) < -2e-12:
            raise ArithmeticError('actual receiver-gradient diffusion payment fails')
        receiver_gradient_cost += jet_cost
        receiver_payment += jet_payment
        receiver_divergence += Njet[..., :, j]
        for i in range(3):
            left = Njet[..., i, j]*test_sin
            right = 2*weight*P[..., i, j]*qtest[j]*test_cos
            weak_moments.append(float(np.mean(left+right)))
            weak_scales.append(float(np.mean(abs(left)+abs(right))))
            weak_left.append(float(np.mean(left)))
            weak_right.append(float(np.mean(right)))
        Qgeom += (flow.nu/3)*(np.trace(Hj @ Hj, axis1=-2, axis2=-1)
                                  -np.trace(Hj, axis1=-2, axis2=-1)**2/3)
    # Apply the full discrete orthogonal gradient projection to the
    # sampled literal divergence. There is no Galerkin mask in this test.
    divergence_hat = flow.fft(receiver_divergence)
    projected_hat = -flow.K*flow.inv[..., None]*np.sum(
        flow.K*divergence_hat, axis=-1)[..., None]
    projected_energy = float(np.sum(abs(projected_hat)**2)/flow.n**6)
    divergence_energy = float(np.mean(np.sum(receiver_divergence**2, axis=-1)))
    projection_slack = divergence_energy-projected_energy
    if projection_slack < -2e-12*max(1, divergence_energy):
        raise ArithmeticError('actual discrete pressure projection is not contractive')
    if 3*float(np.mean(receiver_gradient_cost))-flow.nu*divergence_energy < -2e-12:
        raise ArithmeticError('receiver divergence Cauchy--Schwarz estimate fails')
    weak_relative = max((abs(a)/b if b > 1e-14 else abs(a))
                        for a, b in zip(weak_moments, weak_scales))
    del divergence_hat, projected_hat, receiver_divergence, Njet, Jj
    del jet_cost, jet_payment, left, right, test_phase, test_sin, test_cos
    new_diffusion = base_diffusion+2*flow.nu*pressure_grad2
    pressure_lower = flow.nu*((56/5)*observer_grad2+2*pressure_grad2)
    local_slack = (33/56)*pressure_lower-flow.nu*memory_grad2
    relative_slack = float(np.min(local_slack/np.maximum(1, pressure_lower)))
    if relative_slack < -2e-12:
        raise ArithmeticError('pointwise memory-gradient absorption fails')
    if np.min(base_diffusion-flow.nu*(56/5)*observer_grad2) < -2e-9*max(1, np.max(base_diffusion)):
        raise ArithmeticError('completed observer Hessian lower bound fails')
    del gc, H, invH, E, L, PP, CP, Cj, Hj, dh, dPsi, ddPsi, dz

    gp = np.stack([flow.derivative(p, j) for j in range(3)], axis=-1)
    sym = np.einsum('...i,...j->...ij', u, gp)+np.einsum('...i,...j->...ij', gp, u)
    pressure_source = -flow.observe(sym)[0]
    stress = tensor+C
    advstress = sum(u[..., j, None, None]*flow.derivative(stress, j) for j in range(3))
    advPh = sum(u[..., j, None, None]*flow.derivative(Ph, j) for j in range(3))
    DPh = pressure_source+advPh-flow.observe(advstress)[0]
    base_production, _ = cellular.Prefix.observable(B, Ph, (-B @ B-P, DPh))
    del advstress, advPh, stress, DPh, Ph, sym, gp
    advtensor = sum(u[..., j, None, None]*flow.derivative(tensor, j) for j in range(3))
    advP = sum(u[..., j, None, None]*flow.derivative(P, j) for j in range(3))
    canonical_commutator = advP-flow.observe(advtensor)[0]
    viscous_source = -2*flow.nu*flow.observe(G)[0]
    extra_pressure = 2*dot(P, pressure_source)
    extra_transport = 2*dot(P, canonical_commutator)
    extra_viscous = 2*dot(P, viscous_source)
    extra_production = extra_pressure+extra_transport+extra_viscous
    production = base_production+extra_production
    signed = (weight*production-capacity_weight*h*Qgeom
              -weight*new_diffusion-selection_diffusion)
    mean = lambda q: float(np.mean(q))
    selected_D = mean(weight*new_diffusion)
    selected_lower = mean(weight*pressure_lower)
    memory_cost = mean(flow.nu*weight*memory_grad2)
    canonical_source = np.trace(P, axis1=-2, axis2=-1)+np.trace(B @ B, axis1=-2, axis2=-1)
    return {'time': t, 'diagnostic_n': diagnostic_n,
            'datum_fixed_augmented_threshold': threshold,
            'augmented_excess_mass': mean(F), 'active_fraction': mean(active),
            'maximum_augmented_ratio': float(np.max(z)),
            'minimum_memory_eigenvalue': minimum_eigenvalue,
            'pressure_square_mass': mean(square),
            'additional_signed_production': mean(extra_production),
            'additional_square_diffusion_mass': mean(2*flow.nu*pressure_grad2),
            'canonical_pressure_source_error_l2sq': mean(canonical_source**2),
            'pointwise_absorption_minimum_relative_slack': relative_slack,
            'selected_memory_gradient_cost': memory_cost,
            'selected_augmented_diffusion': selected_D,
            'selected_pressure_diffusion_lower': selected_lower,
            'selected_memory_vs_augmented_diffusion': memory_cost/selected_D if selected_D > 0 else None,
            'selected_memory_vs_pressure_diffusion_lower': memory_cost/selected_lower if selected_lower > 0 else None,
            'selected_extra_signed_production': mean(weight*extra_production),
            'selected_extra_pressure_work': mean(weight*extra_pressure),
            'selected_extra_transport_commutator': mean(weight*extra_transport),
            'selected_extra_viscous_source': mean(weight*extra_viscous),
            'selected_weight_gradient_diffusion': mean(selection_diffusion),
            'literal_receiver_gradient_cost': mean(receiver_gradient_cost),
            'literal_receiver_gradient_payment': mean(receiver_payment),
            'literal_receiver_gradient_payment_ratio':
                mean(receiver_gradient_cost)/mean(receiver_payment)
                if mean(receiver_payment) > 0 else None,
            'receiver_divergence_cost': flow.nu*divergence_energy,
            'receiver_pressure_projection_cost': flow.nu*projected_energy,
            'receiver_projection_unscaled_slack': projection_slack,
            'receiver_weak_test_mode': list(map(int, qtest)),
            'receiver_weak_test_phase': weak_phase,
            'receiver_weak_test_amplitude': weak_amplitude,
            'receiver_weak_test_derivative_moments': weak_left,
            'receiver_weak_test_undifferentiated_moments': weak_right,
            'receiver_weak_test_moments': weak_moments,
            'receiver_weak_test_relative_residual': weak_relative,
            'signed_augmented_excess_PDE_expression': mean(signed),
            'scope': 'padded full-PDE expression on saved Galerkin slice; '
                     'no continuum enclosure or arbitrary-history payment'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--state', help='saved reciprocal-parent velocity/memory state')
    parser.add_argument('--diagnostic-n', type=int, default=0)
    args = parser.parse_args()
    if args.state:
        with np.load(args.state, allow_pickle=False) as saved:
            n = int(saved['n'])
            epsilon = Fraction(str(saved['epsilon']))
            flow = reciprocal.Flow(n, float(saved['nu']), epsilon, int(saved['phase']))
            flow.threshold = float(saved['threshold'])
            diagnostic_n = args.diagnostic_n or 2*n
            if diagnostic_n < 2*n or diagnostic_n % 2:
                parser.error('even diagnostic grid at least twice the evolution grid required')
            result = diagnose(flow, saved['state'], float(saved['time']), diagnostic_n)
        print(json.dumps(result, indent=2))
        return
    checks = [exact_check(epsilon, phase, Fraction(1, 100))
              for epsilon in (Fraction(0), Fraction(1, 5)) for phase in (1, -1)]
    maximum_error = 0.
    for check in checks[2:]:
        flow = reciprocal.Flow(24, .01, Fraction(1, 5), check['phase'])
        sample = diagnose(flow, flow.initial, 0, 48)
        for name in ('pressure_square_mass', 'additional_signed_production',
                     'additional_square_diffusion_mass'):
            error = abs(sample[name]-float(Fraction(check[name])))
            maximum_error = max(maximum_error, error)
        if sample['active_fraction'] != 0:
            raise ArithmeticError('augmented threshold must majorize the full datum')
    if maximum_error > 2e-12:
        raise ArithmeticError('canonical pressure augmentation operator mismatch')
    print(json.dumps({'exact_checks': checks,
                      'initial_operator_maximum_error': maximum_error}, indent=2))


if __name__ == '__main__':
    main()
