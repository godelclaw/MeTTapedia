#!/usr/bin/env python3
"""Spatial diagnostics of the complete signed NS/memory generator.

Every polynomial initial PDE output is resolved on independent periodic
grids. The nonpolynomial observable is integrated by quadrature. This is
not a time evolution, continuum enclosure or nonlinear history bound.
The default b=40 tests the all-active spatial consumer. The optional
initialized case uses an analytic Fourier bound above the full initial
supremum, with zero initial soft excess.
"""

import json
import numpy as np
from signed_viscous_pressure import interacting_datum
from cellular_parent_history import Prefix
from joint_receiver_quadrature import dot, vecdot, mv, sm, outer, slots


class Grid:
    def __init__(self, n):
        self.n = n
        freq = np.fft.fftfreq(n)*n
        self.K = np.stack(np.meshgrid(freq, freq, freq, indexing='ij'), axis=-1)
        self.k2 = vecdot(self.K, self.K)
        self.inv = np.divide(1, self.k2, out=np.zeros_like(self.k2), where=self.k2 != 0)
        t = np.arange(n)*2*np.pi/n
        self.X = np.stack(np.meshgrid(t, t, t, indexing='ij'), axis=-1)

    def fft(self, v): return np.fft.fftn(v, axes=(0, 1, 2))
    def ifft(self, v): return np.fft.ifftn(v, axes=(0, 1, 2)).real

    def deriv(self, v, j):
        ext = (None,)*(v.ndim-3)
        return self.ifft(self.fft(v)*(1j*self.K[..., j])[(...,)+ext])

    def lap(self, v):
        ext = (None,)*(v.ndim-3)
        return self.ifft(self.fft(v)*(-self.k2)[(...,)+ext])

    def jac(self, u): return np.stack([self.deriv(u, j) for j in range(3)], axis=-1)

    def potential(self, T):
        return self.ifft(-np.einsum('...i,...j,...ij->...', self.K, self.K, self.fft(T))*self.inv)

    def observe(self, T): return self.jac(self.jac(self.potential(T)))

    def field(self, modes):
        result = np.zeros(self.k2.shape, dtype=complex)
        for k, a in modes.items():
            result += complex(float(a.x), float(a.y))*np.exp(1j*np.einsum('...i,i->...', self.X, k))
        if np.max(abs(result.imag)) > 2e-12:
            raise ArithmeticError('nonreal exact datum')
        return result.real


def datum_threshold(amplitude):
    """A fixed analytic Fourier bound, independent of the quadrature grid."""
    import pressure_history_source as f
    u = [f.scale(amplitude, q) for q in interacting_datum()]
    B = f.jac(u)
    P = f.hess(f.tensor_pressure(f.tensor(u, u)))

    def square_bound(M):
        return sum(sum(abs(a.x)+abs(a.y) for a in q.values())**2
                   for row in M for q in row)

    r, pressure_square = square_bound(B), square_bound(P)
    # sigma=1, and Phi_infinity=1+48sqrt(2)<100. The complete
    # branch upper bound is uniform in the positive vorticity regularizer.
    bound = 100+256*(r*r+r+2*pressure_square)
    return int(bound)+1


def check(n, amplitude, sign, nu=.1, b=40, initialized=False):
    g = Grid(n)
    u = np.stack([sign*amplitude*g.field(q) for q in interacting_datum()], axis=-1)
    B = g.jac(u)
    r = dot(B, B)
    p = g.potential(outer(u, u))
    P = g.jac(g.jac(p))
    s = -np.trace(P, axis1=-2, axis2=-1)
    if np.max(abs(s-np.trace(B@B, axis1=-2, axis2=-1))) > 1e-10*max(1, np.max(abs(s))):
        raise ArithmeticError('canonical pressure source mismatch')
    G = B@np.swapaxes(B, -1, -2)
    q = g.potential(G)
    qgrad = g.jac(q)
    PG = g.jac(qgrad)
    Ct = 2*nu*G
    Phi, _, _, _, _, _, _, _, _ = slots(B, P)
    if initialized:
        b = datum_threshold(amplitude)
        if np.max(Phi) >= b:
            raise ArithmeticError('datum-fixed above-initial threshold required')
    elif np.min(Phi) <= b:
        raise ArithmeticError('all-active consumer required')
    active = Phi > b
    a = np.where(active, 1-b*b/Phi**2, 0)
    beta = np.where(active, 2*b*(1-b/Phi), 0)
    DPhi = np.zeros(g.k2.shape)
    J = np.zeros_like(DPhi)
    parent = np.zeros_like(DPhi)
    crossed = np.zeros_like(DPhi)
    grad_a = []
    for j in range(3):
        E, L = g.deriv(B, j), g.deriv(P, j)
        dPsi, ddPsi = Prefix.observable(B, P, (E, L))
        dPhi = dPsi+2*dot(P, L)
        da = np.where(active, 2*b*b*dPhi/Phi**3, 0)
        grad_a.append(da)
        DPhi += nu*(ddPsi+2*dot(L, L))
        J += np.where(active, nu*2*b*b*dPhi*dPhi/Phi**3, 0)
        parent += r*dot(E, E)
        crossed += np.trace(E@E, axis1=-2, axis2=-1)
    grad_a = np.stack(grad_a, axis=-1)
    source_cost = nu*np.mean(vecdot(qgrad, qgrad))
    divG = sum(g.deriv(G, j)[..., :, j] for j in range(3))
    div_cost = nu*np.mean(vecdot(divG, divG))
    parent_cost = nu*np.mean(parent)
    selectedD = np.mean(a*DPhi)
    nativeD = np.mean(DPhi)
    Jmean = np.mean(J)
    native = selectedD+Jmean+8*nativeD
    flux_field = mv(P+sm(s, np.broadcast_to(np.eye(3), P.shape)), qgrad)
    flux = 4*nu*np.mean(vecdot(grad_a, flux_field))
    local = -4*nu*np.mean(a*s*crossed)
    selected = -4*nu*np.mean(a*dot(P, PG))
    unselected = -4*nu*np.mean(dot(P, PG))
    source = selected+8*unselected

    gp = g.jac(p)
    nl = -mv(B, u)-gp
    ut = nl+nu*g.lap(u)
    Pt = g.observe(outer(u, ut)+outer(ut, u))
    Ph_t = Pt+g.observe(Ct)
    dPsi_t, _ = Prefix.observable(B, P, (g.jac(ut), Ph_t))
    Phi_t = dPsi_t+2*dot(P, Pt)
    capacity = np.mean(beta*np.trace(Ct, axis1=-2, axis2=-1)/3)
    direct = np.mean((a+8)*Phi_t)-capacity
    stress = outer(u, u)
    advstress = sum(sm(u[..., j], g.deriv(stress, j)) for j in range(3))
    comm = sum(sm(u[..., j], g.deriv(P, j)) for j in range(3))-g.observe(advstress)
    pressure_reaction = comm-g.observe(outer(u, gp)+outer(gp, u))
    reactionPsi, _ = Prefix.observable(B, P, (-B@B-P, pressure_reaction))
    reaction = np.mean((a+8)*(reactionPsi+2*dot(P, pressure_reaction)))
    scale = max(1, abs(direct), abs(reaction), native)
    errors = {'signed_generator': abs(direct-reaction-source+capacity+native)/scale,
              'selected_flux': abs(selected-local-flux)/max(1, abs(selected), abs(local), abs(flux)),
              'source_poisson': float(np.max(abs(crossed+g.lap(q)))/max(1, np.max(abs(crossed))))}
    if max(errors.values()) > 2e-7:
        raise ArithmeticError(('complete signed identity mismatch', errors))
    tol = 2e-10*max(1, nativeD)
    if not source_cost <= div_cost+tol <= parent_cost+2*tol <= nativeD/8+3*tol:
        raise ArithmeticError('source/parent/unselected diffusion payment')
    if abs(local) > selectedD/2+tol or abs(flux) > Jmean/2+2*nativeD+tol:
        raise ArithmeticError('selected crossed-source/flux payment')
    if abs(source) > .75*native+tol or direct+.25*native > reaction-capacity+tol:
        raise ArithmeticError('augmented full generator payment')
    return {'grid': n, 'amplitude': amplitude, 'velocity_sign': sign, 'test_threshold': b,
            'initialized_above_initial_envelope': initialized,
            'initial_envelope_sample_max': float(np.max(Phi)),
            'source_gradient_cost': float(source_cost), 'source_divergence_cost': float(div_cost),
            'local_parent_cost': float(parent_cost), 'unselected_diffusion': float(nativeD),
            'selected_diffusion': float(selectedD), 'selector_diffusion': float(Jmean),
            'selected_canonical_viscous_work': float(selected),
            'local_selected_crossed_work': float(local), 'selector_boundary_work': float(flux),
            'unselected_canonical_viscous_work': float(unselected),
            'complete_signed_nonlinear_work': float(reaction), 'capacity_payment': float(capacity),
            'complete_initial_reserve_derivative': float(direct),
            'surviving_quarter_diffusion': float(native/4),
            'relative_identity_errors': errors}


def diagnose(initialized=False):
    cases = [check(n, 1, sign, initialized=initialized)
             for n in (96, 128) for sign in (-1, 1)]
    coarse = {(q['amplitude'], q['velocity_sign']): q for q in cases if q['grid'] == 96}
    comparisons = []
    if not (min(q['complete_signed_nonlinear_work'] for q in cases) < -1 and
            max(q['complete_signed_nonlinear_work'] for q in cases) > 1):
        raise ArithmeticError('nonzero opposite signed actual nonlinear work required')
    for q in cases:
        if q['grid'] != 128:
            continue
        old = coarse[(q['amplitude'], q['velocity_sign'])]
        changes = {name: abs(q[name]-old[name])/max(1, abs(q[name])) for name in
                   ('selected_diffusion', 'selector_diffusion', 'selector_boundary_work',
                    'complete_signed_nonlinear_work', 'complete_initial_reserve_derivative')}
        if max(changes.values()) > 2e-5:
            raise ArithmeticError(('independent quadrature mismatch', changes))
        comparisons.append({'amplitude': q['amplitude'], 'velocity_sign': q['velocity_sign'],
                            'relative_changes': changes})
    scope = ('datum-fixed above-initial threshold; actual initial generator, not a time history'
             if initialized else 'actual initial PDE generator; no initialized history or continuum enclosure')
    return {'cases': cases, 'independent_quadratures': comparisons, 'scope': scope}


if __name__ == '__main__':
    print(json.dumps(diagnose(), indent=2))
