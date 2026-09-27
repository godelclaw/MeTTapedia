#!/usr/bin/env python3
"""Signed tail history for the real, unforced viscous Kida--Pelz flow.

On the 2*pi-periodic cube, u_x=sin(x)*(cos(3*y)*cos(z)-cos(y)*cos(3*z)),
with cyclic permutations for u_y and u_z. See the real initial field in
Siegel and Caflisch, Physica D 238 (2009):
https://doi.org/10.1016/j.physd.2009.09.016
Only that real initial datum is used here. The evolution is the full real
Navier--Stokes Galerkin equation at constant viscosity, using the strict
two-thirds rule and the existing full_history RK4 implementation.

Energies are physical volume integrals: K=||u||_2^2/2, Y=||grad u||_2^2/2,
D=nu*||grad^2 u||_2^2. Cutoffs are angular wave numbers. The tail ledger
separates self-stretching (all three inputs high), lower-frequency feeding,
and dissipation, integrated at the same RK stages as the velocity.

The high-frequency palinstrophy fraction is a resolution warning, not an
error certificate. Prefix maxima are sampled at steps. No finite run or
cutoff above the truncation proves an endpoint-independent PDE budget.
Requires NumPy and SciPy.
"""
import argparse
import json
import time

import numpy as np

if __package__:
    from .full_history import FullFlow, cross
    from .triaxial_history import self_stretching
else:
    from full_history import FullFlow, cross
    from triaxial_history import self_stretching


class KidaPelzFlow(FullFlow):
    def __init__(self, n, viscosity, self_cutoffs):
        self.n = self.nz = n
        self.box = 2 * np.pi
        self.viscosity = viscosity
        labels = np.rint(np.fft.fftfreq(n, 1 / n))
        self.k = np.array(np.meshgrid(labels, labels, labels, indexing='ij'))
        self.ksq = np.sum(self.k * self.k, axis=0)
        self.inv = np.divide(1, self.ksq, out=np.zeros_like(self.ksq), where=self.ksq > 0)
        self.mask = np.all(np.abs(self.k) < n / 3, axis=0)
        self.high = np.any(np.abs(self.k) > .8 * n / 3, axis=0)
        self.tail_cutoffs = np.array([0., 4., 8., 12., 16., 24.])
        self.tail_bins = np.searchsorted(self.tail_cutoffs**2, self.ksq, side='right')
        self.self_cutoffs = np.array(self_cutoffs, dtype=float)
        self.area = (2 * np.pi)**3 / n**6
        x = 2 * np.pi * np.arange(n) / n
        s, c, c3 = np.sin(x), np.cos(x), np.cos(3 * x)
        velocity = np.array([
            s[:, None, None] * (c3[None, :, None] * c[None, None, :]
                                - c[None, :, None] * c3[None, None, :]),
            s[None, :, None] * (c3[None, None, :] * c[:, None, None]
                                - c[None, None, :] * c3[:, None, None]),
            s[None, None, :] * (c3[:, None, None] * c[None, :, None]
                                - c[:, None, None] * c3[None, :, None])])
        self.initial = self.project(self.fft(velocity))

    def rhs(self, u):
        velocity, rates, work = super().rhs(u)
        return velocity, np.concatenate([rates, self.self_stretching(u, self.self_cutoffs)]), work

    def self_stretching(self, u, cutoffs):
        return self_stretching(self, u, cutoffs)

    def resolution(self, u):
        density = np.sum(np.abs(u)**2, axis=0)
        pal = self.ksq**2 * density
        v = self.ifft(u)
        omega = self.ifft(1j * cross(self.k, u))
        return {
            'high_palinstrophy_fraction': float(np.sum(pal[self.high]) / np.sum(pal)),
            'high_enstrophy_fraction': float(np.sum((self.ksq * density)[self.high])
                                               / np.sum(self.ksq * density)),
            'max_velocity': float(np.max(np.sqrt(np.sum(v.real**2, axis=0)))),
            'max_vorticity': float(np.max(np.sqrt(np.sum(omega.real**2, axis=0)))),
            'divergence_l2': float(np.sqrt(self.area * np.sum(np.abs(np.sum(self.k * u, axis=0))**2))),
            'max_reality_error': float(np.max(np.abs(v.imag)))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=128)
    parser.add_argument('--backend', choices=['full', 'reflections'], default='full',
                        help='n is always the equivalent full-cube grid size')
    parser.add_argument('--viscosity', type=float, default=.001)
    parser.add_argument('--time', type=float, default=1.5)
    parser.add_argument('--step', type=float, default=.002)
    parser.add_argument('--report-every', type=float, default=.1)
    parser.add_argument('--self-cutoffs', nargs='+', type=float, default=[4., 8., 12.])
    parser.add_argument('--max-high-palinstrophy', type=float, default=.005)
    parser.add_argument('--checkpoint', help='optional final NumPy checkpoint')
    parser.add_argument('--check-only', action='store_true')
    a = parser.parse_args()
    if a.n < 48 or a.n % 2:
        parser.error('an even grid size of at least 48 is required')
    if any(not np.isfinite(v) or v <= 0 for v in
           [a.viscosity, a.time, a.step, a.report_every, a.max_high_palinstrophy]):
        parser.error('positive finite viscosity, times and resolution threshold required')
    if len(set(a.self_cutoffs)) != len(a.self_cutoffs) or any(
            k not in [0, 4, 8, 12, 16, 24] for k in a.self_cutoffs):
        parser.error('self cutoffs must be distinct members of 0,4,8,12,16,24')
    if a.backend == 'reflections':
        if __package__:
            from .kida_pelz_symmetry import ReflectionFlow
        else:
            from kida_pelz_symmetry import ReflectionFlow
        m = ReflectionFlow(a.n, a.viscosity, a.self_cutoffs)
    else:
        m = KidaPelzFlow(a.n, a.viscosity, a.self_cutoffs)
    u = m.initial.copy()
    initial = m.energies(u)
    initial_tails = m.tail_enstrophy(u)
    nt = len(m.tail_cutoffs)
    indices = np.array([list(m.tail_cutoffs).index(k) for k in a.self_cutoffs])
    _, initial_rates, work = m.rhs(u)
    expected = np.array([3 * np.pi**3, 33 * np.pi**3, 726 * a.viscosity * np.pi**3])
    actual = np.array([initial[0], initial[1], initial_rates[2]])
    errors = np.abs(actual / expected - 1)
    if np.max(errors) > 1e-12 or abs(initial_rates[1]) > 1e-10 * initial[1]:
        raise ArithmeticError('initial Fourier energy or zero-production check failed')
    # Independent velocity-space cubic calculation versus filtered RHS pairing.
    total_self = m.self_stretching(u, [0.])[0]
    if abs(total_self - initial_rates[1]) > 1e-10 * initial[1]:
        raise ArithmeticError('Betchov identity check failed')
    print(json.dumps({'configuration': vars(a), 'normalization_relative_errors': errors.tolist(),
        'initial_K_Y_D': actual.tolist(), 'initial_production': float(initial_rates[1]),
        'initial_resolution': m.resolution(u)}), flush=True)
    if a.check_only:
        return
    integrated = np.zeros_like(initial_rates)
    maxima = np.zeros(len(indices))
    started = time.monotonic()
    t = 0.
    steps = 0
    next_report = min(a.report_every, a.time)
    reason = 'requested_time'
    while t < a.time - 1e-13:
        velocity = m.ifft(u).real
        cfl_rate = (a.n / 3) * float(np.max(np.sum(np.abs(velocity), axis=0)))
        dt = min(a.step, .5 / max(cfl_rate, 1e-30),
                 2 / (a.viscosity * np.max(m.ksq[m.mask])), next_report - t)
        del velocity
        u, di, dw = m.step(u, dt)
        integrated += di
        work = max(work, dw)
        steps += 1
        t += dt
        ps = integrated[3 + 2 * nt:]
        ds = integrated[3 + nt:3 + 2 * nt][indices]
        maxima = np.maximum(maxima, ps - .5 * ds)
        if not np.all(np.isfinite(u)):
            raise ArithmeticError('nonfinite velocity')
        if t >= next_report - 1e-13:
            energy = m.energies(u)
            tails = m.tail_enstrophy(u)
            _, rates, _ = m.rhs(u)
            pfull = integrated[3:3 + nt]
            dfull = integrated[3 + nt:3 + 2 * nt]
            resolution = m.resolution(u)
            reason = ('resolution_limit' if resolution['high_palinstrophy_fraction']
                      > a.max_high_palinstrophy else 'requested_time')
            print(json.dumps({'time': t, 'steps': steps, 'last_step': dt, 'energy': energy.tolist(),
                'integrated_production': float(integrated[1]),
                'integrated_dissipation': float(integrated[2]),
                'kinetic_ledger': float(energy[0] - initial[0] + integrated[0]),
                'enstrophy_ledger': float(energy[1] - initial[1] - integrated[1] + integrated[2]),
                'tail_ledger_max': float(np.max(np.abs(tails - initial_tails - pfull + dfull))),
                'tails': [dict(cutoff=float(k), enstrophy=float(tails[i]),
                    integrated_self=float(ps[j]), integrated_low_input=float(pfull[i] - ps[j]),
                    integrated_dissipation=float(ds[j]), half_excess=float(ps[j] - .5 * ds[j]),
                    sampled_prefix_max=float(maxima[j]),
                    instantaneous_self=float(rates[3 + 2 * nt + j]),
                    instantaneous_low_input=float(rates[3 + i] - rates[3 + 2 * nt + j]),
                    instantaneous_dissipation=float(rates[3 + nt + i]))
                    for j, (k, i) in enumerate(zip(a.self_cutoffs, indices))],
                'resolution': resolution, 'max_nonlinear_kinetic_work': float(work),
                'stop_reason': reason if reason == 'resolution_limit' or t >= a.time - 1e-13 else None,
                'wall_seconds': time.monotonic() - started}), flush=True)
            if reason == 'resolution_limit':
                break
            next_report = min(next_report + a.report_every, a.time)
    if a.checkpoint:
        np.savez(a.checkpoint, velocity=u, integrated=integrated, time=t,
                 configuration=json.dumps(vars(a)), sampled_prefix_max=maxima, stop_reason=reason)


if __name__ == '__main__':
    main()
