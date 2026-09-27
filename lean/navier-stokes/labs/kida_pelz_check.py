#!/usr/bin/env python3
"""Crosscheck real reflection transforms against full complex Fourier evolution.

The two solvers use different spatial transforms and representations of curl.
Compare evolved fields on the same shifted grid, their complete right-hand
sides, physical energy, and signed rates. Also compare Betchov's formula
against the independently filtered nonlinear RHS and halve the time step.
These are numerical consistency checks, not continuum error enclosures.
"""
import json
import numpy as np

if __package__:
    from .full_history import FullFlow
    from .kida_pelz_history import KidaPelzFlow
    from .kida_pelz_symmetry import ReflectionFlow
else:
    from full_history import FullFlow
    from kida_pelz_history import KidaPelzFlow
    from kida_pelz_symmetry import ReflectionFlow


def evolve(m, dt, count):
    u = m.initial.copy()
    integrals = np.zeros_like(m.rhs(u)[1])
    for _ in range(count):
        u, increment, _ = m.step(u, dt)
        integrals += increment
    return u, integrals


def check():
    n = 48
    full = KidaPelzFlow(n, .001, [4, 8, 12])
    reflected = ReflectionFlow(n, .001, [4, 8, 12])
    expected = np.array([3 * np.pi**3, 33 * np.pi**3])
    for m in (full, reflected):
        if np.max(np.abs(m.energies(m.initial) / expected - 1)) > 1e-12:
            raise ArithmeticError('initial physical energy normalization')
    coarse, ci = evolve(full, .004, 25)
    fine, fi = evolve(full, .002, 50)
    other, oi = evolve(reflected, .002, 50)
    phase = np.exp(1j * np.sum(full.k, axis=0) * np.pi / n)

    def on_octant(u):
        return full.ifft(u * phase).real[:, :n // 2, :n // 2, :n // 2]

    a = on_octant(fine)
    b = reflected.ifft(other)
    fu, fr, _ = full.rhs(fine)
    ru, rr, _ = reflected.rhs(other)
    result = {
        'relative_reflection_velocity': float(np.linalg.norm(a - b) / np.linalg.norm(a)),
        'relative_reflection_rhs': float(np.linalg.norm(on_octant(fu) - reflected.ifft(ru))
                                         / np.linalg.norm(on_octant(fu))),
        'max_rate_difference': float(np.max(np.abs(fr - rr))),
        'max_integral_difference': float(np.max(np.abs(fi - oi))),
        'relative_time_step_velocity': float(np.linalg.norm(coarse - fine) / np.linalg.norm(fine)),
        'time_step_energy_difference': (full.energies(coarse) - full.energies(fine)).tolist(),
        'time_step_self_integral_difference': (ci[-3:] - fi[-3:]).tolist(),
        'independent_stretching_checks': []}
    for k in [0, 4, 8, 12]:
        v = fine * (full.ksq >= k * k)
        independent = FullFlow.rhs(full, v)[1][1]
        betchov = full.self_stretching(fine, [k])[0]
        error = abs(independent - betchov)
        if error > 1e-9:
            raise ArithmeticError('filtered RHS versus Betchov formula')
        result['independent_stretching_checks'].append(
            dict(cutoff=k, filtered_rhs=float(independent), betchov=float(betchov),
                 absolute_difference=float(error)))
    if (result['relative_reflection_velocity'] > 1e-11
            or result['relative_reflection_rhs'] > 1e-10
            or result['max_rate_difference'] > 1e-8
            or result['max_integral_difference'] > 1e-9
            or result['relative_time_step_velocity'] > 1e-8):
        raise ArithmeticError(result)
    return result


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
