#!/usr/bin/env python3
"""Check pressure-history projection loss against the complete spatial operator.

The enlarged grid evaluates every product of the retained polynomial fields.
This is an instantaneous spatial residual, not a continuum trajectory error
bound: time discretization and stability amplification remain separate.
"""

import json
import numpy as np
from scipy.fft import fftn, ifftn
from cellular_parent_history import PAIRS


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def fft(a):
    return fftn(a, axes=(0, 1, 2), workers=1)


def ifft(a):
    return ifftn(a, axes=(0, 1, 2), workers=1).real


def frequencies(n):
    axis = np.rint(np.fft.fftfreq(n)*n)
    return np.stack(np.meshgrid(axis, axis, axis, indexing='ij'), axis=-1)


def enlarge(state):
    n = state.shape[0]
    require(n % 2 == 0 and state.shape == (n, n, n, 16), 'Even cubic pressure-history state')
    pad = n//2
    return np.fft.ifftshift(np.pad(np.fft.fftshift(state, axes=(0, 1, 2)),
        ((pad, pad), (pad, pad), (pad, pad), (0, 0))), axes=(0, 1, 2))*8


def complete_operator(state):
    """Unfiltered canonical pressure and every conditional-moment source."""
    n = state.shape[0]
    K = frequencies(n)
    k2 = np.sum(K*K, axis=-1)
    inv = np.divide(1., k2, out=np.zeros_like(k2), where=k2 > 0)
    values = ifft(state)
    gradient = [ifft(1j*K[..., j, None]*state) for j in range(3)]
    u = values[..., :3]
    adv = sum(u[..., j, None]*gradient[j] for j in range(3))
    ah = fft(adv)
    gh = -K*inv[..., None]*np.sum(K*ah[..., :3], axis=-1)[..., None]
    g = ifft(gh)
    result = -adv
    result[..., :3] -= g
    result[..., 3:6] += g
    second = np.zeros(values.shape[:-1]+(3, 3))
    for j, (a, b) in enumerate(PAIRS):
        second[..., a, b] = second[..., b, a] = values[..., 6+j]
        result[..., 6+j] += values[..., 3+a]*g[..., b]+values[..., 3+b]*g[..., a]
    result[..., 12:15] += 2*np.einsum('...ij,...j->...i', second, g) \
        +np.trace(second, axis1=-2, axis2=-1)[..., None]*g
    rhs = fft(result)
    rhs[..., 15] = 0
    rhs[0, 0, 0, 15] = 4*np.mean(np.sum(g*values[..., 12:15], axis=-1))*n**3
    return rhs, gh


def spatial_residual(state, retained_rhs):
    n = state.shape[0]
    K = frequencies(n)
    keep = np.all(abs(K) < n/3, axis=-1)
    require(np.max(abs(state[~keep])) < 1e-12*max(1., np.max(abs(state))),
            'The enlarged product calculation requires the stated retained Fourier support')
    padded = enlarge(state)
    full, gh = complete_operator(padded)
    residual = full-enlarge(retained_rhs)
    m = 2*n
    weights = np.array([1 if i == j else 2 for i, j in PAIRS])
    groups = [('velocity', slice(0, 3), 1), ('first', slice(3, 6), 1),
              ('second', slice(6, 12), weights), ('third', slice(12, 15), 1)]
    Kfull = frequencies(m)
    Sobolev = (1+np.sum(Kfull*Kfull, axis=-1))**3
    report = {}
    for name, block, weight in groups:
        square = np.sum(abs(residual[..., block])**2*weight, axis=-1)/m**6
        report[name] = {'L2': float(np.sqrt(np.sum(square))),
                        'H3': float(np.sqrt(np.sum(square*Sobolev)))}
    outside = ~np.all(abs(Kfull) < n/3, axis=-1)
    report['omitted_pressure_gradient_L2'] = float(np.sqrt(np.sum(abs(gh[outside])**2)/m**6))
    report['fourth_rate_difference'] = float(residual[0, 0, 0, 15].real/m**3)
    report['scope'] = 'Instantaneous spatial operator mismatch; no time-discretization or continuum stability enclosure'
    return report


def exact_fixture():
    """Compare all unfiltered coefficients against independent exact algebra."""
    from fractions import Fraction as Q
    import pressure_history_source as f
    u = f.fixture()
    I = [f.scale(Q(1, 3), a) for a in u]
    second = [[f.add({f.ORIGIN: f.QQ_I(3)} if i == j else {},
                      f.scale(Q(1, 5), u[(i+j) % 3])) for j in range(3)] for i in range(3)]
    T = [f.scale(Q(2, 7), a) for a in u]
    p = f.tensor_pressure(f.tensor(u, u))
    g = f.grad(p)
    fields = u+I+[second[i][j] for i, j in PAIRS]+T+[{}]
    rhs = [f.add(f.scale(-1, f.adv(u, u[i])), f.scale(-1, g[i])) for i in range(3)]
    rhs += [f.add(f.scale(-1, f.adv(u, I[i])), g[i]) for i in range(3)]
    rhs += [f.add(f.scale(-1, f.adv(u, second[i][j])), f.mul(I[i], g[j]), f.mul(g[i], I[j]))
            for i, j in PAIRS]
    rhs += [f.add(f.scale(-1, f.adv(u, T[i])), f.scale(2, f.dot(second[i], g)),
                  f.mul(f.trace(second), g[i])) for i in range(3)]
    rhs += [{f.ORIGIN: 4*f.dot(g, T).get(f.ORIGIN, f.ZERO)}]

    def array(rows, n):
        result = np.zeros((n, n, n, len(rows)), complex)
        for j, field in enumerate(rows):
            for k, a in field.items():
                result[tuple(v % n for v in k)+(j,)] = complex(float(a.x), float(a.y))*n**3
        return result

    state = array(fields, 8)
    actual, gradient = complete_operator(enlarge(state))
    expected = array(rhs, 16)
    error = float(np.max(abs(actual-expected))/max(1., np.max(abs(expected))))
    pressure_error = float(np.max(abs(gradient-array(g, 16)))/max(1., np.max(abs(array(g, 16)))))
    require(error < 5e-14 and pressure_error < 5e-14,
            'Every complete spatial operator coefficient matches exact Fourier algebra')
    # An exactly restricted full RHS has nonzero omitted spatial fields,
    # while the global fourth-moment rate is preserved by orthogonality.
    kept = array([{k: a for k, a in row.items() if all(abs(v) < 8/3 for v in k)}
                  for row in rhs], 8)
    report = spatial_residual(state, kept)
    require(report['first']['L2'] > 1e-3 and report['omitted_pressure_gradient_L2'] > 1e-3,
            'The fixture retains genuinely omitted pressure/history channels')
    require(abs(report['fourth_rate_difference']) < 1e-12,
            'Global cost-rate agreement does not certify the preceding moment equations')
    return dict(status='complete spatial operator check passed', relative_error=error,
                pressure_relative_error=pressure_error, residual=report)


def cellular_blind_spot():
    """Exact global NS velocity, but the projected pressure history is zero."""
    from fractions import Fraction as Q
    import pressure_history_source as f
    from pressure_parent_bellman import trig
    m, n = 2, 12
    u = [f.mul(trig(0, m, 'sin'), trig(1, m, 'cos')),
         f.scale(-1, f.mul(trig(0, m, 'cos'), trig(1, m, 'sin'))), {}]
    p = f.tensor_pressure(f.tensor(u, u))
    expected_p = f.scale(Q(1, 4), f.add(trig(0, 2*m, 'cos'), trig(1, 2*m, 'cos')))
    f.equal(p, expected_p, 'Literal cellular canonical pressure')
    g = f.grad(p)
    for j in range(3):
        f.equal(f.add(f.adv(u, u[j]), g[j]), {}, 'Exact Euler balance of the decaying NS profile')
        f.equal(f.lap(u[j]), f.scale(-2*m*m, u[j]), 'Exact viscous eigenvalue')
        require(all(any(abs(v) >= n/3 for v in k) for k in g[j]),
                'Every nonzero pressure gradient mode lies outside the retained band')
    square = f.dot(g, g)
    require(f.mul(square, square).get(f.ORIGIN, f.ZERO) == f.QQ_I(Q(5*m**4, 64)),
            'The actual pressure fourth moment has a strictly positive leading coefficient')
    state = np.zeros((n, n, n, 16), complex)
    for j, field in enumerate(u):
        for k, a in field.items():
            state[tuple(v % n for v in k)+(j,)] = complex(float(a.x), float(a.y))*n**3
    K = frequencies(n)
    high = np.any(abs(K) > .8*n/3, axis=-1)
    require(not np.any(state[high]), 'The usual outer-band velocity diagnostic is exactly zero')
    report = spatial_residual(state, np.zeros_like(state))
    require(report['first']['L2'] > .1 and abs(report['fourth_rate_difference']) < 1e-13,
            'The latent pressure-history error is visible before the scalar rate changes')
    return dict(m=m, grid=n, actual_velocity='exp(-2nu m^2 t) U_m, exact globally',
                actual_phi_leading=str(Q(5*m**4, 64)), approximate_phi='0 at every time',
                scope='The same exact blind spot holds at n=6m for every integer m>=2',
                spatial_residual=report)


if __name__ == '__main__':
    print(json.dumps(dict(operator=exact_fixture(), actual_flow=cellular_blind_spot()), indent=2))
