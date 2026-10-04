#!/usr/bin/env python3
"""Numerical full NS tangents for the completed pressure/receiver stock.

Gaussian whole-space data are sampled in periodic boxes. Canonical pressure
and its variation are computed from the complete velocity tangent, with an
independent Poisson-source check. Refinement and domain enlargement are
numerical evidence, not continuum enclosures, Lean proofs or time evolution.
"""

import argparse
import hashlib
import json
import time
from pathlib import Path

import numpy as np

class Grid:

    def __init__(self, n, box):
        self.n = n
        self.box = box
        self.dx = box / n
        x = (np.arange(n) - n // 2) * self.dx
        self.X = np.meshgrid(x, x, x, indexing='ij', sparse=True)
        k = np.fft.fftfreq(n, d=self.dx) * 2 * np.pi
        self.K = np.meshgrid(k, k, k, indexing='ij', sparse=True)
        self.k2 = sum((q * q for q in self.K))
        self.inv = np.divide(1.0, self.k2, out=np.zeros_like(self.k2), where=self.k2 > 0)

    def fft(self, a):
        return np.fft.fftn(a)

    def real(self, a):
        return np.fft.ifftn(a).real

    def derivative(self, a, j):
        return self.real(1j * self.K[j] * self.fft(a))

    def integral(self, a):
        return float(np.sum(a) * self.dx ** 3)

    def dot(self, a, b):
        return sum((x * y for (x, y) in zip(a, b)))

    def stress_pressure(self, u, v):
        out = np.zeros(self.k2.shape, dtype=complex)
        for i in range(3):
            for j in range(i, 3):
                field = u[i] * v[j] + v[i] * u[j]
                out -= (1 if i == j else 2) * self.K[i] * self.K[j] * self.fft(field)
        return out * self.inv

def jet(n, box, B, L=1.0, nu=0.01, amp=1.0, kappa=0.0001, ell=100.0):
    start = time.time()
    g = Grid(n, box)
    (x, y, z) = g.X
    r2 = x * x + y * y
    rho2 = r2 + z * z
    ex = np.exp(-rho2)
    u = [-x * (1 - 2 * z * z) * ex, -y * (1 - 2 * z * z) * ex, 2 * z * (1 - r2) * ex]
    u[0] = u[0] - B * y * z * ex
    u[1] = u[1] + B * x * z * ex
    U = [g.fft(a) for a in u]
    G = [[g.real(1j * g.K[j] * U[i]) for j in range(3)] for i in range(3)]
    divergence = sum((G[i][i] for i in range(3)))
    source = sum((G[i][j] * G[j][i] for i in range(3) for j in range(3)))
    p_hat = g.fft(source) * g.inv
    gp = [g.real(1j * k * p_hat) for k in g.K]
    tangentE = [-g.dot(u, G[i]) - gp[i] for i in range(3)]
    tangentV = [g.real(-g.k2 * a) for a in U]
    dtp = {}
    errors = {'divergence': float(np.max(abs(divergence))), 'poisson_mean': abs(g.integral(source))}
    for (name, v) in [('Euler', tangentE), ('viscous', tangentV)]:
        pt_hat = g.stress_pressure(u, v)
        V = [g.fft(a) for a in v]
        pt_source = 2 * sum((G[i][j] * g.real(1j * g.K[i] * V[j]) for i in range(3) for j in range(3)))
        alternative = g.fft(pt_source) * g.inv
        errors[name + '_pressure_derivative'] = float(np.max(abs(g.real(pt_hat - alternative))))
        dtp[name] = pt_hat
    multiplier = -np.expm1(-L * L * g.k2) * g.inv
    q_hat = p_hat * multiplier
    beta = [g.real(1j * g.K[i] * q_hat) for i in range(2)]
    H = 1 + kappa * r2 * ex
    dH = [2 * kappa * x * (1 - r2) * ex, 2 * kappa * y * (1 - r2) * ex, -2 * kappa * r2 * z * ex]
    Hr_over_r = 2 * kappa * (1 - r2) * ex
    Ht = {'Euler': -g.dot(u, dH), 'viscous': kappa * r2 * (4 * rho2 - 10) * ex}
    E = g.integral(g.dot(u, u))
    delta = g.integral(u[2] ** 2 - (u[0] ** 2 + u[1] ** 2) / 2)
    F0 = 3 * (ell * ell + r2 - 4 * z * z) / (4 * np.pi * (ell * ell + rho2) ** 3.5)
    gradq0 = [x * F0, y * F0]
    w = u[:2]
    norm = np.sqrt(g.dot(w, w))
    bnorm = np.sqrt(g.dot(beta, beta))
    inverse_norm = np.divide(1, norm, out=np.zeros_like(norm), where=norm > 0)
    a = [-3 * norm * v / H ** 1.5 for v in w]
    R = g.integral(norm ** 3 / H ** 1.5)
    C = g.integral(g.dot(a, beta))
    stockB = g.integral(bnorm ** 3 / H ** 1.5)
    coefficients = {}
    for (name, v) in [('Euler', tangentE), ('viscous', tangentV)]:
        wt = [v[i] + (delta * gradq0[i] if name == 'Euler' else 0) for i in range(2)]
        bt = [g.real(1j * g.K[i] * dtp[name] * multiplier) for i in range(2)]
        ht = Ht[name]
        wd = g.dot(w, wt)
        at = [-3 * (norm * wt[i] + w[i] * wd * inverse_norm) / H ** 1.5 + 4.5 * norm * w[i] * ht / H ** 2.5 for i in range(2)]
        coefficients['R_' + name] = g.integral(3 * norm * wd / H ** 1.5 - 1.5 * norm ** 3 * ht / H ** 2.5)
        coefficients['C_' + name] = g.integral(g.dot(at, beta) + g.dot(a, bt))
        coefficients['B_' + name] = g.integral(3 * bnorm * g.dot(beta, bt) / H ** 1.5 - 1.5 * bnorm ** 3 * ht / H ** 2.5)
    D = -coefficients['R_viscous']
    inverse_bnorm = np.divide(1, bnorm, out=np.zeros_like(bnorm), where=bnorm > 0)
    dbeta = 0
    for j in range(3):
        db = [g.real(-g.K[i] * g.K[j] * q_hat) for i in range(2)]
        bd = g.dot(beta, db)
        dbeta += 3 * bnorm * g.dot(db, db) / H ** 1.5 + 3 * inverse_bnorm * bd * bd / H ** 1.5 - 9 * bnorm * bd * dH[j] / H ** 2.5 + 3.75 * bnorm ** 3 * dH[j] ** 2 / H ** 3.5
    dbeta -= 3 * bnorm ** 3 * Hr_over_r / H ** 2.5
    Db = g.integral(dbeta)
    Wh = g.integral(g.dot(a, [g.real(1j * g.K[i] * p_hat * -np.expm1(-L * L * g.k2)) for i in range(2)]))
    Wres = g.integral(g.dot(a, [gp[i] - delta * gradq0[i] for i in range(2)]))
    errors['base_transport_balance'] = abs(coefficients['R_Euler'] - Wres)
    output = []
    for sign in [1, -1]:
        c = amp
        Rt = sign * c ** 4 * coefficients['R_Euler'] + nu * c ** 3 * coefficients['R_viscous']
        Ct = c ** 5 * coefficients['C_Euler'] + sign * nu * c ** 4 * coefficients['C_viscous']
        Bt = sign * c ** 7 * coefficients['B_Euler'] + nu * c ** 6 * coefficients['B_viscous']
        J = c ** 3 * R + sign * c ** 4 * C / (2 * nu) + 2 * c ** 6 * stockB / nu ** 3
        Jt = Rt + Ct / (2 * nu) + 2 * Bt / nu ** 3
        Dstar = nu * c ** 3 * D + 2 * c ** 6 * Db / nu ** 2
        Ecorr = Ct + 2 * nu * sign * c ** 4 * Wh
        Wbeta = Bt + nu * c ** 6 * Db
        Fstar = Ecorr / (2 * nu) + 2 * Wbeta / nu ** 3
        output.append(dict(sign=sign, J=J, J_prime=Jt, D_star=Dstar, F_star=Fstar, gap=Fstar - Dstar / 2, viscous_J_prime=nu * c ** 3 * coefficients['R_viscous'] + sign * c ** 4 * coefficients['C_viscous'] / 2 + 2 * c ** 6 * coefficients['B_viscous'] / nu ** 2))
    return dict(n=n, box=box, B=B, L=L, nu=nu, amplitude=amp, kappa=kappa, ell=ell, E=E, delta=delta, R=R, C=C, pressure_stock=stockB, D=D, D_beta=Db, W_high=Wh, coefficients=coefficients, rows=output, errors=errors, elapsed=time.time() - start)

def validate(result):
    """Reject unresolved identities; these tolerances are not error enclosures."""
    errors = result['errors']
    pressure_keys = ('divergence', 'poisson_mean', 'Euler_pressure_derivative',
                     'viscous_pressure_derivative')
    if max(errors[k] for k in pressure_keys) > 1e-8:
        raise ArithmeticError('Refine the grid: pressure identities are unresolved')
    if errors['base_transport_balance'] > 1e-4:
        raise ArithmeticError('Refine the observable quadrature: transport is unresolved')
    B2 = result['B']**2
    expected_energy = np.sqrt(2)*np.pi**1.5*(B2+7)/32
    expected_delta = np.sqrt(2)*np.pi**1.5*(5-B2)/64
    if max(abs(result['E']-expected_energy), abs(result['delta']-expected_delta)) > 1e-8:
        raise ArithmeticError('Enlarge or refine the box: Gaussian energy moments unresolved')
    c = result['amplitude']
    for row in result['rows']:
        lower = c**3*result['R']/2
        upper = 3*c**3*result['R']/2+4*c**6*result['pressure_stock']/result['nu']**3
        if not lower-1e-10*upper <= row['J'] <= upper*(1+1e-10):
            raise ArithmeticError('Completed-stock bound failed')
    if not result['D'] > 0 or not result['D_beta'] > 0:
        raise ArithmeticError('Weighted diffusion is unresolved')
    if not all(np.isfinite(v) for v in result['coefficients'].values()):
        raise ArithmeticError('Nonfinite initial derivative')
    coefficients = result['coefficients']
    vR, vC, vB = (coefficients[k] for k in ('R_viscous', 'C_viscous', 'B_viscous'))
    viscous_max = None
    if vB < 0:
        viscous_max = vR+abs(vC)/3*np.sqrt(abs(vC)/(12*abs(vB)))
    result['diagnostic_checks'] = dict(
        energy_error=abs(result['E']-expected_energy),
        anisotropy_error=abs(result['delta']-expected_delta),
        inferred_viscous_polynomial_max=viscous_max,
        scope='Floating-point identity and resolution checks; no certified continuum sign or time interval.')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--n', type=int, default=128)
    p.add_argument('--box', type=float, default=16.0)
    p.add_argument('--swirl-squared', type=int, choices=(5, 8), default=8)
    p.add_argument('--nu', type=float, default=0.01)
    p.add_argument('--L', type=float, default=1.0)
    p.add_argument('--amp', type=float, default=16.0)
    a = p.parse_args()
    if a.n < 4 or min(a.box, a.nu, a.L, a.amp) <= 0:
        p.error('Positive physical parameters and at least four grid points are required')
    result = validate(jet(a.n, a.box, np.sqrt(a.swirl_squared), a.L, a.nu, a.amp))
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(result, indent=2), flush=True)
