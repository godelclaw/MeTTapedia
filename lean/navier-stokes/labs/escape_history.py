#!/usr/bin/env python3
"""Fourier-family escape over one fixed unforced Navier--Stokes history.

On the normalized 2*pi torus, u=(exp(-nu*t)*sin(y), 0,
Re(exp(i*x)*a(y,t))) is an exact invariant class of the full equation.
The scalar satisfies a_t=nu*(a_yy-a)-i*exp(-nu*t)*sin(y)*a, a(y,0)=1.
All reported families are projections of the SAME reference history.

Factorial rescaling keeps very small Fourier coefficients observable.
The numerical reference is a finite section, with an analytic factorial
tail estimate stated in README.md. Refinement and independent physical
convection checks are diagnostics, not interval arithmetic or Lean proofs.
"""
import argparse
from fractions import Fraction
import json
from math import factorial

import numpy as np
from scipy.integrate import solve_ivp


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def normalization(order):
    return np.array([float(2**j * factorial(j)) for j in range(order + 1)])


def convection_scaled(b, U):
    """b_j=(-1)^j*2^j*j!*a_j; a_-j=(-1)^j*a_j."""
    n = np.empty_like(b)
    n[0] = -U * b[1] / 2
    j = np.arange(1, len(b))
    n[1:] = U * j * b[:-1]
    n[1:-1] -= U * b[2:] / (4 * (j[:-1] + 1))
    return n


def history(order, nu, step, rtol, atol):
    j = np.arange(order + 1)

    def rhs(t, b):
        return convection_scaled(b, np.exp(-nu*t)) - nu*(1+j*j)*b

    initial = np.zeros(order + 1)
    initial[0] = 1
    sol = solve_ivp(rhs, (0., 1.), initial, method='DOP853',
                    dense_output=True, max_step=step, rtol=rtol, atol=atol)
    require(sol.success, sol.message)
    return sol


def family_rates(b_full, U, nu, m):
    b = b_full[:m+1]
    c = normalization(m)
    j = np.arange(m + 1)
    multiplicity = np.where(j == 0, 1., 2.)
    w = 1 + j*j
    n = convection_scaled(b, U)
    square = multiplicity*(b/c)**2
    Z = (U*U + np.sum(w*square))/4
    Pi = np.sum(multiplicity*w*b*n/(c*c))/2
    loss = nu*(U*U + np.sum(w*w*square))/2
    # Compute this integral before dividing by (2^m*m!)^2.
    escape_scaled = U*U*b[m]*b[m]/4
    am = (-1.)**m*b_full[m]/c[m]
    anext = (-1.)**(m+1)*b_full[m+1]/normalization(m+1)[-1]
    unresolved_work = U*(1+m*m)*am*anext/2
    return np.array([Z, Pi, loss, escape_scaled, unresolved_work])


def integrate_families(sol, nu, families, quadrature):
    x, w = np.polynomial.legendre.leggauss(quadrature)
    times, weights = (x+1)/2, w/2
    b = sol.sol(times)
    endpoint = sol.sol(1.)
    result = []
    for m in families:
        samples = np.array([family_rates(b[:, i], np.exp(-nu*t), nu, m)
                            for i, t in enumerate(times)])
        integral = weights @ samples
        final = family_rates(endpoint, np.exp(-nu), nu, m)
        gain = integral[1]-integral[2]
        escape = integral[3]/normalization(m)[-1]**2
        ledger = final[0]-.5-gain-integral[4]
        result.append({'family_order': m, 'final_half_enstrophy': float(final[0]),
                       'self_integral': float(integral[1]),
                       'viscous_loss_integral': float(integral[2]),
                       'signed_surplus': float(gain),
                       'escape_source_squared_integral': float(escape),
                       'unresolved_work_integral': float(integral[4]),
                       'filtered_ledger_error': float(ledger)})
    return result


def physical_check(b_full, U, nu, m=6):
    """Independent physical convection and vorticity stretching on a 2D grid.

    There are three velocity components; only their z derivatives vanish.
    Both input orders and every nonlinear output are retained.
    """
    nx, ny = 16, 4*(m+2)
    vhat = np.zeros((3, nx, ny), dtype=complex)
    vhat[0, 0, 1], vhat[0, 0, -1] = -1j*U/2, 1j*U/2
    c = normalization(m)
    for j in range(-m, m+1):
        aj = (-1.)**max(j, 0)*b_full[abs(j)]/c[abs(j)]
        vhat[2, 1, j % ny] = aj/2
        vhat[2, -1, (-j) % ny] = aj/2
    kx = np.fft.fftfreq(nx)*nx
    ky = np.fft.fftfreq(ny)*ny
    ksq = kx[:, None]**2 + ky[None, :]**2
    inverse = lambda x: np.fft.ifft2(x, axes=(-2, -1), norm='forward').real
    v = inverse(vhat)
    dx = inverse(1j*kx[None, :, None]*vhat)
    dy = inverse(1j*ky[None, None, :]*vhat)
    nonlinear = -(v[0]*dx + v[1]*dy)
    nhat = np.fft.fft2(nonlinear, axes=(-2, -1), norm='forward')
    div = kx[:, None]*nhat[0] + ky[None, :]*nhat[1]
    require(np.max(np.abs(div)) < 1e-13, 'physical source is transverse')
    pi_pairing = np.sum(ksq*(np.conj(vhat)*nhat).real)
    # omega=(theta_y,-theta_x,-U*cos(y)); omega.S.omega=-U_y*theta_x*theta_y.
    pi_stretching = np.mean(-dy[0]*dx[2]*dy[2])
    loss = nu*np.sum(ksq*ksq*np.abs(vhat)**2)
    mask = np.zeros((nx, ny), dtype=bool)
    mask[0, 1] = mask[0, -1] = True
    for j in range(-m, m+1):
        mask[1, j % ny] = mask[-1, (-j) % ny] = True
    escape = np.sum(np.abs(nhat[:, ~mask])**2)
    rates = family_rates(b_full, U, nu, m)
    expected_escape = rates[3]/c[m]**2
    differences = {'source_pairing': abs(pi_pairing-rates[1]),
                   'physical_stretching': abs(pi_stretching-rates[1]),
                   'viscous_loss': abs(loss-rates[2]),
                   'escape_relative': abs(escape/expected_escape-1)}
    require(max(differences.values()) < 1e-9, 'independent physical check')
    return {k: float(x) for k, x in differences.items()}


def analytic_bounds(m, nu=Fraction(1, 1000)):
    """Rational consequences of the analytic estimates, using exp(2)<9."""
    tail = Fraction(9*(1+(m+1)**2), factorial(m+1)**2)
    incoming = Fraction(9*(1+m*m), 4*(m+1)*factorial(m)*factorial(m+1))
    gain = Fraction(1, 8)-Fraction(31, 2)*nu-tail-incoming
    escape = Fraction(9, 4*(2*m+1)*factorial(m)**2)
    require(gain > Fraction(1, 10), 'analytic surplus lower bound for m>=6')
    return {'surplus_lower': str(gain), 'escape_upper': str(escape),
            'surplus_lower_decimal': float(gain), 'escape_upper_decimal': float(escape)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
                        help='refine the reference and quadrature; check physical convection')
    args = parser.parse_args()
    nu, families = .001, [6, 8, 12, 16, 20]
    sol = history(32, nu, 1/64, 5e-13, 1e-14)
    rows = integrate_families(sol, nu, families, 80)
    require(max(abs(r['filtered_ledger_error']) for r in rows) < 1e-10,
            'complete filtered enstrophy ledger')
    for row in rows:
        row['analytic_bounds'] = analytic_bounds(row['family_order'])
        require(row['signed_surplus'] > row['analytic_bounds']['surplus_lower_decimal'],
                'computed surplus satisfies the analytic lower bound')
        require(0 < row['escape_source_squared_integral'] < row['analytic_bounds']['escape_upper_decimal'],
                'computed escape satisfies the analytic upper bound')
    result = {'viscosity': nu, 'time': 1, 'reference_order': 32,
              'initial_velocity': '(sin(y), 0, cos(x))',
              'normalization': 'mean over the 2*pi torus', 'families': rows,
              'scope': 'Finite reference and analytic bounds; no interval or Lean certificate.'}
    if args.check:
        refined = history(40, nu, 1/128, 2e-13, 2e-15)
        fine = integrate_families(refined, nu, families, 120)
        gain_error = max(abs(a['signed_surplus']-b['signed_surplus'])
                         for a, b in zip(rows, fine))
        escape_error = max(abs(a['escape_source_squared_integral']/b['escape_source_squared_integral']-1)
                           for a, b in zip(rows, fine))
        require(gain_error < 1e-10 and escape_error < 1e-8, 'reference refinement')
        result['checks'] = {'surplus_refinement': gain_error,
                            'escape_relative_refinement': escape_error,
                            'physical': physical_check(refined.sol(1.), np.exp(-nu), nu)}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
