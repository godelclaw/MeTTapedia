#!/usr/bin/env python3
"""Exact NS shear transfers and a parent-dependent fluctuation reserve.

The complete nonlinear source is retained. Finite Fourier checks establish
algebra, not an evolution theorem. The all-frequency obstruction, passive
scalar evolution and reserve payment are derived analytically in README.md.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from reciprocal_pattern_cycles import inner, mode, vector_add, vector_scale, require
from refeeding_stretching import cubic, nonlinear, vertical_mean, linear_cubic_term
from generated_mean_enstrophy import (
    derivative_pair, minus_laplacian, second_gradient_squared, oscillation,
)
from reference_stretching_control import equal_vectors, gradient_norm_squared, bilinear
from cellular_parent_refeeding import seed
from cellular_transfer_reversal import real_field


def wave(n):
    return (n, 0, n + 1)


def radius(n):
    return n*n + (n+1)*(n+1)


def datum(n, a, b, c):
    parent = mode((1, 0, 1), a, True)
    return [parent, f.add(mode(wave(n), b), mode(wave(n+1), c)), f.scale(-1, parent)]


def project_wave(u, k):
    support = {k, tuple(-x for x in k)}
    return [{j: v for j, v in a.items() if j in support} for a in u]


def checks():
    records = []
    for n, a, b, c, nu in [
            (0, Q(1), Q(2), Q(3), Q(2, 7)),
            (1, Q(-3, 2), Q(2, 3), Q(5, 4), Q(1, 9)),
            (4, Q(2), Q(1), Q(-1), Q(3, 5)),
            (17, Q(1, 5), Q(-2), Q(3), Q(7, 2))]:
        u = datum(n, a, b, c)
        f.equal(f.trace(f.jac(u)), {}, 'initial field is solenoidal')
        equal_vectors(vertical_mean(u), [{}, {}, {}], 'initial vertical mean is empty')
        pressure = f.green(f.trace(f.matmul(f.jac(u), f.jac(u))))
        f.equal(pressure, {}, 'canonical pressure is constant in this triangular class')
        N = nonlinear(u)
        expected = [{}, f.add(mode(wave(n-1), -a*b/2),
                              mode(wave(n+1), a*b/2),
                              mode(wave(n), -a*c/2),
                              mode(wave(n+2), a*c/2)), {}]
        equal_vectors(N, expected, 'all four receiver outputs retained')
        q, r = project_wave(u, wave(n)), project_wave(u, wave(n+1))
        require(2*inner(q, N) == -a*b*c/2, 'lower receiver kinetic transfer')
        require(2*inner(r, N) == a*b*c/2, 'upper receiver kinetic transfer')
        require(inner(u, N) == 0, 'complete kinetic transfer cancels')
        require(cubic(u) == a*b*c*(n+1), 'physical vorticity stretching')
        require(derivative_pair(u, N) == cubic(u), 'independent enstrophy pairing')
        rhs = vector_add(N, vector_scale(-nu, minus_laplacian(u)))
        require(2*derivative_pair(u, rhs)
                == 2*cubic(u)-2*nu*second_gradient_squared(u),
                'complete positive-viscosity enstrophy law')
        rhoq, rhor = Q(7, 3), Q(11, 5)
        storage_nonlinear = 2*rhoq*inner(q, N)+2*rhor*inner(r, N)
        require(storage_nonlinear+2*cubic(u)
                == a*b*c*(rhor+radius(n+1)-rhoq-radius(n))/2,
                'quadratic storage must balance enstrophy-adjusted weights')
        # Include every first output and a separately chosen nonzero mean.
        evolved_probe = vector_add(u, vector_scale(Q(1, 10), N))
        evolved_probe[1] = f.add(evolved_probe[1], mode((3, 0, 0), Q(2, 7)))
        Z = gradient_norm_squared(evolved_probe)
        gw = cubic(oscillation(evolved_probe))
        require(abs(gw) <= 2*abs(a)*Z,
                'fluctuation stretching bound retains generated modes and mean')
        records.append({'n': n, 'stretching': str(cubic(u)),
                        'lower_kinetic_rate': str(-a*b*c/2),
                        'upper_kinetic_rate': str(a*b*c/2),
                        'source_modes': len(N[1]),
                        'source_contains_mean': any(vertical_mean(N))})
    return records


def symbolic_checks():
    n = s.symbols('n', real=True)
    require(s.expand(radius(n+1)-radius(n)-4*(n+1)) == 0,
            'all-index spectral gap polynomial identity')
    require(s.expand(radius(n)-radius(0)-2*n*(n+1)) == 0,
            'all-index finite-chain reserve cost')
    nu, a, Z, D, v, L, F, extra, slack = s.symbols(
        'nu a Z D v L F extra slack', real=True)
    # v stands for exp(2a/nu); the differentiation coefficient is explicit.
    adot = -2*nu*a+F
    Zdot = 4*a*Z-2*nu*D+L-slack
    Rdot = (v-1)*Zdot+(2/nu)*v*adot*Z
    require(s.expand(Rdot+4*a*Z+extra+2*nu*(v-1)*D
                     -((v-1)*L+(2/nu)*v*F*Z+extra)
                     +(v-1)*slack) == 0,
            'parent renewal and receiver defects retained in full')
    # The joint enstrophy envelope obeys the companion inequality.
    Sdot = v*Zdot+(2/nu)*v*adot*Z
    require(s.expand(Sdot+2*nu*v*D-v*L-(2/nu)*v*F*Z+v*slack) == 0,
            'complete joint enstrophy compensation')
    h = s.symbols('h', real=True)
    factor = s.exp((2*a/nu)*(1-s.exp(-2*nu*h)))
    value = (factor-1)*Z
    hjb = -s.diff(value, h)-2*nu*a*s.diff(value, a)
    hjb += (4*a*Z-2*nu*D)*s.diff(value, Z)+4*a*Z
    require(s.simplify(hjb+2*nu*(factor-1)*D) == 0,
            'finite-horizon HJB equation with full diffusion loss')
    return {'weight_cost_through_n': 'rho(0) >= 2*n*(n+1)',
            'reserve': '(exp(2*abs(a)/nu)-1)*Z',
            'finite_horizon_value': '(exp((2*a/nu)*(1-exp(-2*nu*h)))-1)*Z',
            'parent_renewal_defect': '(2/nu)*exp(2*a/nu)*F*Z (a>=0)',
            'receiver_defect': '(exp(2*a/nu)-1)*L+extra'}


def mandatory_return():
    u = real_field(seed())
    N = nonlinear(u)
    parent = [mode((1, 0, 1), 1), {}, mode((1, 0, 1), -1)]
    require(inner(parent, parent) == 1, 'parent observation is normalized')
    require(inner(u, parent) == Q(1, 10), 'actual initial parent amplitude')
    require(inner(N, parent) == 0, 'initial parent nonlinear forcing is zero')
    T = vector_add(bilinear(u, N), bilinear(N, u))
    viscous = vector_scale(Q(-2, 7), minus_laplacian(u))
    Tv = vector_add(bilinear(u, viscous), bilinear(viscous, u))
    require(inner(Tv, parent) == 0, 'viscosity has zero parent-forcing derivative here')
    require(inner(T, parent) == Q(-22019, 546000),
            'this actual parent first depletes while self-stretching grows')
    require(linear_cubic_term(u, oscillation(N)) == Q(6252773, 5460000),
            'compulsory positive non-mean return is retained')
    return {'a_initial': '1/10', 'F_initial': '0',
            'F_derivative': '-22019/546000',
            'fluctuation_stretching_derivative': '6252773/5460000',
            'scope': 'actual initial jets; receiver defects remain unpaid for this 3D seed'}


if __name__ == '__main__':
    print(json.dumps({'fixtures': checks(), 'symbolic': symbolic_checks(),
                     'mandatory_return': mandatory_return(),
                     'scope': 'exact complete Fourier tangents and scalar identities; PDE proof analytic',
                     'unpaid': 'mutual parent renewal in arbitrary flows'}, indent=2))
