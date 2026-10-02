#!/usr/bin/env python3
"""Exact algebra for the evolving planar-mean enstrophy comparison.

All nonlinear outputs and the Leray projection are retained. The anisotropic
Sobolev estimate and smooth-solution interval conclusions are analytic in
README.md. These finite fixtures do not certify a global PDE bound.
"""

import json
from fractions import Fraction as Q
import sympy as s

import pressure_history_source as f
from reciprocal_pattern_cycles import inner, mode, vector_add, vector_scale, require
from cellular_parent_refeeding import seed
from cellular_transfer_reversal import real_field
from refeeding_stretching import cubic, nonlinear, vertical_mean, linear_cubic_term
from reference_stretching_control import bilinear, equal_vectors, gradient_norm_squared


def subtract(u, v):
    return vector_add(u, vector_scale(-1, v))


def horizontal_mean(u):
    return [{k: z for k, z in a.items() if k[0] == k[1] == 0} for a in u]


def oscillation(u):
    return subtract(u, vertical_mean(u))


def minus_laplacian(u):
    return [f.scale(-1, f.lap(a)) for a in u]


def derivative_pair(u, v):
    return inner(minus_laplacian(u), v)


def second_gradient_squared(u):
    return inner(minus_laplacian(u), minus_laplacian(u))


def exact_checks():
    M0 = [mode((0, 1, 0), 1, True), mode((1, 0, 0), -1, True),
          f.add(mode((1, 0, 0), 1), mode((1, 1, 0), 1))]
    w0 = real_field(seed())
    source = nonlinear(w0)
    mean_source, side_source = vertical_mean(source), oscillation(source)
    shear = [mode((0, 0, 1), Q(2, 3)), mode((0, 0, 2), Q(-1, 4), True), {}]
    fixtures = [vector_add(M0, w0),
                vector_add(vector_add(M0, mean_source), vector_add(w0, side_source)),
                vector_add(vector_scale(Q(-3, 2), M0),
                           vector_add(shear, vector_add(w0, vector_scale(Q(1, 10), side_source))))]
    records = []
    for u in fixtures:
        M, w = vertical_mean(u), oscillation(u)
        r = horizontal_mean(w)
        z = subtract(w, r)
        f.equal(f.trace(f.jac(u)), {}, 'full field is solenoidal')
        equal_vectors(vertical_mean(w), [{}, {}, {}], 'observed fluctuation is mean-free')
        equal_vectors(horizontal_mean(z), [{}, {}, {}], 'horizontal oscillation has zero mean')
        F = vertical_mean(bilinear(w, w))
        cross = vector_add(bilinear(M, w), bilinear(w, M))
        Nu = nonlinear(u)
        equal_vectors(vertical_mean(Nu), vector_add(nonlinear(M), F),
                      'actual mean retains full internally generated force')
        equal_vectors(oscillation(Nu), vector_add(cross, oscillation(nonlinear(w))),
                      'actual fluctuations retain every non-mean output')
        require(linear_cubic_term(M, w) == 0, 'mean-linear cubic term vanishes by averaging')
        mixed = linear_cubic_term(w, M)
        require(cubic(u) == cubic(M)+mixed+cubic(w), 'complete cubic decomposition')
        require(linear_cubic_term(r, M) == 0,
                'horizontally constant gradient contribution cancels before estimation')
        require(inner(M, F)+inner(w, cross) == 0,
                'internal mean forcing has equal and opposite fluctuation work')
        require(mixed == derivative_pair(w, cross)+derivative_pair(M, F),
                'both sides of the enstrophy transfer remain')
        require(gradient_norm_squared(u) == gradient_norm_squared(M)+gradient_norm_squared(w),
                'mean and fluctuation gradient energies are orthogonal')
        require(second_gradient_squared(u) == second_gradient_squared(M)+second_gradient_squared(w),
                'complete second-gradient dissipation is orthogonal')
        require(gradient_norm_squared(w) == gradient_norm_squared(r)+gradient_norm_squared(z),
                'horizontal constant and oscillating gradients are orthogonal')
        nu = Q(2, 7)
        rhs = subtract(Nu, vector_scale(nu, minus_laplacian(u)))
        require(2*derivative_pair(u, rhs)+2*nu*second_gradient_squared(u) == 2*cubic(u),
                'full positive-viscosity enstrophy balance')
        records.append({'mean_stretching': str(cubic(M)), 'mixed_stretching': str(mixed),
                        'fluctuation_stretching': str(cubic(w)),
                        'mean_energy_source': str(inner(M, F))})

    # This is the initial fluctuation of the existing actual refeeding history.
    # For ANY z-independent reference and positive viscosity, its linear
    # fluctuation tangent still has kz=+/-1, so its cubic variation is zero.
    linear = vector_add(bilinear(M0, w0), bilinear(w0, M0))
    viscous = vector_scale(Q(-2, 7), minus_laplacian(w0))
    require(linear_cubic_term(w0, linear) == 0, 'reference does not alter the first self-cubic jet')
    require(linear_cubic_term(w0, viscous) == 0, 'viscosity does not alter the first self-cubic jet')
    require(cubic(w0) == 0, 'initial single-vertical-band cubic is zero')
    require(second_gradient_squared(w0) == Q(631, 20), 'initial second-gradient dissipation')
    first_mean = linear_cubic_term(w0, mean_source)
    first_side = linear_cubic_term(w0, side_source)
    require(first_mean == Q(-3283, 10000), 'generated mean first return is depleting here')
    require(first_side == Q(6252773, 5460000) > 0,
            'new non-mean outputs produce positive self-stretching immediately')
    require(first_mean+first_side == linear_cubic_term(w0, source),
            'all first nonlinear returns are accounted for')
    return records, {'initial_self_stretching': '0', 'mean_return': str(first_mean),
                     'fluctuation_return': str(first_side),
                     'initial_second_gradient_energy': '631/20',
                     'physical_scaling': 'g(w(t)) = epsilon^4 * fluctuation_return * t + O(t^2)'}


def scalar_checks():
    nu, C, A, x, y = s.symbols('nu C A x y', positive=True)
    zero = lambda q, label: require(s.expand(q) == 0, label)
    zero(nu*y*y/2+C*C*A*A*x*x/(2*nu)-C*A*x*y
         -(nu*y-C*A*x)**2/(2*nu), 'complete viscous absorption square')
    a, Z, R, P, G, g, loss = s.symbols('a Z R P G g loss', real=True)
    Zrate = 2*g+a*Z-s.Rational(3, 2)*nu*P-loss
    Rrate = -2*g+nu*P/2
    discounted_rate = -a*G*(Z+R)+G*(Zrate+Rrate)
    zero(discounted_rate+nu*G*P+G*(a*R+loss),
         'remaining self-stretching reserve cancels without resetting')
    M, beta = s.symbols('M beta', real=True)
    Zrate = 2*g-s.Rational(3, 2)*nu*P+beta*M*Z-loss
    relative_rate = Zrate+Rrate-beta*Z*(Z+R)
    zero(relative_rate+nu*P+beta*((Z-M)*Z+Z*R)+loss,
         'actual kinetic-loss exponential pays the evolving mean coefficient')
    zero(2*nu*(C*C/(4*nu*nu))-C*C/(2*nu), 'kinetic compensation price')
    return 'exp(C^2 E/(4nu^2))*(Z+R); R is the still-open self-stretching reserve'


if __name__ == '__main__':
    fixtures, first_return = exact_checks()
    print(json.dumps({'fixtures': fixtures, 'first_return': first_return,
                     'reserve': scalar_checks(),
                     'scope': 'periodic actual evolving mean; no independent-reference or smallness hypothesis',
                     'status': 'exact finite algebra; anisotropic estimate and PDE interval conclusions analytic'}, indent=2))
