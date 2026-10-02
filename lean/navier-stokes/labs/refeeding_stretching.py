#!/usr/bin/env python3
"""Exact derivative-level certificates for stretching during parent refeeding.

The analytic comparison retains the generated vertical mean and the actual
annular reference. The script checks finite Fourier identities and rational
bounds; the nonlinear interval argument is not Lean-certified.
"""

import json
from fractions import Fraction as Q

import pressure_history_source as f
from cellular_parent_refeeding import seed
from cellular_transfer_reversal import (
    ZERO, T, add, scale, linear_operator, sqrt_upper, force, real_field, require,
)
from reciprocal_pattern_cycles import inner, mode, vector_add, vector_scale


def h1_squared(r, laplacian=False):
    return 2*sum((x*x+y*y+2)*(x*x+y*y+1)**(2 if laplacian else 0)*
                 sum(a*a for a in z) for (x, y), z in r.items())


def quadratic_stretching(r):
    linear = linear_operator(r)
    return force(r)+2*sum((x*x+y*y+1)*sum(a*b for a, b in zip(z, linear.get((x, y), ZERO)))
                          for (x, y), z in r.items())


def nonlinear(u):
    pressure = f.green(f.trace(f.matmul(f.jac(u), f.jac(u))))
    return [f.add(f.scale(-1, f.adv(u, a)), f.scale(-1, f.diff(pressure, j)))
            for j, a in enumerate(u)]


def cubic(u):
    omega = f.curl(u)
    return inner(omega, f.matvec(f.jac(u), omega))


def vertical_mean(u):
    return [{k: z for k, z in a.items() if k[2] == 0} for a in u]


def linear_cubic_term(u, y):
    omega, eta = f.curl(u), f.curl(y)
    return (inner(eta, f.matvec(f.jac(u), omega))
            + inner(omega, f.matvec(f.jac(y), omega))
            + inner(omega, f.matvec(f.jac(u), eta)))


def check_generated_mean():
    v = [mode((0, 1, 0), 1, True), mode((1, 0, 0), -1, True), {}]
    receiver = [{}, {}, f.add(mode((1, 1, 0), Q(2, 3)),
                             mode((2, -1, 0), Q(1, 5), True))]
    u = vector_add(v, receiver)
    r = real_field(seed())
    require(vertical_mean(r) == [{}, {}, {}], 'initial vertical mean is zero')
    generated = vertical_mean(nonlinear(r))
    require(any(generated), 'the full nonlinearity actually generates a vertical mean')
    for y in [vector_add(r, generated), f.fixture()]:
        require(linear_cubic_term(u, y) == linear_cubic_term(u, vertical_mean(y)),
                'receiver-linear stretching retains precisely the vertical mean')
        require(cubic(vector_add(u, y))-cubic(u)
                == linear_cubic_term(u, y)+linear_cubic_term(y, u)+cubic(y),
                'complete mixed receiver expansion')
        ly = [f.add(a, f.scale(-1, b), f.scale(-1, c))
              for a, b, c in zip(nonlinear(vector_add(u, y)), nonlinear(u), nonlinear(y))]
        my = vertical_mean(y)
        lm = [f.add(a, f.scale(-1, b), f.scale(-1, c))
              for a, b, c in zip(nonlinear(vector_add(u, my)), nonlinear(u), nonlinear(my))]
        for a, b in zip(vertical_mean(ly), lm):
            f.equal(a, b, 'vertical averaging commutes with full projected linearization')


def check_complete_expansion():
    v = [mode((0, 1, 0), 1, True), mode((1, 0, 0), -1, True), {}]
    for r in [real_field(seed()), f.fixture()]:
        f.equal(f.trace(f.jac(r)), {}, 'complete test field is solenoidal')
        nr, nv = nonlinear(r), nonlinear(v)
        linear = [f.add(a, f.scale(-1, b), f.scale(-1, c))
                  for a, b, c in zip(nonlinear(vector_add(v, r)), nv, nr)]
        minus_lap = [f.scale(-1, f.lap(a)) for a in r]
        coefficient = inner(minus_lap, linear)+inner(v, nr)
        require(inner(v, linear) == 0, 'full linear stretching variation vanishes')
        for amplitude, epsilon in [(Q(1), Q(1)), (Q(3, 2), Q(1, 7))]:
            u = vector_add(vector_scale(amplitude, v), vector_scale(epsilon, r))
            require(cubic(u) == amplitude*epsilon**2*coefficient+epsilon**3*cubic(r),
                    'complete cubic expansion retains canonical pressure and all terms')
    r = real_field(seed())
    require(cubic(r) == 0, 'three vertical frequencies +/-1 cannot sum to zero')
    require(cubic(vector_add(v, r)) == quadratic_stretching(seed()),
            'independent physical-vorticity check of the sparse coefficient')


def main():
    check_complete_expansion()
    check_generated_mean()
    c = seed()
    require(quadratic_stretching(c) == Q(-3, 40), 'initial stretching is depleting')
    values = [{}, {}]
    laplacian_h1 = Q(0)
    for j in range(17):
        values = [add(p, scale(t**j, c)) for p, t in zip(values, [T/2, T])]
        laplacian_h1 += sqrt_upper(h1_squared(c, True))*T**j
        c = scale(Q(1, j+1), linear_operator(c))
    require(laplacian_h1 <= 116, 'uniform Laplacian H1 norm')
    require(h1_squared(c)*T**34 <= Q(1, 1500)**2, 'complete H1 residual')
    for p in values:
        require(h1_squared(p) <= Q(11, 4)**2, 'H1 observation bound')
    require(quadratic_stretching(values[0]) >= Q(8, 25), 'positive middle coefficient')
    require(quadratic_stretching(values[1]) >= Q(9, 10), 'positive refeeding coefficient')
    error = 9*Q(1, 1500)+Q(1, 1000)
    require(error == Q(7, 1000), 'full derivative-level comparison error')
    quadratic_error = 3*(Q(11, 2)+error)*error
    mixed_error = Q(1, 100)
    require(Q(-3, 40)+mixed_error <= Q(-1, 20), 'actual initial excess is negative')
    require(Q(8, 25)-quadratic_error-mixed_error >= Q(3, 16),
            'actual middle excess is positive')
    require(Q(9, 10)-quadratic_error-mixed_error >= Q(3, 4),
            'actual refeeding excess is positive')
    print(json.dumps({
        'clock_times': ['0', '3/8', '3/4'], 'polynomial_degree': 16,
        'H1_residual_integral_bound': '1/1500', 'Laplacian_H1_bound': '116',
        'observation_H1_bound': '11/4', 'actual_H1_error_bound': str(error),
        'quadratic_stretching_bounds': ['=-3/40', '>=8/25', '>=9/10'],
        'quadratic_error_bound': str(quadratic_error),
        'required_mixed_reference_error_bound': '1/100',
        'actual_reference_subtracted_stretching_bounds': ['<=-1/20', '>=3/16', '>=3/4'],
        'stretching_normalization': '(g(u)-g(U))/(a epsilon^2)',
        'generated_mean_bound': '||vertical_mean(y)||H1<=delta J; delta=epsilon/A',
        'generated_mean_checks': 'nonzero generation; averaging commutes; complete mixed cubic expansion',
        'scope': 'additional explicit small-parameter conditions in README.md; same full nonlinear history',
        'status': 'exact finite identities and bounds; nonlinear identification and existence analytic'
    }, indent=2))


if __name__ == '__main__':
    main()
