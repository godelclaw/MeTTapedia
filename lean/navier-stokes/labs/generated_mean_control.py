#!/usr/bin/env python3
"""Bellman payment for the generated mean in the actual cellular NS history.

Checks the scalar control algebra and its non-resetting composition. The
domination of actual NS trajectories uses the analytic H1 source estimate
in README.md. The scalar maximizing control is not asserted to be a fluid.
"""

import json
import sympy as s

from reciprocal_pattern_cycles import require
from refeeding_stretching import check_generated_mean


def zero(expr, label):
    require(s.simplify(s.expand(expr)) == 0, label)


def main():
    k, h, n, beta, source, loss = s.symbols('k h n beta source loss', positive=True)
    alpha = (s.exp(k*h)-1)/k
    bravo = (s.exp(k*h)-1-k*h)/k**2
    value = alpha*n+beta*bravo
    zero(s.diff(alpha, h)-(1+k*alpha), 'adjoint equation')
    zero(s.diff(bravo, h)-alpha, 'integrated adjoint')
    zero(s.diff(value, h)-(n+(k*n+beta)*s.diff(value, n)), 'backward Bellman identity')
    rate = -s.diff(value, h)+s.diff(value, n)*(k*n+source-loss)
    zero(rate+n+alpha*(beta-source+loss), 'complete source and loss slack')
    zero(value.subs(h, 0), 'zero terminal value')
    zero(s.limit(alpha, k, 0)-h, 'zero-growth adjoint limit')
    zero(s.limit(bravo, k, 0)-h**2/2, 'zero-growth source allowance limit')

    # Exponential propagation composes multiplicatively. Keeping E1,E2
    # symbolic checks the whole law without selecting a time discretization.
    E1, E2, h1, h2 = s.symbols('E1 E2 h1 h2', positive=True)
    a1, a2 = (E1-1)/k, (E2-1)/k
    b1, b2 = (E1-1-k*h1)/k**2, (E2-1-k*h2)/k**2
    a12 = (E1*E2-1)/k
    b12 = (E1*E2-1-k*(h1+h2))/k**2
    zero(a12-a1-E1*a2, 'adjoint composition')
    zero(b12-b1-b2-a1*a2, 'retained cross-interval memory')
    mid = E1*n+source*a1
    first_cost = a1*n+source*b1
    terminal = a2*mid+beta*b2
    zero(a12*n+beta*b12-first_cost-terminal-(beta-source)*(b1+a1*a2),
         'one-seam Bellman payment with complete state')
    zero((beta*b12)-(beta*b1+beta*b2)-beta*a1*a2,
         'resetting a zero-start mean discards the cross term')

    # A third interval tests associativity and the inherited mean, not
    # pairwise matching of labels. Saturating controls attain the value.
    E3, h3 = s.symbols('E3 h3', positive=True)
    n1 = E1*n+beta*a1
    n2 = E2*n1+beta*a2
    a3, b3 = (E3-1)/k, (E3-1-k*h3)/k**2
    costs = a1*n+beta*b1+a2*n1+beta*b2+a3*n2+beta*b3
    direct = (E1*E2*E3-1)*n/k+beta*(E1*E2*E3-1-k*(h1+h2+h3))/k**2
    zero(costs-direct, 'three-interval optimal cost with original mean history')

    # This is the physical scaling that removes the inverse perturbation
    # amplitude from the receiver-linear stretching cost.
    epsilon, A, a, rho, Kw, Gw, m = s.symbols('epsilon A a rho Kw Gw m', positive=True)
    delta = epsilon/A
    ell = 6*rho*Kw+12*rho**2*Gw*Kw
    zero((a*epsilon**2*(ell/delta)*m)/a-epsilon**2*ell*(m/delta),
         'physical-time to original-clock cost conversion')
    check_generated_mean()
    print(json.dumps({
        'value': 'alpha_k(T-sigma) n + beta b_k(T-sigma)',
        'alpha': '(exp(k h)-1)/k',
        'b': '(exp(k h)-1-k h)/k^2',
        'admissible_scalar_history': 'n>=0, n_dot=k n+source-loss, 0<=source<=beta, loss>=0',
        'payment': 'V_dot+n=-alpha*(beta-source+loss)<=0',
        'seam': 'n and original T retained; lost reset term beta alpha(h1) alpha(h2)',
        'physical_map': 'n=||vertical_mean((u-U)/epsilon)||H1/(epsilon/A)',
        'physical_parameters': 'k=C1 V; beta=2 Cb K^2; ell=6rho Kw+12rho^2 Gw Kw',
        'mean_stretching_reserve': 'epsilon^2 ell V',
        'full_excess_reserve': 'epsilon^2 [C0 (T-sigma)+ell V]',
        'C0': '3K^2+12rho Gw K^2+4delta Ce K^3',
        'checks': 'Bellman equation, source/loss slack, two/three seams, zero-growth limit, physical scaling, generated mean',
        'scope': 'actual restricted periodic histories via analytic source bounds; no arbitrary-data budget',
        'status': 'exact symbolic checks; no new Lean theorem; scalar optimizer need not be NS-realizable'
    }, indent=2))


if __name__ == '__main__':
    main()
