#!/usr/bin/env python3
"""Explicit future pressure payment after a certified Wiener-small seam.

The actual Fourier NS inequalities and preservation of the inherited impulse
are analytic in README.md. This checks the reserve and envelope algebra;
it does not certify a numerical seam or arbitrary-data entry into the region.
"""

import json
import mpmath as mp
import sympy as s


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def tail_radius(a, nu):
    """Future pathwise pressure-impulse allowance, in period-2pi units."""
    a, nu = mp.mpf(a), mp.mpf(nu)
    require(0 <= a < nu, 'The actual Wiener norm must be strictly below viscosity')
    return -nu*mp.log1p(-a/nu)-a


def envelope_floor(a_now, d_limit):
    """For all future a>=a_now and 0<=d<=d_limit, a^2/(a+d)>=this."""
    require(a_now > 0 and d_limit >= 0, 'Positive envelope stock and nonnegative depletion bound')
    return a_now*a_now/(a_now+d_limit)


def exact_checks():
    a, nu, b, force = s.symbols('a nu b force', positive=True)
    R = nu*s.log(nu/(nu-a))-a
    require(s.simplify(s.diff(R, a)-a/(nu-a)) == 0, 'Exact pressure-reserve slope')
    require(s.simplify(R.subs(a, 0)) == 0, 'Zero future resource at zero velocity')
    require(s.simplify(s.diff(R, a)*(-(nu-a)*b)+a*b) == 0,
            'The Fourier dissipative loss pays the full pressure gradient')
    require(s.simplify(s.diff(R, a)*(-(nu-a)*b+force)+a*b-a*force/(nu-a)) == 0,
            'An external force leaves its explicit unpaid positive term')
    require(s.limit(R/a**2, a, 0, dir='+') == 1/(2*nu), 'Small-state allowance is quadratic')
    x, y, d, D = s.symbols('x y d D', nonnegative=True)
    difference = x*x*(y+D)-y*y*(x+d)
    positive = (x-y)*(x*y+D*(x+y))+y*y*(D-d)
    require(s.expand(difference-positive) == 0, 'Future-envelope floor needs no rate monotonicity')
    # Inherited and future impulses can point in the same direction.
    # Their fourth powers cannot be added as though they were independent.
    inherited, future = s.symbols('inherited future', nonnegative=True)
    cross = 4*inherited**3*future+6*inherited**2*future**2+4*inherited*future**3
    require(s.expand((inherited+future)**4-inherited**4-future**4-cross) == 0,
            'All inherited/future mixed costs remain in the composed allowance')
    return dict(status='all exact reserve checks passed',
                region='A=sum_{k!=0}|u_hat(k)| < nu on the period-2pi torus',
                reserve='R(A)=nu log(nu/(nu-A))-A',
                physical_bound='d/dt R(A(t))+||grad p(t)||_infinity <= 0',
                inherited_history='Phi(t)^(1/4) <= Phi(s)^(1/4)+R(A(s))',
                future_envelope_floor='a(s)^2/(a(s)+d_infinity)',
                scope='Analytic physical handoff; actual seam and finite-prefix enclosure remain obligations')


def envelope_checks():
    from fractions import Fraction as Q
    import paired_stretching_history as e
    from pressure_impulse_payment import history
    from pressure_impulse_envelope import polynomial_interval
    coefficients = history(1)
    a, b = coefficients[12], coefficients[14]
    da, db = e.derivative(a), e.derivative(b)
    # At nu=1/4 and physical time12 the coefficient clock equals3.
    # Positive factors leave this numerator as the sign of B_nu'.
    numerator = e.add(e.multiply(a, da), e.scale(16, e.add(
        e.multiply(a, db), e.scale(-2, e.multiply(da, b)))))
    lo, hi = polynomial_interval(numerator, Q(3))
    require(lo <= hi < 0, 'The candidate envelope itself is not always increasing')
    scale = 10**60
    upper = Q(hi.numerator*scale//hi.denominator+1, scale)
    require(hi < upper < 0, 'A compact rational upper bound preserves the strict sign')
    a_lo, _ = polynomial_interval(a, Q(3))
    a_lo *= 4**8
    d_limit = -4**10*b[(0, 0)]
    floor_lo = envelope_floor(a_lo, d_limit)
    require(floor_lo > Q(1647, 2000), 'A rational lower floor holds for every time after twelve')
    # Certified seam box: A<=1/10, Phi<=2/5 at viscosity1/4.
    # -log(1-r) is bounded by its positive series and a geometric tail.
    r, order = Q(2, 5), 12
    log_upper = sum((r**j/j for j in range(1, order+1)), Q(0)) \
        +r**(order+1)/((order+1)*(1-r))
    require(Q(1, 4)*log_upper-Q(1, 10) < Q(7, 250), 'The future impulse costs less than .028')
    require(Q(2, 5) < Q(4, 5)**4, 'The inherited fourth root costs less than .8')
    require((Q(4, 5)+Q(7, 250))**4 < Q(4, 5) < floor_lo,
            'The explicit seam box pays the full inherited-plus-future fourth moment')
    return dict(viscosity='1/4', time=12, coefficient_clock=3,
                numerator_upper=str(upper), sign='strictly negative by rational exponential enclosure',
                future_envelope_floor_lower='1647/2000',
                sufficient_actual_seam={'velocity_wiener_upper': '1/10', 'phi_upper': '2/5'},
                completed_bound_upper='4/5',
                consequence='The seam box pays the tail; its physical verification and preceding history remain open')


if __name__ == '__main__':
    print(json.dumps(dict(reserve=exact_checks(), envelope=envelope_checks()), indent=2))
