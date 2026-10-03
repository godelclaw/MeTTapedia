#!/usr/bin/env python3
"""A retained-label pressure allowance can pass initially and fail later.

Exact checks cover the cellular Euler reference, its paired material
histories, rational crossing margins, and reciprocal three-dimensional
NS jets. Smooth labels, positive viscosity and stability on an actual
solution interval are justified analytically in README.md. This is not
a numerical blowup construction or a Lean certificate.
"""

import json
from fractions import Fraction as Q
from math import factorial

import sympy as s


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(expression, label):
    reduced = s.cancel(s.expand(expression))
    if reduced != 0:
        reduced = s.cancel(s.trigsimp(s.expand_trig(reduced)))
    require(reduced == 0, label)


def cellular_history():
    x, y, z, t, c = s.symbols('x y z t c', real=True)
    coordinates = (x, y, z)
    U = s.Matrix([s.sin(y), s.sin(x), 0])
    p = s.cos(x)*s.cos(y)
    grad = lambda f: s.Matrix([s.diff(f, v) for v in coordinates])
    lap = lambda f: sum(s.diff(f, v, 2) for v in coordinates)
    zero(U.jacobian(coordinates).trace(), 'Incompressible cellular reference')
    for entry in U.jacobian(coordinates)*U+grad(p):
        zero(entry, 'Exact steady Euler equation with canonical pressure')
    for entry in U.applyfunc(lap)+U:
        zero(entry, 'The viscous reference is exp(-nu*t)*U')
    sine_x, sine_y = s.symbols('sine_x_squared sine_y_squared')
    zero(grad(p).dot(grad(p))
         -(s.sin(x)**2+s.sin(y)**2-2*s.sin(x)**2*s.sin(y)**2),
         'The pressure-gradient square has the stated scalar form')
    zero(1-(sine_x+sine_y-2*sine_x*sine_y)
         -((1-sine_x)*(1-sine_y)+sine_x*sine_y),
         'The reference pressure gradient is bounded by one')

    # On x=y, x'=sin x. If c=cos x(0), the speed ratio is h(t).
    h = 1/(s.cosh(t)-c*s.sinh(t))
    evolved_cos = (c*s.cosh(t)-s.sinh(t))/(s.cosh(t)-c*s.sinh(t))
    require(s.cancel((s.diff(h, t)-h*evolved_cos).rewrite(s.exp)) == 0,
            'Exact separatrix speed equation')
    require(s.cancel((s.diff(evolved_cos, t)+(1-c*c)*h*h).rewrite(s.exp)) == 0,
            'Exact separatrix cosine equation')
    # Paired original labels differ by (pi,pi,pi), reversing U. Their
    # even fourth moment, divided by 4*sin(x(0))^4, is the even part.
    speed_jet = s.series(h, t, 0, 6).removeO()
    fourth = s.series((1-speed_jet)**4, t, 0, 9).removeO().expand()
    A = c**4
    B = c*c*(60*c**4-56*c*c+9)/6
    D = (2800*c**8-4800*c**6+2416*c**4-340*c*c+5)/80
    for order, coefficient in ((4, A), (6, B), (8, D)):
        zero(fourth.coeff(t, order)-coefficient,
             'Complete even material pressure coefficient')
    for order in range(4):
        zero(fourth.coeff(t, order), 'No premature pressure fourth moment')

    chosen = s.Rational(5, 9)
    values = [s.factor(v.subs(c, chosen)) for v in (A, B, D)]
    a, b, d = values
    gap = s.factor(d-b*b/a)
    require(a > 0 and b < 0 and gap < 0,
            'The component allowance has a strictly favorable initial gap')
    require(values == [s.Rational(625, 6561), s.Rational(-140425, 1062882),
                       s.Rational(124769021, 688747536)],
            'Exact chosen coefficients')
    require(gap == s.Rational(-1433735, 688747536), 'Exact initial margin')

    # T=log4: cosh(T)=17/8 and sinh(T)=15/8. These rational values
    # avoid evaluating logarithms or transcendental functions numerically.
    ch, sh, q = Q(17, 8), Q(15, 8), Q(5, 9)
    require(ch*ch-sh*sh == 1 and ch+sh == 4, 'Exact exponential time')
    plus, minus = 1/(ch-q*sh), 1/(ch+q*sh)
    require((plus, minus) == (Q(12, 13), Q(6, 19)), 'Exact two material paths')
    actual = ((1-plus)**4+(1-minus)**4)/2
    upper_time = Q(7, 5)
    lower_exp = sum(upper_time**n/factorial(n) for n in range(6))
    require(lower_exp > 4, 'Positive exponential series proves log4<7/5')
    aa, bb = Q(str(a)), Q(str(b))
    envelope_upper = aa*upper_time**4/(1-bb/aa*upper_time**2)
    later_gap = actual-envelope_upper
    require(later_gap > Q(1, 100), 'A strict later crossing, not just a derivative')
    require(later_gap == Q(1268944547747833, 113505838798158963),
            'Exact lower bound for the later normalized gap')
    k = s.symbols('k', positive=True)
    zero(s.diff(t**4/(1+k*t*t), t)-2*t**3*(2+k*t*t)/(1+k*t*t)**2,
         'The reference envelope increases with positive time')
    factor = 4*(1-q*q)**2
    return dict(cos_initial_angle=str(q), time='log(4)',
                normalization='Divide by 4*sin(theta)^4',
                coefficients=list(map(str, values)), initial_gap=str(gap),
                actual_normalized=str(actual), envelope_upper=str(envelope_upper),
                later_gap_lower=str(later_gap),
                physical_gap_lower=str(factor*later_gap))


def complete_three_dimensional_jets():
    x, y, z, d, nu = s.symbols('x y z delta nu', real=True)
    coordinates = (x, y, z)
    grad = lambda f: s.Matrix([s.diff(f, q) for q in coordinates])
    lap = lambda f: sum(s.diff(f, q, 2) for q in coordinates)
    curl = lambda v: s.Matrix([s.diff(v[2], y)-s.diff(v[1], z),
                               s.diff(v[0], z)-s.diff(v[2], x),
                               s.diff(v[1], x)-s.diff(v[0], y)])
    U = s.Matrix([s.sin(y)+d*s.sin(z), s.sin(x), d*s.sin(x)])
    B = U.jacobian(coordinates)
    p = s.cos(x)*s.cos(y)+d*d*s.cos(x)*s.cos(z)
    zero(B.trace(), 'Literal three-dimensional incompressibility')
    zero(lap(p)+s.trace(B*B), 'Complete initial canonical pressure')
    N = -B*U-grad(p)
    expected = s.Matrix([0, -d*s.sin(z)*s.cos(x), -d*s.sin(y)*s.cos(x)])
    for entry in N-expected:
        zero(entry, 'New reciprocal outputs are retained')
    p1 = s.Rational(2, 3)*s.sin(x)*(d*d*s.sin(y)*s.cos(z)+d*s.sin(z)*s.cos(y))
    zero(lap(p1)+2*s.trace(B*N.jacobian(coordinates)),
         'The generated pressure is canonical, not discarded')
    tangent = nu*U.applyfunc(lap)+N
    pt = -2*nu*p+p1
    zero(lap(pt)+2*s.trace(B*tangent.jacobian(coordinates)),
         'Complete positive-viscosity pressure derivative')
    second = (nu*tangent.applyfunc(lap)-tangent.jacobian(coordinates)*U
              -B*tangent-grad(pt))
    return_to_first = d*s.cos(x)*(d*s.sin(y)*s.cos(z)+s.sin(z)*s.cos(y))/3
    zero(second[0]-nu*nu*U[0]-return_to_first,
         'Generated parents return into the first velocity component')
    omega, omega_t = curl(U), curl(tangent)
    stretching = omega.dot(B*omega)
    zero(stretching, 'The original scalar stretching is zero')
    derivative = (omega_t.dot(B*omega)+omega.dot(tangent.jacobian(coordinates)*omega)
                  +omega.dot(B*omega_t))
    # Normalized integration is exact and keeps every Fourier product.
    average = s.integrate(s.expand(derivative), (x, -s.pi, s.pi),
                          (y, -s.pi, s.pi), (z, -s.pi, s.pi))/(2*s.pi)**3
    zero(average-d*d/2, 'Positive first integrated stretching at every viscosity')
    for entry in U.subs({x: x+s.pi, y: y+s.pi, z: z+s.pi})+U:
        zero(entry, 'The same paired label removes odd amplitudes in 3D')
    return dict(datum=list(map(str, U)), pressure=str(p),
                nonlinear_outputs=list(map(str, expected)), pressure_renewal=str(p1),
                first_component_return=str(return_to_first),
                stretching_initial='0', stretching_time_derivative='delta^2/2',
                scope='Exact full unforced jets; fixed-interval persistence is analytic')


def retained_defect():
    a, b, ap, bp = s.symbols('a b ap bp', real=True)
    candidate = a*a/(a-b)
    rate = ((a*a-2*a*b)*ap+a*a*bp)/(a-b)**2
    zero(s.diff(candidate, a)*ap+s.diff(candidate, b)*bp-rate,
         'Complete rational allowance derivative')
    return dict(allowance_rate=str(rate),
                actual_rate='(4/m) integral grad(p) dot T_chi; m is the fixed initial label mass',
                seam='Carry rho,I,Q,T,K and the existing value gap without resetting')


if __name__ == '__main__':
    print(json.dumps(dict(reference=cellular_history(),
        actual_three_dimensional_jets=complete_three_dimensional_jets(),
        retained_defect=retained_defect(), status='All exact checks passed',
        limitation='A component envelope fails; no singularity or full-budget refutation'),
        indent=2))
