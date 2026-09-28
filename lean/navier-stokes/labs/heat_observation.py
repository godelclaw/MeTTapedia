#!/usr/bin/env python3
"""Exact checks for a heat/HJB observation, its hidden mode, and fluid residual."""
import json
import sympy as s


def require_zero(expression, label):
    value = s.simplify(s.expand_trig(expression))
    if value != 0:
        raise AssertionError((label, value))


t, theta = s.symbols('t theta', real=True)
nu, epsilon = s.symbols('nu epsilon', positive=True)
a, b = s.symbols('a b', real=True)
phi = 1 + a*s.exp(-nu*t)*s.sin(theta) + b*s.exp(-4*nu*t)*s.sin(2*theta)
W = -2*nu*s.log(phi)
require_zero(s.diff(phi, t)-nu*s.diff(phi, theta, 2), 'heat equation')
require_zero(s.diff(W, t)-nu*s.diff(W, theta, 2)
             + s.diff(W, theta)**2/2, 'HJB equation where phi > 0')
v = s.simplify(-s.diff(W, theta).subs(theta, 0))
expected_v = 2*nu*(a*s.exp(-nu*t)+2*b*s.exp(-4*nu*t))
require_zero(v-expected_v, 'identity-gradient observation')
hidden_force = s.simplify(s.diff(v, t)+nu*v)
require_zero(hidden_force+12*nu**2*b*s.exp(-4*nu*t), 'hidden force')
require_zero(s.diff(hidden_force, t)+4*nu*hidden_force, 'hidden force evolution')
require_zero(s.diff(v, t, 2)+5*nu*s.diff(v, t)+4*nu**2*v, 'eliminated memory')

counter = {a: epsilon, b: -epsilon/2}
require_zero(v.subs(counter).subs(t, 0), 'same zero initial observation')
require_zero(s.diff(v, t).subs(counter).subs(t, 0)-6*nu**2*epsilon,
             'nonzero initial observed acceleration')
require_zero(hidden_force.subs(counter)-6*nu**2*epsilon*s.exp(-4*nu*t),
             'persistent explicit fluid residual')

x, y, z = s.symbols('x y z', real=True)
physical = s.Matrix([v*s.sin(y), 0, 0])
coords = [x, y, z]
divergence = sum(s.diff(physical[j], coords[j]) for j in range(3))
convection = physical.jacobian(coords)*physical
laplacian = physical.applyfunc(lambda f: sum(s.diff(f, q, 2) for q in coords))
residual = physical.diff(t)+convection-nu*laplacian
require_zero(divergence, 'incompressibility')
for j in range(3):
    require_zero(convection[j], 'zero shear convection')
    require_zero(residual[j]-hidden_force*s.Matrix([s.sin(y), 0, 0])[j],
                 'literal Navier-Stokes residual')
curl_residual = s.diff(residual[1], x)-s.diff(residual[0], y)
require_zero(curl_residual+hidden_force*s.cos(y), 'residual is not a pressure gradient')
require_zero(hidden_force.subs(b, 0), 'invariant unforced shear sector')
require_zero(s.diff(v**2/4, t)+nu*v**2/2-v*hidden_force/2,
             'physical kinetic energy balance includes hidden force work')

c, d = s.symbols('c d', real=True)
Q = c**2+d**2
Qdot = s.diff(Q, c)*(-nu*c)+s.diff(Q, d)*(-4*nu*d)
require_zero(Qdot+2*nu*c**2+8*nu*d**2, 'nonnegative hidden-state reserve')
require_zero(20*nu**2*Q-(2*nu*(c+2*d))**2-4*nu**2*(2*c-d)**2,
             'observation controlled by full reserve')

# Nonconstant, noncommuting frame: lower jets vanish, leaving only the
# third-order principal symbol. No constant-frame simplification is used.
q = s.Matrix([x, y, z])
frames = [s.Matrix([1, 0, y]), s.Matrix([0, 1, -x]), s.Matrix([x, -y, 1])]
ell = s.Matrix([1, 2, -1])
F = epsilon*(ell.dot(q))**3
origin = {x: 0, y: 0, z: 0}
def D(frame, expression):
    return sum(frame[j]*s.diff(expression, coords[j]) for j in range(3))
LF = sum(D(frame, D(frame, F)) for frame in frames)
GammaF = sum(D(frame, F)**2 for frame in frames)
S = sum(frame.dot(ell).subs(origin)**2 for frame in frames)
# A nonzero seed also has the same acceleration difference: the perturbation
# leaves both its first and second jets unchanged at the observation point.
seed = x+2*y-z+x*y+y*z+x**2/2
def hjb(potential):
    return (nu*sum(D(frame, D(frame, potential)) for frame in frames)
            - sum(D(frame, potential)**2 for frame in frames)/2)
generator_difference = hjb(seed+F)-hjb(seed)
observed_jet = []
for frame in frames:
    require_zero(D(frame, F).subs(origin), 'vanishing initial first jet')
    actual = (-D(frame, nu*LF-GammaF/2)).subs(origin)
    predicted = -6*nu*epsilon*S*frame.dot(ell).subs(origin)
    require_zero(actual-predicted, 'third-jet obstruction')
    require_zero((-D(frame, generator_difference)).subs(origin)-predicted,
                 'third-jet perturbation of a nonzero seed')
    observed_jet.append(str(s.factor(actual)))

# For any m, the analytic odd perturbation sin(theta)^(2m+3) leaves the
# first m observed time derivatives zero. The next one is nonzero.
# Check the finite Laurent expansion independently of the moment sums.
Z = s.symbols('Z', nonzero=True)
late_jets = []
for m in range(13):
    power = 2*m+3
    r = m+1
    coeffs = {power-2*j: s.Rational((-1)**(r-j)*s.binomial(power, j), 2**(2*r))
              for j in range(r+1)}
    laurent = sum(c*(Z**k-Z**(-k))/(2*s.I) for k, c in coeffs.items())
    require_zero(laurent-((Z-Z**(-1))/(2*s.I))**power, 'odd-power Fourier identity')
    require_zero(sum(abs(c) for c in coeffs.values())-1, 'positive heat-data margin')
    for order in range(m+1):
        require_zero(sum(c*(-1)**order*k**(2*order+1) for k, c in coeffs.items()),
                     'hidden higher time jet')
    next_moment = sum(c*(-1)**(m+1)*k**(2*m+3) for k, c in coeffs.items())
    require_zero(next_moment-s.factorial(power), 'first nonzero observed time jet')
    late_jets.append({'matched_time_derivatives_through': m,
                      'next_derivative_divided_by_2_epsilon_nu_power': str(next_moment)})

# Both chart coordinates have derivative one at the origin. A cutoff equal
# to one nearby leaves these jets unchanged and makes the potential bounded.
amplitude = s.symbols('amplitude', real=True)
chart = theta+epsilon*theta**3
chart_potential = amplitude*chart
require_zero(s.diff(chart, theta).subs(theta, 0)-1, 'normalized chart')
require_zero((-s.diff(chart_potential, theta)).subs(theta, 0)+amplitude,
             'chart change preserves initial observation')
chart_acceleration = (-s.diff(nu*s.diff(chart_potential, theta, 2)
                             - s.diff(chart_potential, theta)**2/2, theta)).subs(theta, 0)
require_zero(chart_acceleration+6*nu*amplitude*epsilon,
             'normalized chart change changes acceleration')

print(json.dumps({
    'status': 'all exact checks passed',
    'positive_data_condition': 'nu > 0, t >= 0, |a|+|b| < 1; '
                               'counterexample 0 < epsilon < 2/3',
    'observed_velocity': str(v),
    'hidden_force': str(hidden_force),
    'counterexample_initial_velocity': '0',
    'counterexample_initial_acceleration': '6*nu**2*epsilon',
    'full_state_reserve_derivative': str(s.factor(Qdot)),
    'third_jet_acceleration_coefficients': observed_jet,
    'normalized_chart_acceleration': str(chart_acceleration),
    'finite_time_jet_checks': late_jets,
    'scope': 'exact scalar heat/HJB model and periodic fluid residual; '
             'general frame-jet argument is analytic, not Lean-certified',
}, indent=2))
