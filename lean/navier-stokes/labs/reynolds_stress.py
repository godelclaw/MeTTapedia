#!/usr/bin/env python3
"""Exact local checks for the angular-mean defect calculation.

These polynomial fields test differential identities, not PDE solutions.
The fields are not finite-energy whole-space data. Requires Sympy.
"""
import json
from math import factorial
import sympy as s

x, y, z, r = s.symbols('x y z r', real=True)
c, sn = s.symbols('c sn', real=True)
coords = (x, y, z)
Q = s.Matrix([[c, -sn, 0], [sn, c, 0], [0, 0, 1]])
shift = dict(zip(coords, Q.T * s.Matrix(coords)))


def require_zero(expr, label):
    entries = list(expr) if isinstance(expr, s.MatrixBase) else [expr]
    for e in entries:
        if s.cancel(s.expand(e)) != 0:
            raise ArithmeticError(label + ': ' + str(e))


def avg_poly(expr):
    answer = 0
    for (a, b), coefficient in s.Poly(s.expand(expr), c, sn).terms():
        if a % 2 or b % 2:
            continue
        i, j = a // 2, b // 2
        moment = s.Rational(factorial(2*i)*factorial(2*j),
                            4**(i+j)*factorial(i)*factorial(j)*factorial(i+j))
        answer += moment * coefficient
    return s.expand(answer)


def mean_vector(u):
    return (Q * u.subs(shift, simultaneous=True)).applyfunc(avg_poly)


def mean_tensor(T):
    return (Q * T.subs(shift, simultaneous=True) * Q.T).applyfunc(avg_poly)


def curl(u):
    return s.Matrix([s.diff(u[2], y)-s.diff(u[1], z),
                     s.diff(u[0], z)-s.diff(u[2], x),
                     s.diff(u[1], x)-s.diff(u[0], y)])


def div(u):
    return sum(s.diff(u[i], coords[i]) for i in range(3))


def adv(a, b):
    return b.jacobian(coords) * a


potential = s.Matrix([
    -y*z*z,
    x*z*z+x*x/2+x*y,
    x*y+(x*x+y*y)*(x*x-y*y)+x*z+2*y*z*z+(x*x+y*y)*z,
])
u = curl(potential)
v = mean_vector(u)
w = u-v
require_zero(div(u), 'div u')
require_zero(div(w), 'div w')
require_zero(mean_vector(v)-v, 'P^2=P')
require_zero(mean_vector(w), 'P w=0')
require_zero(mean_vector(adv(u, u))-adv(v, v)-mean_vector(adv(w, w)),
             'actual mean equation')

stress = mean_tensor(w*w.T)
force = -mean_vector(adv(w, w))
stress_force = -s.Matrix([sum(s.diff(stress[i, j], coords[j])
                               for j in range(3)) for i in range(3)])
require_zero(force-stress_force, 'force is minus div stress')
at = lambda e: s.expand(e.subs({x: r, y: 0}, simultaneous=True))
a, b, cc, d, e, f = [at(stress[i, j])
                     for i, j in [(0, 0), (1, 1), (2, 2),
                                  (0, 2), (0, 1), (1, 2)]]
fr = -s.diff(a, r)-(a-b)/r-s.diff(d, z)
fz = -s.diff(d, r)-d/r-s.diff(cc, z)
ftheta = -s.diff(e, r)-2*e/r-s.diff(f, z)
require_zero(at(force[0])-fr, 'radial divergence formula')
require_zero(at(force[1])-ftheta, 'azimuthal divergence formula')
require_zero(at(force[2])-fz, 'axial divergence formula')
require_zero(d.subs(r, 0), 'r-z stress axis trace')
require_zero((a-b).subs(r, 0), 'horizontal stress axis isotropy')

g = at(curl(force)[1])/r
psi = d/r
lifted = (s.diff(psi, r, 2)+3*s.diff(psi, r)/r-s.diff(psi, z, 2)
          +s.diff(cc-a, r, z)/r-s.diff(a-b, z)/r**2)
require_zero(g-lifted, 'lifted potential-vorticity force')

# The same identity with arbitrary differentiable stress components,
# independently of the preceding polynomial sample.
ga, gb, gc, gd = [s.Function(name)(r, z)
                  for name in ['stress_a', 'stress_b', 'stress_c', 'stress_d']]
generic_fr = -s.diff(ga, r)-(ga-gb)/r-s.diff(gd, z)
generic_fz = -s.diff(gd, r)-gd/r-s.diff(gc, z)
generic_g = (s.diff(generic_fr, z)-s.diff(generic_fz, r))/r
generic_lift = (s.diff(gd/r, r, 2)+3*s.diff(gd/r, r)/r
                -s.diff(gd/r, z, 2)+s.diff(gc-ga, r, z)/r
                -s.diff(ga-gb, z)/r**2)
require_zero(generic_g-generic_lift, 'arbitrary-stress lifted identity')
generic_div = s.diff((gc-ga)/r, r)+3*(gc-ga)/r**2
require_zero(generic_div-2*(gc-ga)/r**2-s.diff(gc-ga, r)/r,
             'four-dimensional divergence conversion')

# Independent telescoping and integration-by-parts check in Cartesian space.
ou, ov, ow = curl(u), curl(v), curl(w)
stretch = lambda a: curl(a).dot(adv(curl(a), a))
delta = stretch(u)-stretch(v)
telescoped = ou.dot(adv(ow, u))+ou.dot(adv(ov, w))+ow.dot(adv(ov, v))
require_zero(delta-telescoped, 'stretching telescope')
flux = s.zeros(3, 1)
remainder = 0
for m in range(3):
    for j in range(3):
        coefficient = ov[m]*ou[j]
        flux[m] += w[j]*coefficient
        remainder += w[j]*s.diff(coefficient, coords[m])
    for i in range(3):
        for j in range(3):
            for b_index in range(3):
                coefficient = (s.LeviCivita(i, m, b_index)
                               *s.diff(u[j], coords[i])*ou[j]
                               +s.LeviCivita(j, m, b_index)
                               *ov[i]*s.diff(v[j], coords[i]))
                flux[m] += w[b_index]*coefficient
                remainder += w[b_index]*s.diff(coefficient, coords[m])
require_zero(delta-div(flux)+remainder, 'stretching divergence identity')

# Check the Hardy power-profile constant as a rational-function identity.
eta, alpha = s.symbols('eta alpha', real=True)
bb, dd = 1+eta-alpha, 1-2*eta
norm_sq = (1/dd-2/(dd+bb)+1/(dd+2*bb))/bb**2
require_zero(norm_sq-2/((1-2*eta)*(2-eta-alpha)*(3-2*alpha)),
             'power-profile Hardy norm')
bound_sq = 1/((1-2*eta)*(s.Rational(3, 2)-alpha)**2)
require_zero(bound_sq-norm_sq-2/((3-2*alpha)**2*(2-eta-alpha)),
             'power-profile Hardy slack')

print(json.dumps({
    'status': 'all exact residuals zero',
    'scope': 'local polynomial identities; not Navier-Stokes solutions',
    'mean_velocity': [str(e) for e in v],
    'lifted_force': str(s.cancel(g)),
    'stress_entries_nonzero': sum(e != 0 for e in [a, b, cc, d, e, f]),
    'arbitrary_stress_identity': 'checked by symbolic differentiation',
    'stretching_difference_nonzero': s.expand(delta) != 0,
    'hardy_profile_conditions': '0<=eta<1/2 and alpha<3/2',
}, indent=2))
