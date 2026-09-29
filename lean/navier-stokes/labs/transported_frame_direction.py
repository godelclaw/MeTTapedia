#!/usr/bin/env python3
"""Exact directional quotient identities and an unforced initial-data test."""
import json
import sympy as s


def zero(expr, label):
    result = s.factor(s.trigsimp(s.expand(expr)))
    if result != 0:
        result = s.simplify(result)
    if result != 0:
        raise AssertionError((label, result))


def matrix_zero(matrix, label):
    for i, entry in enumerate(matrix):
        zero(entry, (label, i))


# Independent rational spatial/time jets of the vector and frame equations.
t, x = s.symbols('t x', real=True)
nu, eta = s.symbols('nu eta', positive=True)
M = s.Matrix([[2, 1, 0], [1, 3, 1], [0, 1, 2]])
Q = M.inv()
B = s.Matrix([[1, 2, 3], [-3, 0, 1], [2, -1, -1]])
v = s.Matrix([-2, 1, -5])
P = [s.Matrix([[1, 2, 0], [2, -1, 1], [0, 1, 3]]),
     s.Matrix([[0, 1, -1], [1, 2, 0], [-1, 0, -2]]),
     s.Matrix([[2, 0, 1], [0, 1, -2], [1, -2, 0]])]
T = [s.diag(1, -2, 3), s.ones(3), s.diag(-1, 2, 0)]
z = [s.Matrix([1, 3, -1]), s.Matrix([2, 0, 1]), s.Matrix([-1, 2, 2])]
h = [s.Matrix([2, -1, 3]), s.Matrix([0, 1, 4]), s.Matrix([3, -2, 0])]
Mdot = B*M+M*B.T+nu*sum(T, s.zeros(3))
vdot = B*v+nu*sum(h, s.zeros(3, 1))
vt = v+t*vdot
mt = M+t*Mdot
q0 = (v.T*Q*v)[0]
physical0 = v.dot(v)
denominator0 = q0+eta
qt = (vt.T*mt.inv()*vt)[0]
kt = (vt.dot(vt)+eta)/(qt+eta)
time_derivative = s.diff(kt, t).subs(t, 0)
laplacian = 0
drift = 0
F = 0
G = 0
for j in range(3):
    mx = M+x*P[j]+x*x*T[j]/2
    vx = v+x*z[j]+x*x*h[j]/2
    qx = (vx.T*mx.inv()*vx)[0]
    kx = (vx.dot(vx)+eta)/(qx+eta)
    laplacian += s.diff(kx, x, 2).subs(x, 0)
    drift += 2*nu*s.diff(qx, x).subs(x, 0)*s.diff(kx, x).subs(x, 0)/denominator0
    residual = z[j]-P[j]*Q*v
    F += (residual.T*Q*residual)[0]
    G += z[j].dot(z[j])
stretch = v.dot(B*v)
expected = (2*stretch-2*nu*G)/denominator0+2*nu*(physical0+eta)*F/denominator0**2
zero(time_derivative-nu*laplacian-drift-expected,
     'directional quotient equation from independently differentiated jets')

# A logarithmic change of scalar normalization cancels the geometric F term
# from both sides of a proposed HJB supersolution inequality.
q, cost, psi_rate, ell_norm, psi_norm, cross = s.symbols(
    'q cost psi_rate ell_norm psi_norm cross', real=True, nonzero=True)
ell_rate = -2*nu*cost/q+nu*ell_norm
reserve_rate = psi_rate-ell_rate-2*nu*(cross-ell_norm)
reserve_norm = psi_norm-2*cross+ell_norm
zero(reserve_rate-nu*reserve_norm-2*nu*cost/q-(psi_rate-nu*psi_norm),
     'scalar logarithmic HJB gauge cancellation')

# A complete actual unforced shear with the vorticity-aligned initial
# tensor. Use e=exp(-2nu t) and c=cos(y) to keep every identity rational.
# Its nonconstant regularized quotient has a finite explicit Bellman value.
A, delta, e = s.symbols('A delta e', positive=True)
c = s.symbols('c', real=True)
shear_s = A*A*e*c*c
aligned_m = delta+A*A*(1+e*e*(2*c*c-1))/2
shear_q = shear_s/aligned_m
Qshear = shear_q+eta
kshear = (shear_s+eta)/Qshear
Gshear = A*A*e*(1-c*c)
Fshear = Gshear*(1-c*s.diff(aligned_m, c)/aligned_m)**2/aligned_m
Vshear = -2*nu*Gshear/(shear_s+eta)+2*nu*Fshear/Qshear
time_k = -2*nu*e*s.diff(kshear, e)
lap_k = (1-c*c)*s.diff(kshear, c, 2)-c*s.diff(kshear, c)
drift_k = 2*nu*(1-c*c)*s.diff(Qshear, c)*s.diff(kshear, c)/Qshear
if s.factor(s.together(time_k-nu*lap_k-drift_k-Vshear*kshear)) != 0:
    raise AssertionError('full-time actual aligned-shear Bellman quotient')
if s.factor(s.together(kshear-(shear_q*aligned_m+eta)/Qshear)) != 0:
    raise AssertionError('convex scalar comparison for the aligned shear')

# Smooth periodic initial data, not an asserted closed-form time evolution.
# The pressure is the actual initial pressure. The resulting solenoidal RHS
# is the initial tangent of their smooth local unforced NS evolution.
y, zz = s.symbols('y z', real=True)
a, b = s.symbols('a b', positive=True)
coordinates = (x, y, zz)
origin = {c: 0 for c in coordinates}
u = s.Matrix([-a*s.sin(x)*s.cos(zz)-b*s.sin(y),
              b*s.sin(x), a*s.cos(x)*s.sin(zz)])
grad_u = u.jacobian(coordinates)
pressure = a*a*(s.cos(2*x)+s.cos(2*zz))/4-b*b*s.cos(x)*s.cos(y)


def lap(expr):
    return sum(s.diff(expr, c, 2) for c in coordinates)


def curl(field):
    return s.Matrix([s.diff(field[2], y)-s.diff(field[1], zz),
                     s.diff(field[0], zz)-s.diff(field[2], x),
                     s.diff(field[1], x)-s.diff(field[0], y)])


omega = curl(u)
grad_omega = omega.jacobian(coordinates)
velocity_rate = nu*u.applyfunc(lap)-grad_u*u-s.Matrix([s.diff(pressure, c) for c in coordinates])
omega_rate = curl(velocity_rate)
zero(s.trace(grad_u), 'incompressibility')
zero(lap(pressure)+s.trace(grad_u*grad_u), 'actual pressure Poisson equation')
zero(s.trace(velocity_rate.jacobian(coordinates)), 'solenoidal unforced velocity RHS')
matrix_zero(omega_rate+grad_omega*u-grad_u*omega-nu*omega.applyfunc(lap),
            'actual vorticity equation including generated modes')
matrix_zero(u.subs(origin), 'fixed initial symmetry point')
matrix_zero(grad_omega.subs(origin), 'zero initial vorticity gradient')
matrix_zero(u.subs({c: -c for c in coordinates}, simultaneous=True)+u, 'odd initial velocity')
matrix_zero(velocity_rate.subs({c: -c for c in coordinates}, simultaneous=True)+velocity_rate,
            'odd actual initial velocity RHS')

# At M(0)=I the initial metric time derivative is B+B^T. Retain this
# derivative when differentiating q, instead of freezing the frame.
physical = omega.dot(omega)
physical_t = 2*omega.dot(omega_rate)
metric_t = physical_t-(omega.T*(grad_u+grad_u.T)*omega)[0]
metric_D = metric_t+(s.Matrix([s.diff(physical, c) for c in coordinates]).dot(u))-nu*lap(physical)
initial_F = sum(entry**2 for entry in grad_omega)
zero(metric_D+2*nu*initial_F, 'metric production for the actual initial NS tangent')
zero(initial_F.subs(origin), 'zero geometric diffusion cost at symmetry point')
zero(metric_D.subs(origin), 'zero metric parabolic production at symmetry point')
zero(s.trace(grad_u+grad_u.T), 'zero initial frame trace and log determinant rates')
matrix_zero(s.Matrix([s.diff(physical, c) for c in coordinates]).subs(origin),
            'zero spatial scalar-observation gradient')
alpha_origin = s.simplify((omega.dot(grad_u*omega)/physical).subs(origin))
kappa_t_origin = s.simplify(((physical_t-metric_t)/physical).subs(origin))
zero(alpha_origin-a, 'positive physical stretching rate')
zero(kappa_t_origin-2*a, 'positive directional conversion growth without local cost')
regularized_rate = s.simplify(((physical_t-metric_t)/(physical+eta)).subs(origin))
zero(regularized_rate-8*a*b*b/(4*b*b+eta), 'positive conversion growth for fixed regularization')
zero(physical_t.subs(origin)-8*b*b*(a-nu), 'ordinary vorticity grows for a > nu')

# Follow the generator of stretching itself. This is the parabolic version
# of the existing material stretching identity, with its cross-gradient term.
stretch_vector = grad_u*omega
stretch_time = velocity_rate.jacobian(coordinates)*omega+grad_u*omega_rate
stretch_D = stretch_time+stretch_vector.jacobian(coordinates)*u-nu*stretch_vector.applyfunc(lap)
cross_diffusion = sum((grad_u.diff(c)*omega.diff(c) for c in coordinates), s.zeros(3, 1))
matrix_zero(stretch_D+s.hessian(pressure, coordinates)*omega+2*nu*cross_diffusion,
            'actual pressure-driven stretching-vector production')
matrix_zero(stretch_D.subs(origin)-s.Matrix([0, 0, 2*a*a*b]),
            'positive unforced pressure production at the zero-cost point')
alpha_time = ((omega_rate.dot(stretch_vector)+omega.dot(stretch_time))/physical
              -omega.dot(stretch_vector)*physical_t/physical**2)
zero(alpha_time.subs(origin)+2*nu*a, 'initial directional strain decays in this example')
zero(lap(initial_F).subs(origin)-(16*a*a+4*b*b), 'initial diffusion-cost Hessian')
zero(lap(initial_F).subs(origin)/(4*b*b)-(4*a*a/(b*b)+1),
     'initial normalized-cost Laplacian at its zero')

# The pair a and -a has identical entire initial scalar q and F fields,
# zero initial tensor entropy, and identical scalar parabolic production.
# Their velocity drifts differ. The ordinary q time derivatives agree at
# the origin, where both drifts vanish, not throughout the whole domain.
zero(physical.subs(a, -a)-physical, 'same entire initial scalar metric norm')
zero(initial_F.subs(a, -a)-initial_F, 'same entire initial diffusion cost')
zero(metric_D.subs(a, -a)-metric_D, 'same entire scalar parabolic production')
zero((metric_t.subs(a, -a)-metric_t).subs(origin),
     'same scalar metric time derivative at the common stationary point')
zero(kappa_t_origin.subs(a, -a)+kappa_t_origin, 'opposite actual directional growth')

print(json.dumps({
    'status': 'all exact checks passed',
    'directional_reaction': '2*(stretch-nu*G)/(q+eta) + 2*nu*(s+eta)*F/(q+eta)^2',
    'scalar_gauge': 'Lq(Psi-log q)-nu|grad(Psi-log q)|^2 = D Psi-nu|grad Psi|^2+2nu F/q',
    'initial_data_pressure': str(pressure),
    'geometric_cost_at_origin': str(initial_F.subs(origin)),
    'metric_parabolic_production_at_origin': str(s.simplify(metric_D.subs(origin))),
    'directional_growth_at_origin': str(kappa_t_origin),
    'regularized_directional_growth_at_origin': str(regularized_rate),
    'physical_enstrophy_time_derivative_at_origin': str(s.factor(physical_t.subs(origin))),
    'parabolic_stretch_vector_rate_at_origin': str(s.simplify(stretch_D.subs(origin)).T),
    'initial_directional_strain_time_derivative': '-2*nu*a',
    'normalized_cost_laplacian_at_origin': '4*a^2/b^2 + 1',
    'aligned_shear_control_value_upper_bound': 'log(max(1, delta+A^2)), uniformly for t >= 0',
    'scope': 'exact rational jets, full-time aligned shear and an initial NS tangent; '
             'stochastic control verification and local solution realization are analytic; '
             'no arbitrary-data history bound is asserted',
}, indent=2))
