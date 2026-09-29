#!/usr/bin/env python3
"""Exact transported-frame metric identities and a genuine unforced shear."""
import json
import sympy as s


def zero(expr, label):
    result = s.simplify(s.trigsimp(s.expand(expr)))
    if result != 0:
        raise AssertionError((label, result))


def matrix_zero(matrix, label):
    for i, entry in enumerate(matrix):
        zero(entry, (label, i))


t, x = s.symbols('t x', real=True)
nu = s.symbols('nu', positive=True)
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
force = v
for k in range(1, 4):
    if M[:k, :k].det() <= 0:
        raise AssertionError('positive definite seed')

# Direct differentiation of exact rational quadratic forms. These are
# jets of Dv=Bv+force and DM=BM+MB^T, D=partial_t-nu Delta at a point
# whose transport velocity is zero. The Hessians remain arbitrary here.
Mdot = B*M+M*B.T+nu*sum(T, s.zeros(3))
vdot = B*v+nu*sum(h, s.zeros(3, 1))+force
qt = ((v+t*vdot).T*(M+t*Mdot).inv()*(v+t*vdot))[0]
time_derivative = s.diff(qt, t).subs(t, 0)
spatial_second = 0
logdet_second = 0
square_sum = 0
for j in range(3):
    Mx = M+x*P[j]+x**2*T[j]/2
    vx = v+x*z[j]+x**2*h[j]/2
    qx = (vx.T*Mx.inv()*vx)[0]
    spatial_second += s.diff(qx, x, 2).subs(x, 0)
    logdet_second += s.diff(s.log(Mx.det()), x, 2).subs(x, 0)
    r = z[j]-P[j]*Q*v
    square_sum += (r.T*Q*r)[0]
production = s.simplify(time_derivative-nu*spatial_second)
zero(production-2*(v.T*Q*force)[0]+2*nu*square_sum,
     'forced covariant diffusion identity from actual rational derivatives')
if production.subs(nu, s.Rational(1, 1000)) <= 0:
    raise AssertionError('forcing can produce positive metric growth')
logdet_time = s.diff(s.log((M+t*Mdot).det()), t).subs(t, 0)
zero(logdet_time-nu*logdet_second-2*s.trace(B)
     -nu*sum(s.trace(Q*p*Q*p) for p in P), 'log determinant production')

# Explicit periodic unforced NS shear. The frame tensor solves the full
# prescribed-gradient equation, including its off-diagonal correlations.
A, y = s.symbols('A y', real=True)
decay = s.exp(-nu*t)
shear = A*decay*s.sin(y)
sigma = s.diff(shear, y)
b = A*t*decay*s.cos(y)
I0 = (1-(1+2*nu*t)*s.exp(-2*nu*t))/(4*nu**2)
I2 = ((2*nu*t-1)*s.exp(-2*nu*t)+s.exp(-4*nu*t))/(4*nu**2)
c = A**2*(I0+I2*s.cos(2*y))
zero(s.diff(shear, t)-nu*s.diff(shear, y, 2), 'literal unforced shear equation')
zero(s.diff(b, t)-nu*s.diff(b, y, 2)-sigma, 'off-diagonal frame evolution')
zero(s.diff(c, t)-nu*s.diff(c, y, 2)-2*sigma*b, 'diagonal frame evolution')
zero(I0+I2-(1-s.exp(-2*nu*t))**2/(4*nu**2), 'uniform shear frame bound')
zero(I0.subs(t, 0), 'frame initial value I0')
zero(I2.subs(t, 0), 'frame initial value I2')
zero(s.diff(s.exp(4*nu*t)*I2, t)-t*s.exp(2*nu*t), 'positive integral for I2')
variance = c-b*b
zero(s.diff(variance, t)-nu*s.diff(variance, y, 2)
     -2*nu*s.diff(b, y)**2, 'frame determinant excess has nonnegative source')

bs, cs = s.symbols('b_s c_s', real=True)
Ms = s.Matrix([[1+cs, bs, 0], [bs, 1, 0], [0, 0, 1]])
Qs = Ms.inv()
omega = s.Matrix([0, 0, -sigma])
q_shear = (omega.T*Qs*omega)[0]
zero(q_shear-sigma**2, 'actual vorticity avoids the stretched frame plane')
zero(s.diff(q_shear, t)-nu*s.diff(q_shear, y, 2)
     +2*nu*A**2*decay**2*s.sin(y)**2, 'genuine shear metric dissipation')
eta = s.symbols('eta', positive=True)
psi = -2*nu*s.log(q_shear+eta)
metric_loss = A**2*decay**2*s.sin(y)**2
zero(s.diff(psi, t)-nu*s.diff(psi, y, 2)+s.diff(psi, y)**2/2
     -4*nu**2*metric_loss/(q_shear+eta), 'actual fluid-derived HJB identity')

# An initial tensor aligned with the actual vorticity avoids charging the
# irrelevant horizontal frame stretching. Delta keeps the tensor positive.
delta = s.symbols('delta', positive=True)
aligned_zz = delta+A**2*(1+s.exp(-4*nu*t)*s.cos(2*y))/2
zero(s.diff(aligned_zz, t)-nu*s.diff(aligned_zz, y, 2), 'aligned frame heat component')
zero(aligned_zz.subs(t, 0)-delta-sigma.subs(t, 0)**2, 'aligned frame initial data')
q_aligned = sigma**2/aligned_zz
r_aligned = s.diff(sigma, y)-s.diff(aligned_zz, y)*sigma/aligned_zz
zero(s.diff(q_aligned, t)-nu*s.diff(q_aligned, y, 2)
     +2*nu*r_aligned**2/aligned_zz, 'aligned shear metric dissipation')

# An exact three-dimensional Beltrami solution has nonzero pointwise
# stretching. Check NS with its pressure, then the identity at the initial
# frame M=I. Only the first time derivative of that frame is used here.
zz = s.symbols('z', real=True)
coordinates = (x, y, zz)
abc = A*decay*s.Matrix([s.sin(zz)+s.cos(y),
                        s.sin(x)+s.cos(zz), s.sin(y)+s.cos(x)])
G = abc.jacobian(coordinates)
lap_abc = abc.applyfunc(lambda a: sum(s.diff(a, c, 2) for c in coordinates))
pressure = -abc.dot(abc)/2
matrix_zero(abc.diff(t)+G*abc+s.Matrix([s.diff(pressure, c) for c in coordinates])
            -nu*lap_abc, 'literal unforced Beltrami equation including pressure')
curl_abc = s.Matrix([s.diff(abc[2], y)-s.diff(abc[1], zz),
                     s.diff(abc[0], zz)-s.diff(abc[2], x),
                     s.diff(abc[1], x)-s.diff(abc[0], y)])
matrix_zero(curl_abc-abc, 'physical Beltrami vorticity')
omega0 = abc.subs(t, 0)
omega_dot0 = abc.diff(t).subs(t, 0)
G0 = G.subs(t, 0)
norm0 = omega0.dot(omega0)
qdot0 = 2*omega0.dot(omega_dot0)-(omega0.T*(G0+G0.T)*omega0)[0]
qadv0 = sum(omega0[j]*s.diff(norm0, c) for j, c in enumerate(coordinates))
qlap0 = sum(s.diff(norm0, c, 2) for c in coordinates)
grad_norm0 = sum(s.diff(omega0, c).dot(s.diff(omega0, c)) for c in coordinates)
zero(qdot0+qadv0-nu*qlap0+2*nu*grad_norm0, 'Beltrami metric production at initial time')
origin = {x: 0, y: 0, zz: 0}
stretch_at_origin = (omega0.T*G0*omega0)[0].subs(origin)
zero(stretch_at_origin-3*A**3, 'positive physical stretching in genuine unforced flow')
kappa_dot_origin = ((2*omega0.dot(omega_dot0)-qdot0)/norm0).subs(origin)
zero(kappa_dot_origin-2*A, 'directional coercivity can initially worsen')

# Pure matrix obstruction to coercivity; no fluid realization is claimed.
lam = s.symbols('lambda', positive=True)
Ml = s.diag(lam**2, lam**(-2), 1)
vl = s.Matrix([lam, 0, 0])
zero(Ml.det()-1, 'fixed determinant')
zero((vl.T*Ml.inv()*vl)[0]-1, 'fixed metric norm')
zero(vl.dot(vl)-lam**2, 'unbounded Euclidean norm')

print(json.dumps({
    'status': 'all exact checks passed',
    'rational_jet_dissipation_square': str(s.factor(square_sum)),
    'rational_jet_forced_production': str(s.factor(production)),
    'shear_frame_trace_bound': '3 + A^2/(4 nu^2), uniformly for t >= 0',
    'shear_directional_coercivity': '1 wherever omega != 0',
    'aligned_shear_directional_coercivity_bound': 'delta + A^2',
    'regularized_log_metric_hjb_source': '4 nu^2 F/(q+eta), with F >= 0',
    'beltrami_initial_stretching_at_origin': str(stretch_at_origin),
    'beltrami_initial_directional_coercivity_derivative': str(kappa_dot_origin),
    'scope': 'exact local parabolic jets and explicit unforced shear; '
             'the general PDE comparison and stochastic representation are analytic',
}, indent=2))
