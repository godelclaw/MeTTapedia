#!/usr/bin/env python3
"""Exact pressure response, remote-parent jets and the joint stretching law.

Symbolic identities are checked independently of Lean. The final quadrature
is a numerical consistency check, not a proof of the exterior formula.
See README.md for the analytic realization and the remaining near-pressure
and viscous-commutator obligations.
"""
import json
import sympy as s
import numpy as np
from numpy.polynomial.legendre import leggauss


def zero(expr, label):
    result = s.factor(s.together(expr))
    if result != 0:
        result = s.simplify(result)
    if result != 0:
        raise AssertionError((label, result))


def matrix_zero(matrix, label):
    for i, entry in enumerate(matrix):
        zero(entry, (label, i))


x, y, z, h, c, vx, vy, vz = s.symbols('x y z h c vx vy vz', real=True)
r = s.symbols('r', positive=True)
coordinates = (x, y, z)
rad = s.sqrt(x*x+y*y+z*z)
v = s.Matrix([vx, vy, vz])
position = s.Matrix([x, y, z])
# First differentiate the Newtonian kernel in the velocity direction, then
# twice in e=(h,0,c). The factor 1/(4pi) is restored after the polynomial.
second_v = 3*v.dot(position)**2/rad**5-v.dot(v)/rad**3
direction_e = lambda f: h*s.diff(f, x)+c*s.diff(f, z)
raw = (r**5*direction_e(direction_e(second_v))).subs({x: 0, y: 0, z: r})
kernel = ((9*h*h-12*c*c)*vx*vx+(3*h*h-12*c*c)*vy*vy
          +(24*c*c-12*h*h)*vz*vz-48*c*h*vx*vz)
zero(raw-kernel, 'fourth directional Newtonian derivative')
norm2 = vx*vx+vy*vy+vz*vz
e2 = h*h+c*c
lower = 4*(3*c*vz-2*h*vx)**2+5*h*h*vx*vx+15*h*h*vy*vy
upper = (4*(3*h*vz+2*c*vx)**2+(15*h*h+20*c*c)*vx*vx
         +(21*h*h+36*c*c)*vy*vy)
zero(kernel+12*e2*norm2-lower, 'sharp lower kernel square certificate')
zero(24*e2*norm2-kernel-upper, 'sharp upper kernel square certificate')
zero(kernel.subs({h: 0, c: 1, vx: 0, vy: 0, vz: 1})-24,
     'upper kernel constant attained')
zero(kernel.subs({h: 0, c: 1, vx: 1, vy: 0, vz: 0})+12,
     'lower kernel constant attained')

# u=chi(r) (e_z cross x): exact divergence and pressure source.
g, radial_derivative = s.symbols('g radial_derivative', real=True)
spin = s.Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 0]])
gradient = g*spin+radial_derivative*(spin*position)*position.T
zero(s.trace(gradient), 'radial swirl incompressibility')
zero(s.trace(gradient*gradient)+2*g*g+2*g*radial_derivative*(x*x+y*y),
     'radial swirl pressure Poisson source')

# I(r)=integral_0^r s^4 chi(s)^2 ds; T(r)=integral_r^infinity s chi(s)^2 ds.
chi = s.Function('chi')(r)
I = s.Function('I')(r)
tail = s.Function('T')(r)
derivatives = {
    s.diff(I, r, 2): 4*r**3*chi**2+2*r**4*chi*s.diff(chi, r),
    s.diff(I, r): r**4*chi**2,
    s.diff(tail, r, 2): -chi**2-2*r*chi*s.diff(chi, r),
    s.diff(tail, r): -r*chi**2,
}
p0 = -s.Rational(2, 3)*tail
p2 = -s.Rational(2, 3)*I/r**3
zero((s.diff(p0, r, 2)+2*s.diff(p0, r)/r).subs(derivatives)
     -2*chi**2-s.Rational(4, 3)*r*chi*s.diff(chi, r), 'radial monopole equation')
zero((s.diff(p2, r, 2)+2*s.diff(p2, r)/r-6*p2/r**2).subs(derivatives)
     +s.Rational(4, 3)*r*chi*s.diff(chi, r), 'radial quadrupole equation')
J, mu, E = s.symbols('J mu E', real=True)
energy = 8*s.pi*J/3
zero(-s.Rational(2, 3)*J/r**3*(3*mu**2-1)/2
     +energy*(3*mu**2-1)/(8*s.pi*r**3), 'energy-normalized exact exterior pressure')

# Exact exterior axial Hessian for an arbitrary swirl axis.
nx, ny, nz, L, b, eta = s.symbols('nx ny nz L b eta', real=True)
Lpos, bpos, etapos = s.symbols('Lpos bpos etapos', positive=True)
n = s.Matrix([nx, ny, nz])
exterior = -E*(3*n.dot(position)**2-n.dot(n)*rad**2)/(8*s.pi*rad**5)
axial = s.diff(exterior, z, 2).subs({x: 0, y: 0, z: Lpos})
zero(axial-3*E*(nx*nx+ny*ny-2*nz*nz)/(2*s.pi*Lpos**5),
     'exterior axial pressure Hessian')

# A central plateau swirl has rigid rotation near zero and this exact
# quadratic pressure there, up to an irrelevant additive constant.
core_pressure = bpos*bpos*(2*x*x+2*y*y+z*z)/5
plateau_pressure = (bpos*bpos*r*r/3
                    -2*bpos*bpos*r*r/15*(3*mu*mu-1)/2)
zero(plateau_pressure.subs(mu, z/r).subs(r, rad)-core_pressure,
     'core pressure derived from the radial solution')
Pcore = s.hessian(core_pressure, coordinates)
zero(Pcore[2, 2]-2*bpos*bpos/5, 'central plateau swirl axial Hessian')
packet_energy = s.pi*bpos*bpos*Lpos**5
parallel = axial.subs({nx: 0, ny: 0, nz: 1, E: packet_energy})
perpendicular = axial.subs({nx: 1, ny: 0, nz: 0, E: packet_energy})
Pplus_zz = Pcore[2, 2]+parallel
Pminus_zz = Pcore[2, 2]+perpendicular
zero(Pplus_zz+13*bpos*bpos/5, 'negative total axial pressure from parallel parents')
zero(Pminus_zz-19*bpos*bpos/10, 'positive total axial pressure from transverse parents')

# Actual second NS/frame time jets in the central rigid-rotation region.
t = s.symbols('t', real=True)
p11, p22, p33 = s.symbols('p11 p22 p33', real=True)
Ptotal = s.diag(p11, p22, p33)
B0 = bpos*spin
omega0 = s.Matrix([0, 0, 2*bpos])
Bdot = -B0*B0-Ptotal
omega2 = Bdot*omega0
M2 = Bdot+Bdot.T
omega_taylor = omega0+t*t*omega2/2
M_taylor = s.eye(3)+t*t*M2/2
q_taylor = (omega_taylor.T*M_taylor.inv()*omega_taylor)[0]
s_taylor = omega_taylor.dot(omega_taylor)
k_taylor = (s_taylor+etapos)/(q_taylor+etapos)
zero(s.diff(q_taylor, t, 2).subs(t, 0), 'zero second metric time derivative in plateau core')
k2 = s.simplify(s.diff(k_taylor, t, 2).subs(t, 0))
zero(k2+8*bpos*bpos*p33/(4*bpos*bpos+etapos), 'pressure determines second directional growth')
positive_k2 = s.factor(k2.subs(p33, Pplus_zz))
negative_k2 = s.factor(k2.subs(p33, Pminus_zz))
if positive_k2.is_positive is not True or negative_k2.is_negative is not True:
    raise AssertionError('opposite directional curvatures at equal remote energy')

# Check the full parabolic stretching law on actual periodic initial data.
# The pressure solves the Poisson equation and the tangent is the unforced
# NS right-hand side. Unlike the plateau jets, this check has nonzero
# spatial gradients and retains the viscous cross term.
nu, tau = s.symbols('nu tau', positive=True)
a, b = s.symbols('a b', real=True)
u = s.Matrix([-a*s.sin(x)*s.cos(z)-b*s.sin(y), b*s.sin(x), a*s.cos(x)*s.sin(z)])
p = a*a*(s.cos(2*x)+s.cos(2*z))/4-b*b*s.cos(x)*s.cos(y)


def laplacian(f):
    if isinstance(f, s.MatrixBase):
        return f.applyfunc(laplacian)
    return sum(s.diff(f, q, 2) for q in coordinates)


def curl(f):
    return s.Matrix([s.diff(f[2], y)-s.diff(f[1], z),
                     s.diff(f[0], z)-s.diff(f[2], x),
                     s.diff(f[1], x)-s.diff(f[0], y)])


B = u.jacobian(coordinates)
zero(s.trace(B), 'periodic initial incompressibility')
zero(laplacian(p)+s.trace(B*B), 'periodic initial pressure Poisson equation')
omega = curl(u)
zeta = B*omega
pressure_gradient = s.Matrix([s.diff(p, q) for q in coordinates])
u_rate = -B*u-pressure_gradient+nu*laplacian(u)
zero(s.trace(u_rate.jacobian(coordinates)), 'solenoidal unforced initial tangent')
omega_rate = curl(u_rate)
zeta_rate = u_rate.jacobian(coordinates)*omega+B*omega_rate
cross = sum((B.diff(q)*omega.diff(q) for q in coordinates), s.zeros(3, 1))
cross_sample = s.simplify(cross.dot(cross).subs(
    {a: 1, b: 2, x: s.pi/4, y: s.pi/6, z: s.pi/3}))
if cross_sample.is_positive is not True:
    raise AssertionError('viscous cross term must be active in the full-field test')
parabolic_zeta = zeta_rate+zeta.jacobian(coordinates)*u-nu*laplacian(zeta)
matrix_zero(parabolic_zeta+s.hessian(p, coordinates)*omega+2*nu*cross,
            'actual unforced parabolic stretching-vector law')
joint = omega.dot(omega)+tau*tau*zeta.dot(zeta)
joint_rate = 2*omega.dot(omega_rate)+2*tau*tau*zeta.dot(zeta_rate)
joint_D = joint_rate+sum(u[i]*s.diff(joint, q) for i, q in enumerate(coordinates))-nu*laplacian(joint)
grad_omega = sum(omega.diff(q).dot(omega.diff(q)) for q in coordinates)
grad_zeta = sum(zeta.diff(q).dot(zeta.diff(q)) for q in coordinates)
joint_expected = (2*omega.dot(zeta)-2*tau*tau*zeta.dot(s.hessian(p, coordinates)*omega)
                  -4*nu*tau*tau*zeta.dot(cross)-2*nu*(grad_omega+tau*tau*grad_zeta))
zero(joint_D-joint_expected, 'actual unforced joint vorticity-stretching production')


def quadrature(axis, count):
    # Independent integration of the stress against the fourth Newtonian
    # derivative. The packet has a C-infinity radial profile on the unit ball.
    nodes, weights = leggauss(count)
    rho = ((nodes+1)/2)[:, None, None]
    wr = (weights/2)[:, None, None]
    theta = nodes[None, :, None]
    wt = weights[None, :, None]
    phi = (2*np.pi*np.arange(2*count)/(2*count))[None, None, :]
    xx = rho*np.sqrt(1-theta**2)*np.cos(phi)
    yy = rho*np.sqrt(1-theta**2)*np.sin(phi)
    zz = np.broadcast_to(rho*theta, xx.shape)
    local = np.stack([xx, yy, zz], axis=-1)
    profile = np.exp(-1/(1-rho*rho))
    velocity = profile[..., None]*np.cross(axis, local)
    separation = local+np.array([0., 0., 3.])
    distance = np.linalg.norm(separation, axis=-1)
    normal = separation/distance[..., None]
    na = normal[..., 2]
    va = velocity[..., 2]
    vn = np.sum(velocity*normal, axis=-1)
    vsq = np.sum(velocity*velocity, axis=-1)
    kernel4 = (105*na*na*vn*vn-15*(vn*vn+na*na*vsq+4*na*va*vn)
               +3*(vsq+2*va*va))/(4*np.pi*distance**5)
    weight = wr*wt*rho*rho*(2*np.pi/(2*count))
    packet_e = float(np.sum(weight*vsq))
    observed = float(np.sum(weight*kernel4))
    expected = 3*packet_e*(1-3*axis[2]**2)/(2*np.pi*3**5)
    relative = abs(observed-expected)/abs(expected)
    if relative > 1.e-8:
        raise AssertionError(('independent exterior Hessian quadrature', count, relative))
    return {'resolution': count, 'energy': packet_e,
            'axial_hessian': observed, 'relative_error': relative}


print(json.dumps({
    'status': 'all exact checks passed',
    'directional_kernel_interval': '[-12,24]*|e|^2*|v|^2/(4pi r^5)',
    'far_pressure_operator_bound': '6 E/(pi R^5)',
    'parallel_core_directional_second_rate': str(positive_k2),
    'transverse_core_directional_second_rate': str(negative_k2),
    'joint_parabolic_identity': 'verified on the full periodic initial field, including viscous cross terms',
    'independent_quadrature': {
        'parallel': [quadrature(np.array([0., 0., 1.]), n) for n in (24, 40)],
        'transverse': [quadrature(np.array([1., 0., 0.]), n) for n in (24, 40)],
    },
    'scope': 'symbolic pressure identities and NS/frame initial jets; '
             'physical realization and exterior-response derivation are analytic; quadrature is numerical',
}, indent=2))
