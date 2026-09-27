#!/usr/bin/env python3
"""Exact checks for the angular-mean defect calculation.

The polynomial fields test local differential identities. The Gaussian
fields are Schwartz initial data; their kinetic energy jets use the exact
unforced equation. A final scaling check concerns a prescribed path which
is not a Navier--Stokes solution. No solution is integrated. Requires Sympy.
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

# General cylindrical stretching, after substituting the three vorticity
# identities. No particular velocity field is chosen in this calculation.
ar, bt, cz, jj, rr0, r0, z0, rz0 = s.symbols(
    'omega_r omega_theta omega_z swirl_over_r radial_r radial_over_r axial_z radial_z')
omega_general = s.Matrix([ar, bt, cz])
gradient_general = s.Matrix([[rr0, -jj, rz0],
                             [cz-jj, r0, -ar], [rz0-bt, 0, z0]])
stretch_general = (ar**2*rr0+bt**2*r0+cz**2*z0
                   +2*ar*cz*rz0-ar*bt*cz-2*ar*bt*jj)
require_zero(omega_general.dot(gradient_general*omega_general)-stretch_general,
             'general cylindrical stretching identity')

theta_fun = s.Function('v_theta')(r, z)
cutoff_fun = s.Function('radial_cutoff')(r, z)
hardy_cross = cutoff_fun**2*r*((s.diff(theta_fun, r)+theta_fun/r)**2
                               -s.diff(theta_fun, r)**2-theta_fun**2/r**2)
hardy_boundary = (s.diff(cutoff_fun**2*theta_fun**2, r)
                  -2*cutoff_fun*s.diff(cutoff_fun, r)*theta_fun**2)
require_zero(hardy_cross-hardy_boundary, 'localized radial Hardy identity')

time_var = s.symbols('time', real=True)
sv = s.Function('scaled_swirl')(r, z, time_var)
vrift, wrift = s.symbols('radial_drift axial_drift')
gamma = r*sv
gamma_operator = (s.diff(gamma, time_var)+vrift*s.diff(gamma, r)
                   +wrift*s.diff(gamma, z)-s.diff(gamma, r, 2)
                   +s.diff(gamma, r)/r)
swirl_operator = (s.diff(sv, time_var)+vrift*s.diff(sv, r)
                   +wrift*s.diff(sv, z)+vrift*sv/r-s.diff(sv, r, 2)
                   -s.diff(sv, r)/r+sv/r**2)
require_zero(gamma_operator-r*swirl_operator, 'ancient circulation equation')

# Signed work before taking a norm of the Reynolds stress. All coefficient
# functions and the test density are arbitrary; the remainder is a divergence.
aspect = s.symbols('aspect', positive=True)
test_density = s.Function('test_density')(r, z, time_var)
circulation_fun = s.Function('circulation')(r, z, time_var)
radial_drift = s.Function('radial_drift')(r, z, time_var)
axial_drift = s.Function('axial_drift')(r, z, time_var)
radial_stress = s.Function('radial_azimuthal_stress')(r, z, time_var)
axial_stress = s.Function('axial_azimuthal_stress')(r, z, time_var)
transport_drift = radial_drift+1/r
primal = (s.diff(circulation_fun, r, 2)
          +aspect**2*s.diff(circulation_fun, z, 2)
          -transport_drift*s.diff(circulation_fun, r)
          -axial_drift*s.diff(circulation_fun, z))
adjoint = (s.diff(test_density, r, 2)
           +aspect**2*s.diff(test_density, z, 2)
           +s.diff(transport_drift*test_density, r)
           +s.diff(axial_drift*test_density, z))
dual_radial_flux = (test_density*s.diff(circulation_fun, r)
                   -circulation_fun*s.diff(test_density, r)
                   -transport_drift*circulation_fun*test_density)
dual_axial_flux = (aspect**2*(test_density*s.diff(circulation_fun, z)
                              -circulation_fun*s.diff(test_density, z))
                  -axial_drift*circulation_fun*test_density)
require_zero(primal*test_density-circulation_fun*adjoint
             -s.diff(dual_radial_flux, r)-s.diff(dual_axial_flux, z),
             'circulation adjoint identity')
source_pairing = (-r*s.diff(radial_stress, r)-2*radial_stress
                  -aspect*r*s.diff(axial_stress, z))*test_density
signed_work = (radial_stress*(r*s.diff(test_density, r)-test_density)
               +aspect*axial_stress*r*s.diff(test_density, z))
require_zero(source_pairing-signed_work
             +s.diff(r*radial_stress*test_density, r)
             +aspect*s.diff(r*axial_stress*test_density, z),
             'signed dual Reynolds work')

# Finite-energy data: each stored vector is the polynomial multiplying
# exp(-x^2-y^2-z^2). Rotation preserves this common Gaussian factor.
phase = s.symbols('phase', real=True)


def gaussian_derivative(p, j):
    return s.diff(p, coords[j])-2*coords[j]*p


def gaussian_planar_curl(p):
    return s.Matrix([gaussian_derivative(p, 1),
                     -gaussian_derivative(p, 0), 0])


def gaussian_gradient(p):
    return s.Matrix(3, 3, lambda i, j: gaussian_derivative(p[i], j))


def gaussian_integral_factor(p, rate):
    """Integral of p exp(-rate |x|^2), divided by (pi/rate)^(3/2)."""
    rate = s.sympify(rate)
    answer = 0
    for powers, coefficient in s.Poly(s.expand(p), *coords).terms():
        if any(j % 2 for j in powers):
            continue
        for j in powers:
            n = j//2
            coefficient *= (s.Rational(factorial(2*n), 4**n*factorial(n))
                            / rate**n)
        answer += coefficient
    return s.factor(answer)


gv = gaussian_planar_curl(s.Integer(1))
gw = gaussian_planar_curl(x*x-y*y+2*phase*x*y*(x*x+y*y))
ggv, ggw = gaussian_gradient(gv), gaussian_gradient(gw)
require_zero(sum(gaussian_derivative(gv[i], i) for i in range(3)),
             'Gaussian mean divergence')
require_zero(sum(gaussian_derivative(gw[i], i) for i in range(3)),
             'Gaussian defect divergence')
require_zero(mean_vector(gv)-gv, 'Gaussian mean invariance')
require_zero(mean_vector(gw), 'Gaussian zero angular mean')
require_zero(gaussian_integral_factor(gv.dot(gw), 2),
             'Gaussian energy orthogonality')
require_zero(gaussian_integral_factor(gw.dot(ggw*gw), 3),
             'Gaussian defect self-advection energy cancellation')
gstress = mean_tensor(gw*gw.T)
require_zero(at(gstress[0, 1])-2*phase*r**4,
             'Gaussian radial-azimuthal stress')
gtorque = -r*at(mean_vector(ggw*gw)[1])
require_zero(gtorque-4*phase*r**4*(2*r**2-3),
             'Gaussian actual mean circulation source')
require_zero(gtorque.subs({r: 1, z: 0})+4*phase,
             'Gaussian circulation source at its initial maximum')
circulation = 2*r*r
radial_derivative = lambda p: s.diff(p, r)-2*r*p
radial_diffusion = radial_derivative(radial_derivative(circulation))
radial_diffusion -= radial_derivative(circulation)/r
require_zero(radial_diffusion.subs(r, 1)+8,
             'Gaussian radial circulation diffusion at maximum')
require_zero(((4*z*z-2)*circulation).subs({r: 1, z: 0})+4,
             'Gaussian axial circulation diffusion at maximum')

# A different radial phase exports mean kinetic energy while increasing
# and moving inward the mean circulation peak. These are initial jets;
# the short actual unforced interval is justified in the analytic note.
export_radius_sq = x*x+y*y
export_phase = (20*export_radius_sq-15*export_radius_sq**2
                +4*export_radius_sq**3)
export_defect = gaussian_planar_curl(x*x-y*y+2*x*y*export_phase)
export_gradient = gaussian_gradient(export_defect)
require_zero(mean_vector(export_defect), 'exporting defect has zero angular mean')
export_stress = mean_tensor(export_defect*export_defect.T)
require_zero(at(export_stress[0, 1])-2*r**4*(20-30*r*r+12*r**4),
             'exporting defect radial-azimuthal stress')
export_transfer = gaussian_integral_factor(export_defect.dot(ggv*export_defect), 3)
require_zero(export_transfer+s.Rational(320, 27), 'negative transfer into the mean')
export_torque = -r*at(mean_vector(export_gradient*export_defect)[1])
require_zero(export_torque-(96*r**10-480*r**8+640*r**6-240*r**4),
             'exporting defect full mean circulation source')
require_zero(export_torque.subs(r, 1)-16, 'positive circulation source at peak')
require_zero((s.diff(export_torque, r)-4*r*export_torque).subs(r, 1)+64,
             'negative radial derivative of circulation source at peak')
export_norms = [
    gaussian_integral_factor(export_defect.dot(export_defect), 2),
    gaussian_integral_factor(sum(export_gradient[i, j]**2
                                for i in range(3) for j in range(2)), 2),
    gaussian_integral_factor(sum(export_gradient[i, 2]**2 for i in range(3)), 2)]
for actual, expected in zip(export_norms, [s.Rational(2601, 4), 4512, s.Rational(2601, 4)]):
    require_zero(actual-expected, 'exporting defect Gaussian norm')
require_zero(20-30*r*r+12*r**4-(12*(r*r-s.Rational(5, 4))**2+s.Rational(5, 4)),
             'strict positivity of the stress polynomial')
export_e = at(export_stress[0, 1])*s.exp(-2*(r*r+z*z))
export_vtheta = 2*r*s.exp(-(r*r+z*z))
export_local_work = export_vtheta*export_torque*s.exp(-2*(r*r+z*z))/r
export_exchange = export_e*(s.diff(export_vtheta, r)-export_vtheta/r)
export_flux = s.diff(r*export_vtheta*export_e, r)/r
require_zero(s.simplify(export_local_work-export_exchange+export_flux),
             'local work keeps the spatial flux divergence')
for actual, expected in [(export_local_work, 32), (export_exchange, -16),
                         (-export_flux, 48)]:
    require_zero(s.simplify(actual.subs({r: 1, z: 0})*s.exp(3))-expected,
                 'local work, exchange and influx at the peak')

# Motion of the nondegenerate mean circulation peak for the phase -1.
# The mean has no meridional advection initially. All the quantities below
# are obtained from the already checked actual torque and viscous terms.
scaled_viscosity, scaled_aspect, perturbation = s.symbols(
    'scaled_viscosity scaled_aspect perturbation', real=True)
# Rotation covariance gives the exact mean/defect split for the scaled
# derivative too, before applying its Leray projection.
scaled_derivative = s.diag(1, 1, scaled_aspect)
scaled_adv = lambda a, b: b.jacobian(coords)*scaled_derivative*a
linear_defect = scaled_adv(v, w)+scaled_adv(w, v)
quadratic_defect = scaled_adv(w, w)
full_convection = scaled_adv(u, u)
require_zero(mean_vector(linear_defect), 'scaled mean of the linear defect terms')
require_zero(full_convection-mean_vector(full_convection)-linear_defect
             -quadratic_defect+mean_vector(quadratic_defect),
             'exact scaled fluctuation equation split')
initial_point = {r: 1, z: 0}
gamma_rr = radial_derivative(radial_derivative(circulation)).subs(initial_point)/s.E
gamma_zz = ((4*z*z-2)*circulation).subs(initial_point)/s.E
torque_at_peak = gtorque.subs({r: 1, z: 0, phase: -1})/s.E**2
torque_radial_at_peak = (s.diff(gtorque, r)-4*r*gtorque).subs(
    {r: 1, z: 0, phase: -1})/s.E**2
diffusion_radial_at_peak = radial_derivative(radial_diffusion).subs(initial_point)/s.E
axial_diffusion_radial_at_peak = radial_derivative(
    (4*z*z-2)*circulation).subs(initial_point)/s.E
gamma_time_at_peak = (scaled_viscosity*(radial_diffusion.subs(initial_point)/s.E
                        +scaled_aspect**2*gamma_zz)
                      +perturbation**2*torque_at_peak)
gamma_time_radial_at_peak = (scaled_viscosity*(diffusion_radial_at_peak
                               +scaled_aspect**2*axial_diffusion_radial_at_peak)
                             +perturbation**2*torque_radial_at_peak)
peak_radial_velocity = s.simplify(-gamma_time_radial_at_peak/gamma_rr)
require_zero(gamma_rr+8/s.E, 'Gaussian radial Hessian at mean peak')
require_zero(gamma_zz+4/s.E, 'Gaussian axial Hessian at mean peak')
require_zero(gamma_time_at_peak-4*perturbation**2/s.E**2
             +4*scaled_viscosity*(2+scaled_aspect**2)/s.E,
             'Gaussian spin-up rate with full anisotropic viscosity')
require_zero(peak_radial_velocity-2*scaled_viscosity+2*perturbation**2/s.E,
             'Gaussian inward peak velocity')
require_zero(gamma_time_at_peak/(2/s.E)+peak_radial_velocity
             +2*scaled_viscosity*(1+scaled_aspect**2),
             'initial logarithmic rate of radius times circulation')
require_zero(gw.subs({x: 1, y: 0, z: 0, phase: -1})-s.Matrix([-2, 0, 0]),
             'Gaussian defect at the fixed point used for the history lower bound')

# The axisymmetric radial mean is determined by its actual anisotropic
# divergence constraint. These are FTC identities, with no chosen profile.
dummy_radius = s.symbols('dummy_radius', real=True)
axial_derivative_fun = s.Function('axial_mean_derivative')
radial_primitive = s.Integral(dummy_radius*axial_derivative_fun(dummy_radius, z),
                             (dummy_radius, 0, r))
radial_mean = -scaled_aspect*radial_primitive/r
require_zero(s.diff(radial_mean, r)+scaled_aspect*axial_derivative_fun(r, z)
             +radial_mean/r, 'radial mean from anisotropic incompressibility')
require_zero(s.diff(radial_mean, r, 2)
             +scaled_aspect*s.diff(axial_derivative_fun(r, z), r)
             -scaled_aspect*axial_derivative_fun(r, z)/r-2*radial_mean/r**2,
             'second radial derivative of the actual mean')

gtransfer = gaussian_integral_factor(gw.dot(ggv*gw), 3)
require_zero(gtransfer+16*phase/9, 'Gaussian signed mean transfer')
amplitude = s.symbols('amplitude', real=True)
gfull = gv+amplitude*gw
gfull_gradient = ggv+amplitude*ggw
require_zero(gaussian_integral_factor(
    (amplitude*gw).dot(gfull_gradient*gfull), 3)-amplitude**2*gtransfer,
    'Gaussian complete convection work on the defect')
require_zero(gaussian_integral_factor(gv.dot(gfull_gradient*gfull), 3)
             +amplitude**2*gtransfer,
             'Gaussian complete convection work on the mean')
require_zero(gaussian_integral_factor(sum(ggv[i,j]*ggw[i,j]
                                         for i in range(3) for j in range(3)),2),
             'Gaussian gradient orthogonality')

gaussian_norms = {}
for name, field in [('mean', gv), ('defect', gw)]:
    gradient = gaussian_gradient(field)
    gaussian_norms[name] = [
        gaussian_integral_factor(field.dot(field), 2),
        gaussian_integral_factor(sum(gradient[i, j]**2
                                    for i in range(3) for j in range(2)), 2),
        gaussian_integral_factor(sum(gradient[i, 2]**2 for i in range(3)), 2),
    ]
for name, expected in [('mean', [2, 8, 2]),
                       ('defect', [3*(2*phase**2+1)/2,
                                   6*(3*phase**2+2), 3*(2*phase**2+1)/2])]:
    for value, target in zip(gaussian_norms[name], expected):
        require_zero(value-target, 'Gaussian squared norm: '+name)
    for value in gaussian_norms[name]:
        require_zero(value.subs(phase, 1)-value.subs(phase, -1),
                     'Gaussian opposite-phase norms: '+name)

# The concentrating actual-flow interval uses the same normalized data
# for every aspect ratio. Check its physical scaling independently.
concentration, geometry_exponent, normalization_energy = s.symbols(
    'concentration geometry_exponent normalization_energy', positive=True)
axial_concentration = concentration**(1-2*geometry_exponent)
velocity_amplitude = concentration**(1+2*geometry_exponent)/s.sqrt(normalization_energy)
aspect_ratio = axial_concentration/concentration
initial_physical_energy = (velocity_amplitude**2*normalization_energy
                           /(concentration**2*axial_concentration))
require_zero(s.simplify(initial_physical_energy-concentration**(-1+6*geometry_exponent)),
             'actual-flow family initial energy scaling')
require_zero(s.simplify(velocity_amplitude*aspect_ratio
                        -concentration/s.sqrt(normalization_energy)),
             'actual radial mean amplitude gain')
require_zero(s.simplify(velocity_amplitude/concentration
                        -concentration**(2*geometry_exponent)/s.sqrt(normalization_energy)),
             'actual critical history lower-bound scaling')

# This time-dependent rescaling is a kinematic path, not an unforced flow.
# Its exact energy inequality does not pay its critical defect history.
tau, h, viscosity, window_ratio = s.symbols(
    'tau h viscosity window_ratio', positive=True)
energy_exponent = s.Rational(1, 2)-2*h
radial_width_sq = 160*viscosity/(3*energy_exponent)
axial_width_sq = 8*viscosity/energy_exponent
path_energy = tau**energy_exponent
horizontal_ratio = (gaussian_norms['defect'][1]
                    /gaussian_norms['defect'][0]).subs(phase, 1)
axial_ratio = (gaussian_norms['defect'][2]
               /gaussian_norms['defect'][0]).subs(phase, 1)
path_dissipation = path_energy*(horizontal_ratio/(radial_width_sq*tau)
                               +axial_ratio/(axial_width_sq*tau**(1-2*h)))
path_balance = -s.diff(path_energy, tau)/2+viscosity*path_dissipation
path_balance_formula = energy_exponent*path_energy*(tau**(2*h)-3)/(8*tau)
require_zero(s.simplify(path_balance-path_balance_formula),
             'kinematic path energy loss')
total_viscous_dissipation = energy_exponent*s.Rational(1, 8)*(
    1/energy_exponent+1/(energy_exponent+2*h))
require_zero(total_viscous_dissipation-(1-2*h)/4,
             'kinematic path finite total dissipation')
stress_primitive = -tau**(-h)/h
require_zero(s.simplify(s.diff(stress_primitive, tau)-tau**(-1-h)),
             'stress time primitive')
window_stress = tau**h*(stress_primitive.subs(tau, window_ratio*tau)
                        -stress_primitive)
require_zero(s.simplify(window_stress-(1-window_ratio**(-h))/h),
             'nonvanishing normalized stress on each time interval')

# A separate three-component seed for the full signed-history diagnostic.
tria_a, tria_b, tria_c = s.symbols('tria_a tria_b tria_c', real=True)
tria_potential = s.Matrix([tria_a*y*z, tria_b*z*x, tria_c*x*y])
tria_velocity = s.Matrix([
    gaussian_derivative(tria_potential[2], 1)-gaussian_derivative(tria_potential[1], 2),
    gaussian_derivative(tria_potential[0], 2)-gaussian_derivative(tria_potential[2], 0),
    gaussian_derivative(tria_potential[1], 0)-gaussian_derivative(tria_potential[0], 1)])
tria_gradient = gaussian_gradient(tria_velocity)
tria_strain = (tria_gradient+tria_gradient.T)/2
tria_curl = s.Matrix([tria_gradient[2,1]-tria_gradient[1,2],
                     tria_gradient[0,2]-tria_gradient[2,0],
                     tria_gradient[1,0]-tria_gradient[0,1]])
tria_quadratic = (3*(tria_a**2+tria_b**2+tria_c**2)
                  -tria_a*tria_b-tria_a*tria_c-tria_b*tria_c)/8
tria_production = -s.Rational(16,27)*(tria_a-tria_b)*(tria_a-tria_c)*(tria_b-tria_c)
require_zero(s.trace(tria_gradient), 'three-component Gaussian divergence')
require_zero(gaussian_integral_factor(tria_velocity.dot(tria_velocity),2)-tria_quadratic,
             'three-component Gaussian energy')
require_zero(gaussian_integral_factor(sum(v*v for v in tria_gradient),2)-9*tria_quadratic,
             'three-component Gaussian gradient energy')
require_zero(gaussian_integral_factor(sum(gaussian_derivative(tria_gradient[i,j],k)**2
             for i in range(3) for j in range(3) for k in range(3)),2)-99*tria_quadratic,
             'three-component Gaussian second-derivative energy')
require_zero(gaussian_integral_factor(tria_curl.dot(tria_strain*tria_curl),3)-tria_production,
             'three-component Gaussian vorticity production')
require_zero(-4*gaussian_integral_factor(tria_strain.det(),3)-tria_production,
             'three-component Gaussian Betchov production')

print(json.dumps({
    'status': 'all exact residuals zero',
    'scope': 'differential identities, initial energy jets, and a kinematic path; no NS evolution',
    'mean_velocity': [str(e) for e in v],
    'lifted_force': str(s.cancel(g)),
    'stress_entries_nonzero': sum(e != 0 for e in [a, b, cc, d, e, f]),
    'arbitrary_stress_identity': 'checked by symbolic differentiation',
    'stretching_difference_nonzero': s.expand(delta) != 0,
    'hardy_profile_conditions': '0<=eta<1/2 and alpha<3/2',
    'general_cylindrical_stretching': 'checked for arbitrary component symbols',
    'localized_radial_hardy': 'checked for arbitrary swirl and cutoff functions',
    'ancient_circulation_operator': 'checked for an arbitrary swirl function',
    'signed_dual_reynolds_work': 'checked for arbitrary stress and test functions',
    'circulation_adjoint': 'checked for arbitrary drift and test functions',
    'gaussian_norms_divided_by_pi_over_2_to_3_over_2': {
        name: [str(value) for value in values]
        for name, values in gaussian_norms.items()
    },
    'gaussian_norm_order': ['velocity', 'horizontal_gradient', 'axial_gradient'],
    'gaussian_transfer_divided_by_pi_over_3_to_3_over_2': str(gtransfer),
    'gaussian_mean_circulation_source_polynomial': str(s.factor(gtorque)),
    'gaussian_circulation_diffusion_at_max_divided_by_exp_minus_1': [-8, -4],
    'gaussian_peak_initial_radial_velocity': str(peak_radial_velocity),
    'gaussian_peak_initial_circulation_rate': str(s.simplify(gamma_time_at_peak)),
    'exporting_mean_transfer_over_g3': str(export_transfer),
    'exporting_mean_defect_norms_over_g2': [str(value) for value in export_norms],
    'exporting_mean_peak_torque_and_radial_derivative_over_exp_minus_2': [16, -64],
    'exporting_mean_local_work_exchange_influx_over_exp_minus_3': [32, -16, 48],
    'radial_mean_divergence_constraint': 'checked for an arbitrary axial profile',
    'scaled_fluctuation_equation': 'mean and defect split checked before Leray projection',
    'actual_flow_energy_power': '-1+6h; 0<h<=1/6',
    'actual_flow_critical_history_power': '2h; finite interval, initial data vary with concentration',
    'triaxial_energy_over_g2': str(tria_quadratic),
    'triaxial_derivative_energy_ratios': [9, 99],
    'triaxial_production_over_g3': str(tria_production),
    'triaxial_parameters': ['tria_a', 'tria_b', 'tria_c'],
    'triaxial_history_seed_parameters': [0, 1, 2],
    'kinematic_path_energy_exponent': str(energy_exponent),
    'kinematic_path_balance_divided_by_energy': str(s.simplify(
        path_balance_formula/path_energy)),
    'kinematic_path_total_viscous_dissipation': str(s.simplify(
        total_viscous_dissipation)),
    'kinematic_path_conditions': '0<h<1/4, 0<tau<=1; not a Navier-Stokes solution',
}, indent=2))
