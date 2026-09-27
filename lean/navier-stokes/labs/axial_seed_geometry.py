#!/usr/bin/env python3
"""Exact angular sources of standing and travelling helical Gaussian seeds.

The accompanying note proves local persistence analytically. This script
checks the phase symmetry, stress, pressure source, derivative scaling and
initial mean-curvature rates; it does not integrate a Navier--Stokes flow.
Requires Sympy.
"""
import json
import sympy as s

r, z, theta, phi, t = s.symbols('r z theta phi t', real=True)
c, d = s.symbols('c d', real=True)
radial = s.exp(-r*r-z*z)

def mean_phi(expr):
    polynomial = s.Poly(s.expand_trig(s.expand(expr)).subs(
        {s.cos(phi): c, s.sin(phi): d}).expand(), c, d)
    out = 0
    for (i, j), coefficient in polynomial.terms():
        if i % 2 or j % 2:
            continue
        moment = (s.factorial(i)*s.factorial(j)
                  /(4**((i+j)//2)*s.factorial(i//2)*s.factorial(j//2)
                    *s.factorial((i+j)//2)))
        out += coefficient*moment
    return s.simplify(s.expand_trig(out).expand())

def require_zero(expr, label):
    value = s.trigsimp(s.simplify(expr))
    if value != 0:
        raise ArithmeticError((label, value))

psi0 = radial*(r**2*s.cos(2*phi)-r**4*s.sin(2*phi))
psis = psi0*s.cos(theta)
psih = radial*(r**2*s.cos(2*phi+theta)-r**4*s.sin(2*phi+theta))
stress = {}
for name, psi in [('standing', psis), ('helical', psih), ('base_defect', psi0)]:
    wr, wt = s.diff(psi, phi)/r, -s.diff(psi, r)
    ar, at, cross = [mean_phi(expr) for expr in [wr*wr, wt*wt, wr*wt]]
    torque = s.simplify(-r*s.diff(cross, r)-2*cross)
    pressure_source = s.simplify(s.diff(ar, r, 2)+(2*s.diff(ar, r)-s.diff(at, r))/r)
    stress[name] = dict(rr=ar, tt=at, rt=cross, torque=torque,
                        pressure_source=pressure_source)

base = stress['base_defect']
for key in base:
    require_zero(stress['standing'][key]-base[key]*s.cos(theta)**2,
                 'standing mean '+key)
    require_zero(stress['helical'][key]-base[key], 'helical mean '+key)
require_zero(base['rt']+2*r**4*radial**2, 'base signed Reynolds entry')
require_zero(base['torque']-4*r**4*(3-2*r*r)*radial**2, 'base circulation torque')
require_zero(s.diff(stress['standing']['torque'], theta, 2).subs(
    {r: 1, z: 0, theta: 0})+8/s.E**2, 'standing mean curvature source')
require_zero(s.diff(stress['helical']['torque'], theta, 2),
             'helical mean curvature cancellation')


# Joint rotation and phase shift is an exact symmetry of the helical seed.
angle = s.symbols('angle', real=True)
require_zero(psih.subs({phi: phi+angle, theta: theta-2*angle}, simultaneous=True)-psih,
             'joint rotation and phase symmetry')

# Pulling the independent phase back to theta=z/delta gives the actual
# axial derivative. Independent coefficients check all bivariate
# polynomials of total degree at most four, including mixed terms.
aspect = s.symbols('aspect', positive=True)
profile = sum(s.Symbol('p_'+str(i)+'_'+str(j))*z**i*theta**j
              for i in range(5) for j in range(5-i))
lifted = profile.subs(theta, z/aspect)
axial = lambda f: aspect*s.diff(f, z)+s.diff(f, theta)
require_zero(aspect*s.diff(lifted, z)-axial(profile).subs(theta, z/aspect),
             'first axial derivative under phase restriction')
require_zero(aspect**2*s.diff(lifted, z, 2)
             -axial(axial(profile)).subs(theta, z/aspect),
             'second axial derivative under phase restriction')

viscosity, amplitude = s.symbols('viscosity amplitude', real=True)
gamma0 = 2*r**2*radial
radial_diffusion = s.diff(gamma0, r, 2)-s.diff(gamma0, r)/r
initial_rate = (viscosity*(radial_diffusion+axial(axial(gamma0)))
                +amplitude**2*stress['standing']['torque'])
initial_curvature = axial(axial(gamma0)).subs({r: 1, z: 0, theta: 0})
initial_curvature_rate = axial(axial(initial_rate)).subs({r: 1, z: 0, theta: 0})
require_zero(initial_curvature+4*aspect**2/s.E, 'initial mean axial curvature')
require_zero(initial_curvature_rate-viscosity*aspect**2*(16+24*aspect**2)/s.E
             +amplitude**2*(16*aspect**2+8)/s.E**2,
             'actual initial curvature rate including viscosity')

wavenumber = s.symbols('wavenumber', positive=True)
axial_mass = s.integrate(s.exp(-2*z*z)*s.cos(wavenumber*z)**2, (z, -s.oo, s.oo))
require_zero(axial_mass-s.sqrt(s.pi/2)*(1+s.exp(-wavenumber**2/2))/2,
             'standing seed axial energy factor')

# Exact two-dimensional heat evolution of the angular-mean pressure source
# at the origin. This identifies its resolvent for any axial wave number.
poly_r = s.Poly(s.expand(base['pressure_source']/radial**2), r)
heat = 0
for (power,), coefficient in poly_r.terms():
    if power % 2:
        raise ArithmeticError('odd radial power')
    n = power//2
    heat += coefficient*s.factorial(n)*(4*t)**n/(1+8*t)**(n+1)
heat = s.factor(heat)
require_zero(heat.subs(t, 0)-8, 'initial planar pressure source at origin')
heat_integral = 8*t*(1024*t**4+1792*t**3+320*t**2+28*t+1)/(8*t+1)**5
require_zero(s.diff(heat_integral, t)-heat, 'cumulative planar pressure heat source')
require_zero(s.limit(heat_integral, t, s.oo)-s.Rational(1, 4),
             'integrated planar pressure heat source')
print(json.dumps({
    'status': 'all exact residuals zero',
    'standing_mean_torque': str(stress['standing']['torque']),
    'helical_mean_torque': str(stress['helical']['torque']),
    'standing_fast_curvature_rate_at_peak': '-8 epsilon^2 / e^2',
    'helical_fast_curvature_rate_at_peak': '0',
    'planar_mean_pressure_source': str(s.factor(base['pressure_source']/radial**2)),
    'planar_pressure_source_heat_at_origin': str(heat),
    'cumulative_planar_pressure_heat_source': str(heat_integral),
    'joint_phase_symmetry': 'checked exactly for an arbitrary rotation',
    'restriction_derivatives': 'checked on all bivariate polynomials through degree four',
    'initial_mean_curvature_rate': str(s.factor(initial_curvature_rate)),
    'standing_axial_energy': str(axial_mass),
    'scope': 'exact source identities; local persistence is analytic, no long-time closure'
}, indent=2))
