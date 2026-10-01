#!/usr/bin/env python3
"""A geometric curl observer, its physical defects, and a horizon reserve.

Symbolic identities use the full cylindrical Navier--Stokes differential
operator. Smooth Gaussian fields test nonlinear transport and internal swirl
production. The maximum principle, Biot--Savart estimate and stochastic
representation used for the no-swirl payment are analytic, not certified here.
"""

import json
import sympy as s


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(value, label):
    entries = list(value) if isinstance(value, s.MatrixBase) else [value]
    require(all(s.simplify(s.expand(v)) == 0 for v in entries), label)


def cylindrical_observer():
    r = s.symbols('r', positive=True)
    theta, z, nu = s.symbols('theta z nu', real=True)
    ur, ut, uz, p = [s.Function(name)(r, theta, z)
                     for name in ('ur', 'ut', 'uz', 'p')]
    lap = lambda f: (s.diff(f, r, 2) + s.diff(f, r)/r
                     + s.diff(f, theta, 2)/r**2 + s.diff(f, z, 2))
    adv = lambda f: (ur*s.diff(f, r) + ut*s.diff(f, theta)/r
                     + uz*s.diff(f, z))
    # Full vector Laplacian and convection, including the moving basis.
    ur_t = (nu*(lap(ur)-ur/r**2-2*s.diff(ut, theta)/r**2)
            - adv(ur)+ut**2/r-s.diff(p, r))
    ut_t = (nu*(lap(ut)-ut/r**2+2*s.diff(ur, theta)/r**2)
            - adv(ut)-ur*ut/r-s.diff(p, theta)/r)
    uz_t = nu*lap(uz)-adv(uz)-s.diff(p, z)
    eta = (s.diff(ur, z)-s.diff(uz, r))/r
    omega_r = s.diff(uz, theta)/r-s.diff(ut, z)
    b = ut/r
    angular = ((s.diff(uz, theta)*s.diff(b, r)
                - s.diff(ur, theta)*s.diff(b, z))/r
               + eta*s.diff(b, theta)
               + 2*nu*s.diff(omega_r, theta)/r**3)
    source = s.diff(b*b, z)+angular
    predicted = nu*(lap(eta)+2*s.diff(eta, r)/r)-adv(eta)+source
    actual = (s.diff(ur_t, z)-s.diff(uz_t, r))/r
    div = s.diff(ur, r)+ur/r+s.diff(ut, theta)/r+s.diff(uz, z)
    zero(actual-predicted+eta*div,
         'literal curl of full NS; only the displayed incompressibility defect')
    # Restrict only after differentiating the full equations.
    v, w, q, pressure = [s.Function(name)(r, z)
                         for name in ('v', 'w', 'q', 'pressure')]
    sub = {ur:v, ut:w, uz:q, p:pressure}
    axis = lambda expr: expr.subs(sub).doit()
    zero(axis(angular), 'every angular defect vanishes under exact axisymmetry')
    gamma = r*w
    gamma_prediction = (nu*(s.diff(gamma, r, 2)-s.diff(gamma, r)/r
                            + s.diff(gamma, z, 2))
                        - v*s.diff(gamma, r)-q*s.diff(gamma, z))
    zero(r*axis(ut_t)-gamma_prediction, 'unforced angular momentum equation')
    b_axis = w/r
    b_prediction = (nu*(s.diff(b_axis, r, 2)+3*s.diff(b_axis, r)/r
                         + s.diff(b_axis, z, 2))
                     - v*s.diff(b_axis, r)-q*s.diff(b_axis, z)
                     - 2*v*b_axis/r)
    zero(axis(ut_t)/r-b_prediction, 'swirl source retains meridional feedback')
    # A signed source pairing is paid even with swirl. Keep the actual
    # angular equation before integrating the physical kinetic balance.
    swirl_diss = s.diff(w, r)**2+s.diff(w, z)**2+w*w/r**2
    radial_flux = w*s.diff(w, r)
    axial_flux = w*s.diff(w, z)
    kinetic_rate = w*axis(ut_t)
    flux_div = (s.diff(r*v*w*w/2, r)/r+s.diff(q*w*w/2, z)
                - nu*(s.diff(r*radial_flux, r)/r+s.diff(axial_flux, z)))
    div_meridional = s.diff(v, r)+v/r+s.diff(q, z)
    zero(kinetic_rate+flux_div+v*w*w/r+nu*swirl_diss-w*w*div_meridional/2,
         'signed meridional transfer paid by actual swirl kinetic energy')
    lift_div = s.diff(v, r)+3*v/r+s.diff(q, z)
    physical_div = s.diff(v, r)+v/r+s.diff(q, z)
    zero(lift_div-physical_div-2*v/r, 'five-dimensional drift is not solenoidal')
    density = r**-2
    zero(s.diff(density, r, 2)+3*s.diff(density, r)/r,
         'physical volume density is harmonic only away from the axis')
    weighted_div = s.diff(density*v, r)+3*density*v/r+s.diff(density*q, z)
    zero(weighted_div-density*physical_div, 'weighted drift preserves physical volume')
    chi, beta = s.Function('chi')(r,z), s.Function('beta')(r,z)
    v_chi, q_chi = -r*s.diff(chi,z), 2*chi+r*s.diff(chi,r)
    eta_chi = (s.diff(v_chi,z)-s.diff(q_chi,r))/r
    zero(eta_chi+s.diff(chi,r,2)+3*s.diff(chi,r)/r+s.diff(chi,z,2),
         'physical meridional velocity fixes its elliptic streamfunction')
    zero(r*(v_chi**2+q_chi**2)-r**3*(s.diff(chi,r)**2+s.diff(chi,z)**2)
         -s.diff(2*r*r*chi**2,r), 'meridional kinetic energy with full radial boundary flux')
    zero(r**3*chi*s.diff(beta**2,z)-r**3*(v_chi/r)*beta**2
         -s.diff(r**3*chi*beta**2,z), 'source pairing is the same signed physical transfer')
    return {'observer':'eta=omega_theta/r',
            'axisymmetric_source':'partial_z((u_theta/r)**2)',
            'additional_angular_source':str(angular),
            'five_dimensional_drift_divergence':'2*u_r/r',
            'paid_signed_pairing':'integral r^2*chi*partial_z(b^2) dx = integral (u_r/r)*u_theta^2 dx',
            'physical_swirl_reserve':'R_swirl=||u_theta||_2^2/2; R_swirl_prime+pairing+nu*D_swirl=0',
            'scope':'exact differential identities; r>0, no solution existence asserted'}


def gaussian_fields():
    r = s.symbols('r', positive=True)
    z = s.symbols('z', real=True)
    amplitude, nu = s.symbols('A nu', positive=True)
    profile = s.exp(-r*r-z*z)
    psi = r*r*profile
    ur, uz = -s.diff(psi, z)/r, s.diff(psi, r)/r
    eta = (s.diff(ur, z)-s.diff(uz, r))/r
    zero(s.diff(r*ur, r)/r+s.diff(uz, z), 'Gaussian meridional incompressibility')
    zero(eta-2*(5-2*r*r-2*z*z)*profile, 'actual rotating-direction vorticity')
    transport = ur*s.diff(eta, r)+uz*s.diff(eta, z)
    zero(transport-(16*(r*r+z*z)-56)*z*profile**2,
         'genuine nonlinear parent transport, not a heat-only solution')
    require(transport.subs({r:1, z:1}) != 0, 'nonzero nonlinear vorticity evolution')
    # Whole-space smooth solenoidal swirl u=A*(-y,x,0)*exp(-|x|^2).
    # Its initial meridional velocity and eta vanish. Pressure drops out of
    # curl, but not out of the velocity; no zero-pressure assumption is made.
    b = amplitude*profile
    omega_r = -r*s.diff(b, z)
    omega_z = 2*b+r*s.diff(b, r)
    source = s.diff(b*b, z)
    zero(source+4*z*amplitude**2*profile**2, 'actual internal source from smooth swirl')
    zero(omega_r*s.diff(b, r)+omega_z*s.diff(b, z)-source,
         'source is generated by actual vorticity and velocity')
    require(source.subs({r:1, z:1, amplitude:1}) < 0, 'strict first generation')
    # A fixed cylindrical observer need not be bounded on general smooth
    # data. This is the same Gaussian swirl rotated to the x-axis.
    x, y = s.symbols('x y', real=True)
    xyz = (x, y, z)
    phi = s.exp(-x*x-y*y-z*z)
    u = s.Matrix([0, -2*z*phi, 2*y*phi])
    omega = s.Matrix([s.diff(u[2], y)-s.diff(u[1], z),
                      s.diff(u[0], z)-s.diff(u[2], x),
                      s.diff(u[1], x)-s.diff(u[0], y)])
    zero(sum(s.diff(u[i], xyz[i]) for i in range(3)), 'Cartesian datum incompressibility')
    numerator = -y*omega[0]+x*omega[1]
    axis_ray = (numerator/(x*x+y*y)).subs({x:0, z:0})
    zero(s.limit(y*axis_ray, y, 0, dir='+')+4,
         'regular physical curl but a singular fixed-axis observer')
    return {'nonlinear_no_swirl_transport':str(s.factor(transport)),
            'pure_swirl_eta_initial':'0', 'pure_swirl_eta_rate':str(source),
            'rotated_smooth_datum_observer':'eta(0,y,0) ~ -4/y',
            'scope':'smooth Schwartz initial data and exact initial NS curl rates; no finite-time blowup claim'}


def horizon_payment():
    E, G, D, nu, c, H, t, source, c_rate = s.symbols(
        'E G D nu c H t source c_rate', real=True)
    remaining = c*(H-t)
    reserve = E*(s.exp(2*remaining)-1)
    E_rate = 2*G-2*nu*D+2*source
    rate = s.diff(reserve, E)*E_rate+s.diff(reserve, t)+s.diff(reserve, c)*c_rate
    full = rate+2*G+2*nu*(s.exp(2*remaining)-1)*D
    expected = (2*s.exp(2*remaining)*(G-c*E)
                + 2*(s.exp(2*remaining)-1)*source
                + 2*E*s.exp(2*remaining)*(H-t)*c_rate)
    zero(full-expected, 'signed geometric clock including both feedback costs')
    zero(reserve.subs(t, H), 'reserve vanishes at its prescribed horizon')
    # Moving the observer itself produces a cost, even with the physical
    # vorticity held fixed. This is separate from material evolution.
    e1, e2, e3, d1, d2, d3, w1, w2, w3 = s.symbols('e1 e2 e3 d1 d2 d3 w1 w2 w3')
    k, kt, w = s.Matrix([e1,e2,e3]), s.Matrix([d1,d2,d3]), s.Matrix([w1,w2,w3])
    quotient = k.dot(w)/k.dot(k)
    observer_rate = sum(s.diff(quotient, k[i])*kt[i] for i in range(3))
    zero(observer_rate-(kt.dot(w)-2*quotient*k.dot(kt))/k.dot(k),
         'adaptive geometry is not free')
    return {'reserve':'Z*(exp(2*c*(H-t))-1)',
            'no_swirl_payment':'R_prime+2*abs(G)+2*nu*(exp(2*c*(H-t))-1)*D <= 0',
            'feedback_costs':['2*(exp(2*c*(H-t))-1)*source',
                              '2*Z*exp(2*c*(H-t))*(H-t)*c_prime'],
            'scope':'scalar identity; analytic bounds supply c and Lean PlanarParentReserve supplies absorption'}


def physical_scaling():
    r, lam = s.symbols('r lam', positive=True)
    z = s.symbols('z', real=True)
    b = s.exp(-r*r-z*z)
    scaled = lam**2*b.subs({r:lam*r, z:lam*z}, simultaneous=True)
    source = s.diff(b*b, z)
    zero(s.diff(scaled**2, z)-lam**5*source.subs(
        {r:lam*r, z:lam*z}, simultaneous=True), 'physical source has NS scaling degree five')
    zero(r*r*scaled-(r*r*b).subs({r:lam*r, z:lam*z}, simultaneous=True),
         'angular momentum supremum is invariant under NS scaling')
    return {'u_scaling_degree':1, 'kinetic_energy_scaling_degree':-1,
            'Gamma_sup_scaling_degree':0, 'eta_sup_scaling_degree':3,
            'eta_physical_L1_scaling_degree':0,
            'integrated_source_sup_scaling_degree':3,
            'integrated_radial_strain_scaling_degree':0,
            'scope':'exact NS rescaling of a fixed local solution; source growth does not refute radial-strain payment'}


def main():
    print(json.dumps({'cylindrical_equations':cylindrical_observer(),
                      'physical_data':gaussian_fields(),
                      'reserve':horizon_payment(),
                      'scaling':physical_scaling()}, indent=2))


if __name__ == '__main__':
    main()
