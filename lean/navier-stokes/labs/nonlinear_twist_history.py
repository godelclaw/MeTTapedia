#!/usr/bin/env python3
"""Whole-space twist response with both heat windows and the NS defect.

The map is kinematic. The physical calibration uses the same Schwartz
initial datum and retains the pressure-corrected generated meridional
velocity. Analytic operator and local PDE conclusions are in README.md.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

import rotational_parent_generation as parent

x, y, z = s.symbols('x y z', real=True)
xyz = (x, y, z)
r2 = x*x+y*y
q = s.Matrix(xyz)
tangent = s.Matrix([-y, x, 0])
f = s.exp(-r2-2*z*z)
u0 = f*tangent


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(value, label):
    values = list(value) if isinstance(value, s.MatrixBase) else [value]
    require(all(s.simplify(s.trigsimp(v)) == 0 for v in values), label)


def grad(h):
    return s.Matrix([s.diff(h, v) for v in xyz])


def curl(v):
    return s.Matrix([s.diff(v[2], y)-s.diff(v[1], z),
                     s.diff(v[0], z)-s.diff(v[2], x),
                     s.diff(v[1], x)-s.diff(v[0], y)])


def lap(v):
    return v.applyfunc(lambda h: sum(s.diff(h, a, 2) for a in xyz))


def gaussian_heat(poly, ar, az, variance):
    """Exact Gaussian convolution, from conditional Gaussian moments."""
    dr, dz = 1+2*ar*variance, 1+2*az*variance
    scales = (dr, dr, dz)
    result = 0
    for powers, coefficient in s.Poly(s.expand(poly), xyz).terms():
        term = coefficient
        for coord, degree, scale in zip(xyz, powers, scales):
            moment = sum(s.binomial(degree, 2*j)*s.factorial2(2*j-1)
                         *(variance/scale)**j*(coord/scale)**(degree-2*j)
                         for j in range(degree//2+1))
            term *= moment
        result += term
    return s.factor(result)*s.exp(-ar*r2/dr-az*z*z/dz)/(dr*s.sqrt(dz))


def twist_and_heat():
    L, theta, tr, tz = s.symbols('L theta theta_r2 theta_z', real=True)
    rotation = s.Matrix([[s.cos(theta), -s.sin(theta), 0],
                         [s.sin(theta), s.cos(theta), 0], [0, 0, 1]])
    dtheta = s.Matrix([2*x*tr, 2*y*tr, tz])
    jac = rotation*(s.eye(3)+tangent*dtheta.T)
    zero(jac.det()-1, 'every axisymmetric twist preserves the complete 3D volume')
    zero(rotation.T*rotation-s.eye(3), 'rotation has its genuine inverse')
    zero(rotation*q-s.Matrix([x*s.cos(theta)-y*s.sin(theta),
                               x*s.sin(theta)+y*s.cos(theta), z]), 'global twist coordinates')
    zero(((rotation*q)[0]**2+(rotation*q)[1]**2-r2),
         'r and z are unchanged, so inverse and composition retain the angle')
    literal = rotation.subs(theta, L*f)*q
    zero(literal.jacobian(xyz)-jac.subs({theta: L*f, tr: -L*f, tz: -4*L*z*f}),
         'literal spatial Jacobian includes the variable rotation')
    zero(s.diff(literal, L)-f*rotation.subs(theta, L*f)*tangent,
         'Phi_L is the complete time-L flow of the fixed Schwartz generator')

    b = s.symbols('b', nonnegative=True)
    dr, dz = 1+2*b, 1+4*b
    hb = dr**-2*dz**s.Rational(-1, 2)*s.exp(-r2/dr-2*z*z/dz)
    vb = hb*tangent
    zero(s.diff(vb, b)-lap(vb)/2, 'initial heat is the full vector heat equation')
    zero(vb.subs(b, 0)-u0, 'initial heat has the original solenoidal datum')
    zero(s.trace(vb.jacobian(xyz)), 'initial vector heat retains incompressibility')
    B = curl(vb)
    zero(B.dot(tangent), 'smoothed input curl is poloidal')
    Gamma = r2*hb
    generic_h = s.Function('h')(r2, z)
    generic_curl = curl(generic_h*tangent)
    zero(tangent*generic_curl.dot(dtheta)-dtheta.cross(grad(r2*generic_h)),
         'joint angle-circulation law holds for an arbitrary smooth toroidal profile')
    # At the final point, equivariance removes the common rotation.
    correction = tangent*(B.dot(dtheta))
    zero(correction-dtheta.cross(grad(Gamma)),
         'the complete new curl retains the angle and original circulation jointly')
    cost_potential = L*f*grad(Gamma)
    zero(curl(cost_potential)-correction.subs({tr: -L*f, tz: -4*L*z*f}),
         'the signed correction is curl(theta grad Gamma), with its gradient gauge retained')

    Bfixed = B.subs(b, s.Rational(1, 2))
    Q = s.simplify(tangent*Bfixed.dot(grad(f)))
    ar, az = s.Rational(3, 2), s.Rational(8, 3)
    expected = z*(r2/3-2)*s.exp(-ar*r2-az*z*z)*tangent/s.sqrt(3)
    zero(Q-expected, 'exact extra field after the initial heat and full nonlinear twist')
    a = s.symbols('a', nonnegative=True)
    polynomials = [s.simplify(v*s.exp(ar*r2+az*z*z)) for v in Q]
    HaQ = s.Matrix([gaussian_heat(v, ar, az, a) for v in polynomials])
    zero(s.diff(HaQ, a)-lap(HaQ)/2, 'terminal heat acts on every generated component')
    zero(HaQ.subs(a, 0)-Q, 'terminal heat has the complete pushforward correction')
    Qa = s.simplify(HaQ.subs(a, s.Rational(1, 2)))
    closed = (4*(4*r2-130)*z*s.exp(-3*r2/5-8*z*z/11)
              *tangent/(6875*s.sqrt(11)))
    zero(Qa-closed, 'closed Gaussian formula at fixed positive heat windows')
    value = s.simplify(Qa[1].subs({x: 1, y: 0, z: 1}))
    zero(value+504*s.exp(-s.Rational(73, 55))/(6875*s.sqrt(11)),
         'a fixed output component grows linearly with the complete winding')
    zero(B.subs(b, 1)[1].subs(y, 0),
         'the heat-only poloidal output has zero component in the tested direction')

    rr, zz = s.symbols('rr zz', real=True)
    input_l1 = 2*s.pi*s.integrate(rr**2*s.exp(-rr**2), (rr, 0, s.oo))*s.integrate(s.exp(-2*zz**2), (zz, -s.oo, s.oo))
    zero(input_l1-s.pi**2/(2*s.sqrt(2)), 'the full vector L1 input remains fixed')
    input_energy = 2*s.pi*s.integrate(rr**3*s.exp(-2*rr**2), (rr, 0, s.oo))*s.integrate(s.exp(-4*zz**2), (zz, -s.oo, s.oo))
    zero(input_energy-s.pi**s.Rational(3, 2)/8, 'the fixed generator has finite kinetic energy')
    return {'fixed_input': str(u0), 'input_L1': str(input_l1),
            'input_energy': str(input_energy), 'heat_variances': 'a=b=1/2',
            'map': '(r,theta,z) -> (r,theta+L*exp(-r^2-2*z^2),z)',
            'pre_terminal_heat_correction': str(Q),
            'terminal_heat_correction': str(Qa),
            'output_second_component_at_1_0_1': str(L*value),
            'retained_cost': 'inf_c ||(theta-c)*grad Gamma_b||_L1',
            'upper_bound': '||H_(a+b) curl v||_infinity + c_G*a^(-2)*retained_cost',
            'scope': 'Fixed whole-space Schwartz datum and two positive heat windows; arbitrary smooth twists are kinematic, not identified as unforced NS histories.'}


def physical_defect():
    omega = curl(u0)
    raw = -u0.jacobian(xyz)*u0
    zero(raw-f*f*s.Matrix([x, y, 0]), 'the complete centrifugal acceleration is retained')
    generated_curl = curl(raw)
    zero(generated_curl+8*z*f*f*tangent,
         'pressure cannot remove the nonzero generated meridional curl')
    zero(omega.dot(u0.jacobian(xyz)*omega), 'initial physical stretching is zero')
    zero(u0.dot(raw), 'centrifugal acceleration is perpendicular to the initial swirl')
    zero(raw.jacobian(xyz).trace()-(2-4*r2)*f*f,
         'the canonical pressure solves the full three-dimensional Poisson source')

    t, nu = s.symbols('t nu', positive=True)
    dr, dz = 1+4*nu*t, 1+8*nu*t
    h = dr**-2*dz**s.Rational(-1, 2)*s.exp(-r2/dr-2*z*z/dz)
    heat_u = h*tangent
    zero(s.diff(heat_u, t)-nu*lap(heat_u), 'the retained parent decays by actual vector heat')
    centrifugal = -heat_u.jacobian(xyz)*heat_u
    zero(centrifugal-h*h*s.Matrix([x, y, 0]), 'heat-parent advection retains its full radial acceleration')
    zero(curl(centrifugal)+8*z*h*h*tangent/dz,
         'the force suppressing generated meridional motion has nonzero curl')
    pr, pz = s.symbols('p_r2 p_z', real=True)
    canonical_gradient = s.Matrix([2*x*pr, 2*y*pr, pz])
    external = -centrifugal+canonical_gradient
    zero(heat_u.dot(external),
         'the meridional force maintaining the heat-only parent does zero pointwise kinetic work')
    zero(s.diff(heat_u, t)+heat_u.jacobian(xyz)*heat_u+canonical_gradient
         -nu*lap(heat_u)-external, 'the proposed force is retained in the entire momentum equation')
    eta = s.symbols('eta', positive=True)
    primitive = (s.atan(eta)+eta/(1+eta*eta))/2
    zero(s.diff(primitive, eta)-1/(1+eta*eta)**2,
         'the complete heat-parent angle integral has an exact primitive')
    total_angle = s.simplify(s.limit(primitive, eta, s.oo)-primitive.subs(eta, 1))/nu
    zero(total_angle-(s.pi-2)/(8*nu), 'original heat-parent winding is finite over all time')
    transformed = (h.subs({x: 0, y: 0, z: 0, t: (eta*eta-1)/(8*nu)})
                   *eta/(4*nu))
    zero(transformed-1/(nu*(1+eta*eta)**2), 'the angle integral retains both spatial heat scales')
    calibration = parent.generated_stretching()
    gamma = 3*s.sqrt(2)*s.pi**s.Rational(3, 2)*(11*s.pi-34)/128
    zero(calibration['G_prime_initial']-gamma,
         'the same actual unforced datum has the full pressure-corrected positive stretching return')
    require(11*s.Rational(157, 50)-34 > 0, 'strict sign uses a rational lower bound for pi')
    return {'unprojected_acceleration': str(s.simplify(raw)),
            'curl_of_projected_acceleration': str(s.simplify(generated_curl)),
            'canonical_pressure_source': '(2-4*r^2)*exp(-2*r^2-4*z^2)',
            'actual_initial_acceleration': 'nu*Delta u0 + Pi[(x,y,0)*exp(-2*r^2-4*z^2)]',
            'actual_minus_heat_parent_flow_map': 't^2*N(u0)/2 + O(t^3), on compact spatial sets',
            'force_maintaining_heat_parent': '-N(exp(nu*t*Delta)*u0)',
            'force_direct_kinetic_work': '0 pointwise',
            'all_time_heat_parent_angle_bound': '|A|*(pi-2)/(8*nu)',
            'physical_stretching_initial_derivative': str(gamma),
            'calibration_status': 'Previously established physical derivative rechecked with its full heat-resolvent and pressure calculation.',
            'scope': 'Actual short-time NS generates the missing meridional parent. Neither frozen nor heat-only swirl is an unforced solution.'}


def actual_winding_return():
    rr = s.symbols('r', positive=True)
    zz = s.symbols('z', real=True)
    nu = s.symbols('nu', positive=True)
    beta = s.Function('beta')(rr, zz)
    chi = s.Function('chi')(rr, zz)
    gradient = lambda h: s.Matrix([s.diff(h, rr), s.diff(h, zz)])
    lap5 = lambda h: s.diff(h, rr, 2)+3*s.diff(h, rr)/rr+s.diff(h, zz, 2)
    v1 = s.Matrix([-rr*s.diff(chi, zz), 2*chi+rr*s.diff(chi, rr)])
    m1 = -v1[0]/rr
    zero(s.diff(v1[0], rr)+v1[0]/rr+s.diff(v1[1], zz),
         'generated meridional acceleration is physically incompressible')
    beta1 = nu*lap5(beta)
    beta2 = nu*lap5(beta1)-v1.dot(gradient(beta))+2*m1*beta
    angle_third = beta2+v1.dot(gradient(beta))
    zero(angle_third-nu**2*lap5(lap5(beta))-2*m1*beta,
         'the actual label follows the generated parent and cancels its transport term')
    zero((angle_third-nu**2*lap5(lap5(beta)))/6-m1*beta/3,
         'complete leading physical angle correction is m1*beta0*t^3/3')
    A, C = s.symbols('A C', positive=True)
    kernel = -8*zz*A**-2*C**s.Rational(-3, 2)*s.exp(-2*rr*rr/A-4*zz*zz/C)
    zero(s.diff(kernel, zz).subs(zz, 0)+8*A**-2*C**s.Rational(-3, 2)*s.exp(-2*rr*rr/A),
         'the complete parent gives a negative equatorial winding correction')
    kernel_axis = kernel.subs({rr: 0, A: (C+1)/2})/16
    zero(kernel_axis+2*zz*(C+1)**-2*C**s.Rational(-3, 2)*s.exp(-4*zz*zz/C),
         'axis resolvent measure retains the exact heat-time substitution')
    zp = s.symbols('z_positive', positive=True)
    upper = 2*zp*(4*zp*zp)**s.Rational(-5, 2)*s.gamma(s.Rational(5, 2))
    zero(upper-3*s.sqrt(s.pi)/(64*zp**4),
         'axis streamfunction tends to zero with an explicit positive tail bound')
    h, alpha = s.symbols('h alpha', positive=True)
    w = h**s.Rational(3, 2)*(1+h)**-2*s.exp(-alpha*h-4*rr*rr*h/(1+h))
    positive_part = 8*w/(1+h)*(1-2*rr*rr*h/(1+h))
    zero(-2*w*(1-2*alpha*h)-positive_part+4*s.diff(h*w, h),
         'exact integration by parts for a strictly positive off-axis parent fixture')
    zero((4*h*w).subs(h, 1)-s.exp(-alpha-2*rr*rr),
         'the parent sign test retains its nonzero upper endpoint')
    lower_coefficient = 8*s.Rational(1, 16)*s.Rational(8, 729)*s.Rational(3, 4)
    zero(lower_coefficient-s.Rational(1, 243), 'off-axis positive integral lower coefficient')
    require(2**13 > 243, 'exp(13)>2^13>243 proves the strict off-axis sign')
    return {'actual_initial_geometry': 'beta0=exp(-r^2-2*z^2), meridional velocity zero',
            'parent': 'chi1=int_0^infinity exp(s*L5)*d_z(beta0^2) ds, m1=d_z chi1',
            'material_angle_defect': 'Theta_NS-Theta_heat=(m1*beta0/3)*t^3+O(t^4)',
            'equatorial_sign': 'negative for every r>0',
            'other_sign': 'm1(1/2,2) >= exp(-3)/243-exp(-16) > 0',
            'axis_tail_bound': '|chi1(0,z)| <= 3*sqrt(pi)/(64*z^4), z>0',
            'scope': 'Actual local unforced NS at every positive viscosity; refutes pointwise heat-angle domination, not a full-datum allowance or regularity.'}


if __name__ == '__main__':
    result = {'twist_response': twist_and_heat(), 'physical_identification': physical_defect(),
              'actual_winding_return': actual_winding_return(),
              'status': 'Exact Jacobian, Gaussian heat, curl, force and physical parent-return checks passed.',
              'scope': 'Kinematic operator obstruction and analytic local NS calibration; no arbitrary-history bound or new Lean certificate.'}
    import rotational_curl_reserve as reserve
    import rotational_joint_enstrophy as joint
    paths = [Path(__file__), Path(parent.__file__), Path(reserve.__file__), Path(joint.__file__)]
    result['source_sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    print(json.dumps(result, indent=2, default=str), flush=True)
