#!/usr/bin/env python3
"""Exact identities for transverse parent response in actual 2D3C NS.

The continuum gradient lower bound, positive-viscosity comparison and
all-time reserve are analytic arguments in README.md. These checks do not
certify a PDE evolution by truncating its generated Fourier modes.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

import optimal_cubic_gauge as og

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require = og.require


def scalar_pair(a, b):
    return am.pairing([a], [b])


def check_physical_receiver(theta, amplitude, label):
    sx, sy = og.vd.sine((1, 0, 0)), og.vd.sine((0, 1, 0))
    parent = [f.scale(amplitude, sy), f.scale(amplitude, sx), {}]
    u = wh.addv(parent, [{}, {}, theta])
    f.equal(f.trace(f.jac(u)), {}, "complete velocity is incompressible")
    f.equal(f.diff(theta, 2), {}, "vertical receiver has no vertical dependence")
    p = f.tensor_pressure(f.tensor(u, u))
    expected_pressure = f.scale(amplitude**2, f.mul(og.cosine((1, 0, 0)),
                                                  og.cosine((0, 1, 0))))
    f.equal(p, expected_pressure, "canonical pressure includes the complete receiver")
    rhs = wh.scalev(-1, wh.addv(og.adv(u, u), f.grad(p)))
    expected_rhs = [{}, {}, f.scale(-1, f.adv(parent, theta))]
    wh.same_vectors(rhs, expected_rhs, "exact unforced nonlinear split")
    wh.same_vectors([f.lap(a) for a in parent], wh.scalev(-1, parent),
                    "both actual parents decay with their common heat rate")
    require(am.pairing(u, rhs) == f.ZERO, "nonlinearity supplies no kinetic energy")
    gradient = f.grad(theta)
    production = f.ZERO
    for i in range(2):
        for j in range(2):
            production -= scalar_pair(gradient[i], f.mul(f.diff(parent[j], i), gradient[j]))
    omega = f.curl(u)
    cubic = am.pairing(omega, og.adv(omega, u))
    require(cubic == production, "receiver production is actual vorticity stretching")
    energy_rate = am.pairing(gradient, f.grad(rhs[2]))
    require(energy_rate == production, "full transport gives the same signed work")
    laplacian = f.lap(theta)
    viscous_rate = am.pairing(gradient, f.grad(laplacian))
    require(viscous_rate == -scalar_pair(laplacian, laplacian),
            "complete scalar diffusion pays its second derivative")
    return {"label": label, "amplitude": str(amplitude),
            "gradient_squared": str(am.pairing(gradient, gradient)),
            "stretching": str(cubic),
            "diffusion": str(-viscous_rate),
            "generated_vertical_modes": len(rhs[2])}


def check_hyperbolic_geometry():
    a, b = s.symbols("a b", real=True)
    x, y = a+b, a-b
    velocity = s.Matrix([(s.sin(y)+s.sin(x))/2, (s.sin(y)-s.sin(x))/2])
    expected = s.Matrix([s.sin(a)*s.cos(b), -s.cos(a)*s.sin(b)])
    require(all(s.trigsimp(v) == 0 for v in velocity-expected),
            "rotated material coordinates retain the actual cellular field")
    c, h = s.cos(a)*s.cos(b), s.sin(a)*s.sin(b)
    gradient_generator = -expected.jacobian([a, b]).T
    require(s.simplify(gradient_generator-s.Matrix([[-c, -h], [h, c]])) == s.zeros(2),
            "exact covector transport at every point in the patch")
    require(s.diff(expected[0], a)+s.diff(expected[1], b) == 0,
            "the complete patch flow preserves area")
    B1 = s.Matrix([[0, 0], [-1, 0]])
    B2 = s.Matrix([[0, -1], [0, 0]])
    require(B1**2 == B2**2 == s.zeros(2), "each individual shear generator is nilpotent")
    require((B1+B2)**2 == s.eye(2), "their joint generator has a nonzero return loop")
    require((B1+B2)*s.Matrix([1, -1]) == s.Matrix([1, -1]),
            "the receiver has the expanding covector direction")
    delta, eta = s.Rational(1, 4), s.Rational(1, 4)
    c_lower, h_upper = s.Rational(15, 16), delta**2
    require((1-delta**2/2)**2 >= c_lower, "cosine lower bound on the whole patch")
    margin = 2*c_lower*eta-h_upper*(1+eta**2)
    require(margin > 0, "both cone boundaries point strictly inward")
    growth = c_lower-h_upper*eta
    initial = 2*(1-(2*delta)**2/2)
    require(growth == s.Rational(59, 64) and initial == s.Rational(7, 4),
            "uniform positive gradient growth and initial size")
    exponent = 2*growth-1
    coefficient_without_pi = 2*delta**2*initial**2/2
    require(exponent == s.Rational(27, 32), "patch-volume loss leaves exponential L2 growth")
    require(coefficient_without_pi == s.Rational(49, 256),
            "normalized physical area and gradient include the coordinate Jacobian")
    # For each derivative of order m, the commutator coefficient sum is 2^m-1.
    commutator_square = 2*sum((m+1)*(2**m-1)**2 for m in range(4))
    require(commutator_square == 450 and commutator_square < 32**2,
            "a uniform third-derivative reference bound has exponent at most 32")
    require(sum(m+1 for m in range(4))/2 == 5, "the original third-derivative stock is five")
    return {"cone_margin": str(margin), "pointwise_gradient_exponent": str(growth),
            "inviscid_gradient_squared_lower_bound": "49/(256*pi^2)*exp(27*s/32)",
            "positive_viscosity_gradient_squared_lower_bound": "49/(1024*pi^2)*exp(27*s/32)",
            "reference_error_majorant": "epsilon*3*s*(4*s+2)*exp(33*s)",
            "single_shear_nilpotence_index": 2, "joint_generator_square": "identity"}


def check_reserve():
    Y, D, r, nu, a, G = s.symbols("Y D r nu a G", real=True)
    V = Y*(s.exp(2*r)-1)
    derivative = s.diff(V, Y)*(2*G-2*nu*D)-s.diff(V, r)*a
    worst = derivative.subs(G, a*Y)+2*a*Y+2*nu*(s.exp(2*r)-1)*D
    require(s.simplify(worst) == 0, "the existing finite reserve pays absolute stretching")
    return {"reserve": "Y*(exp(2*r)-1)", "remaining_parent_strain": "r=A*exp(-nu*t)/nu",
            "payment": "V'+2*abs(G)+2*nu*(exp(2*r)-1)*D<=0"}


if __name__ == "__main__":
    receivers = [
        ("fixed transverse phase", og.vd.sine((1, -1, 0))),
        ("oblique receiver", og.cosine((2, 1, 0))),
        ("mixed phases", f.add(og.cosine((1, 0, 0)), og.cosine((0, 1, 0)),
                               f.scale(Q(1)/3, og.vd.sine((2, -1, 0)))))
    ]
    unit_parent = [og.vd.sine((0, 1, 0)), og.vd.sine((1, 0, 0)), {}]
    receivers.append(("retained generated phase", f.add(receivers[0][1],
                      f.scale(-Q(1)/4, f.adv(unit_parent, receivers[0][1])))))
    rows = [check_physical_receiver(v, A, label) for label, v in receivers for A in (Q(1), Q(3)/2)]
    require(any(row["stretching"] != "0" for row in rows),
            "the physical energy identities include nonzero internal stretching")
    geometry, reserve = check_hyperbolic_geometry(), check_reserve()
    dependencies = [Path(__file__), Path(og.__file__), Path(f.__file__),
                    Path(wh.__file__), Path(am.__file__), Path(og.vd.__file__)]
    result = {"physical_fixtures": rows, "geometry": geometry, "finite_payment": reserve,
              "scope": "Transverse parent composition requires more than a viscosity-uniform fixed-degree polynomial receiver response. The actual unforced 2D3C examples are globally smooth and paid by the existing full-datum exponential reserve. No arbitrary-data 3D payment or whole-space result is asserted.",
              "status": "Exact algebraic checks passed; interval, norm and PDE arguments remain analytic, not Lean-certified.",
              "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies}}
    print(json.dumps(result, indent=2), flush=True)
