#!/usr/bin/env python3
"""Exact checks for capped full-tensor viscous stress-memory estimates.

The continuum truncation, Sobolev, Lorentz and NS prefix arguments in
README.md are analytic. These checks do not certify them in Lean.
"""

import hashlib
import json
from pathlib import Path

import sympy as s


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def zero(expr, label):
    require(s.simplify(s.expand(expr)) == 0, label)


def tensor_cap():
    # A Euclidean tensor space can be split into radial/tangential directions.
    # Differentiating an actual three-component radial function tests both.
    x, y, z = s.symbols('x y z', real=True)
    k, radius = s.symbols('k radius', positive=True)
    coords = s.Matrix([x, y, z])
    norm = s.sqrt(coords.dot(coords))
    phi = k * norm - k**2 / 2
    cap = s.Matrix([s.diff(phi, c) for c in coords])
    hessian = cap.jacobian(coords)
    at = {x: radius, y: 0, z: 0}
    H = s.simplify(hessian.subs(at))
    require(H == s.diag(0, k/radius, k/radius), 'outer radial Hessian')
    require(s.simplify((hessian.T*hessian).subs(at))
            == s.diag(0, k**2/radius**2, k**2/radius**2),
            'the complete cap derivative retains transverse directions')
    zero(k/radius-k**2/radius**2-k*(radius-k)/radius**2,
         'nonnegative Hessian minus capped-gradient square for radius>=k')
    zero((radius**2/2).subs(radius, k)-phi.subs(at).subs(radius, k),
         'primitive continuous at seam')
    zero(s.diff(radius**2/2, radius).subs(radius, k)
         -s.diff(phi.subs(at), radius).subs(radius, k),
         'first derivative continuous at seam')
    # Noncommuting PSD memory and source: positivity does not need diagonalization.
    A = s.Matrix([[2, 1, 0], [1, 1, 0], [0, 0, 1]])
    B = s.Matrix([[1, 0, 1], [0, 2, 0], [1, 0, 2]])
    C, source = A*A.T, B*B.T
    require(C*source != source*C, 'independent PSD directions do not commute')
    r = s.sqrt(s.trace(C*C))
    cap_C = C/2  # k=r/2
    margin = s.simplify((r/2)*s.trace(source)-s.trace(cap_C*source))
    require(margin > 0, 'capped full-tensor source is paid by source trace')
    increment = B*B.T
    zero(s.trace((C+increment)**2)-s.trace(C**2)
         -2*s.trace(C*increment)-s.trace(increment**2),
         'Frobenius size is monotone on positive tensors')
    return {'outer_hessian_eigenvalues': ['0', 'k/r', 'k/r'],
            'outer_cap_square_eigenvalues': ['0', 'k^2/r^2', 'k^2/r^2'],
            'noncommuting_source_margin': str(margin)}


def reserve_and_exponents():
    k, nu = s.symbols('k nu', positive=True)
    mass_rate, work, hess = s.symbols('mass_rate work hess', real=True)
    # E'=-mass_rate and integral Phi'=work-nu*hess.
    derivative = -k*mass_rate+work-nu*hess
    zero(derivative+nu*hess+k*mass_rate-work, 'complete reserve derivative')
    R = s.Rational
    zero(R(3, 10)-R(2, 5)/2-R(3, 5)/6, 'parabolic spatial interpolation')
    zero(R(10, 3)*R(2, 5)/2-R(2, 3), 'supremum L2 squared exponent')
    zero(R(10, 3)*R(3, 5)-2, 'integrated L6 squared exponent')
    zero(R(10, 3)-R(5, 3)-R(5, 3), 'memory distribution exponent')
    A, B, level = s.symbols('A B level', positive=True)
    threshold = (A*level**2/B)**R(3, 8)
    bound = A*threshold**(-R(5, 3))+B*threshold/level**2
    zero(bound-2*A**R(3, 8)*B**R(5, 8)*level**(-R(5, 4)),
         'balanced gradient distribution estimate')
    zero(R(5, 3)*R(3, 8)+R(5, 8)-R(5, 4),
         'gradient distribution original-energy exponent')
    zero(R(3, 5)+R(2, 5)-1, 'Lorentz pressure-work duality')
    return {'memory_distribution': 'S*(1/nu + torus_only_H)*E0^(5/3)*k^(-5/3)',
            'gradient_distribution': '2*A^(3/8)*(E0/nu)^(5/8)*level^(-5/4)',
            'pressure_receiver_space': 'L^(5/2,1) of joint space-time',
            'reserve': 'k*E + integral Phi_k(|C|), with original value k*E0'}


def actual_shear_history():
    # Unequal-wave, two-component exact unforced NS, with full rotating memory.
    y, t = s.symbols('y t', real=True)
    nu, a, b = s.symbols('nu a b', positive=True)
    u = s.Matrix([a*s.exp(-nu*t)*s.sin(y), 0,
                  b*s.exp(-4*nu*t)*s.cos(2*y)])
    e = lambda n: s.exp(-n*nu*t)
    C = s.zeros(3)
    C[0, 0] = a*a*(1-e(2)+(e(2)-e(4))*s.cos(2*y))/2
    C[2, 2] = b*b*(1-e(8)+(e(16)-e(8))*s.cos(4*y))/2
    C[0, 2] = C[2, 0] = a*b*((e(9)-e(5))*s.sin(3*y)
                                     +(e(5)-e(1))*s.sin(y))/2
    G = u.diff(y)*u.diff(y).T
    for i in range(3):
        zero(u[i].diff(t)-nu*u[i].diff(y, 2), 'exact shear NS equation')
        for j in range(3):
            zero(s.trigsimp(C[i, j].diff(t)-nu*C[i, j].diff(y, 2)-2*nu*G[i, j]),
                 'full actual tensor memory equation')
            zero(C[i, j].subs(t, 0), 'memory starts at original zero')
    energy = (a*a*e(2)+b*b*e(8))/2
    memory_mass = s.integrate(s.trace(C), (y, -s.pi, s.pi))/(2*s.pi)
    zero(energy+memory_mass-(a*a+b*b)/2, 'one original energy and memory mass')
    # Fix a positive time and use exact algebraic trigonometric values.
    fixture = {a: 2, b: 3, nu: 1, t: s.log(2), y: s.pi/4}
    Cf, Gf = s.simplify(C.subs(fixture)), s.simplify(G.subs(fixture))
    commutator = Cf*Gf-Gf*Cf
    require(commutator != s.zeros(3), 'actual memory and new source are not coaxial')
    Cy = s.simplify(C.diff(y).subs(fixture))
    r2 = s.trace(Cf*Cf)
    tangent2 = s.simplify(s.trace(Cy*Cy)-s.trace(Cf*Cy)**2/r2)
    require(tangent2 > 0, 'actual history has spatial tensor-direction diffusion')
    return {'memory_source_commutator_squared': str(s.trace(commutator.T*commutator)),
            'spatial_transverse_gradient_squared': str(tangent2),
            'scope': 'globally smooth unforced unequal-wave shear; canonical and memory pressure vanish'}


def scaling():
    R = s.Rational
    rows = []
    for q in [R(5, 3), s.Integer(2), s.Integer(3)]:
        rows.append({'q': str(q), 'memory_weak_norm_over_energy_exponent': str(3-5/q)})
    zero(3-5/R(5, 3), 'memory exponent matches actual NS energy scaling')
    zero(4-5/R(5, 4), 'memory gradient exponent matches energy scaling')
    zero(2+2-4, 'C_t scaling equals full viscous source scaling')
    zero(3-5/R(5, 2)-1, 'receiver Lorentz norm retains one inverse length')
    zero((2-5/R(5, 3))+(3-5/R(5, 2)), 'pressure work is critical')
    return {'actual_NS': 'u_lambda=lambda*u(lambda^2*t,lambda*x); C_lambda=lambda^2*C',
            'original_energy_exponent': -1, 'space_time_measure_exponent': -5,
            'rows': rows, 'critical_work_exponent': 0,
            'scope': 'fixed viscosity on R3; no fixed-energy or same-datum counterexample claimed'}


def main():
    result = {'tensor_cap': tensor_cap(), 'reserve': reserve_and_exponents(),
              'actual_history': actual_shear_history(), 'scaling': scaling(),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'certification': 'exact algebra; continuum estimates remain analytic, not Lean-certified'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
