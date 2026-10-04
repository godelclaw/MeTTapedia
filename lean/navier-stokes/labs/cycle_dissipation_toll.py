#!/usr/bin/env python3
"""Exact checks for actual pattern cycles with a vanishing energy fraction.

The smooth PDE construction, annular phases and rigid-orbit separation
are analytic in README.md. These fixtures retain the complete NS source
and check the symmetry, clock, energy and physical-vorticity calculations.
They are not an infinite cascade or a new Lean certificate.
"""

import ast
import hashlib
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
from reciprocal_pattern_cycles import exact_fixture, mode, require


def zero(expression, label):
    require(s.simplify(s.expand_trig(expression)) == 0, label)


def source_hashes():
    root = Path(__file__).resolve().parent
    pending, seen = [Path(__file__).resolve()], set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for node in ast.walk(ast.parse(path.read_text())):
            names = ([a.name for a in node.names] if isinstance(node, ast.Import)
                     else [node.module] if isinstance(node, ast.ImportFrom) and node.level == 0
                     else [])
            for name in names:
                if name:
                    dependency = root / (name.split('.')[0] + '.py')
                    if dependency.is_file():
                        pending.append(dependency)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)}


def rigid_fixtures():
    x, y = s.symbols('x y', real=True)
    coordinates = s.Matrix([x, y])
    def velocity(q):
        return s.Matrix([s.sin(q[1]), -s.sin(q[0])])
    def stream(q):
        return s.cos(q[0])+s.cos(q[1])
    rows = []
    for permutation in ((0, 1), (1, 0)):
        for signs in itertools.product((-1, 1), repeat=2):
            rotation = s.zeros(2)
            for j in range(2):
                rotation[j, permutation[j]] = signs[j]
            determinant = rotation.det()
            shift = s.zeros(2, 1) if determinant == 1 else s.Matrix([s.pi, s.pi])
            argument = rotation.T*(coordinates-shift)
            for value in rotation*velocity(argument)-velocity(coordinates):
                zero(value, 'The horizontal stabilizer keeps vector components and spatial arguments')
            zero(stream(argument)-determinant*stream(coordinates),
                 'The reflection branch exchanges the positive and negative cells')
            rows.append(dict(rotation=[[int(a) for a in row] for row in rotation.tolist()],
                             determinant=int(determinant),
                             horizontal_shift_pi=[int(a/s.pi) for a in shift],
                             stream_sign=int(determinant)))
    require(len(rows) == 8, 'All planar lattice orthogonal maps are included')
    angle = s.symbols('angle', real=True)
    zero(-s.cos(angle)-s.cos(angle+s.pi),
         'An independent vertical reflection only adds a half-turn to receiver phase')
    # Units of pi: three phases cannot agree under a quarter-turn rotation.
    phases = [Q(0), Q(2, 3), Q(4, 3)]
    gaps = []
    for i, first in enumerate(phases):
        for j, second in enumerate(phases):
            if i >= j:
                continue
            gap = min(abs(first-second-Q(k, 2)) for k in range(-8, 9))
            require(gap == Q(1, 6), 'Three comparison states remain distinct modulo quarter rotations')
            gaps.append(dict(first=i, second=j, phase_gap_pi=str(gap)))
    return dict(horizontal_stabilizers=rows, vertical_signs=[-1, 1], phase_gaps=gaps,
                scope='Continuous translation separation and annular phase regularity are proved analytically.')


def physical_identities():
    x, y, z, t = s.symbols('x y z t', real=True)
    A, nu = s.symbols('A nu', positive=True)
    coordinates = (x, y, z)
    parent = s.Matrix([s.sin(y), -s.sin(x), 0])
    amplitude = A*s.exp(-nu*t)
    w = s.Function('w')(t, x, y)
    u = amplitude*parent+s.Matrix([0, 0, A*w])
    pressure = -amplitude**2*s.cos(x)*s.cos(y)
    lap = lambda a: sum(s.diff(a, q, 2) for q in coordinates)
    rhs = u.diff(t)+u.jacobian(coordinates)*u+s.Matrix([s.diff(pressure, q) for q in coordinates])-nu*u.applyfunc(lap)
    for value in rhs[:2]:
        zero(value, 'The complete unforced horizontal NS equations hold')
    zero(rhs[2]-A*(w.diff(t)+amplitude*(s.sin(y)*w.diff(x)-s.sin(x)*w.diff(y))-nu*lap(w)),
         'The vertical component retains its full advection and diffusion')
    curl_parent = s.Matrix([0, 0, -s.cos(x)-s.cos(y)])
    curl_curl_parent = s.Matrix([s.diff(curl_parent[2], y), -s.diff(curl_parent[2], x), 0])
    for value in curl_curl_parent-parent:
        zero(value, 'The actual parent projection is a vorticity test after integration by parts')
    for field, expected, label in [
            (parent.dot(parent), 1, 'parent squared L2 norm'),
            (curl_parent.dot(curl_parent), 1, 'curl test squared L2 norm')]:
        average = s.integrate(s.integrate(field, (x, 0, 2*s.pi)), (y, 0, 2*s.pi))/(2*s.pi)**2
        zero(average-expected, label)
    sigma = A*(1-s.exp(-nu*t))/nu
    zero(sigma.diff(t)-amplitude, 'The same original clock measures physical vorticity cost')
    return dict(parent_norm_squared=1, curl_test_norm_squared=1,
                physical_cost='integral ||curl u||infinity dt >= integral alpha dt >= S/2',
                retained_equation='Full NS; the annular passive receiver and 3D perturbation are not Fourier truncations.')


def cost_algebra():
    A, nu, S, D, C = s.symbols('A nu S D C', positive=True)
    sigma, r = s.symbols('sigma r', nonnegative=True)
    time_slack = 2/A-1/(A-nu*sigma)
    zero(time_slack-(A-2*nu*sigma)/(A*(A-nu*sigma)),
         'Physical duration is at most 2S/A when A>=2nu S')
    upper = 2*nu*(2*S/A)*(2*A*A*C+2*D*D)/A**2
    zero(upper-8*nu*S/A*(C+D*D/A**2), 'Full perturbation is retained in the fractional energy loss')
    coarse = 8*nu*S*(C+1)/A
    zero(coarse-upper-8*nu*S/A*(1-D*D/A**2), 'D<=A permits a coarser original-data bound')
    zero(s.diff(2*r+s.log(1-r), r)-(1-2*r)/(1-r),
         'On [0,1/2], minus log(1-r) is at most 2r')
    lower_coefficient = (S/2)/(2*coarse)
    zero(lower_coefficient-A/(32*nu*(C+1)),
         'A pure logarithmic-energy payment needs at least a Reynolds-sized coefficient')
    parent_stock = (A-nu*sigma)/nu
    zero(s.diff(parent_stock, sigma)+1, 'The original parent stock pays each unit of parent time')
    zero(parent_stock.subs(sigma, 0)-parent_stock.subs(sigma, S)-S,
         'Small fractional kinetic loss does not reset or prevent spending the parent stock')
    return dict(horizon_upper='2 S/A',
                reference_gradient_constant='C_S=1+||grad w0||infinity^2 exp(2S)',
                fractional_loss_upper='8 nu S (C_S+1)/A',
                physical_vorticity_lower='S/2',
                logarithmic_energy_coefficient_lower='A/[32 nu (C_S+1)]',
                hypotheses='A>=2nu S; sqrt(Y0)exp(M/2)<=A/4; fractional upper<=1/2 for the logarithmic comparison.')


def checks():
    receiver = f.add(mode((1, 0, 0), Q(1, 5), True), mode((0, 2, 0), Q(1, 7)))
    fixtures = [exact_fixture(Q(7), Q(1, 100), sign, Q(2, 7), receiver) for sign in (-1, 1)]
    require(fixtures[0]['full_energy'] == fixtures[1]['full_energy'],
            'Opposite nonzero parent transfers have identical initial energy')
    return dict(rigid=rigid_fixtures(), physical=physical_identities(), costs=cost_algebra(),
                full_source_fixtures=fixtures,
                scope='Analytic actual periodic NS cycles, not a return to the separate whole-space rigid-frame seed. The explicit Fourier fixtures test identities, not the small perturbation threshold. No full-datum allowance or signed-renewal budget is refuted.',
                source_sha256=source_hashes())


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
