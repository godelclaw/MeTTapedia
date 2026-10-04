#!/usr/bin/env python3
"""Exact identities underlying the original-parent heat-work payment.

Complete pressure, transport and heat commutators are retained. The
arbitrary-data Sobolev/heat estimates and continuation implication are
analytic in README.md; finite fixtures are not their proof or a Lean
certificate. No time integration or closed Fourier evolution is used.
"""

import hashlib
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import heat_work_reserve as reserve
from cyclic_pressure_history import velocity_time_jets
from generated_fourth_moment import pressure, mixed_pressure, pair, vector_pair
from heat_remainder_pressure import plus, times, adv, solenoidal, projection, require, same
from pressure_gradient_stock import weighted_datum
from pressure_quadratic_storage import mode


def heat(vector, q):
    return [{k: value*q**sum(x*x for x in k) for k, value in row.items()} for row in vector]


def variation(v, h):
    """The pressure derivative is valid even for nonsolenoidal h."""
    magnitude, cross = f.dot(v, v), f.dot(v, h)
    receiver = [f.mul(magnitude, row) for row in v]
    change = [f.add(f.mul(magnitude, h[i]), f.scale(2, f.mul(cross, v[i]))) for i in range(3)]
    return (-vector_pair(change, f.grad(pressure(v)))
            -vector_pair(receiver, f.grad(mixed_pressure(v, h))))


def multiplier(k, tensor):
    square = sum(x*x for x in k)
    if not square:
        return f.ZERO
    return -sum((k[i]*k[j]*tensor[i][j] for i in range(3) for j in range(3)), f.ZERO)/square


def commutator_fourier(v, tensor):
    result = {}
    for ell in set().union(*v):
        for eta in set().union(*(row for matrix_row in tensor for row in matrix_row)):
            k = tuple(x+y for x, y in zip(ell, eta))
            coefficient = f.II*sum((eta[i]*v[i].get(ell, f.ZERO) for i in range(3)), f.ZERO)
            stress = [[tensor[i][j].get(eta, f.ZERO) for j in range(3)] for i in range(3)]
            value = coefficient*(multiplier(eta, stress)-multiplier(k, stress))
            result[k] = result.get(k, f.ZERO)+value
    return f.clean(result)


def commutator_checks():
    parent = weighted_datum(2, (1, 1, 1))
    receiver = plus(parent, times(Q(1, 4), reserve.nonlinear(parent)))
    rows = []
    for q in (Q(1), Q(1, 2)):
        z = heat(receiver, q)
        p, tensor = pressure(z), f.tensor(z, z)
        transported_tensor = [[f.adv(parent, row) for row in matrix_row] for matrix_row in tensor]
        defect = f.add(f.adv(parent, p), f.scale(-1, f.tensor_pressure(transported_tensor)))
        f.equal(defect, commutator_fourier(parent, tensor),
                'Transport-pressure commutator agrees with its full multiplier difference')
        magnitude = f.dot(z, z)
        cubic = [f.mul(magnitude, row) for row in z]
        gp, jac = f.grad(p), f.jac(parent)
        deformation = [f.add(*(f.mul(jac[j][i], gp[j]) for j in range(3))) for i in range(3)]
        lhs = variation(z, times(-1, adv(parent, z)))
        commutator_work = pair(f.trace(f.jac(cubic)), defect)
        deformation_work = vector_pair(cubic, deformation)
        rhs = commutator_work+deformation_work
        require(lhs == rhs, 'Transport cancels exactly, leaving pressure commutator and deformation')
        require(commutator_work > 0 > deformation_work and lhs > 0,
                'Both retained terms are nonzero and their competing signs matter')

        h0 = plus(times(-1, adv(receiver, parent)), times(2, projection(adv(receiver, parent))))
        mixed = times(-1, solenoidal(plus(adv(parent, receiver), adv(receiver, parent))))
        same(mixed, plus(times(-1, adv(parent, receiver)), h0),
             'Full mixed operator retains its order-zero projection correction')
        heat_comm = plus(heat(adv(parent, receiver), q), times(-1, adv(parent, z)))
        expected = plus(times(-1, adv(parent, z)), heat(h0, q), times(-1, heat_comm))
        same(heat(mixed, q), expected, 'Heating the mixed operator retains the complete commutator')
        if q != 1:
            require(any(heat_comm), 'The heat commutator in the nonconstant fixture is nonzero')
        rows.append(dict(heat_parameter=str(q), transport_work=str(lhs),
                         pressure_commutator_work=str(commutator_work),
                         gradient_deformation_work=str(deformation_work),
                         pressure_commutator_modes=len(defect),
                         heat_commutator_modes=len(set().union(*heat_comm))))

    # Finite edge cases support the universal normalized-vector argument in
    # the analytic derivation; they do not replace that argument.
    vectors = [(0, 0, 0), (1, 0, 0), (-1, 0, 0), (0, 1, 2), (2, -1, 0),
               (1, 2, 3), (-1, -2, -3), (8, -3, 1)]
    def matrix(k):
        square = sum(x*x for x in k)
        return [[Q(-k[i]*k[j], square) if square else Q(0) for j in range(3)] for i in range(3)]
    for eta, ell in itertools.product(vectors, repeat=2):
        first, second = matrix(eta), matrix(tuple(x+y for x, y in zip(eta, ell)))
        gap = sum((first[i][j]-second[i][j])**2 for i in range(3) for j in range(3))
        require(sum(x*x for x in eta)*gap <= 16*sum(x*x for x in ell),
                'Multiplier bound includes zero input, zero output and separated scales')
    return rows


def actual_source_checks():
    base = weighted_datum(2, (1, 1, 1))
    target = plus(base, times(Q(1, 4), reserve.nonlinear(base)))
    direction, k0, n = (1, 2, 3), (2, -1, 0), 32
    h = f.add(mode(k0, (1, 0, 0), 1)[0], mode(tuple(2*x for x in k0), (1, 0, 0), 1)[0])
    receiver = [{tuple(n*x for x in k): f.II*value/(n*sum(x*y for x, y in zip(direction, k)))
                 for k, value in row.items()} for row in target]
    initial = plus([f.scale(d, h) for d in direction], receiver)
    A = reserve.nonlinear(initial)
    work = -pair(f.dot(A, A), f.adv(A, pressure(A)))
    require(work > 0, 'The actual first generated source has positive present heat work')
    require(variation(A, A) == 5*work, 'The known source supplies the quintic radial derivative')
    viscous = velocity_time_jets(initial, Q(2, 7), 1)[0][1]
    same(plus(viscous, times(Q(-2, 7), [f.lap(row) for row in initial])), A,
         'The actual positive-viscosity first remainder derivative is the same full source')
    return dict(scale=n, input_modes=len(set().union(*initial)), source_modes=len(set().union(*A)),
                present_work=str(work), present_work_approximate=float(work),
                radial_variation=str(5*work),
                scope='Positive R_nu(A) follows analytically from positive work and heat continuity; no all-heat-age sign or exact reserve value is asserted')


def mixing_requires_energy():
    # This is a field-level coercivity test, not an asserted reachable
    # original-heat/remainder pair. The actual payment uses kinetic energy.
    U = weighted_datum(2, (1, 1, 1))
    mixed = times(-1, solenoidal(plus(adv(U, U), adv(U, U))))
    same(mixed, times(2, reserve.nonlinear(U)), 'The mixed direction for equal shapes')
    profile = reserve.variation(reserve.heat(U), reserve.heat(mixed))
    expected = reserve.q**10*(11+16*reserve.q**4-3*reserve.q**8)/33
    require(s.expand(profile-expected) == 0, 'An original-parent deformation can create zero-profile capacity')
    require(reserve.profile(reserve.heat(U)) == 0, 'Zero entire initial heat-work profile in the field test')
    rate = reserve.integrate(profile)
    require(rate == s.Rational(218, 3465), 'Exact positive mixed capacity derivative')
    # Positive-part directional derivatives are 1-Lipschitz in their scalar
    # direction, including at zero work. These edge cases catch sign errors.
    def selector(value, direction):
        return direction if value > 0 else (0 if value < 0 else max(direction, 0))
    for value, first, second in itertools.product((-2, 0, 3), repeat=3):
        require(abs(selector(value, first+second)-selector(value, first)) <= abs(second),
                'One-sided positive-part derivative does not assume additivity at zero')
    x = s.symbols('x', nonnegative=True)
    require(s.expand(x**4-x**3+s.Rational(27, 256)
                     -(x-s.Rational(3, 4))**2*(x*x+x/2+s.Rational(3, 16))) == 0,
            'Exact Young absorption certificate with constant 27/256')
    r = s.symbols('r', positive=True)
    require(s.integrate(r**s.Rational(-7, 8), (r, 0, 1)) == 8
            and s.integrate(r**s.Rational(-5, 4), (r, 1, s.oo)) == 4,
            'Both endpoints of the whole heat integral are integrable')
    return dict(mixed_creation=str(rate), scaled_creation='218*lambda^5/(3465*nu)',
                scope='General field-level failure of a bound by a fixed multiple of Y alone; not a claimed actually reached pair')


def checks():
    report = dict(commutators=commutator_checks(), actual_generated_source=actual_source_checks(),
                  field_coercivity=mixing_requires_energy(),
                  scope='Exact complete Fourier and scalar identities; general all-prefix source/mixed payment and continuation estimates are analytic, not Lean-certified')
    root = Path(__file__).resolve().parent
    sources = ['heat_work_parent_payment.py', 'heat_work_reserve.py', 'pressure_history_source.py',
               'heat_remainder_pressure.py', 'generated_fourth_moment.py',
               'cyclic_pressure_history.py', 'pressure_gradient_stock.py', 'pressure_quadratic_storage.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
    return report


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
