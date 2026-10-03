#!/usr/bin/env python3
"""A complete pressure-impulse return depletes across unequal scales.

Symbolic Fourier phase operators retain the actual physical wave number
and every generated output. Positive coefficient polynomials certify the
unbounded frequency range. Independent physical NS jets and the full
viscous conditional-moment equations check the identities. The transfer
to actual positive-viscosity intervals is analytic in README.md; this is
neither a closed mode system nor a Lean certificate or an all-time bound.
"""

from fractions import Fraction as Q
from math import comb
import json

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import seed, velocity_time_jets
from pressure_impulse_return import (NU, RING, impulse_fourth_coefficients,
    material_fourth_coefficients, viscosity_jets)


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


class PhaseOperators:
    """The third integer phase denotes k*z; k is a symbolic physical scale."""
    def __init__(self):
        self.domain = f.QQ_I.frac_field('k')
        self.k = self.domain.gens[0]
        self.variable = self.domain.symbols[0]

    def diff(self, field, axis):
        return f.clean({n: f.II*n[axis]*(self.k if axis == 2 else 1)*a
                        for n, a in field.items()})

    def advect(self, velocity, field):
        return f.add(*(f.mul(velocity[j], self.diff(field, j)) for j in range(3)))

    def pressure(self, u, v):
        source = f.add(*(self.diff(self.diff(f.mul(u[i], v[j]), i), j)
                         for i in range(3) for j in range(3)))
        require(not source.get(f.ORIGIN, 0), 'Canonical pressure source has zero mean')
        return {n: a/(n[0]**2+n[1]**2+self.k**2*n[2]**2)
                for n, a in source.items() if n != f.ORIGIN}

    def mean(self, field):
        return s.factor(self.domain.to_sympy(self.domain.convert(field.get(f.ORIGIN, 0))))

    def jets(self, amplitudes):
        velocity = [[{n: self.domain.convert(a)*q for n, a in row.items()}
                     for row, q in zip(seed(1), amplitudes)]]
        pressure = []
        for n in range(4):
            p = f.add(*(f.scale(comb(n, j), self.pressure(velocity[j], velocity[n-j]))
                        for j in range(n+1)))
            pressure.append(p)
            if n < 3:
                tangent = [f.add(f.scale(-1, self.diff(p, i)), *(
                    f.scale(-comb(n, j), self.advect(velocity[j], velocity[n-j][i]))
                    for j in range(n+1))) for i in range(3)]
                f.equal(f.add(*(self.diff(tangent[i], i) for i in range(3))), {},
                        'Complete symbolic-frequency Euler tangent is solenoidal')
                velocity.append(tangent)
        require(not pressure[0], 'The complete initial pressure vanishes')
        return velocity, pressure

    def specialize(self, field, scale):
        def evaluate(poly):
            return sum((a*f.QQ_I(scale)**n[0] for n, a in poly.items()), f.ZERO)
        out = {}
        for n, a in field.items():
            a = self.domain.convert(a)
            denominator = evaluate(a.denom)
            require(denominator != 0, 'The physical specialization avoids every pole')
            out[(n[0], n[1], scale*n[2])] = evaluate(a.numer)/denominator
        return f.clean(out)

    def impulse_coefficients(self, velocity, pressure):
        gradient = [[self.diff(p, i) for i in range(3)] for p in pressure]
        material = []
        for i in range(3):
            fields, values = [g[i] for g in gradient], []
            while fields:
                values.append(fields[0])
                fields = [f.add(fields[n+1], *(
                    f.scale(comb(n, j), self.advect(velocity[j], fields[n-j]))
                    for j in range(n+1))) for n in range(len(fields)-1)]
            material.append(values)
        # P_t=t^2 A+t^3 B+t^4 C+O(t^5) on the complete Euler paths.
        A = [f.scale(Q(1, 2), row[1]) for row in material]
        B = [f.scale(Q(1, 6), row[2]) for row in material]
        C = [f.scale(Q(1, 24), row[3]) for row in material]
        aa, ab = f.dot(A, A), f.dot(A, B)
        parts = [self.mean(f.scale(4, f.mul(aa, f.dot(A, C)))),
                 self.mean(f.scale(2, f.mul(aa, f.dot(B, B)))),
                 self.mean(f.scale(4, f.mul(ab, ab)))]
        return [self.mean(f.mul(aa, aa)), self.mean(f.scale(4, f.mul(aa, ab))),
                s.factor(sum(parts))], parts


def positive_coefficients(expression, variable):
    """Exact sufficient positivity certificate for every positive variable."""
    numerator, denominator = s.fraction(s.factor(expression))
    rows = []
    for part in (numerator, denominator):
        poly = s.Poly(part, variable, domain=s.QQ)
        coefficients = poly.all_coeffs()
        require(any(c > 0 for c in coefficients) and all(c >= 0 for c in coefficients),
                'Nonzero polynomials with nonnegative coefficients are positive on the positive axis')
        rows.append(dict(degree=poly.degree(), coefficients=list(map(str, coefficients))))
    return dict(numerator=rows[0], denominator=rows[1])


def full_frequency_law():
    ops = PhaseOperators()
    k = ops.variable
    amplitudes = ((1, 1, 1), (2, 1, 1), (1, 2, 1), (1, 1, 2))
    normalized, pieces, records = [], [], []
    for amps in amplitudes:
        velocity, pressure = ops.jets(amps)
        coeff, parts = ops.impulse_coefficients(velocity, pressure)
        factor = s.prod(amps)**4
        leading = 243*k**4*(9*k**4+4*k*k+20)/(512*(k*k+2)**4)
        require(s.factor(coeff[0]-factor*leading) == 0 and coeff[1] == 0,
                'The leading moment and vanishing odd-time coefficient have the full frequency law')
        normalized.append(coeff[2]/factor)
        pieces.append([a/factor for a in parts])
        # Independent physical Fourier recurrence at previously unused scales.
        for scale in (2, 7):
            initial = [{(n[0], n[1], scale*n[2]): q*a for n, a in row.items()}
                       for row, q in zip(seed(1), amps)]
            literal_v, literal_p = velocity_time_jets(initial, Q(0), 4)
            for actual, wanted in zip(velocity, literal_v):
                for a, b in zip(actual, wanted):
                    f.equal(ops.specialize(a, scale), b, 'Independent complete physical velocity jets')
            for actual, wanted in zip(pressure, literal_p):
                f.equal(ops.specialize(actual, scale), wanted, 'Independent complete physical pressure jets')
            exact = material_fourth_coefficients(literal_v, [f.grad(p) for p in literal_p])
            for symbolic, literal in zip(coeff, exact):
                require(s.factor(symbolic.subs(k, scale)) == s.Rational(str(literal.x))
                        and not literal.y, 'Independent full physical impulse coefficients')
        records.append(dict(amplitudes=amps, time_coefficients=list(map(str, coeff)),
                            signed_parts=list(map(str, parts))))
    base = normalized[0]
    # The analytic degree/divisibility/translation argument in README.md
    # gives exactly the basis (abc)^4(a^2,b^2,c^2). The fourth evaluation
    # independently checks the coefficient inferred from the other three.
    da = s.factor((base-normalized[1])/3)
    db = s.factor((base-normalized[2])/3)
    dc = s.factor(-base-da-db)
    require(s.factor(normalized[3]+da+db+4*dc) == 0,
            'Unused amplitude evaluation checks the complete three-term basis')
    certificates = [positive_coefficients(a, k) for a in (da, db, dc)]
    old = -pieces[0][0]
    new = pieces[0][1]+pieces[0][2]
    joint_margin = positive_coefficients(s.Rational(2, 3)*old-new, k)
    require(s.factor(-base-old+new) == 0, 'Signed return minus both positive terms is the full depletion')
    require(s.limit(new/old, k, s.oo) == s.Rational(2, 5),
            'Exact large-scale ratio of positive costs to signed payment')
    return dict(status='Uniform frequency and unequal-amplitude law passed',
                coefficients=list(map(str, (da, db, dc))), sign_certificates=certificates,
                balanced_margin=joint_margin, balanced_cost_ratio_limit='2/5',
                fixtures=records), (da, db, dc), k


def viscous_checks(depletion, variable):
    reports = []
    for scale, amps in ((3, (1, 2, 3)), (6, (2, 1, 1))):
        initial = [{(n[0], n[1], scale*n[2]): q*a for n, a in row.items()}
                   for row, q in zip(seed(1), amps)]
        velocity, pressure = viscosity_jets(initial, 4)
        gradient = [f.grad(p) for p in pressure]
        actual = impulse_fourth_coefficients(velocity, gradient, NU)
        eigenvalue = scale*scale+2
        generated = [[{}, {}, {}], gradient[1],
                     [f.scale(-2*NU*eigenvalue, a) for a in gradient[1]],
                     [f.scale(3*NU**2*eigenvalue**2, a) for a in gradient[1]]]
        forecast = impulse_fourth_coefficients([[{}, {}, {}] for _ in range(5)], generated, NU)
        d = s.prod(amps)**4*sum(a*a*c.subs(variable, scale) for a, c in zip(amps, depletion))
        difference = [s.expand(RING.to_sympy(a-b)) for a, b in zip(actual, forecast)]
        require(difference == [0, 0, -d],
                'Full viscous moment PDE agrees with the viscosity-independent nonlinear difference')
        reports.append(dict(wave_number=scale, amplitudes=amps,
                            actual_coefficients=list(map(str, actual)),
                            forecast_coefficients=list(map(str, forecast)),
                            difference=list(map(str, difference))))
    return reports


if __name__ == '__main__':
    law, coefficients, variable = full_frequency_law()
    print(json.dumps(dict(frequency=law, viscosity=viscous_checks(coefficients, variable),
        physical_scope='Every integer k>=1, every parent amplitude and positive viscosity; a datum-dependent initial interval',
        open='Later complete returns and an arbitrary-horizon initial-data payment',
        certification='Exact algebra plus analytic local PDE argument; not Lean-certified'), indent=2), flush=True)
