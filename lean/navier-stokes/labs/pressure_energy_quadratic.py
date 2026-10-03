#!/usr/bin/env python3
"""Exact joint pressure/energy obstruction and a generating-parent repair.

The matrix margin, uniform viscous interval and amplitude rescaling are
analytic in README.md. Every Fourier output of the NS jets is retained.
No finite-mode trajectory or claim of singularity is made.
"""

import json
import math
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import seed, velocity_time_jets
from kinetic_pressure_entropy import moment_jets
from retained_energy_alignment import mean, product_jets, constant


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def gram_jets(scale, nu):
    initial = [{(k[0], k[1], scale*k[2]): value for k, value in field.items()}
               for field in seed(1)]
    velocity, pressure = velocity_time_jets(initial, nu, 4)
    tensors, _, _ = moment_jets(velocity, pressure, nu, Q(0))
    energy = [f.trace(L) for L in tensors]
    # An independent Euler calculation uses the actual velocity directly.
    velocity_square = [f.add(*(f.scale(math.comb(n, j),
                          f.dot(velocity[j], velocity[n-j])) for j in range(n+1)))
                       for n in range(5)]
    if not nu:
        for n in range(5):
            f.equal(energy[n], velocity_square[n],
                    ('The retained memory vanishes for the auxiliary Euler flow', n))
    mass = mean(energy[0])
    require(mass == Q(3, 2), 'Original total energy')
    require(all(mean(v) == 0 for v in energy[1:]), 'Memory preserves the original mass')
    centered = [f.add(energy[0], constant(-mass))]+energy[1:]
    # Pressure is known through order3; that suffices for its quadratic
    # leading term and the four vanishing energy/pressure cross terms.
    reports = {name: [mean(v) for v in product_jets(left, right)]
               for name, left, right in [('ee', centered, centered),
                                         ('ep', centered, pressure),
                                         ('pp', pressure, pressure)]}
    h = [f.add(pressure[j+1], f.scale(-nu, f.lap(pressure[j]))) for j in range(3)]
    H = [mean(v) for v in product_jets(h, h)]
    dissipation = mean(f.dot(f.grad(energy[0]), f.grad(energy[0])))
    dissipation += mean(f.dot(f.grad(h[0]), f.grad(h[0])))
    dissipation_first = 2*mean(f.dot(f.grad(energy[0]), f.grad(energy[1])))
    dissipation_first += 2*mean(f.dot(f.grad(h[0]), f.grad(h[1])))
    q0 = f.add(pressure[2], f.scale(-2*nu, f.lap(pressure[1])),
               f.scale(nu*nu, f.lap(f.lap(pressure[0]))))
    require(H[1] == -2*nu*mean(f.dot(f.grad(h[0]), f.grad(h[0])))
                        +2*mean(f.mul(h[0], q0)),
            'Complete pressure-parent rate retains diffusion and the next generated parent')
    require(reports['ee'][0] == Q(3, 8), 'Centered initial energy variance')
    require(reports['ep'][0] == reports['pp'][0] == 0, 'Pressure is initially zero')
    if not nu:
        expected = Q(7184, 15015) if scale == 4 else -Q(23, 5)
        require(reports['ee'][1:4] == [0, 0, 0], 'Three vanishing diagonal returns')
        require(reports['ee'][4] == expected, 'Full fourth energy return')
        require(reports['ep'] == [0, 0, 0, 0], 'Cross moment vanishes through order3')
        require(reports['pp'] == [0, 0, Q(4, 9) if scale == 4 else 1, 0],
                'Complete generated-pressure variance')
    else:
        require(reports['ee'][1] == -(scale*scale+2)*nu,
                'Initial concentration loses the full viscous amount')
        require(reports['ep'][1] == reports['pp'][1] == 0,
                'Every coercive constant quadratic starts with a negative rate')
    if scale == 4:
        require(H[0] == Q(2, 9) and H[1] == -8*nu,
                'The original generating parent has a finite, initially depleting reserve')
        if not nu:
            require(H[2] == -Q(645625, 480249),
                    'The complete nonlinear generating-parent return is strictly negative')
        require(H[2] == 288*nu*nu-Q(645625, 480249),
                'Exact quadratic viscosity polynomial for the generating parent')
        require(reports['ee'][0]+mass*mass+H[0] == Q(205, 72),
                'Original full-data allowance for V=J+H')
        require(reports['ee'][1]+H[1] == -26*nu,
                'Initial viscous decrease of the corrected full reserve')
        require(reports['ee'][2]+H[2] == 2352*nu*nu-Q(645625, 480249),
                'Exact second rate of the corrected reserve')
        require(dissipation == 13 and dissipation_first == -1176*nu,
                'Both physical diffusion costs and their derivatives are retained')
        require(reports['ee'][1]+H[1]+nu*dissipation == -13*nu,
                'Half of both diffusion costs remains paid initially')
        require(reports['ee'][2]+H[2]+nu*dissipation_first
                == 1176*nu*nu-Q(645625, 480249),
                'The funded rate has a strict negative nonlinear derivative')
    return dict(scale=scale, viscosity=str(nu),
                **{name: [str(value) for value in values] for name, values in reports.items()},
                parent_energy=[str(value) for value in H],
                corrected_initial=str(reports['ee'][0]+mass*mass+H[0]),
                corrected_first=str(reports['ee'][1]+H[1]),
                corrected_second=str(reports['ee'][2]+H[2]),
                diffusion=str(dissipation), diffusion_first=str(dissipation_first),
                funded_rate=str(reports['ee'][1]+H[1]+nu*dissipation),
                funded_rate_first=str(reports['ee'][2]+H[2]+nu*dissipation_first))


def matrix_certificate():
    c = Q(7184, 15015)/math.factorial(4)
    b = Q(2, 9)
    require(c == Q(898, 45045), 'Positive energy value coefficient')
    require(0 < c < b, 'Both diagonal limits are positive')
    require(c*b == Q(1796, 405405), 'Leading value determinant')
    require(8*c*b == Q(14368, 405405), 'Leading derivative determinant')
    d = Q(645625, 480249)
    require(2352*Q(1, 64)**2 < d/2,
            'A fixed viscosity range has a strictly decreasing corrected second rate')
    # Congruence is the exact passage to the retained Bernoulli defect.
    x, p = s.symbols('x p', real=True)
    transformation = s.Matrix([[1, 0], [s.Rational(1, 2), 1]])
    vector = s.Matrix([x, p])
    require(transformation*vector == s.Matrix([x, p+x/2]), 'Retained defect coordinate')
    require(transformation.det() == 1, 'The coordinate change loses no joint information')
    w00, w01, w11 = s.symbols('w00 w01 w11', real=True)
    W = s.Matrix([[w00, w01], [w01, w11]])
    require(s.expand(((transformation*vector).T*W*(transformation*vector))[0]
                     -(vector.T*(transformation.T*W*transformation)*vector)[0]) == 0,
            'All constant quadratic corrections transform with their shared cross term')
    # At a positive semidefinite W, tr(W D)>=delta tr W follows from
    # D>=delta I. Verify the rank-one identity used in its spectral proof.
    d00, d01, d11 = s.symbols('d00 d01 d11', real=True)
    D = s.Matrix([[d00, d01], [d01, d11]])
    require(s.expand(s.trace((vector*vector.T)*D)-(vector.T*D*vector)[0]) == 0,
            'Uniform rank-one payment identity, including negative cross coefficients')
    beta = s.symbols('beta', real=True)
    completed = d11*(beta+d01/d11)**2+d00-d01*d01/d11
    require(s.simplify(completed-(d00+2*beta*d01+beta*beta*d11)) == 0,
            'Exact Schur minimum preserves the full shared pressure correlation')
    return dict(c=str(c), b=str(b), delta=str(c/2),
        parent_margin=str(d), corrected_second='2352nu^2-645625/480249',
        small_viscosity_range='0<=nu<=1/64',
        value_limit=[[str(c), '0'], ['0', str(b)]],
        rate_limit=[[str(4*c), '0'], ['0', str(2*b)]],
        determinant_value=str(c*b), determinant_rate=str(8*c*b),
        coordinate_change='(e-E0,p) -> (e-E0,r), r=p+(e-E0)/2',
        scope='All nonzero constant positive semidefinite W, including datum-dependent choices')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed',
        histories=[gram_jets(1, Q(0)), gram_jets(4, Q(0)),
                   gram_jets(4, Q(2, 7)), gram_jets(4, Q(1))],
        certificate=matrix_certificate(),
        failed_claim='A fixed positive quadratic correction in retained energy and pressure is universally nonincreasing',
        repair='V=J+||(partial_t-nu Delta)p||_2^2 decreases on the stated actual local interval',
        retained_options='Additional allowance, adaptive weights, extra state and signed compatible histories',
        certification='Exact full Fourier algebra; actual viscous interval and scaling are analytic'), indent=2))
