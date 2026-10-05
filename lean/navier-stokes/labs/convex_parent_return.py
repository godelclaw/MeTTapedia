#!/usr/bin/env python3
"""Full generated-parent return for the convex-completion datum.

Actual NS jets retain every Fourier output. A second, explicitly projected
finite-dimensional reference is used only to measure what deleting generated
modes loses. The analytic short-time conclusions are stated in README.md.
"""

import hashlib
import json
from pathlib import Path

import pressure_history_source as f
import signed_viscous_pressure as sp
from cyclic_pressure_history import velocity_time_jets
from helical_parent_response import nonlinear

Q = f.QQ_I


def require(test, label):
    if not test:
        raise ArithmeticError(label)


def mean(field):
    z = field.get(f.ORIGIN, f.ZERO)
    require(z.y == 0, 'real spatial integral')
    return z.x


def pairing(u, v, gradient=False):
    if gradient:
        return sum(mean(f.dot([f.diff(a, j) for a in u], [f.diff(a, j) for a in v]))
                   for j in range(3))
    return mean(f.dot(u, v))


def select(u, support):
    return [{k: a for k, a in row.items() if k in support} for row in u]


def linearized(u, v):
    p = f.tensor_pressure([[f.add(f.mul(u[i], v[j]), f.mul(v[i], u[j]))
                           for j in range(3)] for i in range(3)])
    return [f.scale(-1, f.add(f.adv(u, v[i]), f.adv(v, u[i]), f.diff(p, i))) for i in range(3)]


def addv(*vectors):
    return [f.add(*(v[i] for v in vectors)) for i in range(3)]


def scale(c, u):
    return [f.scale(c, a) for a in u]


def check():
    u = scale(-1, sp.interacting_datum())
    support = set().union(*u)
    N = nonlinear(u)
    new = [{k: a for k, a in row.items() if k not in support} for row in N]
    return_field = select(linearized(u, new), support)
    kinetic = 2*pairing(u, return_field)
    gradient = 2*pairing(u, return_field, True)
    B, G = f.jac(u), f.jac(return_field)
    r2 = f.add(*(f.mul(a, a) for row in B for a in row))
    work = f.add(*(f.mul(B[i][j], G[i][j]) for i in range(3) for j in range(3)))
    quartic = 4*mean(f.mul(r2, work))
    generated = 2*pairing(new, new, True)
    excess = gradient+generated
    require(Q(kinetic) == -Q(3343336)/231231, 'depleting kinetic first return')
    require(kinetic == -2*pairing(new, new), 'generated kinetic energy is paid by old modes')
    require(Q(gradient) == -Q(233930128)/3468465, 'depleting parent gradient first return')
    require(Q(quartic) == -Q(2950089092699776)/481209978249,
            'depleting parent quartic first return')
    require(Q(generated) == Q(147931792)/1156155, 'generated gradient energy grows')
    require(Q(excess) == Q(209865248)/3468465 and excess > 0,
            'full gradient gain exceeds the favorable old-mode return')

    for nu in (Q(1), Q(2)/7):
        a = 16*nu
        initial = scale(a, u)
        full, _ = velocity_time_jets(initial, nu, 3)
        # The original-support model is explicitly a projected reference,
        # not a second full NS flow. Both start with the identical datum.
        closed = [initial, select(full[1], support)]
        closed.append(select(addv(scale(nu, [f.lap(v) for v in closed[1]]),
                                  linearized(initial, closed[1])), support))
        closed.append(select(addv(scale(nu, [f.lap(v) for v in closed[2]]),
                                  linearized(initial, closed[2]),
                                  scale(2, nonlinear(closed[1]))), support))
        actual_return = addv(select(full[2], support), scale(-1, closed[2]))
        for observed, expected in zip(actual_return, scale(a**3, return_field)):
            f.equal(observed, expected, 'actual complete second-order parent return')
        def second_gradient(jets):
            return 2*(pairing(jets[1], jets[1], True)+pairing(jets[0], jets[2], True))
        difference = second_gradient(full)-second_gradient(closed)
        require(Q(difference) == a**4*Q(excess), 'complete second-gradient gap from generated modes')
        def third_energy(jets):
            return 2*pairing(jets[0], jets[3])+6*pairing(jets[1], jets[2])
        require(Q(third_energy(full)-third_energy(closed)) == -2*nu*a**4*Q(excess),
                'extra gradient growth consumes additional kinetic energy')
    return dict(
        original_modes=len(support), first_generated_modes=len(set().union(*new)),
        kinetic_return=str(kinetic), parent_gradient_return=str(gradient),
        parent_quartic_return=str(quartic), generated_gradient_second_rate=str(generated),
        total_gradient_second_rate_excess=str(excess),
        physical_scope='actual unforced periodic NS for every fixed nu>0 and amplitude a>0',
        reference_scope='original-support Galerkin reference, not a full NS solution',
        actual_short_time_comparison={
            'gradient': 'Z_NS-Z_reference=(104932624/3468465)*a^4*t^2+O(t^3)>0',
            'kinetic': 'E_NS-E_reference=-(209865248/10405395)*nu*a^4*t^3+O(t^4)<0'},
        certification='exact complete jets; local PDE intervals and remainders analytic, not Lean-certified')


if __name__ == '__main__':
    report = check()
    report['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(report, indent=2, sort_keys=True))
