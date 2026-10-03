#!/usr/bin/env python3
"""Exact fixtures for retained stochastic energy and pressure alignment.

All Fourier products retain every output. The stochastic identification,
maximum-principle payment and actual viscous interval argument are analytic
in README.md; these finite algebra checks are not Lean certificates.
"""

import json
import math
from fractions import Fraction as Q

import pressure_history_source as f
from cyclic_pressure_history import seed, velocity_time_jets
from kinetic_pressure_entropy import moment_jets
from pressure_parent_bellman import abc


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def constant(value):
    return {f.ORIGIN: f.QQ_I(value)} if value else {}


def mean(field):
    value = field.get(f.ORIGIN, f.ZERO)
    require(not value.y, 'Real spatial mean')
    return Q(str(value.x))


def square_gradient(field):
    return f.dot(f.grad(field), f.grad(field))


def gradient_energy(velocity):
    return f.add(*(square_gradient(v) for v in velocity))


def product_jets(left, right):
    order = min(len(left), len(right))
    return [f.add(*(f.scale(math.comb(n, j), f.mul(left[j], right[n-j]))
                    for j in range(n+1))) for n in range(order)]


def pressure_defect(velocity, pressure, nu):
    """The full physical (partial_t - nu Delta)p at this instant."""
    B = f.jac(velocity)
    B2 = f.matmul(B, B)
    source = f.trace(B2)
    cubic = f.trace(f.matmul(B2, B))
    pressure_pair = f.trace(f.matmul(B, f.hess(pressure)))
    derivative_square = f.add(*(f.trace(f.matmul(
        [[f.diff(v, k) for v in row] for row in B],
        [[f.diff(v, k) for v in row] for row in B])) for k in range(3)))
    complete = f.add(f.scale(-1, f.adv(velocity, source)),
                     f.scale(-2, cubic), f.scale(-2, pressure_pair),
                     f.scale(-2*nu, derivative_square))
    require(mean(complete) == 0, 'Canonical pressure source has zero mean')
    return f.green(complete)


def retained_jets(initial, nu):
    velocity, pressure = velocity_time_jets(initial, nu, 4)
    tensors, _, fourth = moment_jets(velocity, pressure, nu, Q(0))
    e = [f.trace(L) for L in tensors]
    e2 = product_jets(e, e)
    # Compare two independent equations: full tensor history versus its trace.
    for n in range(4):
        rhs = f.add(f.scale(nu, f.lap(e[n])), *(
            f.scale(-math.comb(n, j), f.add(
                f.adv(velocity[j], e[n-j]),
                f.scale(2, f.adv(velocity[j], pressure[n-j]))))
            for j in range(n+1)))
        f.equal(e[n+1], rhs, ('Full retained energy equation', n))
        require(mean(e[n+1]) == 0, 'Retained energy mass is conserved')
    E0 = mean(e[0])
    r = [f.add(p, f.scale(Q(1, 2), e[n]),
               constant(-E0/2) if n == 0 else {}) for n, p in enumerate(pressure)]
    for n in range(3):
        Dr = f.add(r[n+1], f.scale(-nu, f.lap(r[n])), *(
            f.scale(math.comb(n, j), f.adv(velocity[j], r[n-j]))
            for j in range(n+1)))
        h = f.add(pressure[n+1], f.scale(-nu, f.lap(pressure[n])))
        f.equal(Dr, h, ('Complete alignment defect with existing memory', n))
    h0 = f.add(pressure[1], f.scale(-nu, f.lap(pressure[0])))
    f.equal(h0, pressure_defect(initial, pressure[0], nu),
            'Nonlinear canonical pressure defect retains every source')
    # Full global concentration balance, checked through three derivatives.
    diffusion = [f.add(*(f.scale(math.comb(n, j),
                       f.dot(f.grad(e[j]), f.grad(e[n-j]))) for j in range(n+1)))
                 for n in range(4)]
    for n in range(4):
        flux = {}
        for i in range(n+1):
            for j in range(n-i+1):
                k = n-i-j
                coefficient = math.comb(n, i)*math.comb(n-i, j)
                flux = f.add(flux, f.scale(coefficient,
                    f.mul(pressure[i], f.adv(velocity[j], e[k]))))
        require(mean(e2[n+1]) == -2*nu*mean(diffusion[n])+4*mean(flux),
                ('Concentration pressure-flux balance', n))
    return dict(E0=str(E0), J=[str(mean(v)) for v in e2],
                K=[str(mean(v)) for v in fourth],
                defect_modes=len(h0)), velocity, pressure, e, r


def abc_checks():
    rows = []
    for amplitudes, k in [((1, 2, 3), 1), ((2, 3, 5), 4), ((0, 0, 3), 2)]:
        u = abc(amplitudes, k)
        w, S = f.dot(u, u), sum(a*a for a in amplitudes)
        lam = k*k
        f.equal(gradient_energy(u), constant(lam*S), 'Constant ABC gradient energy')
        centered = f.add(w, constant(-S))
        f.equal(f.lap(centered), f.scale(-2*lam, centered),
                'ABC energy fluctuation lies on twice the velocity eigenvalue')
        p = f.scale(-Q(1, 2), centered)
        f.equal(f.tensor_pressure(f.tensor(u, u)), p, 'Canonical ABC pressure')
        f.equal(pressure_defect(u, p, Q(2, 7)), {}, 'ABC pressure is caloric')
        variance = mean(f.mul(centered, centered))
        a, b, c = amplitudes
        require(variance == a*a*b*b+b*b*c*c+c*c*a*a,
                'Complete ABC concentration allowance')
        rows.append(dict(amplitudes=amplitudes, wave_number=k, E0=S,
                         J_initial=str(S*S+variance), excess=str(variance),
                         law='J(t)=S^2+(a^2 b^2+b^2 c^2+c^2 a^2) exp(-4nu k^2 t)'))
    # Retain the complete generated tensor, rather than imposing its trace.
    report, _, _, e, r = retained_jets(abc((1, 2, 3), 1), Q(2, 7))
    for n in range(1, 5):
        f.equal(e[n], f.scale((-Q(4, 7))**n, f.add(e[0], constant(-14))),
                ('Physical ABC retained trace is exactly caloric', n))
    require(not any(r), 'ABC alignment survives the complete checked memory jets')
    K = [Q(value) for value in report['K']]
    require(K[:4] == [245, 0, 0, Q(4624, 7)],
            'The same actual viscous ABC history has a growing fourth moment')
    require(K[3]/6 == Q(2312, 21), 'Strict Taylor coefficient of the fourth moment')
    return rows, report


def helical_wave(wave, polarization, curl_eigenvalue):
    """A real wave with curl U = curl_eigenvalue U, in Gaussian rationals."""
    cross = [wave[1]*polarization[2]-wave[2]*polarization[1],
             wave[2]*polarization[0]-wave[0]*polarization[2],
             wave[0]*polarization[1]-wave[1]*polarization[0]]
    require(sum(a*b for a, b in zip(wave, polarization)) == 0, 'Transverse polarization')
    require(sum(a*a for a in wave) == curl_eigenvalue**2, 'Common curl eigenvalue')
    values = [(f.QQ_I(p)+f.II*f.QQ_I(q)/curl_eigenvalue)/2
              for p, q in zip(polarization, cross)]
    negative = tuple(-k for k in wave)
    return [f.clean({wave: a, negative: f.QQ_I(a.x, -a.y)}) for a in values]


def oblique_check():
    waves = [helical_wave((3, 4, 0), (0, 0, 1), 5),
             helical_wave((0, 3, 4), (1, 0, 0), 5)]
    u = [f.add(*(wave[i] for wave in waves)) for i in range(3)]
    for a, b in zip(f.curl(u), u):
        f.equal(a, f.scale(5, b), 'Oblique waves share the actual curl eigenvalue')
    w, G = f.dot(u, u), gradient_energy(u)
    E0 = mean(w)
    p = f.scale(-Q(1, 2), f.add(w, constant(-E0)))
    f.equal(f.tensor_pressure(f.tensor(u, u)), p, 'Full oblique canonical pressure')
    for j in range(3):
        f.equal(f.lap(u[j]), f.scale(-25, u[j]), 'Actual oblique heat evolution')
        f.equal(f.add(f.adv(u, u[j]), f.diff(p, j)), {},
                'The full oblique nonlinear velocity equation cancels with pressure')
    mismatch = f.add(G, constant(-25*E0))
    require(bool(mismatch), 'Single-shell Beltrami geometry need not retain alignment')
    require(mean(f.mul(mismatch, mismatch)) == Q(110736, 625),
            'Exact nonzero oblique alignment production')
    f.equal(pressure_defect(u, p, Q(2, 7)), f.scale(Q(2, 7), mismatch),
            'All alignment production is the stated viscous mismatch')
    return dict(E0=str(E0), curl_eigenvalue=5,
                gradient_mismatch_L2_squared=str(mean(f.mul(mismatch, mismatch))),
                mismatch_Linfinity_upper_bound=str(sum(abs(Q(str(v.x)))+abs(Q(str(v.y)))
                                                       for v in mismatch.values())),
                source='h=nu exp(-2nu lambda t)(|grad U|^2-lambda E0)',
                bound='||r||_infinity <= |||grad U|^2-lambda E0||_infinity/(2lambda)')


def general_defect_checks():
    rows = []
    initial = f.fixture()
    for nu in [Q(0), Q(2, 7), Q(2)]:
        _, pressure = velocity_time_jets(initial, nu, 2)
        h = f.add(pressure[1], f.scale(-nu, f.lap(pressure[0])))
        f.equal(h, pressure_defect(initial, pressure[0], nu),
                'All four defect channels on a nonsymmetric three-dimensional datum')
        require(bool(h), 'The complete physical defect is not identically zero')
        rows.append(dict(nu=str(nu), pressure_modes=len(pressure[0]), defect_modes=len(h)))
    require(Q(1)-2*Q(1, 2)+Q(1, 3) == Q(1, 3),
            'Whole-history integral for the viscous mismatch payment')
    return rows


def independent_ito_check():
    """Backward Ito generator on (X,Z), independent of the raw-moment system."""
    u, nu = abc((1, 2, 3), 1), Q(2, 7)
    p = f.tensor_pressure(f.tensor(u, u))
    gradient = f.grad(p)
    # (j,powers) denotes exp(-j*nu*t) times a Fourier field times Z^powers.
    state = {}
    for i in range(3):
        for j in range(3):
            powers = tuple(2*int(k == i)+2*int(k == j) for k in range(3))
            state[(0, powers)] = f.add(state.get((0, powers), {}), constant(1))
    powers_of_u = [[constant(1)] for _ in range(3)]
    for i in range(3):
        for _ in range(4):
            powers_of_u[i].append(f.mul(powers_of_u[i][-1], u[i]))
    observations = []
    for n in range(4):
        observed = {}
        for (_, powers), coefficient in state.items():
            term = coefficient
            for i in range(3):
                term = f.mul(term, powers_of_u[i][powers[i]])
            observed = f.add(observed, term)
        observations.append(mean(observed))
        if n == 3:
            break
        next_state = {}

        def put(key, field):
            next_state[key] = f.add(next_state.get(key, {}), field)

        for (rate, powers), coefficient in state.items():
            put((rate, powers), f.add(f.scale(-rate*nu, coefficient),
                                      f.scale(nu, f.lap(coefficient))))
            put((rate+1, powers), f.adv(u, coefficient))
            for i, power in enumerate(powers):
                if power:
                    lower = tuple(a-int(k == i) for k, a in enumerate(powers))
                    put((rate+2, lower), f.scale(-power, f.mul(gradient[i], coefficient)))
        state = {key: field for key, field in next_state.items() if field}
    require(observations == [245, 0, 0, Q(4624, 7)],
            'Independent full Ito generator confirms the increasing fourth moment')
    return [str(value) for value in observations]


def cyclic_failure():
    initial = [{(k[0], k[1], 4*k[2]): v for k, v in field.items()} for field in seed(1)]
    rows = []
    for nu in [Q(0), Q(2, 7)]:
        report, _, _, _, _ = retained_jets(initial, nu)
        values = [Q(x) for x in report['J']]
        require(values[0] == Q(21, 8), 'Initial concentration')
        require(values[1] == -18*nu, 'Initial viscous decrease')
        if not nu:
            require(values[1:4] == [0, 0, 0], 'First three Euler returns vanish')
            require(values[4] == Q(7184, 15015), 'Complete positive fourth return')
        rows.append(dict(nu=str(nu), **report))
    return rows


if __name__ == '__main__':
    families, tensor_check = abc_checks()
    print(json.dumps(dict(status='all exact checks passed', abc=families,
        abc_retained_tensor=tensor_check, oblique=oblique_check(),
        complete_pressure_defect=general_defect_checks(),
        independent_ito=independent_ito_check(),
        changing_parents=cyclic_failure(),
        consumer='||u||_4^4 <= integral e^2 <= E|Z|^4',
        OPEN='original-data payment for the full evolving pressure-alignment defect',
        certification='exact Fourier identities; all-time bounds and viscous counterexample are analytic'), indent=2))
