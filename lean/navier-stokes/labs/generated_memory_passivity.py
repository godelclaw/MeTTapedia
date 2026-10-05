#!/usr/bin/env python3
"""Kinetic memory payment and its derivative-weighted obstruction.

Complete unforced NS jets are used; no generated output is deleted from
the evolution. The retained band has one omitted conjugate mode pair.
Actual interval and all-prefix statements are analytic in README.md,
not Lean certificates or proofs of arbitrary-data regularity.
"""

import hashlib
import json
from pathlib import Path

import sympy as sy
import convex_parent_return as c
import helicity_renewal as h

f, Q = c.f, c.Q
require = c.require
TARGET = {(0, 0, 25), (0, 0, -25)}
BAND = 32


def keeps(k):
    return sum(j*j for j in k) <= BAND**2 and k not in TARGET


def hidden(v):
    return [{k: a for k, a in row.items() if not keeps(k)} for row in v]


def retained(v):
    return [{k: a for k, a in row.items() if keeps(k)} for row in v]


def equal(v, w, label):
    for a, b in zip(v, w):
        f.equal(a, b, label)


def lambda_power(v, power):
    # The original and hidden modes in these checks have integer lengths.
    result = []
    for row in v:
        out = {}
        for k, a in row.items():
            r2 = sum(x*x for x in k)
            radius = sy.sqrt(r2)
            require(radius.is_Integer, 'Integer shell radius for exact multiplier')
            out[k] = Q(int(radius)**power)*a
        result.append(out)
    return result


def nonlinear_work(v, power):
    if power == 0:
        return 2*c.pairing(v, c.nonlinear(v))
    if power == 2:
        return 2*c.pairing(v, c.nonlinear(v), True)
    return 2*h.sobolev_pair(v, c.nonlinear(v), power)


def balance_check(u, nu):
    p, r = retained(u), hidden(u)
    n, np_ = c.nonlinear(u), c.nonlinear(p)
    C = retained(c.addv(n, c.scale(-1, np_)))
    tangent = c.addv(c.scale(nu, [f.lap(a) for a in u]), n)
    transfer = 2*c.pairing(p, C)
    ep = 2*c.pairing(p, retained(tangent))
    er = 2*c.pairing(r, hidden(tangent))
    zp, zr = c.pairing(p, p, True), c.pairing(r, r, True)
    require(Q(ep)+2*nu*Q(zp) == Q(transfer), 'Full retained kinetic balance')
    require(Q(er)+2*nu*Q(zr) == -Q(transfer), 'Full hidden kinetic balance')
    # At gradient order the missing term is the complete nonlinear-work
    # difference, not an independently selected pressure or tail source.
    transfer1 = 2*c.pairing(p, C, True)
    hidden_rate = 2*c.pairing(r, hidden(tangent), True)
    hidden_diffusion = c.pairing([f.lap(a) for a in r], [f.lap(a) for a in r])
    defect = nonlinear_work(u, 2)-nonlinear_work(p, 2)
    require(Q(hidden_rate)+2*nu*Q(hidden_diffusion)+Q(transfer1) == Q(defect),
            'Complete derivative-weighted exchange defect')
    return dict(nu=str(nu), kinetic_transfer=str(transfer),
                gradient_transfer=str(transfer1), gradient_defect=str(defect))


def payment_check():
    # E=z^2 and E'=-2 nu Z. Both clocks depend on the original
    # finite bandwidth and retain the same actual energy throughout.
    z, C, H, t, nu, Z = sy.symbols('z C H t nu Z', positive=True)
    finite = 4*C*(H-t)*z**3
    rate = sy.diff(finite, t)+sy.diff(finite, z)*(-nu*Z/z)
    require(sy.expand(rate+4*C*z**3+12*nu*C*(H-t)*z*Z) == 0,
            'Finite-horizon energy clock pays the complete absolute bound')
    periodic = 4*C*z**3/(3*nu)
    rate = sy.diff(periodic, z)*(-nu*Z/z)
    require(sy.expand(rate+4*C*z*Z) == 0, 'Periodic spectral gap pays the all-time clock')
    squares = {1: 0, 2: 0}
    count = 0
    for x in range(-BAND, BAND+1):
        for y in range(-BAND, BAND+1):
            for z0 in range(-BAND, BAND+1):
                k = (x, y, z0)
                r2 = sum(j*j for j in k)
                if r2 and keeps(k):
                    count += 1
                    for power in squares:
                        squares[power] += r2**(power+1)
    return dict(nonzero_retained_modes=count, critical_C_squared=squares[1],
                gradient_C_squared=squares[2],
                finite_horizon_reserve='4*C*(H-t)*E^(3/2)',
                mean_zero_periodic_reserve='4*C*E^(3/2)/(3*nu)')


def check():
    w = h.parents('both')
    equal(hidden(w), [{}, {}, {}], 'Initially empty hidden component')
    f.equal(f.trace(f.jac(w)), {}, 'Literal solenoidal datum')
    equal(f.curl(w), lambda_power(w, 1), 'Every initial parent has positive helicity')
    require(sy.Matrix(h.modes(w)).rank() == 3, 'Original modes span three space')
    n = c.nonlinear(w)
    require(all(sum(j*j for j in k) < BAND**2 for k in h.modes(n)),
            'The only initially hidden output is the omitted pair')
    s = hidden(n)
    require(set(h.modes(s)) == TARGET, 'Exactly the selected conjugate child pair')
    equal(f.curl(s), c.scale(-25, s), 'The coherent child has negative helicity')
    L = retained(c.linearized(w, s))
    e = c.pairing(s, s)
    require(e == 90000, 'Exact generated source energy')
    kinetic = 2*c.pairing(w, L)
    critical = 2*c.pairing(lambda_power(w, 1), L)
    gradient = 2*c.pairing(w, L, True)
    require(kinetic == -180000 and kinetic == -2*e, 'Classical kinetic first-memory damping')
    require(critical == 4500000 and critical == 50*e, 'Positive critical parent-memory work')
    require(gradient == 211500000, 'Positive parent gradient-memory work')
    require(2*c.pairing(f.curl(w), L)+2*c.pairing(f.curl(s), s) == 0,
            'Complete first-return helicity cancellation')

    shell = {}
    for radius in (15, 20):
        part = [{k: a for k, a in row.items() if sum(j*j for j in k) == radius**2}
                for row in w]
        shell[radius] = 2*c.pairing(part, L)
    require(shell == {15: -1620000, 20: 1440000}, 'Exact retained shell exchange')
    for power in (0, 1, 2, 4):
        require(2*c.pairing(lambda_power(w, power), L)
                == 1440000*20**power-1620000*15**power,
                'Complete scalar spectral-weight formula')

    actual = []
    for nu in (Q(1), Q(2)/7):
        a = 3*nu
        initial = c.scale(a, w)
        jets, _ = c.velocity_time_jets(initial, nu, 2)
        p1 = retained(jets[1])
        measured = c.addv(retained(jets[2]),
                         c.scale(-nu, [f.lap(v) for v in p1]),
                         c.scale(-1, retained(c.linearized(initial, p1))))
        equal(measured, c.scale(a**3, L), 'Full viscous NS tangent gives the same memory derivative')
        actual.append(dict(nu=str(nu), amplitude=str(a),
                           complete_first_modes=len(h.modes(jets[1])),
                           complete_second_modes=len(h.modes(jets[2]))))
    balances = [balance_check(c.addv(w, c.scale(b, s)), Q(1)) for b in (Q(0), Q(1)/100, -Q(1)/50)]

    return dict(
        projection='P retains |k|<=32 except (0,0,+/-25); Q retains that pair and every frequency outside the band',
        complete_nonlinear_modes=len(h.modes(n)), hidden_source_modes=len(h.modes(s)),
        source_energy=str(e), kinetic_memory_derivative=str(kinetic),
        critical_memory_derivative=str(critical), gradient_memory_derivative=str(gradient),
        shell_kinetic_derivatives={str(k): str(v) for k, v in shell.items()},
        sobolev_order_s_derivative='1440000*20^(2*s)-1620000*15^(2*s); positive for every s>=1/2',
        actual_viscous_jet_checks=actual, full_balance_checks=balances,
        all_prefix_kinetic_payment='Integral transfer = E_hidden(0)-E_hidden(t)-2*nu*Integral Z_hidden',
        absolute_weighted_payment=payment_check(),
        scope='Exact full Fourier algebra; positive actual intervals, uniform local scaling and all-prefix estimates analytic, not Lean-certified')


if __name__ == '__main__':
    report = check()
    report['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(report, indent=2, sort_keys=True))
