#!/usr/bin/env python3
"""Actual cyclic NS pressure renewal and its retained frame history.

The exact check retains the canonical pressure in complete NS time jets.
It also proves symbolic second-pressure formulas for arbitrary positive
amplitude and viscosity. Optional prefixes evolve all three velocities
and six symmetric entries of the original forward moment, starting at I.
They are dealiased Galerkin approximations, not continuum enclosures or
proofs of an arbitrary-data allowance. Centre pressure is evaluated with
all product outputs on an enlarged grid; omitted dynamical outputs are
reported as signed projection residues in the time ledgers.
The torus has period 2*pi and normalized volume.
"""

import argparse
import json
import math
import time
from fractions import Fraction

import numpy as np
import sympy as s
from scipy.fft import ifftn
import pressure_history_source as f
from reciprocal_parent_history import Flow
from cellular_parent_history import PAIRS, curl


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(expression, label):
    require(s.trigsimp(s.expand_trig(s.expand(expression))) == 0, label)


def seed(amplitude):
    u = [{}, {}, {}]
    for i, k in enumerate(((0, 1, 0), (0, 0, 1), (1, 0, 0))):
        u[i][k] = -f.II*f.QQ_I(amplitude)/2
        u[i][tuple(-v for v in k)] = f.II*f.QQ_I(amplitude)/2
    return u


def time_jets(amplitude, nu, order):
    return velocity_time_jets(seed(amplitude), nu, order)


def velocity_time_jets(initial, nu, order):
    jets, pressures = [initial], []
    for n in range(order):
        tensor = [[f.add(*(f.scale(math.comb(n, r), f.mul(jets[r][i], jets[n-r][j]))
                           for r in range(n+1))) for j in range(3)] for i in range(3)]
        p = f.tensor_pressure(tensor)
        pressures.append(p)
        next_jet = [f.add(f.scale(f.QQ_I(nu), f.lap(jets[n][i])),
                         f.scale(-1, f.diff(p, i)),
                         f.scale(-1, f.add(*(f.scale(math.comb(n, r),
                                                    f.adv(jets[r], jets[n-r][i]))
                                            for r in range(n+1))))) for i in range(3)]
        f.equal(f.trace(f.jac(next_jet)), {}, ('full canonical solenoidal jet', n+1))
        jets.append(next_jet)
    return jets, pressures


def symbolic_pressure():
    x, y, z = s.symbols('x y z', real=True)
    a, nu = s.symbols('a nu', positive=True)
    coordinates = (x, y, z)
    lap = lambda v: sum(s.diff(v, c, 2) for c in coordinates)
    u = a*s.Matrix([s.sin(y), s.sin(z), s.sin(x)])
    B = u.jacobian(coordinates)
    zero(B.trace(), 'literal cyclic datum is incompressible')
    zero(s.trace(B*B), 'canonical pressure initially vanishes')
    u1 = nu*u.applyfunc(lap)-B*u
    B1 = u1.jacobian(coordinates)
    p1 = -2*a**3*s.cos(x)*s.cos(y)*s.cos(z)
    zero(lap(p1)+2*s.trace(B*B1), 'first complete canonical pressure derivative')
    u2 = nu*u1.applyfunc(lap)-B1*u-B*u1-s.Matrix([s.diff(p1, c) for c in coordinates])
    B2 = u2.jacobian(coordinates)
    p2_inviscid = -s.Rational(2, 3)*a**4*(
        s.sin(2*x)*s.cos(y)*s.sin(z)+s.sin(x)*s.sin(2*y)*s.cos(z)
        +s.cos(x)*s.sin(y)*s.sin(2*z))
    p2 = p2_inviscid-6*nu*p1
    zero(lap(p2)+2*s.trace(B1*B1)+2*s.trace(B*B2),
         'second pressure derivative retains viscosity, changing parents and pressure')
    zero(B1.trace(), 'first literal unforced tangent is solenoidal')
    zero(B2.trace(), 'second literal unforced tangent is solenoidal')
    origin = {x: 0, y: 0, z: 0}
    zero(s.diff(p2, x, y).subs(origin)+s.Rational(4, 3)*a**4,
         'renewing pressure is present at every positive viscosity')
    alpha, beta, pd, po = s.symbols('alpha beta pd po', real=True)
    C = s.Matrix([[0, alpha, beta], [beta, 0, alpha], [alpha, beta, 0]])
    P = s.Matrix([[pd, po, po], [po, pd, po], [po, po, pd]])
    reaction = -C*C-P
    ell, w = alpha+beta, beta-alpha
    zero(reaction[0, 1]+reaction[0, 2]+(ell*ell+w*w)/2+2*po,
         'complete scalar stretch reaction retains physical pressure')
    zero(reaction[0, 2]-reaction[0, 1]-ell*w,
         'actual centre vorticity reaction')

    # A manufactured stationary forced filter separates the force gradient
    # from its value at the centre. It is not a singular construction.
    force = B*u-nu*u.applyfunc(lap)
    Jforce = force.jacobian(coordinates)
    zero(Jforce.trace(), 'stationary sustaining force is solenoidal')
    zero(Jforce[0, 1].subs(origin)+Jforce[0, 2].subs(origin)-a*a-nu*a,
         'forcing supplies exactly the missing centre stretch reaction')
    for value in force.subs(origin):
        zero(value, 'zero force value does not imply zero force gradient')
    work = s.integrate((u.dot(force)).expand(), (x, -s.pi, s.pi),
                       (y, -s.pi, s.pi), (z, -s.pi, s.pi))/(2*s.pi)**3
    zero(work-s.Rational(3, 2)*nu*a*a, 'the sustaining force pays positive normalized kinetic work')
    return {'initial_pressure': '0', 'pressure_first': str(p1), 'pressure_second': str(p2),
            'centre_Pi_initial': '0', 'centre_Pi_first': '0',
            'centre_Pi_second': '-4*a^4/3',
            'positive_cumulative_pressure_renewal': '(4/9)*a^4*tau^3+o(tau^3)',
            'scope': 'exact symbolic full pressure/PDE jets; a short actual solution interval uses analytic local existence and Taylor continuity',
            'stationary_forced_filter': {'centre_force': '0', 'stretch_force_gradient': 'a^2+nu*a',
                                        'normalized_kinetic_work': '3*nu*a^2/2',
                                        'scope': 'exact smooth periodic manufactured force, not the imported forced blowup'}}


def reciprocal_pressure_family():
    x, y, z = s.symbols('x y z', real=True)
    a, b, c, nu = s.symbols('a b c nu', positive=True)
    coordinates = (x, y, z)
    lap = lambda v: sum(s.diff(v, q, 2) for q in coordinates)
    u = s.Matrix([a*s.sin(y), c*s.sin(z), b*s.sin(x)])
    B = u.jacobian(coordinates)
    u1 = nu*u.applyfunc(lap)-B*u
    B1 = u1.jacobian(coordinates)
    p1 = -2*a*b*c*s.cos(x)*s.cos(y)*s.cos(z)
    zero(lap(p1)+2*s.trace(B*B1), 'first pressure jet for the full reciprocal family')
    u2 = nu*u1.applyfunc(lap)-B1*u-B*u1-s.Matrix([s.diff(p1, q) for q in coordinates])
    B2 = u2.jacobian(coordinates)
    p2 = -s.Rational(2, 3)*a*b*c*(b*s.sin(2*x)*s.cos(y)*s.sin(z)
                                 +a*s.sin(x)*s.sin(2*y)*s.cos(z)
                                 +c*s.cos(x)*s.sin(y)*s.sin(2*z))-6*nu*p1
    zero(lap(p2)+2*s.trace(B1*B1)+2*s.trace(B*B2),
         'second pressure jet retains all reciprocal parents and viscosity')
    origin = {x: 0, y: 0, z: 0}
    coefficients = (a*a*b*c, a*b*b*c, a*b*c*c)
    rows = []
    for (i, j), coefficient in zip(((0, 1), (0, 2), (1, 2)), coefficients):
        value = s.diff(p2, coordinates[i], coordinates[j]).subs(origin)
        zero(value+s.Rational(4, 3)*coefficient, 'reciprocal pressure renewal vanishes with its feedback parent')
        rows.append({'entry': [i, j], 'second_time_derivative': str(value)})
    zero(p1.subs(c, 0), 'no first pressure renewal in the triangular limit')
    zero(p2.subs(c, 0), 'no second pressure renewal in the triangular limit')
    return {'datum': 'u0=(a sin y,c sin z,b sin x)', 'pressure_second': str(p2),
            'centre_offdiagonal_second_derivatives': rows,
            'scope': 'symbolic jets for arbitrary positive a,b,c,nu; no uniform positive-time Taylor window'}


def exact_checks():
    cases = []
    for a, nu in ((Fraction(1), Fraction(1, 2)), (Fraction(1), Fraction(1, 10)),
                  (Fraction(2), Fraction(1, 2))):
        jets, pressure = time_jets(a, nu, 4)
        rows = []
        for n, p in enumerate(pressure):
            B = f.jac(jets[n])
            values = [[f.evaluate(entry) for entry in row] for row in B]
            alpha, beta = values[0][1], values[0][2]
            wanted = [[0, alpha, beta], [beta, 0, alpha], [alpha, beta, 0]]
            require(values == wanted, ('all centre gradient jets preserve cyclic symmetry', n))
            Pi = f.evaluate(f.diff(f.diff(p, 0), 1))
            require(Pi == f.evaluate(f.diff(f.diff(p, 0), 2)),
                    'complete pressure preserves the common centre direction')
            if n < 2:
                require(Pi == 0, 'no initial offdiagonal pressure or first jet')
            if n == 2:
                require(Pi == -Fraction(4, 3)*a**4, 'complete renewing second pressure jet')
            rows.append({'order': n, 'alpha': str(alpha), 'beta': str(beta),
                         'ell': str(alpha+beta), 'omega_scalar': str(beta-alpha),
                         'pressure_offdiagonal': str(Pi),
                         'velocity_modes': len(set().union(*jets[n]))})
        cases.append({'a': str(a), 'nu': str(nu), 'jets': rows})
    operator = CyclicFlow(16, .5, 1.)
    rhs, _ = operator.rhs(operator.initial)
    jets, _ = time_jets(Fraction(1), Fraction(1, 2), 1)
    expected = np.zeros_like(rhs)
    for j, field in enumerate(jets[1]):
        for k, v in field.items():
            expected[tuple(q % operator.n for q in k)+(j,)] = complex(float(v.x), float(v.y))*operator.n**3
    B = f.jac(jets[0])
    for index, (i, j) in enumerate(PAIRS):
        for k, v in f.add(B[i][j], B[j][i]).items():
            expected[tuple(q % operator.n for q in k)+(3+index,)] = complex(float(v.x), float(v.y))*operator.n**3
    tangent = rhs+operator.heat[..., None]*operator.initial
    relative = float(np.max(abs(tangent-expected))/max(1., np.max(abs(expected))))
    require(relative < 2e-14, 'every initial numerical velocity/moment operator coefficient matches the exact PDE')

    # Check pressure reconstruction and the coupled moment operator away
    # from the initial identity, using complete rational Fourier products.
    h = Fraction(1, 4)
    probe_velocity = [f.add(v, f.scale(h, dv)) for v, dv in zip(jets[0], jets[1])]
    probe_B = f.jac(probe_velocity)
    probe_M = [[f.add({(0, 0, 0): f.QQ_I(1)} if i == j else {},
                       f.scale(h, f.add(B[i][j], B[j][i])))
                for j in range(3)] for i in range(3)]
    probe_pressure = f.tensor_pressure([[f.mul(v, w) for w in probe_velocity]
                                        for v in probe_velocity])
    probe = np.zeros_like(operator.initial)
    for j, field in enumerate(probe_velocity+[probe_M[i][j] for i, j in PAIRS]):
        for k, v in field.items():
            probe[tuple(q % operator.n for q in k)+(j,)] = complex(float(v.x), float(v.y))*operator.n**3
    literal_pressure = np.array([[float(f.evaluate(f.diff(f.diff(probe_pressure, i), j)))
                                  for j in range(3)] for i in range(3)])
    pressure_error = float(np.max(abs(operator.pressure_at_origin(probe)-literal_pressure)))
    require(pressure_error < 2e-14, 'all full-product pressure Hessian components agree with exact Fourier evaluation')
    probe_tangent = [f.add(f.scale(Fraction(1, 2), f.lap(v)),
                           f.scale(-1, f.adv(probe_velocity, v)),
                           f.scale(-1, f.diff(probe_pressure, i)))
                     for i, v in enumerate(probe_velocity)]
    for i, j in PAIRS:
        probe_tangent.append(f.add(f.scale(Fraction(1, 2), f.lap(probe_M[i][j])),
                                   f.scale(-1, f.adv(probe_velocity, probe_M[i][j])),
                                   *(f.add(f.mul(probe_B[i][k], probe_M[k][j]),
                                           f.mul(probe_M[i][k], probe_B[j][k])) for k in range(3))))
    expected.fill(0)
    for j, field in enumerate(probe_tangent):
        for k, v in field.items():
            expected[tuple(q % operator.n for q in k)+(j,)] = complex(float(v.x), float(v.y))*operator.n**3
    probe_rhs, _ = operator.rhs(probe)
    probe_error = float(np.max(abs(probe_rhs+operator.heat[..., None]*probe-expected))
                        /max(1., np.max(abs(expected))))
    require(probe_error < 2e-14, 'all coupled operator coefficients agree away from the identity moment')
    return {'symbolic_pressure_and_reaction': symbolic_pressure(),
            'reciprocal_pressure_family': reciprocal_pressure_family(), 'complete_fourier_jets': cases,
            'initial_full_operator_relative_error': relative,
            'nonidentity_full_operator_relative_error': probe_error,
            'full_pressure_hessian_absolute_error': pressure_error,
            'claims': 'pressure can renew centre stretching in actual unforced histories; a full-datum cumulative allowance remains open'}


class CyclicFlow(Flow):
    """Reuse the existing dealiased grid operations and Lawson RK4 step."""

    def __init__(self, n, nu, amplitude):
        self.n, self.nu, self.amplitude = n, nu, amplitude
        frequencies = np.rint(np.fft.fftfreq(n)*n)
        self.K = np.stack(np.meshgrid(frequencies, frequencies, frequencies, indexing='ij'), axis=-1)
        self.k2 = np.sum(self.K*self.K, axis=-1)
        self.inv = np.divide(1, self.k2, out=np.zeros_like(self.k2), where=self.k2 > 0)
        self.heat = -nu*self.k2
        self.mask = np.all(abs(self.K) < n/3, axis=-1)
        self.high = np.any(abs(self.K) > .8*n/3, axis=-1) & self.mask
        self.initial = np.zeros((n, n, n, 9), dtype=np.complex128)
        for j, field in enumerate(seed(Fraction(str(amplitude)))):
            for k, v in field.items():
                self.initial[tuple(q % n for q in k)+(j,)] = complex(float(v.x), float(v.y))*n**3
        for index, (i, j) in enumerate(PAIRS):
            if i == j:
                self.initial[0, 0, 0, 3+index] = n**3
        self.diagnostic_n = 3*n//2
        k = np.rint(np.fft.fftfreq(self.diagnostic_n)*self.diagnostic_n)
        self.Kp = np.stack(np.meshgrid(k, k, k, indexing='ij'), axis=-1)
        kp2 = np.sum(self.Kp*self.Kp, axis=-1)
        self.invp = np.divide(1, kp2, out=np.zeros_like(kp2), where=kp2 > 0)

    def pressure_at_origin(self, state):
        size, n = self.diagnostic_n, self.n
        shifted = np.fft.fftshift(state[..., :3], axes=(0, 1, 2))
        lo = (size-n)//2
        hi = size-n-lo
        padded = np.fft.ifftshift(np.pad(shifted, ((lo, hi), (lo, hi), (lo, hi), (0, 0))),
                                    axes=(0, 1, 2))*(size/n)**3
        velocity = self.ifft(padded)
        numerator = np.zeros((size,)*3, dtype=np.complex128)
        for i, j in PAIRS:
            product = self.fft(velocity[..., i]*velocity[..., j])
            numerator += (1 if i == j else 2)*self.Kp[..., i]*self.Kp[..., j]*product
        qh = -self.invp*numerator
        P = np.array([[-np.sum(self.Kp[..., i]*self.Kp[..., j]*qh).real/size**3
                       for j in range(3)] for i in range(3)])
        return P

    def centre(self, state, tangent=None):
        uhat = state[..., :3]
        B = np.array([[np.sum(1j*self.K[..., j]*uhat[..., i]).real/self.n**3
                       for j in range(3)] for i in range(3)])
        lapB = np.array([[-np.sum(self.k2*1j*self.K[..., j]*uhat[..., i]).real/self.n**3
                          for j in range(3)] for i in range(3)])
        entries = np.sum(state[..., 3:], axis=(0, 1, 2)).real/self.n**3
        M = self.matrix(entries)
        lapM = self.matrix(-np.sum(self.k2[..., None]*state[..., 3:], axis=(0, 1, 2)).real/self.n**3)
        alpha, beta = B[0, 1], B[0, 2]
        ell, w = alpha+beta, beta-alpha
        mu, lapmu = float(np.sum(M)/3), float(np.sum(lapM)/3)
        require(mu > 0, 'centre frame moment must stay positive for its logarithmic ledger')
        result = {'ell': float(ell), 'omega_scalar': float(w), 'mu': mu,
                  'diffusion_stretch': float(self.nu*(lapB[0, 1]+lapB[0, 2])),
                  'quadratic_stretch_cost': float(alpha*alpha+beta*beta),
                  'log_frame_strain': float(2*ell), 'log_frame_diffusion': float(self.nu*lapmu/mu)}
        if tangent is not None:
            Bt = np.array([[np.sum(1j*self.K[..., j]*tangent[..., i]).real/self.n**3
                            for j in range(3)] for i in range(3)])
            Mt = self.matrix(np.sum(tangent[..., 3:], axis=(0, 1, 2)).real/self.n**3)
            P = self.pressure_at_origin(state)
            stretch_pressure = float(-P[0, 1]-P[0, 2])
            stretch_residue = float(Bt[0, 1]+Bt[0, 2])-result['diffusion_stretch'] \
                +result['quadratic_stretch_cost']-stretch_pressure
            frame_residue = float(np.sum(Mt)/3)/mu \
                -result['log_frame_strain']-result['log_frame_diffusion']
            result.update({'pressure_offdiagonal': float(P[0, 1]),
                           'stretch_pressure': stretch_pressure,
                           'pressure_symmetry_error': float(abs(P[0, 1]-P[0, 2])),
                           'stretch_projection_residue': stretch_residue,
                           'log_frame_projection_residue': frame_residue})
        expected = np.array([[0, alpha, beta], [beta, 0, alpha], [alpha, beta, 0]])
        direction = np.ones(3)
        result['gradient_symmetry_error'] = float(np.max(abs(B-expected)))
        result['moment_direction_error'] = float(np.max(abs(M@direction-mu*direction)))
        return result

    def rhs(self, state):
        u, B, M, gradient = self.fields(state)
        reaction = B@M+M@np.swapaxes(B, -1, -2)
        nonlinear = -sum(u[..., j, None]*gradient[j] for j in range(3))
        for index, (i, j) in enumerate(PAIRS):
            nonlinear[..., 3+index] += reaction[..., i, j]
        rhs = self.fft(nonlinear)*self.mask[..., None]
        rhs[..., :3] = self.project(rhs[..., :3])
        c = self.centre(state, rhs+self.heat[..., None]*state)
        rates = np.array([c['quadratic_stretch_cost'], c['stretch_pressure'],
                          c['diffusion_stretch'], c['stretch_projection_residue'],
                          c['log_frame_strain'], c['log_frame_diffusion'],
                          c['log_frame_projection_residue'],
                          self.nu*np.mean(np.sum(B*B, axis=(-2, -1)))])
        return rhs, rates

    def diagnostic(self, t, state, integrated):
        u, B, M, _ = self.fields(state)
        tangent, _ = self.rhs(state)
        centre = self.centre(state, tangent+self.heat[..., None]*state)
        density = np.sum(abs(state[..., :3])**2, axis=-1)
        pal = self.k2*self.k2*density
        memory_weights = np.array([1 if i == j else 2 for i, j in PAIRS])
        mdensity = self.k2*np.sum(abs(state[..., 3:])**2*memory_weights, axis=-1)
        eigenvalues = np.linalg.eigvalsh(M)
        reality = ifftn(state, axes=(0, 1, 2), workers=1).imag
        energy = float(np.mean(np.sum(u*u, axis=-1))/2)
        initial_energy = 3*self.amplitude**2/4
        stretch_balance = centre['ell']-self.amplitude+integrated[0]-integrated[1] \
            -integrated[2]-integrated[3]
        frame_balance = math.log(centre['mu'])-sum(integrated[4:7])
        return {'time': t, 'centre': centre, 'integrated': integrated.tolist(),
                'stretch_history_balance': float(stretch_balance),
                'log_frame_history_balance': float(frame_balance),
                'kinetic_history_balance': float(energy-initial_energy+integrated[7]),
                'energy': energy, 'enstrophy': float(np.mean(np.sum(curl(B)**2, axis=-1))),
                'minimum_moment_eigenvalue': float(np.min(eigenvalues)),
                'maximum_moment_eigenvalue': float(np.max(eigenvalues)),
                'high_palinstrophy_fraction': float(np.sum(pal[self.high])/np.sum(pal)),
                'high_moment_gradient_fraction': float(np.sum(mdensity[self.high])/np.sum(mdensity))
                    if np.sum(mdensity) > 0 else 0.,
                'divergence_max': float(np.max(abs(np.trace(B, axis1=-2, axis2=-1)))),
                'max_reality_error': float(np.max(abs(reality)))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=.1)
    parser.add_argument('--amplitude', type=float, default=1.)
    parser.add_argument('--final-time', type=float, default=2.)
    parser.add_argument('--dt', type=float, default=.005)
    parser.add_argument('--report-every', type=float, default=.25)
    parser.add_argument('--max-tail', type=float, default=.005)
    args = parser.parse_args()
    if not args.prefix:
        print(json.dumps(exact_checks(), indent=2))
        return
    if args.n < 16 or args.n % 4:
        parser.error('grid size must be a multiple of four, at least sixteen')
    if any(not np.isfinite(v) or v <= 0 for v in (args.nu, args.amplitude, args.final_time,
                                                 args.dt, args.report_every, args.max_tail)):
        parser.error('positive finite viscosity, amplitude, times and diagnostic threshold required')
    flow = CyclicFlow(args.n, args.nu, args.amplitude)
    state, integrated = flow.initial.copy(), np.zeros(8)
    t, steps, started = 0., 0, time.monotonic()
    print(json.dumps({'configuration': vars(args), 'scope': 'Galerkin prefix, not a continuum enclosure',
                      'ledger_order': ['quadratic_stretch_cost', 'signed_pressure_renewal',
                                       'viscous_stretch_diffusion', 'stretch_projection_residue',
                                       'log_frame_strain', 'log_frame_diffusion',
                                       'log_frame_projection_residue', 'kinetic_dissipation'],
                      'initial': flow.diagnostic(t, state, integrated)}), flush=True)
    next_report = min(args.report_every, args.final_time)
    reason = 'requested_time'
    while t < args.final_time-1e-13:
        u, B, _, _ = flow.fields(state)
        advection_rate = (args.n/3)*float(np.max(np.sum(abs(u), axis=-1)))
        reaction_rate = 2*float(np.max(np.sqrt(np.sum(B*B, axis=(-2, -1)))))
        dt = min(args.dt, .4/max(advection_rate, reaction_rate, 1e-30), next_report-t)
        state, increments = flow.step(state, dt)
        integrated += increments
        t, steps = t+dt, steps+1
        require(np.all(np.isfinite(state)), 'finite coupled velocity and moment prefix')
        if t >= next_report-1e-13:
            report = flow.diagnostic(t, state, integrated)
            report.update({'steps': steps, 'last_step': dt, 'elapsed_seconds': time.monotonic()-started})
            print(json.dumps(report), flush=True)
            if report['minimum_moment_eigenvalue'] <= 0:
                reason = 'moment_positivity_resolution_limit'
                break
            if max(report['high_palinstrophy_fraction'], report['high_moment_gradient_fraction']) > args.max_tail:
                reason = 'frequency_resolution_limit'
                break
            next_report = min(next_report+args.report_every, args.final_time)
    print(json.dumps({'completion_reason': reason, 'time': t, 'steps': steps,
                      'elapsed_seconds': time.monotonic()-started}), flush=True)


if __name__ == '__main__':
    main()
