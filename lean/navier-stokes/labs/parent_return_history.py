#!/usr/bin/env python3
"""Returned parent work in complete unforced Navier--Stokes histories.

The torus has period 2*pi and normalized volume. Exact canonical jets
retain every output and the generated pressure. A separate symbolic
calculation checks the first return and its three-parent correction.
Rational phase-integral bounds support the analytic positive-viscosity
return interval described in README.md. They do not certify a continuum
stochastic construction or an arbitrary-history stretching allowance.

Optional prefixes evolve all three velocities with the existing
integrating-factor solver. They are dealiased Galerkin approximations,
not continuum enclosures. Parent kinetic work is distinct from the
vorticity stretching needed for continuation.
"""

import argparse
import json
import math
import time
from fractions import Fraction

import numpy as np
import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
from cyclic_pressure_history import velocity_time_jets
from joint_source_history import seed
from reciprocal_parent_history import Flow


PARENT_MODES = ((0, 1, 0), (0, 0, 1), (1, 0, 0))


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def project_parents(field):
    """Orthogonal projection onto the three original real sine vectors."""
    result = []
    for component, k in zip(field, PARENT_MODES):
        amplitude = -2*component.get(k, f.ZERO).y
        opposite = tuple(-q for q in k)
        require(component.get(opposite, f.ZERO).y == amplitude/2,
                'the real sine projection retains both conjugate modes')
        result.append(f.clean({k: -f.II*f.QQ_I(amplitude)/2,
                               opposite: f.II*f.QQ_I(amplitude)/2}))
    return result


def pair_jet(left, right, n):
    return sum((math.comb(n, j)*pm.mean(f.dot(left[j], right[n-j]))
                for j in range(n+1)), f.ZERO.x)


def gradient(field):
    return [[f.diff(component, k) for component in field] for k in range(3)]


def complete_returns(amplitudes, viscosity):
    initial = seed(amplitudes)
    omega, B = f.curl(initial), f.jac(initial)
    initial_cubic_mass = pm.mean(f.dot(omega, [f.dot(row, omega) for row in B]))
    require(initial_cubic_mass == 0, 'the original signed cubic mass of the cyclic sine family')
    us, ps = velocity_time_jets(initial, viscosity, 4)
    parents = list(map(project_parents, us))
    hidden = [[f.add(u, f.scale(-1, p)) for u, p in zip(field, observed)]
              for field, observed in zip(us, parents)]
    sources = [[f.add(u, f.scale(-f.QQ_I(viscosity), f.lap(old)))
                for u, old in zip(us[n+1], us[n])] for n in range(4)]
    parent_sources = list(map(project_parents, sources))
    works = [pair_jet(parents, parent_sources, n) for n in range(4)]
    hidden_energy = [pair_jet(hidden, hidden, n) for n in range(5)]
    hidden_gradients = list(map(gradient, hidden))
    losses = [sum((pair_jet([g[k] for g in hidden_gradients],
                           [g[k] for g in hidden_gradients], n)
                   for k in range(3)), f.ZERO.x) for n in range(4)]
    for n in range(4):
        require(pair_jet(us, sources, n) == 0,
                ('complete canonical nonlinear kinetic balance', n))
        require(hidden_energy[n+1]+2*f.QQ_I(viscosity).x*losses[n]+2*works[n] == 0,
                ('actual hidden energy retains each returned work', n))
    a, b, c = map(f.QQ_I, amplitudes)
    S22 = (a*a*b*b+a*a*c*c+b*b*c*c).x
    S42 = (a*a*b**4+b*b*c**4+c*c*a**4).x
    R = (a*a*b*b*c*c).x
    nu = f.QQ_I(viscosity).x
    expected = [0, -S22/4, 2*nu*S22, 9*S42/16+3*R/2-12*nu*nu*S22]
    require(works == expected, 'complete returned-work coefficients')
    require(hidden_energy[0] == 0, 'initially unobserved modes have zero energy')
    require(not ps[0], 'complete canonical pressure is initially zero')
    return {'amplitudes': list(map(str, amplitudes)), 'nu': str(viscosity),
            'mode_counts': [len(set().union(*u)) for u in us],
            'pressure_mode_counts': list(map(len, ps)),
            'initial_cubic_mass': str(initial_cubic_mass),
            'parent_work_jets': list(map(str, works)),
            'hidden_energy_jets': list(map(str, hidden_energy)),
            'cycle_correction_third_derivative': str(3*R/2),
            'scope': 'complete exact canonical jets; no uniform NS Taylor remainder'}


def trig_mean(expression, coordinates):
    angles = s.symbols('sx cx sy cy sz cz')
    replacements = {v: angles[2*i+j] for i, q in enumerate(coordinates)
                    for j, v in enumerate((s.sin(q), s.cos(q)))}
    polynomial = s.Poly(s.expand_trig(s.expand(expression)).xreplace(replacements), *angles)
    result = 0
    for powers, coefficient in polynomial.terms():
        weight = s.Integer(1)
        for m, n in zip(powers[::2], powers[1::2]):
            if m % 2 or n % 2:
                weight = 0
                break
            r, t = m//2, n//2
            weight *= s.Rational(math.factorial(2*r)*math.factorial(2*t),
                4**(r+t)*math.factorial(r)*math.factorial(t)*math.factorial(r+t))
        result += weight*coefficient
    return s.factor(result)


def symbolic_returns():
    x, y, z = coordinates = s.symbols('x y z', real=True)
    a, b, c, nu = s.symbols('a b c nu', real=True)
    expand = lambda A: A.applyfunc(s.expand)
    lap = lambda A: A.applyfunc(lambda v: sum(s.diff(v, q, 2) for q in coordinates))
    adv = lambda u, A: A.applyfunc(lambda v: sum(u[i]*s.diff(v, q)
                                               for i, q in enumerate(coordinates)))
    grad = lambda p: s.Matrix([s.diff(p, q) for q in coordinates])
    u = s.Matrix([a*s.sin(y), b*s.sin(z), c*s.sin(x)])
    u1 = expand(nu*lap(u)-adv(u, u))
    p1 = -2*a*b*c*s.cos(x)*s.cos(y)*s.cos(z)
    u2 = expand(nu*lap(u1)-adv(u1, u)-adv(u, u1)-grad(p1))
    p2 = -s.Rational(2, 3)*a*b*c*(c*s.sin(2*x)*s.cos(y)*s.sin(z)
         +a*s.sin(x)*s.sin(2*y)*s.cos(z)+b*s.cos(x)*s.sin(y)*s.sin(2*z))-6*nu*p1
    for n, p in ((1, p1), (2, p2)):
        fields = [u, u1, u2]
        source = sum(math.comb(n, r)*s.trace(fields[r].jacobian(coordinates)*
                                            fields[n-r].jacobian(coordinates))
                     for r in range(n+1))
        require(s.trigsimp(s.expand_trig(s.expand(lap(s.Matrix([p]))[0]+source))) == 0,
                ('literal generated canonical pressure', n))
    u3 = expand(nu*lap(u2)-adv(u2, u)-2*adv(u1, u1)-adv(u, u2)-grad(p2))
    # The full Fourier check retains p3. Its gradient is orthogonal to
    # each divergence-free sine parent, so it has zero parent projection.
    u4_before_pressure = expand(nu*lap(u3)-adv(u3, u)-3*adv(u2, u1)
                               -3*adv(u1, u2)-adv(u, u3))
    phases = (y, z, x)
    observed = [[2*trig_mean(field[i]*s.sin(phases[i]), coordinates)
                 for i in range(3)] for field in (u, u1, u2, u3, u4_before_pressure)]
    amplitudes, advectors, next_parents = (a, b, c), (b, c, a), (c, a, b)
    for i, (amplitude, parent, next_parent) in enumerate(zip(amplitudes, advectors, next_parents)):
        expected = [amplitude, -nu*amplitude,
                    nu**2*amplitude-amplitude*parent**2/2,
                    -nu**3*amplitude+s.Rational(7, 2)*nu*amplitude*parent**2,
                    nu**4*amplitude-17*nu**2*amplitude*parent**2
                    +s.Rational(3, 8)*amplitude*parent**4
                    +amplitude*parent**2*next_parent**2]
        for n in range(5):
            require(s.expand(observed[n][i]-expected[n]) == 0,
                    ('independent complete parent observation', i, n))
    work = [s.factor(sum(math.comb(n, r)*sum(observed[r][i]*
                (observed[n-r+1][i]+nu*observed[n-r][i]) for i in range(3))/2
                for r in range(n+1))) for n in range(4)]
    S22 = a*a*b*b+a*a*c*c+b*b*c*c
    S42 = a*a*b**4+b*b*c**4+c*c*a**4
    expected = [0, -S22/4, 2*nu*S22,
                s.Rational(9, 16)*S42+s.Rational(3, 2)*a*a*b*b*c*c-12*nu*nu*S22]
    for n in range(4):
        require(s.expand(work[n]-expected[n]) == 0, ('independent generic return work', n))
    return {'parent_amplitude_jets': [[str(v) for v in row] for row in observed],
            'returned_work_jets': list(map(str, work)),
            'scope': 'independent symbolic projection; full Fourier jets retain all pressure outputs'}


def phase_interval():
    Q = Fraction
    series0 = lambda n: sum(((-1)**m*Q(9, 4)**m/math.factorial(m)**2
                             for m in range(n+1)), Q(0))
    series1 = lambda n: Q(3, 2)*sum(((-1)**m*Q(9, 4)**m/
        (math.factorial(m)*math.factorial(m+1)) for m in range(n+1)), Q(0))
    lower0, upper0 = series0(5), series0(4)
    lower1, upper1 = series1(5), series1(4)
    # After m=1 both absolute term sequences decrease. The alternating
    # remainder therefore lies between these odd/even partial sums.
    require(Q(9, 16) < 1 and Q(9, 24) < 1, 'decreasing alternating tails')
    require(lower0 < upper0 < Q(-1, 4), 'certified negative original phase mean at sigma=3')
    require(Q(1, 3) < lower1 < upper1, 'certified negative derivative of the phase mean')
    S, kappa = Q(49, 16), Q(1, 1000)
    B = S+3*S*S/4+S**3/6
    error_p, error_r = Q(3, 2)*kappa*B, kappa*(B+S)
    require(error_p < Q(1, 16) and error_r < Q(1, 16),
            'datum-fixed L2 scalar difference margins')
    require(upper0+Q(1, 16)+error_p < Q(-1, 8), 'uniform actual parent-amplitude sign')
    require(-lower1+Q(1, 32)+error_r < Q(-1, 6), 'uniform actual returned-source sign')
    return {'phase_integral_at_three': {'lower': str(lower0), 'upper': str(upper0)},
            'negative_phase_derivative_at_three': {'lower': str(lower1), 'upper': str(upper1)},
            'scaled_interval': ['47/16', '49/16'], 'viscosity_ratio': '0<nu/A<=1/1000',
            'scalar_L2_difference_bound': 'kappa*(S+3*S^2/4+S^3/6)',
            'parent_error_bound': str(error_p), 'source_error_bound': str(error_r),
            'physical_return_work_lower': 'A^3/96', 'integrated_return_work_lower': 'A^2/768',
            'scope': 'rational margins; elementary phase integrals and positive-viscosity contraction passage analytic'}


def reference_reserve():
    """Algebra of the known reference envelope and its paid 3D neighborhood.

    Continuous scalar contraction and the NS perturbation estimate are
    analytic in README.md. This checks their polynomials and scalar rates,
    not those continuum estimates or a numerical smallness certificate.
    """
    L = s.symbols('L', nonnegative=True)
    polynomials = [s.Integer(1)]
    for j in range(1, 5):
        derivative = sum(math.comb(j, r)*polynomials[j-r] for r in range(1, j+1))
        polynomials.append(s.integrate(derivative, (L, 0, L)).expand())
    expected = [1, L, L+L**2, L+3*L**2+L**3, L+7*L**2+6*L**3+L**4]
    require(polynomials == expected, 'complete reference derivative contraction recurrence')
    a, b, t, nu, C3, Cemb, Q4, Y0 = s.symbols('a b t nu C3 Cemb Q4 Y0', positive=True)
    M = C3*Q4/nu
    envelope = Y0*s.exp(M*(1-s.exp(-nu*t))-nu*t)
    require(s.simplify(s.diff(envelope, t)-(C3*Q4*s.exp(-nu*t)-nu)*envelope) == 0,
            'original-data perturbation comparison rate')
    N = Q4+s.sqrt(Y0)*s.exp(M/2)
    reserve = 4*Cemb*N**3*s.exp(-3*nu*t/2)/(3*nu)
    require(s.simplify(-s.diff(reserve, t)-2*Cemb*N**3*s.exp(-3*nu*t/2)) == 0,
            'actual cubic work paid on every compatible interval')
    kinetic_reserve = a*b*b*s.exp(-3*nu*t)/(3*nu)
    require(s.simplify(-s.diff(kinetic_reserve, t)-a*b*b*s.exp(-3*nu*t)) == 0,
            'entire triangular absolute kinetic-return payment')
    return {'reference_derivative_polynomials': list(map(str, polynomials)),
            'reference_H4_squared_envelope': '5a^2/2+(b^2/2)sum_j=0..4(5-j)P_j(|a|/nu)^2',
            'perturbation_threshold': 'sqrt(Y0)*exp(C3*Q4/(2nu))<=nu/(2C3)',
            'third_parent_initial_H3_squared': '2epsilon^2',
            'original_perturbation_envelope': 'Y0 exp[(C3 Q4/nu)(1-exp(-nu t))-nu t]',
            'actual_cubic_reserve': '4 C_emb N^3 exp(-3nu t/2)/(3nu)',
            'triangular_twice_absolute_kinetic_reserve': 'a b^2 exp(-3nu t)/(3nu)',
            'scope': 'exact scalar algebra; derivative/stability/spatial continuum bounds analytic; numerical epsilon not certified'}


class ReturnFlow(Flow):
    """The established velocity integrator, with three sine observers."""

    def __init__(self, n, nu, epsilon):
        self.n, self.nu, self.epsilon = n, nu, epsilon
        frequencies = np.fft.fftfreq(n)*n
        self.K = np.stack(np.meshgrid(frequencies, frequencies, frequencies, indexing='ij'), axis=-1)
        self.k2 = np.sum(self.K*self.K, axis=-1)
        self.inv = np.divide(1, self.k2, out=np.zeros_like(self.k2), where=self.k2 != 0)
        self.heat = -nu*self.k2
        self.mask = np.all(abs(self.K) < n/3, axis=-1)
        self.initial = np.zeros((n, n, n, 3), dtype=np.complex128)
        for i, field in enumerate(seed((1, epsilon, 1))):
            for k, value in field.items():
                self.initial[tuple(q % n for q in k)+(i,)] = complex(float(value.x), float(value.y))*n**3

    def observations(self, state, nonlinear):
        amplitudes = [-2*state[tuple(q % self.n for q in k)+(i,)].imag/self.n**3
                      for i, k in enumerate(PARENT_MODES)]
        sources = [-2*nonlinear[tuple(q % self.n for q in k)+(i,)].imag/self.n**3
                   for i, k in enumerate(PARENT_MODES)]
        energy = np.sum(abs(state/self.n**3)**2, axis=-1)
        E, D = float(np.sum(energy)), float(np.sum(self.k2*energy))
        EP = float(np.dot(amplitudes, amplitudes)/2)
        WP = float(np.dot(amplitudes, sources)/2)
        whole_work = float(np.real(np.sum(np.conj(state)*nonlinear))/self.n**6)
        return amplitudes, sources, E, D, EP, WP, whole_work

    def rhs(self, state):
        u, derivatives = self.ifft(state), self.grad_hat(state)
        adv = sum(u[..., j, None]*derivatives[j] for j in range(3))
        nonlinear = self.project(self.fft(-adv))*self.mask[..., None]
        _, _, E, D, EP, WP, whole_work = self.observations(state, nonlinear)
        rates = np.array([2*WP, 2*(whole_work-WP), 2*self.nu*EP,
                          2*self.nu*(D-EP), 2*self.nu*D])
        return nonlinear, rates

    def diagnostic(self, t, state, ledger):
        nonlinear, _ = self.rhs(state)
        amplitudes, sources, E, D, EP, WP, whole_work = self.observations(state, nonlinear)
        E0 = float(1+self.epsilon*self.epsilon/2)
        EP0 = E0
        density = np.sum(abs(state/self.n**3)**2, axis=-1)
        high = np.any(abs(self.K) > .8*self.n/3, axis=-1)
        div = np.sum(self.K*state, axis=-1)/self.n**3
        # A quadratic pressure product needs every output, including
        # those above the velocity truncation. Doubling each axis keeps
        # these products alias-free for this strictly 2/3-filtered state.
        m, pad = 2*self.n, self.n//2
        enlarged = np.fft.ifftshift(np.pad(np.fft.fftshift(state, axes=(0, 1, 2)),
            ((pad, pad), (pad, pad), (pad, pad), (0, 0))), axes=(0, 1, 2))*8
        frequencies = np.fft.fftfreq(m)*m
        K = np.stack(np.meshgrid(frequencies, frequencies, frequencies, indexing='ij'), axis=-1)
        k2 = np.sum(K*K, axis=-1)
        inverse = np.divide(1, k2, out=np.zeros_like(k2), where=k2 != 0)
        derivatives = [self.ifft(1j*K[..., j, None]*enlarged) for j in range(3)]
        source = sum(derivatives[j][..., i]*derivatives[i][..., j]
                     for i in range(3) for j in range(3))
        pressure = inverse*self.fft(source)/m**3
        negative = (-np.arange(self.n)) % self.n
        reflected = state[np.ix_(negative, negative, negative)]
        reality_error = float(np.max(abs(state-np.conj(reflected)))/self.n**3)
        return {'time': t, 'parent_amplitudes': list(map(float, amplitudes)),
                'parent_nonlinear_sources': list(map(float, sources)),
                'vertical_parent_work': float(amplitudes[2]*sources[2]/2),
                'all_parent_work': WP, 'total_nonlinear_work': whole_work,
                'energy': E, 'hidden_energy': E-EP,
                'energy_balance_error': E-E0+float(ledger[4]),
                'parent_balance_error': EP-EP0-float(ledger[0])+float(ledger[2]),
                'hidden_balance_error': E-EP-float(ledger[1])+float(ledger[3]),
                'canonical_pressure_L2sq': float(np.sum(abs(pressure)**2)),
                'canonical_pressure_hessian_L2sq': float(np.sum(k2*k2*abs(pressure)**2)),
                'pressure_diagnostic_grid': m,
                'divergence_L2sq': float(np.sum(abs(div)**2)),
                'conjugacy_maximum_error': reality_error,
                'high_velocity_energy_fraction': float(np.sum(density[high])/np.sum(density)),
                'high_enstrophy_fraction': float(np.sum((density*self.k2)[high])/D)}


def initial_operator_check():
    nu, epsilon = Fraction(1, 1000), Fraction(1, 20)
    initial = seed((1, epsilon, 1))
    us, _ = velocity_time_jets(initial, nu, 1)
    exact = [f.add(q, f.scale(-f.QQ_I(nu), f.lap(old))) for q, old in zip(us[1], initial)]
    flow = ReturnFlow(24, float(nu), epsilon)
    numeric, _ = flow.rhs(flow.initial)
    reference = np.zeros_like(numeric)
    for i, field in enumerate(exact):
        for k, value in field.items():
            reference[tuple(q % flow.n for q in k)+(i,)] = complex(float(value.x), float(value.y))*flow.n**3
    error = float(np.max(abs(numeric-reference))/flow.n**3)
    require(error < 2e-13, 'complete initial numerical/exact operator comparison')
    # A solenoidal polynomial with nonzero pressure checks the enlarged
    # diagnostic against every canonical pressure output, via its two
    # Parseval moments. This probe is not an asserted solution time slice.
    probe = [f.add(u, f.scale(f.QQ_I(Fraction(1, 7)), du)) for u, du in zip(initial, us[1])]
    pressure = f.green(f.trace(f.matmul(f.jac(probe), f.jac(probe))))
    require(bool(pressure), 'the pressure diagnostic probe is nontrivial')
    exact_pressure = sum((z.x*z.x+z.y*z.y for z in pressure.values()), f.ZERO.x)
    exact_hessian = sum((sum(q*q for q in k)**2*(z.x*z.x+z.y*z.y)
                         for k, z in pressure.items()), f.ZERO.x)
    state = np.zeros_like(flow.initial)
    for i, field in enumerate(probe):
        for k, value in field.items():
            state[tuple(q % flow.n for q in k)+(i,)] = complex(float(value.x), float(value.y))*flow.n**3
    diagnostic = flow.diagnostic(0., state, np.zeros(5))
    pressure_error = abs(diagnostic['canonical_pressure_L2sq']-float(exact_pressure))
    hessian_error = abs(diagnostic['canonical_pressure_hessian_L2sq']-float(exact_hessian))
    require(pressure_error < 2e-13 and hessian_error < 2e-13,
            'enlarged complete pressure moments match exact canonical moments')
    return {'initial_operator_maximum_error': error, 'pressure_L2sq_error': pressure_error,
            'pressure_hessian_L2sq_error': hessian_error, 'probe_pressure_modes': len(pressure)}


def prefix(args):
    flow = ReturnFlow(args.n, args.nu, args.epsilon)
    state, ledger = flow.initial.copy(), np.zeros(5)
    t, samples = 0., []
    targets = [0., .5, 1., 1.5, 2., 2.5, 47/16, 3., 49/16]
    start, window_start = time.monotonic(), None
    for target in targets:
        while t < target-1e-14:
            dt = min(args.dt, target-t)
            state, rates = flow.step(state, dt)
            ledger += rates
            t += dt
        sample = flow.diagnostic(target, state, ledger)
        samples.append(sample)
        if target == 47/16:
            window_start = ledger[0]
        print(json.dumps(sample), flush=True)
    print(json.dumps({'n': args.n, 'dt': args.dt, 'nu': args.nu, 'epsilon': str(args.epsilon),
                      'samples': samples, 'twice_all_parent_return_in_window': float(ledger[0]-window_start),
                      'elapsed_seconds': time.monotonic()-start,
                      'scope': 'three-dimensional full-velocity dealiased Galerkin prefix; not a continuum enclosure'}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--dt', type=float, default=.005)
    parser.add_argument('--nu', type=float, default=.001)
    parser.add_argument('--epsilon', type=Fraction, default=Fraction(1, 20))
    args = parser.parse_args()
    if args.prefix:
        if args.n < 18 or args.n % 2 or args.dt <= 0 or args.nu <= 0 or args.epsilon < 0:
            parser.error('even grid >=18, positive viscosity/time step and nonnegative third parent required')
        prefix(args)
        return
    reports = [complete_returns(amplitudes, nu) for amplitudes, nu in (
        ((1, 2, 3), Fraction(1, 10)), ((2, -1, 3), Fraction(2, 5)),
        ((1, 0, 1), Fraction(1, 1000)), ((0, 2, 0), Fraction(1, 3)))]
    print(json.dumps({'complete_canonical_returns': reports, 'independent_symbolic_returns': symbolic_returns(),
                      'positive_viscosity_phase_interval': phase_interval(),
                      'paid_reference_neighborhood': reference_reserve(),
                      'numerical_operator_and_pressure_checks': initial_operator_check()}, indent=2))


if __name__ == '__main__':
    main()
