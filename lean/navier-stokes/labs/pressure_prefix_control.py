#!/usr/bin/env python3
"""Test velocity error controls before a pressure-history handoff.

The exact residual/control derivation is analytic in README.md. Optional
prefixes sample a quintic time interpolant's complete spatial residual.
The scalar control ODE uses sampled coefficients: it is a feasibility test,
not a continuum certificate or a bound on the pressure moments.
"""

import argparse
import json
import time
import numpy as np
from scipy.integrate import solve_ivp
from reciprocal_parent_history import Flow
from pressure_history_residual import frequencies


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def hermite(y0, y1, f0, f1, j0, j1, dt):
    """Coefficients in tau in [0,1], matching two endpoint time jets."""
    a = y1-y0-dt*f0-dt*dt*j0/2
    b = dt*f1-dt*f0-dt*dt*j0
    c = dt*dt*(j1-j0)
    return [y0, dt*f0, dt*dt*j0/2, 10*a-4*b+c/2,
            -15*a+7*b-c, 6*a-3*b+c/2]


def evaluate(coefficients, tau, dt):
    value = sum(c*tau**j for j, c in enumerate(coefficients))
    tangent = sum(j*c*tau**(j-1) for j, c in enumerate(coefficients) if j)/dt
    return value, tangent


def growth(A, C, error, nu):
    x = A+error
    return C+(x-nu if x <= 2*nu else x*x/(4*nu))


class VelocityFlow(Flow):
    def __init__(self, n, nu):
        from fractions import Fraction as Q
        from cyclic_pressure_history import seed
        self.n, self.nu, self.K = n, nu, frequencies(n)
        self.k2 = np.sum(self.K*self.K, axis=-1)
        self.inv = np.divide(1., self.k2, out=np.zeros_like(self.k2), where=self.k2 > 0)
        self.heat = -nu*self.k2
        self.mask = np.all(abs(self.K) < n/3, axis=-1)
        self.initial = np.zeros((n, n, n, 3), complex)
        for j, field in enumerate(seed(Q(1))):
            for k, a in field.items():
                self.initial[tuple(v % n for v in k)+(j,)] = complex(float(a.x), float(a.y))*n**3

    def bilinear(self, left, right, project=True):
        u, gradient = self.ifft(left), self.grad_hat(right)
        adv = self.fft(sum(u[..., j, None]*gradient[j] for j in range(3)))
        answer = -self.project(adv) if project else -adv
        return answer*self.mask[..., None]

    def rhs(self, state):
        return self.bilinear(state, state), np.array([0.])

    def jets(self, state):
        first = self.heat[..., None]*state+self.bilinear(state, state)
        second = self.heat[..., None]*first+self.bilinear(first, state)+self.bilinear(state, first)
        return first, second

    def enlarged(self, state):
        n = self.n
        pad = n//2
        return np.fft.ifftshift(np.pad(np.fft.fftshift(state, axes=(0, 1, 2)),
            ((pad, pad), (pad, pad), (pad, pad), (0, 0))), axes=(0, 1, 2))*8

    def sample(self, value, tangent):
        K = frequencies(2*self.n)
        k2 = np.sum(K*K, axis=-1)
        inv = np.divide(1., k2, out=np.zeros_like(k2), where=k2 > 0)
        vh = self.enlarged(value)
        u = self.ifft(vh)
        gradient = [self.ifft(1j*K[..., j, None]*vh) for j in range(3)]
        adv = self.fft(sum(u[..., j, None]*gradient[j] for j in range(3)))
        pressure = -K*inv[..., None]*np.sum(K*adv, axis=-1)[..., None]
        residual = self.enlarged(tangent)+self.nu*k2[..., None]*vh+adv+pressure
        square = np.sum(abs(residual)**2, axis=-1)/(2*self.n)**6
        coefficients = np.sqrt(np.sum(abs(value)**2, axis=-1))/self.n**3
        C = float(np.sum(np.sqrt(self.k2)*coefficients))
        D = float(np.sum(self.k2*coefficients))
        B = np.stack(gradient,axis=-1)
        strain = (B+np.swapaxes(B,-1,-2))/2
        sampled_compression = float(np.max(np.linalg.eigvalsh(-strain)[..., -1]))
        # Every point is within sqrt(3)*pi/(2n) of this grid. The exact
        # Fourier Lipschitz bound for strain is D/2 for solenoidal fields.
        compression = min(C/2, sampled_compression+np.sqrt(3)*np.pi*D/(4*self.n))
        return dict(A=float(coefficients.sum()), C=C, D=D, compression=compression,
                    reference_H1=float(np.sqrt(np.sum(self.k2*coefficients**2))),
                    residual_W0=float(np.sum(np.sqrt(square))),
                    residual_L2=float(np.sqrt(square.sum())),
                    residual_H1=float(np.sqrt(np.sum(square*k2))),
                    residual_H3=float(np.sqrt(np.sum(square*(1+k2)**3))))


def exact_checks():
    import sympy as s
    y0, y1, f0, f1, j0, j1, h, tau = s.symbols('y0 y1 f0 f1 j0 j1 h tau')
    coefficients = hermite(y0, y1, f0, f1, j0, j1, h)
    p = sum(c*tau**j for j, c in enumerate(coefficients))
    for endpoint, jet in [(0, (y0, f0, j0)), (1, (y1, f1, j1))]:
        for order, target in enumerate(jet):
            require(s.simplify(s.diff(p, tau, order).subs(tau, endpoint)/h**order-target) == 0,
                    'Quintic endpoint value and physical time derivatives')
    bernstein = [y0,y0+h*f0/5,y0+2*h*f0/5+h*h*j0/20,
                 y1-2*h*f1/5+h*h*j1/20,y1-h*f1/5,y1]
    require(s.expand(sum(s.binomial(5,j)*tau**j*(1-tau)**(5-j)*b
                         for j,b in enumerate(bernstein))-p) == 0,
            'The Bernstein slab is exactly the same quintic reconstruction')
    for left_degree,right_degree in [(5,5),(10,5)]:
        for i in range(left_degree+1):
            for j in range(right_degree+1):
                left = s.binomial(left_degree,i)*tau**i*(1-tau)**(left_degree-i)
                right = s.binomial(right_degree,j)*tau**j*(1-tau)**(right_degree-j)
                weight = s.binomial(left_degree,i)*s.binomial(right_degree,j) \
                    /s.binomial(left_degree+right_degree,i+j)
                target = weight*s.binomial(left_degree+right_degree,i+j) \
                    *tau**(i+j)*(1-tau)**(left_degree+right_degree-i-j)
                require(s.expand(left*right-target) == 0,
                        'Full quadratic and cubic residuals have the stated Bernstein coefficients')
    x, nu, z = s.symbols('x nu z', positive=True)
    expression = -nu*z*z+x*z
    require(s.expand(x*x/(4*nu)-expression-nu*(z-x/(2*nu))**2) == 0,
            'Exact diffusion optimization after C_error^2<=A_error D_error')
    require(s.expand((x-nu)-expression-(z-1)*(nu*(z+1)-x)) == 0,
            'Below x=2nu the constrained maximum is at z=1')
    require(s.expand(z**4/2-z**3+s.Rational(27,32)
                     -(2*z-3)**2*(4*z*z+4*z+3)/32) == 0,
            'The explicit nonlinear enstrophy Young bound is nonnegative')
    n = s.symbols('n', positive=True, integer=True)
    require(s.expand((2*n+1)**3-(2*n-1)**3-24*n*n-2) == 0,
            'Cubic lattice shells give the explicit Agmon constant sqrt(26pi)')
    viscosity, seam = s.Rational(1,4), s.Rational(1,64)
    kappa_upper = 27*(26*4)**2/(32*viscosity**3)  # pi<4
    require(2*kappa_upper*seam**4/viscosity < s.Rational(3,10),
            'The exact gradient seam tolerance gives a strictly dissipative tail')
    tail_dissipation = seam**2/(viscosity*s.Rational(7,10))
    require(tail_dissipation == s.Rational(5,3584) and 26*4*tail_dissipation == s.Rational(65,448),
            'The gradient seam pays explicit dissipation and critical velocity costs')
    ar, ai, br, bi, eigenvalue = s.symbols('ar ai br bi eigenvalue',real=True)
    a, b = ar+s.I*ai, br+s.I*bi
    transverse_strain = s.Matrix([[0,a,b],[a,0,0],[b,0,0]])
    magnitude = ar*ar+ai*ai+br*br+bi*bi
    characteristic = (transverse_strain.conjugate().T*transverse_strain).charpoly(eigenvalue).as_expr()
    # charpoly may create its own symbol with distinct assumptions.
    require(s.simplify(characteristic.subs(next(iter(characteristic.free_symbols-{ar,ai,br,bi})),eigenvalue)
                       -eigenvalue*(eigenvalue-magnitude)**2) == 0,
            'A solenoidal Fourier mode has strain operator norm |k||v_k|/2')
    return dict(status='exact interpolation and control identities passed',
                sufficient_actual_H1_seam={'viscosity':'1/4','gradient_norm_upper':'1/64',
                    'theta_upper':'3/10','tail_dissipation_upper':'5/3584',
                    'tail_integrated_velocity_supremum_squared_upper':'65/448'},
                scope='Analytic velocity-control lemma; no trajectory or moment enclosure')


def independent_jets():
    from fractions import Fraction as Q
    from cyclic_pressure_history import seed, velocity_time_jets
    flow = VelocityFlow(12, float(Q(2, 7)))
    actual = flow.jets(flow.initial)
    jets, _ = velocity_time_jets(seed(Q(1)), Q(2, 7), 2)
    errors = []
    for observed, field in zip(actual, jets[1:]):
        expected = np.zeros_like(observed)
        for j, row in enumerate(field):
            for k, value in row.items():
                expected[tuple(v % flow.n for v in k)+(j,)] = complex(float(value.x),float(value.y))*flow.n**3
        error = float(np.max(abs(observed-expected))/max(1.,np.max(abs(expected))))
        require(error < 5e-14, 'Both interpolation jets match full rational Fourier NS derivatives')
        errors.append(error)
    sample = flow.sample(flow.initial, actual[0])
    require(sample['residual_W0'] < 1e-12, 'The fully retained initial NS tangent has zero residual')
    return dict(relative_errors=errors, initial_residual_W0=sample['residual_W0'])


def translated_cellular_check():
    import sympy as s
    x, y, theta = s.symbols('x y theta', real=True)
    U = s.Matrix([s.sin(x+theta)*s.cos(y),-s.cos(x+theta)*s.sin(y),0])
    p = (s.cos(2*(x+theta))+s.cos(2*y))/4
    adv = U[0]*U.diff(x)+U[1]*U.diff(y)
    gradient = s.Matrix([s.diff(p,x),s.diff(p,y),0])
    for component in adv+gradient:
        require(s.trigsimp(s.expand_trig(component)) == 0, 'Every translated cellular profile has zero projected nonlinearity')
    require(U.diff(x,2)+U.diff(y,2) == -2*U, 'The entire translated family decays at the same viscous rate')
    r, nu, t = s.symbols('r nu t',positive=True)
    a = r*nu*s.exp(-2*nu*t)
    rate = 2*a+a*a/(2*nu)
    endpoint = s.log(r/s.sqrt(2))/(2*nu)
    integral = s.integrate(rate,(t,0,endpoint))
    claimed = r-s.sqrt(2)+(r*r-2)/8
    require(s.simplify(integral-claimed) == 0, 'Exact artificial amplification before the small-rate branch')
    require(s.simplify(s.exp(-2*nu*endpoint)-s.sqrt(2)/r) == 0, 'Actual translated difference decreases over that same interval')
    return dict(status='exact translated unforced-flow comparison passed',
                domain='amplitude/viscosity r>sqrt(2), any nonzero translation phase',
                actual_error_factor='sqrt(2)/r',
                scalar_linear_amplification='exp(r-sqrt(2)+(r^2-2)/8)',
                scope='A sharp failure of this unsigned error majorant to reflect actual stability, not of NS regularity')


def run(n, nu, dt, final, sample_every):
    require(n >= 12 and n % 2 == 0 and nu > 0 and dt > 0 and final > 0,
            'Positive viscosity/time and even retained grid')
    steps = round(final/dt)
    require(abs(steps*dt-final) < 1e-10 and sample_every > 0, 'Integral steps and positive sampling stride')
    flow = VelocityFlow(n, nu)
    state = flow.initial.copy()
    start = time.time()
    records = []
    for step in range(steps):
        next_state, _ = flow.step(state, dt)
        if step == 0 or (step+1) % sample_every == 0 or step+1 == steps:
            f0, j0 = flow.jets(state)
            f1, j1 = flow.jets(next_state)
            polynomial = hermite(state, next_state, f0, f1, j0, j1, dt)
            samples = [flow.sample(*evaluate(polynomial, tau, dt)) for tau in (0., .25, .5, .75, 1.)]
            record = {key: max(row[key] for row in samples) for key in samples[0]}
            record['time'] = (step+.5)*dt
            record['linear_rate'] = growth(record['A'], record['C'], 0., nu)
            record['L2_rate'] = record['C']/2-nu
            records.append(record)
        state = next_state
    times = np.array([r['time'] for r in records])
    def interpolate(key, t):
        return np.interp(t, times, [r[key] for r in records])
    def control(t, y):
        A, C = interpolate('A', t), interpolate('C', t)
        forcing = interpolate('residual_W0', t)
        return [growth(A, C, max(0., y[0]), nu)*y[0]+forcing,
                growth(A, C, 0., nu)*y[1]+forcing,
                (C/2-nu)*y[2]+interpolate('residual_L2', t),
                growth(A, C, 0., nu)]
    def stop(t, y):
        return 1.-y[0]
    stop.terminal = True
    solution = solve_ivp(control, [0, final], [0., 0., 0., 0.], events=stop,
                         rtol=1e-8, atol=1e-14, max_step=.02)
    require(solution.success, 'The sampled scalar control ODE completed')
    linear = solve_ivp(lambda t, y: [growth(interpolate('A', t), interpolate('C', t), 0., nu)*y[0]
                                    +interpolate('residual_W0', t),
                                    (interpolate('C', t)/2-nu)*y[1]+interpolate('residual_L2', t),
                                    growth(interpolate('A', t), interpolate('C', t), 0., nu)],
                       [0, final], [0., 0., 0.], rtol=1e-8, atol=1e-14, max_step=.02)
    require(linear.success, 'The sampled linear controls completed')
    nonlinear_coefficient = 27*(26*np.pi)**2/(32*nu**3)
    def gradient_control(t, y):
        S, D = interpolate('compression',t), interpolate('D',t)
        return [(S-nu)*y[0]+interpolate('residual_L2',t),
                (2*S-nu/2)*y[1]+D*y[0]+nonlinear_coefficient*y[1]**5
                    +interpolate('residual_H1',t)]
    def gradient_stop(t, y):
        return .1-y[1]
    gradient_stop.terminal = True
    gradient_solution = solve_ivp(gradient_control,[0,final],[0.,0.],events=gradient_stop,
                                  rtol=1e-8,atol=1e-14,max_step=.02)
    require(gradient_solution.success,'The sampled transport-cancelling gradient control completed')
    vnorm = np.sqrt(np.sum(abs(state)**2, axis=-1))/n**3
    final_H1 = float(np.sqrt(np.sum(flow.k2*vnorm*vnorm)))
    reaches_final = bool(gradient_solution.t[-1] == final)
    actual_H1_upper = final_H1+float(gradient_solution.y[1,-1]) if reaches_final else None
    theta = 2*nonlinear_coefficient*actual_H1_upper**4/nu if reaches_final else None
    return dict(scope='sampled residual/control feasibility only; no rounding or between-sample enclosure',
                n=n, nu=nu, dt=dt, final=final, elapsed=time.time()-start,
                final_A=float(vnorm.sum()),
                final_H1=final_H1,
                nonlinear_control={'final_time':float(solution.t[-1]),'error':float(solution.y[0,-1])},
                linear_control={'W0':float(linear.y[0,-1]),'L2':float(linear.y[1,-1]),
                                'log_amplification':float(linear.y[2,-1])},
                gradient_control={'final_time':float(gradient_solution.t[-1]),
                    'L2':float(gradient_solution.y[0,-1]),'H1':float(gradient_solution.y[1,-1]),
                    'maximum_H1':float(gradient_solution.y[1].max())},
                approximate_H1_tail={'upper':actual_H1_upper,'theta':theta,
                    'passes':bool(reaches_final and theta < 1),
                    'scope':'Sampled control only; requires a certified continuous-prefix H1 enclosure'}, records=records)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=24)
    parser.add_argument('--nu', type=float, default=.25)
    parser.add_argument('--dt', type=float, default=.01)
    parser.add_argument('--final', type=float, default=12.)
    parser.add_argument('--sample-every', type=int, default=25)
    args = parser.parse_args()
    print(json.dumps(run(args.n,args.nu,args.dt,args.final,args.sample_every)
                     if args.prefix else dict(algebra=exact_checks(), jets=independent_jets(),
                                              actual_family=translated_cellular_check()), indent=2), flush=True)
