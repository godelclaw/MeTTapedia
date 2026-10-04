#!/usr/bin/env python3
"""Actual stress memory: an age-dependent pressure-primitive payment.

Exact algebra checks supplement the analytic propagator and PDE estimates
in README.md. The fine memory-pressure work remains unpaid. No continuum
history or arbitrary-data regularity theorem is certified by this script.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
import viscous_pressure_regeneration as vd
from rotational_curl_reserve import require, zero


def smoothing_exponents():
    # Nash follows from interpolation and the homogeneous Sobolev inequality.
    zero(s.Rational(1, 2)-s.Rational(2, 5)-s.Rational(3, 5)/6,
         'L2 interpolates between L1 and L6')
    zero(s.Rational(5, 6)-s.Rational(2, 3)-s.Rational(1, 3)/2,
         'L6/5 interpolates between L1 and L2')
    age, nu, CS, mass = s.symbols('age nu CS mass', positive=True)
    Y = (3*CS/(4*nu*age))**s.Rational(3, 2)*mass**2
    zero(s.diff(Y, age)+2*nu*Y**s.Rational(5, 3)/(CS*mass**s.Rational(4, 3)),
         'Nash differential inequality has the claimed singular envelope')
    l65 = mass**s.Rational(2, 3)*s.sqrt(Y)**s.Rational(1, 3)
    k = s.sqrt(CS)*(3*CS/4)**s.Rational(1, 4)
    zero(s.sqrt(CS)*l65-k*(nu*age)**(-s.Rational(1, 4))*mass,
         'source packet pressure-primitive exponent and constant')
    E0, H = s.symbols('E0 H', positive=True)
    zero(2*k*k*E0**2*s.sqrt(H/nu)-s.sqrt(3)*CS**s.Rational(3, 2)*E0**2*s.sqrt(H/nu),
         'whole-space original allowance coefficient')
    return {
        'Nash': '||f||2^(10/3)<=C_S ||f||1^(4/3)||grad f||2^2',
        'packet': '||K_L P_(s,t)T||2<=k [nu(t-s)]^(-1/4) integral tr T, T>=0',
        'k_R3': 'sqrt(C_S)(3C_S/4)^(1/4)',
        'k_T3': '2 sqrt(C_S)(3C_S/4)^(1/4)',
        'torus': 'Subtract the conserved tensor mean; its L1 deviation is at most twice the trace mass. K_L kills that mean.',
        'physical_hypothesis': 'P is the actual smooth divergence-free advection-diffusion propagator, acting entrywise. No future drift bound enters the norm estimate.',
        'reuse': 'The drift-independent Nash argument is already used by memory_age_pressure; the pressure multiplier is JP5.'}


def age_reserve():
    E, E0, a, h, gamma, convolution = s.symbols(
        'E E0 a h gamma convolution', positive=True)
    # h=H-t. Differentiate the history integral using its integrable kernel.
    past_rate = s.sqrt(h)*a-convolution/2
    remaining_rate = -E/(2*s.sqrt(h))-s.sqrt(h)*a
    reserve_rate = 2*gamma*(past_rate+remaining_rate)
    zero(reserve_rate+gamma*(convolution+E/s.sqrt(h)),
         'new source cancels between spent history and remaining energy')

    # Check an explicit smooth scalar production history independently.
    # It tests the reserve algebra, not a claimed standalone NS solution.
    t = s.symbols('t', positive=True)
    I = s.Rational(2, 3)*(1-(1-t)**s.Rational(3, 2)-t**s.Rational(3, 2))
    R = 2*gamma*(I+(1-t)**s.Rational(3, 2))
    zero(s.diff(R, t)+gamma*(2*s.sqrt(t)+s.sqrt(1-t)),
         'constant-production fixture checks the full history derivative')
    zero(R.subs(t, 0)-2*gamma, 'original reserve endpoint')
    zero(R.subs(t, 1), 'terminal reserve endpoint')
    zero(s.integrate(2*gamma*s.sqrt(t), (t, 0, 1))-4*gamma/3,
         'integrated observed-cost majorant of the fixture')
    zero(s.integrate(gamma*s.sqrt(1-t), (t, 0, 1))-2*gamma/3,
         'remaining reserve slack of the fixture')

    # At a seam the old source is not assigned age zero.
    a0, a1, a2 = s.symbols('a0 a1 a2', positive=True)
    zero((s.sqrt(a0)-s.sqrt(a1))+(s.sqrt(a1)-s.sqrt(a2))
         -(s.sqrt(a0)-s.sqrt(a2)), 'per-packet residual costs telescope')
    return {
        'actual_source': 'a(t)=2nu Z(t), E_prime=-a, integral_0^t a=E0-E(t)',
        'gamma': 'k^2 nu^(-1/2) E0',
        'observation': '||beta_C(t)||2^2<=gamma integral_0^t a(s)/sqrt(t-s) ds',
        'reserve': 'R_C(t)=2gamma [integral_0^t (sqrt(H-s)-sqrt(t-s))a(s) ds+sqrt(H-t)E(t)]',
        'rate': 'R_C_prime=-gamma [integral_0^t a(s)/sqrt(t-s) ds+E(t)/sqrt(H-t)]',
        'payment': 'integral_0^T ||beta_C||2^2+R_C(T)<=R_C(0)=2k^2 E0^2 sqrt(H/nu)',
        'quantifiers': 'Every available actual unforced prefix T<=H from the same initial datum; H and E0 are fixed at the original start.',
        'seams': 'Inherit C, E and the full age distribution a(s)ds. Do not restart C or its reserve.',
        'fixture': 'a=1, E=1-t, H=E0=1: cost majorant integrates to 4gamma/3; slack integrates to 2gamma/3.'}


def full_augmented_equations():
    # Reuse the unrestricted material product and gradient identities.
    from joint_pressure_entropy import actual_sources
    actual_sources()
    nu, lap_beta, lap_C, low = s.symbols('nu lap_beta lap_C low')
    zero((lap_beta+lap_C)-lap_C-low-(lap_beta-low),
         'physical velocity keeps the induced memory-pressure work')
    ui, uj, pi, pj, G = s.symbols('ui uj pi pj G')
    stress_rate = -ui*pj-uj*pi-2*nu*G
    memory_rate = 2*nu*G
    zero(stress_rate+memory_rate+ui*pj+uj*pi,
         'actual stress memory removes only the explicit viscous production')
    return {
        'memory': 'scriptL C=2nu G, C(0)=0; M=u tensor u+C',
        'q_hat_source': 'S_hat_q=Q_L[-u tensor grad p-grad p tensor u]+[u.grad,Q_L]M',
        'beta_hat_source': 'S_hat_beta=grad S_hat_q-(grad u)^T beta_hat',
        'velocity': 'scriptL u=Delta beta_hat-Delta beta_C-grad p_low',
        'observer': 'beta_C=K_L C; beta_hat=beta+beta_C; y_hat=sqrt(2) beta_hat/nu; r_hat=|(u,y_hat)|; J_hat=integral r_hat^3',
        'balance': 'J_hat_prime+D_hat=W_low_hat+W_mem+F_hat',
        'W_low_hat': '-3 integral r_hat u.grad p_low',
        'W_mem': '-3 integral r_hat u.Delta beta_C',
        'F_hat': '(3sqrt(2)/nu) integral r_hat y_hat.S_hat_beta',
        'diffusion': 'The full JP3 block applies: D_hat>=(4nu/3)integral |grad r_hat^(3/2)|^2',
        'retained': 'p is the actual canonical fluid pressure. All pressure work, transport commutators, receiver deformation and memory forces remain.'}


def coarse_payment():
    E0, CS, ML, nu = s.symbols('E0 CS ML nu', positive=True)
    Zroot, Cnorm2 = s.symbols('sqrt_Z beta_C_norm2', nonnegative=True)
    bnorm2 = CS**s.Rational(3, 2)*E0**s.Rational(3, 2)*Zroot
    bound = 3*ML*E0*(s.Rational(3, 2)*E0+2*(bnorm2+Cnorm2)/nu**2)
    a0 = s.Rational(9, 2)*ML*E0**2
    b0 = 6*ML*CS**s.Rational(3, 2)*E0**s.Rational(5, 2)/nu**2
    d0 = 6*ML*E0/nu**2
    zero(bound-a0-b0*Zroot-d0*Cnorm2,
         'complete augmented coarse work includes both pressure observations')
    from joint_pressure_entropy import energy_payment
    energy_payment()
    return {
        'cost': '|W_low_hat|<=a0+b0 sqrt(Z)+d0 ||beta_C||2^2',
        'a0': str(a0), 'b0': str(b0), 'd0': str(d0),
        'reserve': 'B_hat_low=a0(H-t)+b0 sqrt((H-t)E(t)/(2nu))+d0 R_C(t)',
        'payment': 'integral_0^T |W_low_hat|+B_hat_low(T)<=B_hat_low(0)',
        'OPEN': 'integral_0^T [W_mem+F_hat-D_hat/2]<=K_hat(u0,nu,H,L) on EVERY same-datum prefix',
        'conditional_consumer': 'This OPEN bound gives the JP10 L3_t L9_x estimate and JP11 order-one continuation, with J,D,B replaced by their augmented versions.',
        'limitation': 'The beta_C L2 history bound does not bound Delta beta_C or its weighted pairing W_mem.'}


def adverse_initial_repair():
    rows = []
    for n in (1, 2, 7, 16, 32):
        u = vd.datum(n)
        p = f.tensor_pressure(f.tensor(u, u))
        G = [[f.add(*(f.mul(f.diff(u[i], k), f.diff(u[j], k)) for k in range(3)))
              for j in range(3)] for i in range(3)]
        euler = [f.scale(-1, f.add(f.adv(u, u[i]), f.diff(p, i))) for i in range(3)]
        tensor_tangent = lambda v: [[f.add(f.mul(v[i], u[j]), f.mul(u[i], v[j]))
                                    for j in range(3)] for i in range(3)]
        pE = f.tensor_pressure(tensor_tangent(euler))
        for nu in (f.QQ_I(1), f.QQ_I(2)/7):
            visc = [f.scale(nu, f.lap(v)) for v in u]
            Ct = [[f.scale(2*nu, g) for g in row] for row in G]
            pV = f.tensor_pressure(tensor_tangent(visc))
            pCt = f.tensor_pressure(Ct)
            f.equal(f.add(pV, pCt), f.scale(nu, f.lap(p)),
                    'all initial viscous pressure modes cancel into augmented heat diffusion')
            require(bool(pCt), 'repair has nonzero actual stress-memory pressure')
            require(all(k[1] % 2 for v in u for k in v), 'odd velocity under y-shift')
            require(all(k[1] % 2 == 0 for k in p), 'even pressure under y-shift')
            require(all(k[1] % 2 == 0 for v in euler for k in v), 'even Euler velocity tangent')
            require(all(k[1] % 2 for k in pE), 'odd Euler pressure tangent')
            source_mass = f.trace(Ct).get(f.ORIGIN, f.ZERO)
            energy_rate = 2*f.dot(u, visc).get(f.ORIGIN, f.ZERO)
            require(source_mass == -energy_rate and source_mass.x > 0,
                    'actual memory production is paid by kinetic energy loss')
            rows.append({'n': n, 'nu': str(nu), 'pressure_modes': len(p),
                         'memory_pressure_tangent_modes': len(pCt),
                         'memory_trace_production': str(source_mass)})
    gap = vd.explicit_gap()
    return {
        'fixtures': rows, 'original_gap': gap,
        'initial_identity': 'J_hat_NS_prime(0)=J_NS_prime(0)-F_vis(0)=-D(0)<0',
        'actual_interval': 'On the same smooth unforced solution the original J increases and augmented J_hat decreases for some positive interval, by continuity of the complete equations.',
        'perturbations': 'Sufficiently small genuinely 3D smooth solenoidal perturbations retain both strict initial signs and corresponding short intervals.',
        'limits': 'No uniform interval length, persistent parity, later monotonicity or arbitrary-history source payment is asserted.'}


if __name__ == '__main__':
    result = {
        'smoothing': smoothing_exponents(),
        'age_reserve': age_reserve(),
        'equations': full_augmented_equations(),
        'coarse_payment': coarse_payment(),
        'adverse_repair': adverse_initial_repair(),
        'status': 'Exact checks passed; propagator estimates, actual intervals and continuation remain analytic, not Lean-certified.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2), flush=True)
