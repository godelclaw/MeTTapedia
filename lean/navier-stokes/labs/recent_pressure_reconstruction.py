#!/usr/bin/env python3
"""Recent pressure histories reconstruct the actual unforced velocity.

Exact full NS jets check the transported-gradient defect and its first
solenoidal return. The window smoothing and continuation estimates in
README.md are analytic. No arbitrary-history bound is claimed.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
import aged_joint_memory_payment as am
import viscous_pressure_regeneration as vd
from rotational_curl_reserve import require, zero


def project(vector):
    potential = f.green(f.trace(f.jac(vector)))
    return [f.add(vector[i], f.diff(potential, i)) for i in range(3)]


def addv(*vectors):
    return [f.add(*(v[i] for v in vectors)) for i in range(3)]


def scalev(c, vector):
    return [f.scale(c, v) for v in vector]


def same_vectors(a, b, label):
    for i in range(3):
        f.equal(a[i], b[i], (label, i))


def exponent_checks():
    R = s.Rational
    zero(R(1, 2)-R(1, 9)-R(7, 18), 'velocity propagator gain')
    zero(R(1, 2)-R(4, 9)-R(1, 18), 'stress-source propagator gain')
    zero(1-R(4, 9)-R(5, 9), 'positive incoming stress interpolation')
    zero(R(4, 9)-R(1, 9)-R(1, 3), 'pressure primitive Sobolev exponents')
    delta, nu, N0 = s.symbols('delta nu N0', positive=True)
    integrals = []
    for theta in (R(7, 18), R(1, 18)):
        power = 3*theta/2
        value = N0**theta*nu**(-power)*delta**(1-power)/(1-power)
        zero(s.diff(value, delta)-N0**theta*(nu*delta)**(-power),
             'integrable whole-space age kernel')
        require(power < 1, 'no nonintegrable age endpoint is hidden')
        integrals.append({'theta': str(theta), 'age_power': str(power),
                          'integral': str(value)})
    L, k = s.symbols('L k', positive=True)
    gaussian = 4*s.pi*s.integrate(k**4*s.exp(-2*L**2*k**2), (k, 0, s.oo))/(2*s.pi)**3
    D2 = 3/(4*L**2)*(8*s.pi*L**2)**(-R(3, 2))
    zero(gaussian-D2, 'complete coarse pressure-gradient kernel L2 norm')
    x, y = s.symbols('x y', nonnegative=True)
    zero(4*(x**3+y**3)-(x+y)**3-3*(x+y)*(x-y)**2,
         'cubic continuation cost')
    return {'smoothing_powers': integrals, 'D_L_squared_R3': str(D2),
            'velocity_bound': '||u(t)+V_hi,delta(t)||9<=A_delta, with A_delta fixed from original data.',
            'consumer': 'integral ||u||9^3 <=4H*A_delta^3+4*integral ||V_hi,delta||9^3',
            'OPEN': 'A finite original-data bound for the displayed recent solenoidal pressure history, on every compatible prefix.'}


def differential_intertwining():
    t, nu = s.symbols('t nu', real=True)
    x = s.symbols('x0:3', real=True)
    args = (t,)+x
    u = [s.Function('u'+str(i))(*args) for i in range(3)]
    q = s.Function('q')(*args)
    op = lambda h: s.diff(h, t)+sum(u[j]*s.diff(h, x[j]) for j in range(3))-nu*sum(s.diff(h, a, 2) for a in x)
    for i in range(3):
        zero(op(s.diff(q, x[i]))-s.diff(op(q), x[i])
             +sum(s.diff(u[j], x[i])*s.diff(q, x[j]) for j in range(3)),
             'pressure-potential gradient retains the full deformation defect')
    return {'potential': 'scriptL q_s=p_hi, q_s(s)=0',
            'impulse': 'scriptL I_s=grad p_hi, I_s(s)=0',
            'defect': 'scriptL(I_s-grad q_s)=(grad u)^T grad q_s',
            'projection': 'Pi I_s(t)=Pi integral_s^t P_(a,t)[(grad u(a))^T grad q_s(a)] da',
            'compatibility': 'Both propagators, pressure and deformation belong to the same actual solution; s is fixed while deriving the identity.'}


def actual_jet(u, name, nu):
    stress = f.tensor(u, u)
    p = f.tensor_pressure(stress)
    gp = f.grad(p)
    evolve = lambda field: f.add(f.scale(nu, f.lap(field)), f.scale(-1, f.adv(u, field)))
    ut = [f.add(evolve(ui), f.scale(-1, gp[i])) for i, ui in enumerate(u)]
    stress_t = [[f.add(f.mul(ut[i], u[j]), f.mul(u[i], ut[j])) for j in range(3)] for i in range(3)]
    pt = f.tensor_pressure(stress_t)
    gpt = f.grad(pt)
    f.equal(f.trace(f.jac(u)), {}, 'actual incompressible datum')
    f.equal(f.trace(f.jac(ut)), {}, 'actual full tangent is incompressible')
    utt = [f.add(evolve(ut[i]), f.scale(-1, f.adv(ut, u[i])), f.scale(-1, gpt[i])) for i in range(3)]

    # P_(0,h) has second derivative A0^2+A0_prime, A0=nu Delta-u.grad.
    incoming_second = [f.add(evolve(evolve(ui)), f.scale(-1, f.adv(ut, ui))) for ui in u]
    impulse_second = [f.add(gpt[i], evolve(gp[i])) for i in range(3)]
    same_vectors(addv(incoming_second, scalev(-1, impulse_second)), utt,
                 'actual velocity reconstruction to second order includes evolving drift')

    high_p, high_pt = am.high(p), am.high(pt)
    high_gp, high_gpt = f.grad(high_p), f.grad(high_pt)
    high_impulse_second = [f.add(high_gpt[i], evolve(high_gp[i])) for i in range(3)]
    deformation = [f.add(*(f.mul(f.diff(u[j], i), high_gp[j]) for j in range(3))) for i in range(3)]
    projected = project(deformation)
    same_vectors(project(high_gp), [{}, {}, {}], 'the first pressure impulse is a gradient')
    same_vectors(project(high_impulse_second), projected,
                 'the second solenoidal return is the pressure-deformation coupling')
    f.equal(f.trace(f.jac(projected)), {}, 'the return is genuinely solenoidal')
    norm2 = am.pairing(projected, projected)
    require(norm2.y == 0 and norm2.x > 0, 'nonzero physically generated solenoidal return')
    # The canonical pressure is even in u; the deformation return is odd.
    reverse = scalev(-1, u)
    f.equal(f.tensor_pressure(f.tensor(reverse, reverse)), p, 'velocity reversal retains pressure')
    reversed_deformation = [f.add(*(f.mul(f.diff(reverse[j], i), high_gp[j]) for j in range(3))) for i in range(3)]
    same_vectors(project(reversed_deformation), scalev(-1, projected),
                 'same initial pressure admits opposite returned vectors')

    # Retained memory cancels the complete viscous stress production, not pressure.
    C1 = [[f.scale(2*nu, f.add(*(f.mul(f.diff(u[i], k), f.diff(u[j], k)) for k in range(3))))
           for j in range(3)] for i in range(3)]
    pressure_stress = [[f.add(f.mul(u[i], gp[j]), f.mul(gp[i], u[j])) for j in range(3)] for i in range(3)]
    M1 = am.matrix_add(stress_t, C1)
    expected = [[f.add(evolve(stress[i][j]), f.scale(-1, pressure_stress[i][j])) for j in range(3)] for i in range(3)]
    f.same_matrices(M1, expected, 'complete incoming-stress reconstruction')
    require(am.average(f.trace(M1)) == f.ZERO, 'full augmented trace remains E0')
    return {'datum': name, 'nu': str(nu), 'pressure_modes': len(p),
            'pressure_tangent_modes': len(pt), 'returned_vector_modes': sum(map(len, projected)),
            'second_return_norm_squared': str(norm2),
            'impulse_norm_squared_over_t4_limit': str(norm2/4),
            'actual_interval': 'The projected recent pressure impulse is nonzero for all sufficiently small positive times; this is not a claim of growing kinetic energy or singularity.'}


if __name__ == '__main__':
    data = [('A3 B2 n2', vd.datum(2, 3, 2)),
            ('A11 B10 n2', vd.datum(2, 11, 10)),
            ('genuine three-dimensional datum', f.fixture())]
    result = {
        'bounds': exponent_checks(), 'intertwining': differential_intertwining(),
        'physical_jets': [actual_jet(u, name, nu) for name, u in data
                          for nu in (f.QQ_I(1), f.QQ_I(2)/7)],
        'status': 'Exact checks passed; propagator bounds, actual positive-time consequences and the continuation bridge are analytic, not Lean-certified.',
        'scope': 'Actual histories are reconstructed with every incoming parent. The recent-history allowance remains open; this is not a closed finite-memory model.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2), flush=True)
