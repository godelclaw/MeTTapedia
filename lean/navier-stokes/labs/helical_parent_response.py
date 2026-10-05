#!/usr/bin/env python3
"""Exact physical identities for a time-dependent first-harmonic parent.

The Rayleigh/Squire reserve and continuation implication are analytic in
README.md. Every generated Fourier source is retained; this is neither
a Galerkin evolution nor a proof that nonlinear input is already paid.
"""
import hashlib
import json
from pathlib import Path

import optimal_cubic_gauge as og

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require = og.require


def scalar_pair(a, b):
    return am.pairing([a], [b])


def select(v, predicate):
    return [{k: a for k, a in component.items() if predicate(k)} for component in v]


def parent(v):
    return select(v, lambda k: k[:2] == (0, 0) and abs(k[2]) == 1)


def horizontal_mean(v):
    return select(v, lambda k: k[:2] == (0, 0))


def weight(a, fn):
    return f.clean({k: fn(k)*c for k, c in a.items()})


def nonlinear(v):
    conv = og.adv(v, v)
    p = f.tensor_pressure(f.tensor(v, v))
    rhs = wh.scalev(-1, wh.addv(conv, f.grad(p)))
    wh.same_vectors(rhs, wh.scalev(-1, wh.project(conv)),
                    'complete canonical pressure and Leray nonlinearity agree')
    return rhs


def vertical_variables(v):
    w = v[2]
    q = f.scale(-1, f.lap(w))
    cq = f.add(q, f.scale(-1, w))
    eta = f.curl(v)[2]
    return w, q, cq, eta


def norm_data(v):
    w, q, cq, eta = vertical_variables(v)
    r2 = scalar_pair(q, cq)
    neutral = {k: a for k, a in q.items() if sum(j*j for j in k) == 1}
    a2 = scalar_pair(neutral, neutral)
    y2 = scalar_pair(eta, eta)
    eta_z = f.diff(eta, 2)
    z2 = scalar_pair(eta_z, weight(eta_z, lambda k: Q(1)/(k[0]**2+k[1]**2)))
    mean = horizontal_mean(v)
    m2 = am.pairing([f.diff(a, 2) for a in mean], [f.diff(a, 2) for a in mean])
    grad2 = sum((am.pairing([f.diff(a, j) for a in v], [f.diff(a, j) for a in v])
                 for j in range(3)), f.ZERO)
    pol2 = scalar_pair(q, weight(q, lambda k: Q(1)/(k[0]**2+k[1]**2)))
    require(grad2 == pol2+y2+z2+m2, 'exact reconstruction of the full gradient norm')
    require(pol2.x <= 2*r2.x+a2.x,
            'the Rayleigh metric plus its retained neutral component controls the poloidal gradient')
    for val in (r2, a2, y2, z2, m2):
        require(val.y == 0 and val.x >= 0, 'real nonnegative physical stock square')
    return dict(zip(('r_squared', 'neutral_squared', 'y_squared', 'z_squared', 'mean_squared', 'gradient_squared'),
                    map(str, (r2, a2, y2, z2, m2, grad2))))


def check_flow(U, v, label):
    f.equal(f.trace(f.jac(v)), {}, 'solenoidal physical remainder')
    wh.same_vectors(parent(v), [{}, {}, {}], 'the parent and residual are disjoint')
    wh.same_vectors([f.diff(f.diff(a, 2), 2) for a in U], wh.scalev(-1, U),
                    'the parent has its complete first vertical harmonic')
    wh.same_vectors(nonlinear(U), [{}, {}, {}], 'no artificial self-forcing of the parent')
    modes = set().union(*(a.keys() for a in v))
    parity_lattice = all((k[0]+k[1]) % 2 == 0 for k in modes)
    u = wh.addv(U, v)
    nv, nu_full = nonlinear(v), nonlinear(u)
    lin = wh.scalev(-1, wh.project(wh.addv(og.adv(U, v), og.adv(v, U))))
    wh.same_vectors(nu_full, wh.addv(lin, nv), 'full quadratic splitting without missing outputs')
    wh.same_vectors(parent(lin), [{}, {}, {}], 'parent receives only actual residual self-interaction')
    source = wh.addv(nv, wh.scalev(-1, parent(nv)))
    w, q, cq, eta = vertical_variables(v)
    q_lin = f.scale(-1, f.lap(lin[2]))
    f.equal(q_lin, f.scale(-1, f.adv(U, cq)), 'complete Orr-Sommerfeld pressure cancellation')
    beta = f.add(f.mul(f.diff(U[0], 2), f.diff(w, 1)),
                 f.scale(-1, f.mul(f.diff(U[1], 2), f.diff(w, 0))))
    eta_lin = f.curl(lin)[2]
    f.equal(eta_lin, f.add(f.scale(-1, f.adv(U, eta)), beta),
            'complete Squire forcing retains both parent directions')
    eta_z_lin = f.diff(eta_lin, 2)
    eta_z_rhs = f.add(f.scale(-1, f.adv(U, f.diff(eta, 2))),
                     f.scale(-1, f.adv([f.diff(a, 2) for a in U], eta)), f.diff(beta, 2))
    f.equal(eta_z_lin, eta_z_rhs, 'the receiver derivative retains both source derivatives')
    require(scalar_pair(cq, q_lin) == f.ZERO, 'parent cancels in the full Rayleigh metric')
    for viscosity in (Q(1), Q(2)/7):
        tangent = wh.addv([f.scale(viscosity, f.lap(a)) for a in u], nu_full)
        residual_tangent = wh.addv(tangent, wh.scalev(-1, parent(tangent)))
        expected = wh.addv([f.scale(viscosity, f.lap(a)) for a in v], lin, source)
        wh.same_vectors(residual_tangent, expected, 'actual viscous residual equation')
        parent_expected = wh.addv([f.scale(viscosity, f.lap(a)) for a in U], parent(nv))
        wh.same_vectors(parent(tangent), parent_expected, 'actual coupled parent equation')
        q_actual = f.scale(-1, f.lap(residual_tangent[2]))
        f.equal(q_actual, f.add(f.scale(viscosity, f.lap(q)), q_lin,
                               f.scale(-1, f.lap(source[2]))), 'actual Rayleigh equation with all source modes')
    all_output = set().union(*(a.keys() for a in nv))
    if parity_lattice:
        require(all((k[0]+k[1]) % 2 == 0 for k in all_output), 'all nonlinear outputs retain the lattice')
    return {'label': label, 'stocks': norm_data(v), 'input_modes': len(modes),
            'nonlinear_output_modes': len(all_output),
            'generated_parent_norm_squared': str(am.pairing(parent(nv), parent(nv))),
            'generated_mean_modes': sorted(set().union(*(a.keys() for a in horizontal_mean(nv))))}


def check_weights():
    s = og.s
    b, M = s.symbols('b M', nonnegative=True)
    T = s.Matrix([[0, 0, 0], [1, 0, 0], [2, 1, 0]])
    require(T**3 == s.zeros(3), 'the physical comparison graph has depth two')
    evolution = s.eye(3)+b*T+b*b*T*T/2
    weights = s.ones(1, 3)*evolution
    require(weights == s.Matrix([[1+3*b+b*b/2, 1+b, 1]]), 'finite parent-response weights')
    require(weights.diff(b) == weights*T, 'backward weights cancel the complete parent comparison')
    a, c = s.symbols('a c', nonnegative=True)
    require((evolution.subs(b, a)*evolution.subs(b, c)-evolution.subs(b, a+c))
            .applyfunc(s.expand) == s.zeros(3), 'the same response composes without restarting its clock')
    kh2, nz2 = s.symbols('k n', nonnegative=True)
    total = kh2+nz2+2
    # kh2 here denotes the excess above the minimum horizontal square two.
    inequalities = [total*(total-1)-(kh2+2), total*(total-1)-2,
                    total*(total-1)-2*nz2,
                    (kh2+2)*(total-1)-total]
    for polynomial in inequalities:
        require(all(c >= 0 for c in s.Poly(s.expand(polynomial), kh2, nz2).coeffs()),
                'uniform reconstruction/source inequalities for all horizontal and vertical modes')
    full = s.Matrix([[0, 0, 0, 0], [1, 0, 0, 0], [1, 1, 0, 0], [2, 1, 1, 0]])
    require(full**4 == s.zeros(4), 'retaining neutral modes adds exactly one comparison stage')
    response = s.eye(4)+b*full+b*b*full**2/2+b**3*full**3/6
    full_weights = s.Matrix([[2, 1, 1, 1]])*response
    require(full_weights == s.Matrix([[2+4*b+3*b*b/2+b**3/6, 1+2*b+b*b/2, 1+b, 1]]),
            'positive weights include the neutral-state reconstruction cost')
    require(full_weights.diff(b) == full_weights*full,
            'the complete parent comparison cancels with the backward clock')
    require((response.subs(b, a)*response.subs(b, c)-response.subs(b, a+c))
            .applyfunc(s.expand) == s.zeros(4), 'full response composes without discarding neutral states')
    # All remaining modes have horizontal square >=1 and total square >=2.
    # For horizontal square one, non-neutrality gives vertical square >=1.
    for horizontal, vertical in ((1, nz2+1), (kh2+2, nz2)):
        total = horizontal+vertical
        bounds = [total*(total-1)-horizontal, total*(total-1)-2,
                  total*(total-1)-2*vertical, 2*horizontal*(total-1)-total]
        for polynomial in bounds:
            require(all(c >= 0 for c in s.Poly(s.expand(polynomial), kh2, nz2).coeffs()),
                    'uniform full-periodic source and reconstruction inequalities')
    return {'gap_weights': ['1+3b+b^2/2', '1+b', '1'],
            'full_matrix': [list(full.row(i)) for i in range(4)],
            'full_weights': ['2+4b+3b^2/2+b^3/6', '1+2b+b^2/2', '1+b', '1'],
            'full_nilpotence_index': 4}


def adverse_tests():
    vertical = [{}, {}, og.vd.sine((1, 0, 0))]
    w, q, cq, _ = vertical_variables(vertical)
    require(scalar_pair(q, cq) == f.ZERO and scalar_pair(w, w) == Q(1)/2,
            'neutral horizontal unit mode prevents coercivity without the gap')
    neutral_norms = norm_data(vertical)
    require(neutral_norms['neutral_squared'] == '1/2', 'the full reserve retains precisely the lost neutral mode')
    waves = [(1, 1, 0), (1, -1, 1), (2, 0, 1)]
    v = wh.addv(*(wh.project([og.cosine(k) if j < 2 else og.vd.sine(k), {}, {}])
                  for j, k in enumerate(waves)))
    _, q, cq, _ = vertical_variables(v)
    nv = nonlinear(v)
    input_work = scalar_pair(cq, f.scale(-1, f.lap(nv[2])))
    require(2*input_work == Q(8)/3, 'positive physical nonlinear Rayleigh production')
    require(scalar_pair(q, cq) == Q(29)/15, 'exact original Rayleigh stock of the adverse datum')
    dissipation = -scalar_pair(cq, f.lap(q))
    require(dissipation.x > 0, 'complete positive viscous metric cost')
    wh.same_vectors(parent(v), [{}, {}, {}], 'adverse datum initially has no selected parent')
    wh.same_vectors(parent(nv), [{}, {}, {}], 'the adverse initial feedback also has no selected parent')
    return {'unit_mode_stock': '0', 'unit_mode_vertical_norm_squared': '1/2',
            'neutral_repair': neutral_norms,
            'nonlinear_rayleigh_square_rate': '8/3', 'rayleigh_square': '29/15',
            'rayleigh_diffusion': str(dissipation),
            'adverse_energy': str(am.pairing(v, v)), 'adverse_stocks': norm_data(v),
            'scope': 'The triad is actual smooth initial data with the full NS tangent, not a closed three-mode evolution.'}


if __name__ == '__main__':
    cz, sz = og.cosine((0, 0, 1)), og.vd.sine((0, 0, 1))
    parents = [[cz, sz, {}],
               [f.add(f.scale(2, cz), f.scale(-3, sz)), f.add(f.scale(5, cz), sz), {}]]
    rows = []
    for sign in (0, 1, -1):
        base, G = og.datum(sign)
        w1 = wh.addv(G, wh.scalev(-Q(1)/2, og.scalar_vector(f.dot(base, G), base)))
        v = wh.project(w1)
        for j, U in enumerate(parents):
            rows.append(check_flow(U, v, f'phase {sign}, parent {j}'))
    mean = [og.vd.sine((0, 0, 2)), og.cosine((0, 0, 3)), {}]
    rows.append(check_flow(parents[1], wh.addv(v, mean), 'retained higher mean'))
    neutral = [{}, {}, og.vd.sine((1, 0, 0))]
    rows.append(check_flow(parents[1], neutral, 'retained neutral mode'))
    general = wh.addv(neutral, wh.project([og.cosine((1, 0, 1)), {}, {}]),
                      wh.project([{}, og.vd.sine((0, 1, 2)), {}]), mean)
    rows.append(check_flow(parents[1], general, 'general periodic frequencies and mean'))
    weights = check_weights()
    adverse = adverse_tests()
    dependencies = [Path(__file__), Path(og.__file__), Path(f.__file__), Path(wh.__file__), Path(am.__file__)]
    output = {'fixtures': rows, 'comparison': weights, 'adverse': adverse,
              'scope': 'For arbitrary smooth zero-mean periodic data, retaining neutral modes lets the reserve pay every first-vertical-harmonic parent history from original energy, up to its explicit residual nonlinear source cost. This is not a bound for that source or arbitrary-data regularity, and no whole-space extension is proved.',
              'status': 'Exact Fourier/rational and polynomial checks passed. Infinite-mode estimates and physical-history consequences are analytic, not Lean-certified.',
              'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies}}
    print(json.dumps(output, indent=2, default=str), flush=True)
