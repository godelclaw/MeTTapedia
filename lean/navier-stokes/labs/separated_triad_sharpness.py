#!/usr/bin/env python3
"""Complete polarized-packet checks for separated stretching absorption.

Finite Fourier identities use exact arithmetic and all receiving roles.
The Schwartz construction, concentration, and local NS interval in README.md
are analytic arguments, not certified by these fixtures or by Lean.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

import optimal_cubic_gauge as og
import helical_parent_response as hr
import rotational_curl_reserve as rc

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require = og.require


def real(value):
    require(value.y == 0, 'physical pairing is real')
    return s.Rational(value.x)


def modes(v):
    return {k: tuple(a.get(k, f.ZERO) for a in v)
            for k in set().union(*(a.keys() for a in v))}


def selected(p, q, k, carrier):
    low, middle, _ = sorted(sum(j*j for j in r) for r in (p, q, k))
    return 0 < low <= 4 and middle >= (carrier-1)**2 and 4*low <= middle


def masked_source(v, carrier):
    out = [{}, {}, {}]
    for p, a in modes(v).items():
        for q, b in modes(v).items():
            k = tuple(x+y for x, y in zip(p, q))
            if not selected(p, q, k, carrier):
                continue
            kk = sum(x*x for x in k)
            require(kk > 0, 'selected output is nonzero')
            aq, kb = sum(a[j]*q[j] for j in range(3)), sum(k[j]*b[j] for j in range(3))
            for j in range(3):
                value = -f.II*aq*(b[j]-k[j]*kb/kk)
                out[j][k] = out[j].get(k, f.ZERO)+value
    return [f.clean(a) for a in out]


def masked_stretching(v, carrier):
    velocity, omega = modes(v), modes(f.curl(v))
    total = f.ZERO
    for p, a in omega.items():
        for q, b in velocity.items():
            k = tuple(-x-y for x, y in zip(p, q))
            c = omega.get(k)
            if c is not None and selected(p, q, k, carrier):
                total += f.II*sum(a[j]*q[j] for j in range(3))*sum(c[j]*b[j] for j in range(3))
    return real(total)


def stretching(v):
    return real(am.pairing([f.scale(-1, f.lap(a)) for a in v], hr.nonlinear(v)))


def packet_check(carrier):
    chi = f.add({f.ORIGIN: Q(1)},
                *(f.scale(Q(1)/4, og.cosine(tuple(int(i == j) for i in range(3))))
                  for j in range(3)))
    force = [f.diff(f.mul(chi, chi), 0), {}, {}]
    U = wh.scalev(-1, wh.project(force))
    W = wh.project([{}, {}, f.mul(chi, og.cosine((0, carrier, 0)))])
    v = wh.addv(U, W)
    for field in (U, W, v):
        f.equal(f.trace(f.jac(field)), {}, 'the entire datum is incompressible')
    I = real(am.pairing([f.mul(chi, chi)], [f.diff(U[0], 0)]))
    require(I == real(am.pairing(U, U)) == s.Rational(1, 256),
            'the low strain is positively aligned with the complete envelope square')
    require(am.pairing(U, W) == f.ZERO, 'low and high packets are energy orthogonal')
    require(stretching(W) == stretching(U) == 0, 'pure-packet cubic work vanishes in this fixture')
    complete = stretching(v)
    selected_rhs = masked_source(v, carrier)
    masked = real(am.pairing([f.scale(-1, f.lap(a)) for a in v], selected_rhs))
    require(complete == masked == masked_stretching(v, carrier),
            'all receiving roles equal the independent selected vorticity work')
    require(am.pairing(v, selected_rhs) == f.ZERO,
            'the selected interaction redistributes energy without creating any')
    parent_energy = real(am.pairing(U, selected_rhs))
    receiver_energy = real(am.pairing(W, selected_rhs))
    require(parent_energy+receiver_energy == 0, 'the parent pays the opposite energy transfer')
    require(complete > 0 and abs(complete/carrier**2-I/2) <= I/carrier,
            'exact fixtures have the positive complete leading coefficient and a small error')
    diffusion = real(am.pairing([f.lap(a) for a in v], [f.lap(a) for a in v]))
    energy = real(am.pairing(v, v))
    n2 = s.Integer(carrier)**2
    require(complete == n2**2/(512*(n2+1))
            and energy == (141*n2+137)/(256*(n2+1))
            and diffusion == (35*n2**2+9*n2+3)/64
            and parent_energy == -n2/(1024*(n2+1)),
            'independent Fourier fixture agrees with every symbolic family formula')
    projected_error = wh.addv(W, wh.scalev(-1, [{}, {}, f.mul(chi, og.cosine((0, carrier, 0)))]))
    require(real(am.pairing(projected_error, projected_error)) > 0,
            'the Leray correction is nonzero and has been retained')
    return {'carrier': carrier, 'alignment_integral': str(I),
            'complete_stretching': str(complete), 'stretching_over_carrier_squared': str(complete/carrier**2),
            'predicted_limit': str(I/2), 'parent_energy_work': str(parent_energy),
            'receiver_energy_work': str(receiver_energy), 'energy': str(energy),
            'diffusion': str(diffusion),
            'full_source_modes': len(modes(hr.nonlinear(v))),
            'pressure_modes': len(f.tensor_pressure(f.tensor(v, v)))}


def symbolic_packet():
    """Exact formula for every integer carrier N>6, via nonresonance."""
    N = s.symbols('N', positive=True)
    cx, sx, cy, sy, cz, sz, ct, st = angles = s.symbols('cx sx cy sy cz sz ct st')
    pairs = ((cx, sx), (cy, sy), (cz, sz), (ct, st))

    def angular_derivative(expr, j):
        c, z = pairs[j]
        return -z*s.diff(expr, c)+c*s.diff(expr, z)

    def derivative(expr, j):
        return angular_derivative(expr, j)+(N*angular_derivative(expr, 3) if j == 1 else 0)

    def average(expr):
        total = 0
        for powers, coefficient in s.Poly(s.expand(expr), *angles).terms():
            if any(j % 2 for j in powers):
                continue
            weight = s.Integer(1)
            for j in range(0, 8, 2):
                a, b = powers[j]//2, powers[j+1]//2
                weight *= s.factorial(2*a)*s.factorial(2*b)/(4**(a+b)*s.factorial(a)*s.factorial(b)*s.factorial(a+b))
            total += coefficient*weight
        return s.factor(total)

    eps = s.Rational(1, 4)
    U = [eps**2*sx*(cy+cz), -eps**2*cx*sy, -eps**2*cx*sz]
    W = [s.Integer(0), eps*N*sz*st/(N*N+1),
         (1+eps*(cx+cy)+eps*N*N*cz/(N*N+1))*ct]
    v = [a+b for a, b in zip(U, W)]
    grad = [[derivative(a, j) for j in range(3)] for a in v]
    require(s.simplify(sum(grad[i][i] for i in range(3))) == 0, 'symbolic Leray reconstruction is incompressible')
    work = average(-sum(grad[i][k]*grad[j][k]*grad[i][j]
                        for i in range(3) for j in range(3) for k in range(3)))
    energy = average(sum(a*a for a in v))
    diffusion = average(sum(sum(derivative(derivative(a, j), j) for j in range(3))**2 for a in v))
    parent = average(-sum(U[i]*v[j]*grad[i][j] for i in range(3) for j in range(3)))
    predicted = (N**4/(512*(N*N+1)), (141*N*N+137)/(256*(N*N+1)),
                 (35*N**4+9*N*N+3)/64, -N*N/(1024*(N*N+1)))
    for value, expected in zip((work, energy, diffusion, parent), predicted):
        require(s.factor(value-expected) == 0, 'symbolic complete-packet formula')
    require(s.limit(work/N**2, N, s.oo) == s.Rational(1, 512),
            'positive leading coefficient holds for the entire packet family')
    return dict(zip(('stretching', 'energy', 'diffusion', 'parent_energy_work'),
                    map(str, (work, energy, diffusion, parent))))


def tensor_and_scaling_checks():
    g = s.symbols('g0:8')
    G = s.Matrix([[g[0], g[1], g[2]], [g[3], g[4], g[5]], [g[6], g[7], -g[0]-g[4]]])
    t = s.symbols('t')
    n, a = s.Matrix([0, 1, 0]), s.Matrix([0, 0, 1])
    A = G+t*a*n.T
    cubic = -sum(A[i, k]*A[j, k]*A[i, j] for i in range(3) for j in range(3) for k in range(3))
    require(s.expand(cubic).coeff(t, 2) == g[0],
            'the complete rank-one cross work is the strain in the vorticity direction')
    alpha = s.symbols('alpha', positive=True)
    beta = (1/alpha+s.Rational(5, 4))/2
    require(s.simplify(alpha*beta-1-(5*alpha-4)/8) == 0,
            'for 4/5 < alpha <= 1 all cross triads eventually satisfy the enlarged selector')
    require(s.simplify(s.Rational(5, 2)-2*beta-(5*alpha-4)/(4*alpha)) == 0,
            'on the same range the positive work/diffusion ratio diverges')
    require(s.Rational(9, 8) > 1 and s.Rational(5, 2)-2*s.Rational(9, 8) > 0,
            'beta=9/8 covers alpha > 1 with positive concentration growth')
    return {'complete_rank_one_coefficient': 'G_11',
            'unit_energy_dilation': 'u(x)=lambda^(3/2)*w_N(lambda*x)',
            'cross_work_scale': 'lambda^(9/2)*N^2', 'diffusion_scale': 'lambda^4*N^4',
            'carrier_choice': 'N=lambda^(beta-1), max(1,1/alpha)<beta<5/4',
            'work_diffusion_ratio_scale': 'lambda^(5/2-2*beta)',
            'scope': 'Scaling algebra only; the Schwartz packet and physical interval are analytic.'}


if __name__ == '__main__':
    result = {'fixtures': [packet_check(N) for N in (8, 16, 32, 64)],
              'symbolic_packet_N_greater_than_6': symbolic_packet(),
              'tensor_and_scaling': tensor_and_scaling_checks(),
              'status': 'Exact Fourier, pressure, all-receiver and scaling checks passed.',
              'scope': 'No new Lean proof. No arbitrary-history budget or singularity construction.'}
    files = [Path(__file__), Path(og.__file__), Path(hr.__file__), Path(f.__file__),
             Path(wh.__file__), Path(am.__file__), Path(og.vd.__file__), Path(rc.__file__)]
    result['source_sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    print(json.dumps(result, indent=2), flush=True)
