#!/usr/bin/env python3
"""Exact fixtures for anisotropic viscous absorption and its concentration limit.

The all-prefix estimate, whole-space localization and local NS persistence
are analytic in README.md. These checks retain canonical pressure and every
nonlinear output. No Fourier truncation is treated as an autonomous flow.
"""

import ast
import hashlib
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
from reciprocal_pattern_cycles import inner, mean, mode, require


def zero(expression, label):
    require(s.simplify(expression) == 0, label)


def seed(mu, normal, phase=-1):
    u = [{}, {}, {}]
    data = [((mu, 0, normal), (0, 1, 0), False),
            ((0, mu, normal), (1, 0, 0), False),
            ((-mu, -mu, -2*normal), (1, 1, -Q(mu, normal)), True)]
    for k, v, sine in data:
        for j, value in enumerate(v):
            if value:
                u[j] = f.add(u[j], mode(k, value*(phase if sine else 1), sine))
    return u


def support(u):
    return sorted(set().union(*(set(a) for a in u)))


def strain(u):
    B = f.jac(u)
    return [[f.scale(f.QQ_I(1)/2, f.add(B[i][j], B[j][i]))
             for j in range(3)] for i in range(3)]


def triple(A, B, C):
    return mean(f.trace(f.matmul(A, f.matmul(B, C))))


def stretching(u):
    omega = f.curl(u)
    return inner(omega, f.matvec(f.jac(u), omega))


def full_source(u, nu=Q(2, 7)):
    B = f.jac(u)
    f.equal(f.trace(B), {}, 'solenoidal datum')
    for component in u:
        for k, value in component.items():
            require(component.get(tuple(-a for a in k), f.ZERO) ==
                    f.QQ_I(value.x, -value.y), 'real Fourier field')
    pressure = f.green(f.trace(f.matmul(B, B)))
    f.equal(pressure, f.tensor_pressure(f.tensor(u, u)), 'canonical pressure')
    N = [f.add(f.scale(-1, f.adv(u, a)), f.scale(-1, f.diff(pressure, j)))
         for j, a in enumerate(u)]
    lap = [f.lap(a) for a in u]
    rhs = [f.add(a, f.scale(f.QQ_I(nu), b)) for a, b in zip(N, lap)]
    f.equal(f.trace(f.jac(rhs)), {}, 'complete unforced tangent is solenoidal')
    omega = f.curl(u)
    E, Z, D, g = inner(u, u), inner(omega, omega), inner(lap, lap), stretching(u)
    require(inner(u, N) == 0, 'full nonlinear energy cancellation')
    require(inner(lap, N) == -g, 'full pressure source and stretching agree')
    require(inner(u, rhs) == -nu*Z, 'actual viscous energy identity')
    require(inner(omega, f.curl(rhs)) == g-nu*D, 'actual enstrophy equation')
    S = strain(u)
    require(g == -Q(4, 3)*triple(S, S, S), 'integrated Betchov identity')
    return N, dict(energy=str(E), enstrophy=str(Z), dissipation=str(D),
                   stretching=str(g), normal_vorticity_squared=str(inner([omega[2]], [omega[2]])),
                   input_modes=len(support(u)), full_source_modes=len(support(N)),
                   newly_generated_modes=[list(k) for k in support(N) if k not in support(u)])


def family_fixtures():
    rows = []
    for mu, normal in [(1, 1), (1, 2), (1, 3), (2, 5), (3, 8), (4, 16)]:
        r = Q(mu, normal)
        for phase in (-1, 1):
            u = seed(mu, normal, phase)
            _, row = full_source(u)
            expected = dict(energy=2+r*r/2,
                            enstrophy=normal**2*(5+5*r*r+r**4),
                            dissipation=normal**4*(17+26*r*r+13*r**4+2*r**6),
                            stretching=-phase*normal**3*(3*r+r**3)/2,
                            normal_vorticity_squared=Q(mu*mu))
            for name, value in expected.items():
                require(Q(row[name]) == value, ('anisotropic family identity', name, mu, normal, phase))
            rows.append(dict(mu=mu, normal=normal, phase=phase, **row))
    return rows


def symbolic_family():
    r = s.symbols('r', positive=True)
    base = seed(1, 1)
    def scalar(z):
        return s.Rational(str(z.x))+s.I*s.Rational(str(z.y))
    U = {k: s.diag(1, 1, r)*s.Matrix([scalar(a.get(k, f.ZERO)) for a in base])
         for k in support(base)}
    wave = {k: s.Matrix([r*k[0], r*k[1], k[2]]) for k in U}
    omega = {k: s.I*wave[k].cross(U[k]) for k in U}
    E = Z = D = G = normal = s.Integer(0)
    for k in U:
        neg = tuple(-j for j in k)
        E += U[k].dot(U[neg])
        Z += omega[k].dot(omega[neg])
        D += wave[k].dot(wave[k])**2*U[k].dot(U[neg])
        normal += omega[k][2]*omega[neg][2]
        for p in U:
            q = tuple(-i-j for i, j in zip(k, p))
            if q in U:
                G += s.I*wave[k].dot(omega[p])*U[k].dot(omega[q])
    for actual, expected, label in [
            (E, 2+r*r/2, 'energy'), (Z, 5+5*r*r+r**4, 'enstrophy'),
            (D, 17+26*r*r+13*r**4+2*r**6, 'dissipation'),
            (G, (3*r+r**3)/2, 'stretching'), (normal, r*r, 'normal vorticity')]:
        zero(actual-expected, ('universal symbolic Fourier coefficient', label))
    return dict(parameter='r>0', stretching=str(s.factor(G)),
                scope='Orthogonality calculates the whole polynomial, independently of the rational family fixtures.')


def angular_fixture():
    u = seed(2, 5)
    omega = f.curl(u)
    B = Q(3)
    norm2 = lambda v: sum((Q(str(z.x))**2+Q(str(z.y))**2 for z in v), Q(0))
    count = 0
    for a in support(u):
        require(a[0]**2+a[1]**2 <= B*B, 'gamma=0 cylinder support')
        for b in support(u):
            c = tuple(-i-j for i, j in zip(a, b))
            if c not in support(u):
                continue
            ua, ub, uc = [[field[j].get(k, f.ZERO) for j in range(3)]
                          for field, k in [(u, a), (u, b), (u, c)]]
            ob, oc = [[omega[j].get(k, f.ZERO) for j in range(3)] for k in (b, c)]
            term = sum((a[j]*ob[j] for j in range(3)), f.ZERO)*sum(
                (ua[j]*oc[j] for j in range(3)), f.ZERO)
            sizes = sorted(sum(x*x for x in k) for k in (a, b, c))
            bound = 4*B*B*sizes[1]*sizes[2]*norm2(ua)*norm2(ub)*norm2(uc)
            require(norm2([term]) <= bound, 'full ordered angular triad bound')
            count += 1
    require(count == 12, 'both signs and all six receiving orders are checked')
    return dict(ordered_triads=count, gamma=0, width=str(B))


def mixed_cubic_fixture():
    w = seed(2, 5)
    v = [{}, {}, {}]
    # With gamma=0, B=3, R=1, w is inside and this mode is outside.
    for j, value in enumerate((1, -2, 0)):
        if value:
            v[j] = mode((4, 2, 15), Q(value, 7))
    u = [f.add(a, b) for a, b in zip(w, v)]
    full_source(u)
    S, W, V = strain(u), strain(w), strain(v)
    telescoped = triple(V, S, S)+triple(W, V, S)+triple(W, W, V)
    require(stretching(u)-stretching(w) == -Q(4, 3)*telescoped,
            'all mixed stretching is retained in the three telescoping terms')
    seven = sum((triple(*[V if bit else W for bit in bits])
                 for bits in itertools.product((0, 1), repeat=3) if any(bits)), Q(0))
    require(seven == telescoped, 'all seven exterior-containing terms remain')
    require(seven != 0, 'the mixed-cubic test is nonzero')
    return dict(full_stretching=str(stretching(u)), core_stretching=str(stretching(w)),
                mixed_strain_cube=str(seven), exterior_terms=7)


def leakage_fixture():
    # For gamma=1/2, B=R=1 all inputs are in the spectral core.
    mu, normal = 4, 16
    u = [{}, {}, {}]
    for k, v in [((mu, 0, normal), (0, 1, 0)),
                 ((0, mu, normal), (1, 1, -Q(mu, normal)))]:
        for j, value in enumerate(v):
            if value:
                u[j] = f.add(u[j], mode(k, value))
    for k in support(u):
        require((k[0]**2+k[1]**2)**2 <= sum(a*a for a in k),
                'each input satisfies |k_perp|<=|k|^(1/2)')
    N, row = full_source(u)
    q = (mu, -mu, 0)
    require(sum(a*a for a in q) > 1 and (q[0]**2+q[1]**2)**2 > sum(a*a for a in q),
            'the generated horizontal mode lies above R and outside the initial core')
    expected = [f.II*mu/4, f.II*mu/4, -f.II*mu*mu/(4*normal)]
    for j in range(3):
        require(N[j].get(q, f.ZERO) == expected[j], 'exact nonzero exterior generation')
    return dict(**row, exterior_frequency=list(q),
                exterior_source=[str(a) for a in expected],
                scope='Instantaneous generation outside the fixed initial cone; small L3 leakage is a separate allowed condition.')


def scaling_checks():
    r, a, mu, lam, nu = s.symbols('r a mu lambda nu', positive=True)
    E = 2+r**2/2
    Z = 5+5*r**2+r**4
    D = 17+26*r**2+13*r**4+2*r**6
    G = (3*r+r**3)/2
    # Whole-space change of variables, with generic localized coefficients.
    e, d, g = s.symbols('e d g', positive=True)
    jac = 1/(mu**2*lam)
    amplitude = mu*s.sqrt(lam/e)
    zero((a*a*jac*e).subs(a, amplitude)-1, 'unit-energy normalization on R3')
    ratio = ((a**3*lam**3*jac*g)/(nu*a*a*lam**4*jac*d)).subs(a, amplitude)
    zero(ratio-mu*g/(nu*s.sqrt(lam)*d*s.sqrt(e)), 'actual stretching to dissipation ratio')
    require(s.limit(G/r, r, 0) == Q(3, 2), 'strictly positive leading transverse stretching')
    require(s.limit(D, r, 0) == 17 and s.limit(E, r, 0) == 2,
            'finite positive limiting quadratic coefficients')
    require(s.limit(r*r/Z, r, 0) == 0, 'vorticity becomes planar, not necessarily aligned in one direction')
    scale = s.symbols('scale', positive=True)
    squared_model = mu**2*G**2/(nu**2*lam*D**2*E)
    supercritical = squared_model.subs({mu: scale**7, lam: scale**8, r: 1/scale})
    require(s.limit(supercritical/scale**4, scale, s.oo) == s.Rational(9, 2312)/nu**2,
            'gamma=7/8 has ratio growing as scale^2, with lambda=scale^8')
    subcritical = squared_model.subs({mu: scale, lam: scale**2, r: 1/scale})
    require(s.limit(subcritical*scale**2, scale, s.oo) == s.Rational(9, 2312)/nu**2,
            'gamma=1/2 has ratio decaying as scale^-1, with lambda=scale^2')
    return dict(periodic_polynomials=dict(E=str(E), Z=str(Z), D=str(D), G=str(G)),
                physical_energy='a^2 E(r)/(mu^2 lambda)',
                physical_ratio='mu G(r)/(nu sqrt(lambda) D(r) sqrt(E(r)))',
                asymptotic_ratio='c/nu * lambda^(2 gamma - 3/2)',
                scope='The displayed numerical coefficients are periodic. A fixed Schwartz localization has different positive leading coefficients, established analytically.')


def threshold_algebra():
    gamma = s.symbols('gamma', real=True)
    p = s.symbols('p', positive=True)
    sigma = s.Rational(3, 2)-2*gamma
    zero(4-sigma-(s.Rational(5, 2)+2*gamma), 'angular gain plus cylindrical occupancy')
    zero((p**(4-sigma)/p**4)-p**(-sigma), 'high-frequency viscous gain')
    B, E0 = s.symbols('B E0', positive=True)
    zero(6*B*s.sqrt(2*s.pi*B**2)/(2*s.pi)**s.Rational(3, 2)-3*B**2/s.pi,
         'unitary whole-space Fourier constant')
    zero(6*B*s.sqrt(16*(B+1)**2)*s.sqrt(E0)-24*B*(B+1)*s.sqrt(E0),
         'orientation-independent lattice-cylinder constant')
    CS = s.symbols('C_S', positive=True)
    zero(s.Rational(4, 3)*3*2*s.sqrt(3)*CS-8*s.sqrt(3)*CS,
         'all three Betchov difference terms have one critical leakage payment')
    length = s.symbols('length', positive=True)
    zero((1/length)**2*length-1/length, 'torus rescaling keeps time and convection compatible')
    zero((1/length**2)*(1/length)*length**2-1/length,
         'rescaled viscosity keeps the physical equation')
    zero(2*(1+p*p)-(1+p)**2-(p-1)**2,
         'the exact Lean order-one weight has the required factor two')
    return dict(sigma=str(sigma), core_exponent='5/2+2 gamma',
                whole_space_constant='3 B^2 sqrt(E0)/pi',
                torus_constant='24 B(B+1) sqrt(E0)',
                leakage_constant='8 sqrt(3) C_S',
                unit_torus_consumer_bound='2(E0+Z0 exp(2 L H))/(2 pi)^2',
                hypotheses='0<=gamma<3/4; B>0; R>=1; complete exterior L3<=nu/(32 sqrt(3) C_S) at each time.')


def source_hashes():
    root = Path(__file__).resolve().parent
    pending, seen = [Path(__file__).resolve()], set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for node in ast.walk(ast.parse(path.read_text())):
            names = ([a.name for a in node.names] if isinstance(node, ast.Import)
                     else [node.module] if isinstance(node, ast.ImportFrom) and node.level == 0 else [])
            for name in names:
                if name:
                    dependency = root / (name.split('.')[0]+'.py')
                    if dependency.is_file():
                        pending.append(dependency)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)}


def checks():
    return dict(family=family_fixtures(), symbolic=symbolic_family(), angular=angular_fixture(),
                mixed=mixed_cubic_fixture(),
                generated_leakage=leakage_fixture(), scaling=scaling_checks(),
                threshold=threshold_algebra(), source_sha256=source_hashes(),
                scope='Exact algebraic fixtures. General convolution bounds, Schwartz localization and actual local evolution are analytic, not Lean-certified. Arbitrary-history propagation remains open.')


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
