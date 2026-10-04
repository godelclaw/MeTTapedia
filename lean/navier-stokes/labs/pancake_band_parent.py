#!/usr/bin/env python3
"""Exact checks for spectral-band payment and non-mean geometric escape.

The anisotropic estimates and actual local histories are analytic in
README.md. These calculations retain complete pressure and source terms;
they do not evolve a closed finite Fourier system.
"""

import ast
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import generated_mean_enstrophy as m
import pancake_concentration_threshold as pc
from pancake_mean_parent import in_core
from reciprocal_pattern_cycles import inner, mode, require, vector_add, vector_scale


def zero(expression, label):
    require(s.simplify(expression) == 0, label)


def band(u, width=1, axes=(2,)):
    return [{k: a for k, a in row.items() if any(abs(k[j]) <= width for j in axes)}
            for row in u]


def outside(u, width=1, axes=(2,)):
    return m.subtract(u, band(u, width, axes))


def seed():
    u = [{}, {}, {}]
    for k, v, a in [((4, 0, 64), (0, 1, 0), Q(1)),
                    ((0, 4, 63), (1, 1, -Q(4, 63)), Q(1)),
                    ((1, 1, 64), (1, -1, 0), Q(1, 10))]:
        for j, value in enumerate(v):
            if value:
                u[j] = f.add(u[j], mode(k, a*value))
    return u


def trilinear(a, b, c):
    return inner(f.curl(a), f.matvec(f.jac(b), f.curl(c)))


def split_check(u, width, axes):
    V, w = band(u, width, axes), outside(u, width, axes)
    Nu, record = pc.full_source(u)
    vv, ww = m.nonlinear(V), m.nonlinear(w)
    cross = vector_add(m.bilinear(V, w), m.bilinear(w, V))
    combined = vector_add(vector_add(vv, cross), ww)
    m.equal_vectors(Nu, combined, 'full pressure-corrected source split')
    projected_V = band(combined, width, axes)
    projected_w = outside(combined, width, axes)
    m.equal_vectors(projected_V, band(Nu, width, axes), 'all forcing of the low band remains')
    m.equal_vectors(projected_w, outside(Nu, width, axes), 'all forcing of its complement remains')
    kinetic_V, kinetic_w = inner(V, projected_V), inner(w, projected_w)
    require(kinetic_V+kinetic_w == 0, 'the complete internal kinetic exchange cancels')
    require(m.derivative_pair(V, projected_V)+m.derivative_pair(w, projected_w) == m.cubic(u),
            'the complete enstrophy receivers reconstruct physical stretching')
    require(m.gradient_norm_squared(V)+m.gradient_norm_squared(w) == m.gradient_norm_squared(u),
            'orthogonal band gradients have one full dissipation stock')
    if len(axes) > 1:
        remaining, parts = u, []
        for axis in axes:
            parts.append(band(remaining, width, (axis,)))
            remaining = outside(remaining, width, (axis,))
        total = [{}, {}, {}]
        for part in parts:
            total = vector_add(total, part)
        m.equal_vectors(total, V, 'disjoint slab partition reconstructs the union')
        require(sum(m.gradient_norm_squared(part) for part in parts) == m.gradient_norm_squared(V),
                'slab overlaps are not charged as independent full energies')
    telescoped = trilinear(V, u, u)+trilinear(w, V, u)+trilinear(w, w, V)
    require(telescoped == m.cubic(u)-m.cubic(w), 'three-term cubic telescope includes all seven mixed terms')
    two_parent_work = m.linear_cubic_term(V, w)
    return dict(width=width, axes=list(axes), full_energy=record['energy'],
                two_parent_one_tail_stretching=str(two_parent_work),
                band_to_tail_source_squared=str(inner(outside(vv, width, axes), outside(vv, width, axes))),
                kinetic_work_into_band=str(kinetic_V), full_source_modes=record['full_source_modes'])


def physical_checks():
    u = seed()
    Nu, record = pc.full_source(u)
    require(s.Matrix([[4, 0, 64], [0, 4, 63], [1, 1, 64]]).det() == 516,
            'the initial fluid uses three independent spatial directions')
    require(not any(band(u)), 'the initial low band is empty')
    require(all(in_core(k) for k in pc.support(u)+pc.support(outside(Nu))),
            'initial high field and complete first high-band source lie in the same core')
    q = (4, -4, 1)
    expected = [f.II*Q(2111, 2079), f.II*Q(2080, 2079), -f.II*Q(124, 2079)]
    require([a.get(q, f.ZERO) for a in Nu] == expected, 'nonzero vertical daughter survives complete projection')
    require(not in_core(q) and any(m.oscillation(band(Nu))), 'the exterior source is not just the exact mean')
    require(m.cubic(u) == 0 and m.linear_cubic_term(u, m.minus_laplacian(u)) == 0,
            'first stretching derivative is independent of viscosity')
    c = m.linear_cubic_term(u, Nu)
    require(c == Q(676557198722378987557, 20783325925489050) > 0,
            'the complete first stretching return is positive')
    jets = []
    for nu in (Q(0), Q(1, 7), Q(1)):
        rhs = vector_add(Nu, vector_scale(-nu, m.minus_laplacian(u)))
        Ndot = vector_add(m.bilinear(rhs, u), m.bilinear(u, rhs))
        acc = vector_add(Ndot, vector_scale(-nu, m.minus_laplacian(rhs)))
        require(m.linear_cubic_term(u, rhs) == c, 'complete viscous tangent keeps the first return')
        require(2*inner(rhs, rhs)+2*inner(u, acc) == -4*nu*m.derivative_pair(u, rhs),
                'complete second kinetic law retains all outputs')
        jets.append(dict(viscosity=str(nu), second_tangent_modes=len(pc.support(acc))))
    k, qv = s.Matrix([4, 0, 64]), s.Matrix(q)
    require(k.dot(k) < 65**2 and k.dot(k) < 9**4 and qv.dot(qv) < s.Rational(5, 2)**4,
            'norm bounds used in the moving-axis exclusion')
    require(qv.dot(qv) < 6**2 and k.cross(qv).dot(k.cross(qv)) > 350**2
            and 65*s.Rational(5, 2)+6*9 < 350,
            'no single core axis can contain both the original wave and its non-mean daughter')
    # A finite band is not an algebra: its own pair can generate a tail.
    parent = [mode((0, 1, 1), 1), mode((1, 0, 1), 1), {}]
    tail = outside(m.nonlinear(parent))
    require(inner(tail, tail) > 0, 'band self-interaction generates its complement')
    coupled = vector_add(parent, tail)
    rows = [split_check(coupled, 1, (2,)), split_check(vector_add(u, band(Nu)), 1, (2,)),
            split_check(vector_add(u, Nu), 1, (2,)), split_check(vector_add(u, Nu), 1, (0, 1, 2))]
    require(Q(rows[0]['two_parent_one_tail_stretching']) != 0,
            'the mean-only two-parent cancellation is invalid for a finite band')
    return dict(initial=record, daughter_coefficient=[str(x) for x in expected],
                first_stretching_derivative=str(c), jets=jets, band_fixtures=rows,
                actual_scope='Uniform smooth local Taylor control at physical time A^(-5/3) gives a non-mean exterior of size at least c A^(1/3), while the exterior after removing |kz|<=1 is at most C A^(-1/3). This interval statement is analytic.')


def estimate_checks():
    x, y, a, nu, Z, C = s.symbols('x y a nu Z C', positive=True)
    zero(3*(x*x+y*y)-2*(x*x+x*y+y*y)-(x-y)**2,
         'pointwise telescoping majorant keeps every cross term')
    zero(nu*y*y/2+C*C*a*a*x*x/(2*nu)-C*a*x*y
         -(nu*y-C*a*x)**2/(2*nu), 'first absorption spends half the viscosity')
    zero(C*C*a*a/(2*nu)+nu/2-C*a-(C*a-nu)**2/(2*nu),
         'periodic lower-order coefficient has an original-energy payment')
    z1, z2, z3 = s.symbols('z1 z2 z3', real=True)
    zero(3*(z1*z1+z2*z2+z3*z3)-(z1+z2+z3)**2
         -((z1-z2)**2+(z1-z3)**2+(z2-z3)**2), 'three disjoint slabs cost a factor of three')
    E, h, L, M, D, loss, b, g0 = s.symbols('E h L M D loss b g0', real=True)
    checks = []
    for delta in (0, 1):
        beta = (1+delta)*C*C/(2*nu)
        alpha = 2*L+delta*nu/2
        Gamma = beta/(2*nu)
        phi = s.exp(alpha*h+Gamma*E)
        Zd = (alpha+beta*M)*Z-nu*D/2-loss
        value = (2*phi-1)*Z+2*h*b
        cost = Zd+nu*D-2*g0
        defect = -s.diff(value, h)-2*nu*Z*s.diff(value, E)+Zd*s.diff(value, Z)+cost
        zero(defect+nu*(phi-1)*D+2*beta*phi*(Z-M)*Z+2*phi*loss+2*(b+g0),
             'the full-state Bellman reserve pays the band without resetting')
        checks.append(dict(domain='R3' if delta == 0 else 'T3',
                           beta=str(beta), horizon_coefficient=str(alpha), energy_coefficient=str(Gamma)))
    alpha, Gamma, Gammadot = s.symbols('alpha Gamma Gammadot', real=True)
    value = (2*s.exp(alpha*h+Gamma*E)-1)*Z+2*h*b
    zero(s.diff(value, Gamma)*Gammadot-2*s.exp(alpha*h+Gamma*E)*E*Z*Gammadot,
         'increasing the selected band price has an explicit unpaid reserve defect')
    A = s.symbols('A', positive=True)
    tau = A**(-s.Rational(2, 3))
    zero(A*tau-A**s.Rational(1, 3), 'unpaid mean-complement daughter grows')
    zero(A*tau*tau-A**(-s.Rational(1, 3)), 'band-complement remainder shrinks')
    return dict(constants=checks, physical_time='A^(-5/3)',
                limitation='Fixed finite band widths; no passage to infinite width or free adaptive cutoff.')


def adaptive_checks():
    E, E0, beta0, nu = s.symbols('E E0 beta0 nu', positive=True)
    p = s.symbols('p', real=True)
    Psi = beta0*E0**p*E**(1-p)/(2*nu*(1-p))
    ceiling = beta0*(E0/E)**p
    zero(2*nu*s.diff(Psi, E)-ceiling, 'the integrated energy price pays the moving band ceiling')
    zero(Psi.subs(E, E0)-beta0*E0/(2*nu*(1-p)), 'initial price uses original energy only')
    Z, M, D, alpha, h, loss, slack, b, g0 = s.symbols(
        'Z M D alpha h loss slack b g0', real=True)
    actual_beta = ceiling-slack
    phi = s.exp(alpha*h+Psi)
    Zd = (alpha+actual_beta*M)*Z-nu*D/2-loss
    value = (2*phi-1)*Z+2*h*b
    cost = Zd+nu*D-2*g0
    derivative = -s.diff(value, h)-2*nu*Z*s.diff(value, E)+Zd*s.diff(value, Z)
    zero(derivative+cost+nu*(phi-1)*D+2*phi*(ceiling*(Z-M)+slack*M)*Z
         +2*phi*loss+2*(b+g0), 'adaptive reserve keeps the complete coefficient slack')
    # Endpoint p=1 needs a logarithm, which has no finite nonnegative
    # primitive on the entire interval (0,E0]; no NS realization is inferred.
    charge = beta0*E0*s.log(E0/E)/(2*nu)
    zero(s.diff(charge, E)+beta0*E0/(2*nu*E), 'critical reciprocal-energy price diverges logarithmically')
    return dict(allowed_price='beta(J(t)) <= beta0 (E0/E(t))^p, 0<=p<1',
                energy_potential=str(Psi), initial_potential='beta0 E0/(2nu(1-p))',
                scope='The energy-dependent width can grow; actual geometric control of its complement remains a hypothesis. At p>=1 only this everywhere nonnegative energy-only primitive is excluded.')


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
                    other = root / (name.split('.')[0]+'.py')
                    if other.is_file():
                        pending.append(other)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)}


if __name__ == '__main__':
    print(json.dumps(dict(physical=physical_checks(), estimates=estimate_checks(),
                          adaptive=adaptive_checks(),
                          source_sha256=source_hashes(),
                          scope='Exact finite algebra, not certification of the analytic anisotropic estimates or arbitrary-data regularity.'), indent=2))
