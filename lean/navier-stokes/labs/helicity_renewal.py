#!/usr/bin/env python3
"""Coherent helicity creation in the full unforced NS equation.

Helical triad geometry is classical. These exact checks retain shared
phases, canonical pressure and every output in actual NS initial jets.
Uniform local PDE estimates and continuation are analytic in README.md.
"""

import json
import sympy as sp
from finite_band_renewal import f, pm, Q, add, scale, cross, projection, eqv, velocity_time_jets, zero


def conjugate(a):
    return f.QQ_I(a.x, -a.y)


def modes(v):
    return sorted(set().union(*(p.keys() for p in v)))


def coefficient(v, k):
    return [p.get(k, f.ZERO) for p in v]


def coefficient_inner(v, w):
    return sum((conjugate(a)*b).x for a, b in zip(v, w))


def sobolev_pair(v, w, power=1):
    """Real inner product <Lambda^power v,w> with normalized torus volume."""
    return sp.simplify(sum(sp.Integer(sum(j*j for j in k))**sp.Rational(power, 2)
        *sp.Rational(coefficient_inner(coefficient(v, k), coefficient(w, k))) for k in modes(v)))


def helical_source(v):
    cv = f.curl(v)
    minus = sp.Integer(0)
    rows = []
    for k in modes(v):
        r2 = sum(j*j for j in k)
        a, b = coefficient(v, k), coefficient(cv, k)
        E, H = coefficient_inner(a, a), coefficient_inner(a, b)
        if E < 0 or r2*E*E-H*H < 0:
            raise ArithmeticError('Helical modal Cauchy--Schwarz inequality')
        weighted_minus = (sp.sqrt(r2)*sp.Rational(E)-sp.Rational(H))/2
        minus += weighted_minus
        rows.append(dict(k=k, energy=str(E), signed_helicity=str(H),
                         negative_helicity_magnitude=str(weighted_minus)))
    return sp.simplify(minus), rows


def rotate(v):
    return [-v[1], v[0], v[2]]


def parents(which):
    p, q = (12, 0, 16), (-12, 0, 9)
    A, B = [16, 20*f.II, -12], [9, 15*f.II, 12]
    base = [(p, A), (q, B)]
    rotated = [(tuple(rotate(p)), [-f.II*x for x in rotate(A)]),
               (tuple(rotate(q)), rotate(B))]
    selected = base if which == 'first' else rotated if which == 'second' else base+rotated
    u = [{}, {}, {}]
    for k, pol in selected:
        for j in range(3):
            a = f.QQ_I.convert(pol[j])/2
            u[j][k] = a
            u[j][tuple(-x for x in k)] = conjugate(a)
    return [f.clean(p) for p in u]


def modal_projection(v, k, sign):
    r = sp.sqrt(sum(j*j for j in k))
    if not r.is_Integer:
        raise ArithmeticError('This exact modal projection expects integer mode length')
    a = coefficient(v, k)
    b = coefficient(f.curl(v), k)
    return [(a[j]+sign*b[j]/int(r))/2 for j in range(3)]


def triad_identity():
    P, Qh, R, L = sp.symbols('P Qh R L', real=True)
    p, q = sp.Matrix([P, 0, 0]), sp.Matrix([Qh, R, 0])
    A, B = sp.Matrix([0, 1, sp.I]), sp.Matrix([-R, Qh, sp.I*L])
    k = p+q
    raw = (L-P)*A.cross(B)
    v = raw-k*raw.dot(k)/k.dot(k)
    E = sp.conjugate(v).dot(v)
    H = sp.conjugate(v).dot(sp.I*k.cross(v))
    numerator = sp.fraction(sp.together(H*((P+L)**2+k.dot(k))-2*(P+L)*k.dot(k)*E))[0]
    remainder = sp.rem(sp.Poly(numerator, R), sp.Poly(R**2-L**2+Qh**2, R)).as_expr()
    zero(remainder, 'same-sign isolated triad helicity identity')
    s, r = sp.symbols('s r', positive=True)
    fraction = (s-r)**2/(2*(s*s+r*r))
    zero(sp.Rational(1, 10)-fraction-(2*r-s)*(2*s-r)/(5*(s*s+r*r)),
         'forward daughter negative-helicity fraction is at most one tenth')
    return dict(negative_to_positive_energy_ratio='((|p|+|q|-|k|)/(|p|+|q|+|k|))^2',
        forward_negative_fraction_upper='1/10',
        scope='one coherent same-sign parent PAIR; |k|>=max(|p|,|q|); zero interactions included')


def shared_child():
    k = (0, 0, 25)
    sources = {}
    rows = []
    for label in ('first', 'second', 'full'):
        u = parents(label)
        cv = f.curl(u)
        for mode in modes(u):
            length = int(sp.sqrt(sum(j*j for j in mode)))
            if coefficient(cv, mode) != [length*a for a in coefficient(u, mode)]:
                raise ArithmeticError('All original modes must have positive helicity')
        source = projection(cross(u, cv))
        sources[label] = source
        plus, minus = modal_projection(source, k, 1), modal_projection(source, k, -1)
        Ep, Em = coefficient_inner(plus, plus), coefficient_inner(minus, minus)
        if label != 'full' and (Ep != 36*Em or Em <= 0):
            raise ArithmeticError('Individual forward daughters must have fraction one over37')
        if label == 'full' and (Ep != 0 or Em != 45000):
            raise ArithmeticError('Coherent shared child must be entirely negative')
        rows.append(dict(parents=label, positive_energy=str(Ep), negative_energy=str(Em),
                         negative_fraction=str(Em/(Ep+Em))))
    p1, p2 = (modal_projection(sources[label], k, 1) for label in ('first', 'second'))
    m1, m2 = (modal_projection(sources[label], k, -1) for label in ('first', 'second'))
    if any(p1[j]+p2[j] for j in range(3)) or m1 != m2:
        raise ArithmeticError('Shared positive channels cancel while negative channels agree')
    if coefficient(sources['full'], k) != [f.QQ_I(0, -150), f.QQ_I(-150), f.ZERO]:
        raise ArithmeticError('Explicit full NS child coefficient changed')
    return dict(child=k, parent_lengths=[20, 15], rows=rows,
        child_and_conjugate_negative_helicity_onset='2250000',
        scope='all four original parents positive; all other generated outputs retained')


def actual_return(nu):
    u = parents('full')
    jets, pressures = velocity_time_jets(u, nu, 2)
    omega = f.curl(u)
    source = projection(cross(u, omega))
    eqv(jets[1], add(scale(nu, [f.lap(p) for p in u]), source),
        'actual pressure and all generated modes in the first tangent')
    source1 = projection(add(cross(jets[1], omega), cross(u, f.curl(jets[1]))))
    eqv(jets[2], add(scale(nu, [f.lap(p) for p in jets[1]]), source1),
        'actual return keeps both evolving parents and receivers')
    if set(modes(u)) & set(modes(source)):
        raise ArithmeticError('Initial source must be disjoint from original parents')
    M0, D0 = sobolev_pair(u, u), sobolev_pair(u, u, 3)
    if M0 != 22750 or D0 != 7918750 or sp.Matrix(modes(u)).rank() != 3:
        raise ArithmeticError('Full three-dimensional initial helicity resources')
    nu_s = sp.Rational(nu.numerator, nu.denominator)
    M1 = 2*sobolev_pair(u, jets[1])
    zero(M1+2*nu_s*D0, 'initial critical reserve decays viscously')
    M2 = 2*sobolev_pair(jets[1], jets[1])+2*sobolev_pair(u, jets[2])
    heat2 = 4*nu_s**2*sobolev_pair(u, u, 5)
    negative_birth, rows = helical_source(source)
    zero(M2-heat2-4*negative_birth, 'complete first return creates critical reserve above heat forecast')
    # Signed helicity retains its exact physical viscous law through the return.
    H2 = 2*pm.mean(f.dot(jets[1], f.curl(jets[1])))+2*pm.mean(f.dot(u, f.curl(jets[2])))
    zero(sp.Rational(H2)-heat2, 'signed helicity heat curvature does not see pair creation')
    Z = pm.mean(f.dot(omega, omega))
    if 2*pm.mean(f.dot(u, jets[1])) != -2*f.QQ_I(nu).x*Z:
        raise ArithmeticError('Full kinetic energy remains dissipative')
    if not any(set(p) & set(q) for p, q in zip(jets[2], u)):
        raise ArithmeticError('Return to original parent modes was removed')
    return dict(viscosity=str(nu), energy=str(pm.mean(f.dot(u, u))),
        initial_critical_reserve=str(M0), initial_critical_dissipation=str(D0),
        nonlinear_source_modes=len(modes(source)), second_jet_modes=len(modes(jets[2])),
        pressure_modes=[len(p) for p in pressures],
        negative_helicity_t_squared=str(negative_birth),
        critical_reserve_minus_heat_t_squared=str(2*negative_birth), modal_sources=rows,
        scope='exact full PDE jets; fixed-viscosity finite-interval failure uses analytic local estimates')


def scalar_consumer():
    nu, kappa, D = sp.symbols('nu kappa D', positive=True)
    J = sp.symbols('J', real=True)
    Mprime = -2*nu*D+4*J
    Cprime = 4*J-2*(1-kappa)*nu*D
    zero(Mprime-Cprime+2*kappa*nu*D, 'critical reserve retains the full negative-helicity production')
    x, y = sp.symbols('x y', nonnegative=True)
    zero(x**4-2*y*x**3+sp.Rational(27, 16)*y**4
         -(2*x-3*y)**2*(4*x*x+4*x*y+3*y*y)/16,
         'explicit enstrophy Young inequality for the continuation consumer')
    return dict(actual_balance='M_prime+2nu D=4J, J=<Lambda u_minus,u cross Lambda u_plus>',
        OPEN='C(t)=4 integral J-2alpha nu integral D <= B(original full datum,nu,T)',
        nonnegative_reserve='M+B-C', derivative='-2(1-alpha)nu D',
        continuation='bounded H^(1/2) and integrated H^(3/2)^2 imply L^4_t L^6_x control',
        scope='analytic physical criterion on R3 and the mean-zero torus; not an arbitrary-data payment')


def main():
    print(json.dumps(dict(status='all exact checks passed', isolated_triad=triad_identity(),
        coherent_child=shared_child(), actual_returns=[actual_return(Q(1)), actual_return(Q(3, 2))],
        physical_consumer=scalar_consumer(),
        scope='full NS source, not a helical-decimated model; no new Lean certificate'), indent=2))


if __name__ == '__main__':
    main()
