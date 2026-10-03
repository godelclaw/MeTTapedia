#!/usr/bin/env python3
"""Exact initial renewal beyond a fixed vertical Fourier band.

All pressure and convolution outputs of the NS jets are retained. The
logarithmic band estimate, uniform local PDE argument and continuation
consumer are analytic arguments in README.md, not Lean certificates.
"""

import json
import sympy as sp
from solenoidal_geometric_cost import (
    f, pm, Q, add, scale, cross, harmonic, projection, eqv,
    velocity_time_jets, zero,
)


def outside(v, width=1):
    return [{k: a for k, a in p.items() if abs(k[2]) > width} for p in v]


def datum(a, b, third):
    """Cosine/sine polarizations, with an optional genuinely 3D parent."""
    u = [{}, {}, {}]
    modes = [((2, 0, 1), [f.QQ_I(-1), f.QQ_I(0, a), f.QQ_I(2)]),
             ((0, 0, 1), [f.QQ_I(1), f.QQ_I(0, b), f.QQ_I(0)])]
    for k, pol in modes:
        for i in range(3):
            u[i][k] = pol[i]/2
            u[i][tuple(-x for x in k)] = f.QQ_I(pol[i].x, -pol[i].y)/2
    u[0] = f.add(u[0], f.scale(third, harmonic((0, 1, 0), 'cos')))
    return [f.clean(p) for p in u]


def linearly_polarized_pair():
    P, Qh, R, a, b, c, d = sp.symbols('P Qh R a b c d', real=True)
    p, q = sp.Matrix([P, 0, 0]), sp.Matrix([Qh, R, 0])
    A, B = sp.Matrix([0, a, b]), sp.Matrix([R*c, -Qh*c, d])
    k = p+q
    K = k.dot(k)
    raw = (A.dot(q)*B+B.dot(p)*A)/2
    child = raw-k*raw.dot(k)/K
    work = -(q.dot(q)*child.cross(p.cross(A)).dot(B)
             +p.dot(p)*child.cross(q.cross(B)).dot(A))/4
    M = Qh+2*P*R**2/K
    squares = -P**2*R**2/8*((a*d+M*b*c)**2
              + R**2*(P**2-Qh**2-R**2)**2*(b*c)**2/K**2)
    if sp.factor(work-squares) != 0:
        raise ArithmeticError('Isolated linear-polarization interaction has wrong sign')
    return dict(first_signed_child_work='nonpositive sum of two squares',
        scope='two nonparallel wave vectors, each with one real polarization; first derivative only')


def elliptic_pair():
    a, b = sp.symbols('a b', real=True)
    p, q = sp.Matrix([2, 0, 1]), sp.Matrix([0, 0, 1])
    A, B = sp.Matrix([-1, sp.I*a, 2])/2, sp.Matrix([1, sp.I*b, 0])/2
    k = p+q
    F = A.cross(sp.I*q.cross(B))+B.cross(sp.I*p.cross(A))
    child = F-k*F.dot(k)/k.dot(k)
    receiver = (sp.I*p.cross(A)).cross(q.dot(q)*B) + (sp.I*q.cross(B)).cross(p.dot(p)*A)
    work = 2*sp.re(sp.conjugate(child).dot(receiver))
    formula = -(a*a+8*a*b+5*b*b)/2
    zero(work-formula, 'elliptic pair keeps coherent polarization contributions')
    zero(formula.subs({a: -2, b: 1})-sp.Rational(7, 2), 'positive generated-tail work')
    zero(formula.subs({a: 2, b: 1})+sp.Rational(25, 2), 'same spectral energies, opposite sign')
    cross_term = formula-formula.subs(b, 0)-formula.subs(a, 0)
    zero(cross_term+4*a*b, 'separate polarization accounting loses the shared child')
    return dict(first_signed_work=str(formula),
        separate_terms_at_a_minus2_b1=['-2', '-5/2'], coherent_cross_term='8', total='7/2',
        scope='exact complex Fourier coefficients, with conjugates retaining a real fluid')


def physical_case(a, b, third, nu):
    u = datum(a, b, third)
    f.equal(pm.divergence(u), {}, 'literal incompressibility')
    eqv(outside(u), [{}, {}, {}], 'tail initially empty')
    jets, pressures = velocity_time_jets(u, nu, 2)
    w1, w2 = outside(jets[1]), outside(jets[2])
    om = f.curl(u)
    c = f.curl(om)
    om1, c1 = f.curl(jets[1]), f.curl(f.curl(jets[1]))
    eqv(w1, outside(projection(cross(u, om))), 'actual generated tangent, including pressure')
    F1 = add(cross(jets[1], om), cross(u, om1))
    eqv(w2, add(scale(nu, [f.lap(p) for p in w1]), outside(projection(F1))),
        'second derivative retains generated parents, viscosity and pressure')
    first = pm.mean(f.dot(cross(w1, om), c))
    full_first = pm.mean(f.add(f.dot(F1, c), f.dot(cross(u, om), c1)))
    expected = -Q(a*a+8*a*b+5*b*b)/2
    if first != expected:
        raise ArithmeticError('Full PDE jet differs from polarization formula')
    second = pm.mean(f.add(f.dot(cross(w2, om), c),
        f.scale(2, f.dot(cross(w1, om1), c)), f.scale(2, f.dot(cross(w1, om), c1))))
    E = pm.mean(f.dot(u, u))
    Z = pm.mean(f.dot(om, om))
    D = pm.mean(f.dot(c, c))
    if 2*pm.mean(f.dot(u, jets[1])) != -2*f.QQ_I(nu).x*Z:
        raise ArithmeticError('Full kinetic energy must decrease')
    child_energy = pm.mean(f.dot(w1, w1))
    all_modes = sorted(set().union(*(p.keys() for p in w1)))
    if all_modes != [(-2, 0, -2), (2, 0, 2)]:
        raise ArithmeticError('Unexpected first generated tail support')
    modes = sorted(set().union(*(p.keys() for p in u)))
    rank = sp.Matrix(modes).rank()
    if third and rank != 3:
        raise ArithmeticError('Third parent must give three-dimensional spatial dependence')
    if any(k[1] for k in all_modes):
        raise ArithmeticError('First tail support changed')
    # The full second jet is allowed, and required here, to generate |k_z|=3.
    second_modes = set().union(*(p.keys() for p in w2))
    if not any(abs(k[2]) == 3 for k in second_modes):
        raise ArithmeticError('A finite band was accidentally closed during evolution')
    return dict(polarization=[a, b], third_parent=str(third), viscosity=str(nu),
        energy=str(E), enstrophy=str(Z), dissipation=str(D), spatial_rank=rank,
        pressure_modes=[len(p) for p in pressures],
        first_tail_modes=all_modes, first_tail_tangent_energy=str(child_energy),
        signed_tail_work_first=str(first), signed_tail_work_second=str(second),
        full_stretching_first=str(full_first),
        tail_cost_onset_lower_at_zeta_Z0=str(first**2/(D*2*Z)) if first > 0 else None,
        second_tail_modes=len(second_modes),
        scope='full unforced PDE jets; the actual short-interval conclusion is analytic')


def paid_two_coordinate_case():
    u = datum(-2, 1, 0)
    planar = [u[0], {}, u[2]]
    Eh = pm.mean(f.dot(planar, planar))
    Zh = pm.mean(f.dot(f.curl(planar), f.curl(planar)))
    if Eh != 3 or Zh != 13:
        raise ArithmeticError('Original planar reserve normalization changed')
    nu, amp, T = sp.symbols('nu amp T', positive=True)
    B = 16*amp**2*(52*sp.sqrt(39)/nu+9*T)
    zero(B-(3+1)**2*(52*sp.sqrt((3*amp**2)*(13*amp**2))/nu+T*(3*amp)**2),
         'finite-band tail has a full-data payment on the two-coordinate calibration')
    return dict(horizontal_energy='3', horizontal_enstrophy='13', passive_supremum_upper='3',
        tail_allowance='16 A^2 [52 sqrt(39)/nu+9T]',
        scope='actual two-coordinate prefixes, all amplitudes; no claim for the genuinely 3D added parent')


def band_reserve():
    nu, kappa, m, d = sp.symbols('nu kappa m d', positive=True)
    E, Z, Zv, ell, h, b, gap = sp.symbols('E Z Zv ell h b gap', nonnegative=True)
    A = 96*m/(kappa*nu)
    rate = A*Zv*(ell+h)-kappa*nu*d/4-gap-A*Z*(ell+h+b)
    zero(rate+kappa*nu*d/4+gap+A*((Z-Zv)*(ell+h)+Z*b),
         'whole-fluid energy pays the fixed band without autonomy')
    zero(sp.diff(48*m*E/(kappa*nu**2), E)*(-2*nu*Z)+A*Z,
         'one full energy reserve, fixed band width')
    zero(2*(kappa**2/8)*nu**2/(kappa*nu)-kappa*nu/4,
         'logarithmic interpolation retains a positive diffusion share')
    j = sp.symbols('j', integer=True, positive=True)
    zero(((2*j+1)**2-(2*j-1)**2)*m-8*m*j, 'horizontal shells in a vertical band')
    amp, s, D, Y = sp.symbols('amp s D Y', positive=True)
    zero((amp**3*s)**2/(nu**2*(amp**2*D)**2)-amp**2*s**2/(nu**2*D**2),
         'actual amplitude scaling defeats amplitude-uniform pointwise damping')
    zero((amp**3*s)**2/((amp**2*D)*(amp**2*Y))-amp**2*s**2/(D*Y),
         'tail cone cost scales quadratically when zeta scales with initial enstrophy')
    return dict(width='N fixed before future prefixes', multiplicity='m=2N+1',
        logarithmic_constant='48m', ell='log(e+384m zeta/(kappa^2 nu^2))',
        reserve='exp(48m E/(kappa nu^2)) [ell+log(Y/zeta)+(B_N-C_N)/nu]',
        rate='R_prime<=-(kappa nu/4) exp(48m E/(kappa nu^2)) D/Y',
        OPEN='C_N=integral(theta_N-alpha nu^2 D/Y)<=B_N(original full datum,nu,T)',
        scope='analytic periodic consumer; no bound for arbitrary generated tails')


def main():
    physical = [physical_case(a, b, third, nu)
        for a, b, third, nu in [(-2, 1, 0, Q(1)), (-2, 1, 1, Q(1)),
                                (2, 1, 1, Q(1)), (-2, 1, 1, Q(3, 2))]]
    if any(physical[1][key] != physical[2][key] for key in ('energy', 'enstrophy', 'dissipation')):
        raise ArithmeticError('Phase comparison changed spectral energy resources')
    print(json.dumps(dict(status='all exact checks passed', fixed_band=band_reserve(),
        linear_pair=linearly_polarized_pair(), elliptic_pair=elliptic_pair(), physical=physical,
        paid_calibration=paid_two_coordinate_case(),
        scope='no truncated dynamical system; general PDE estimates remain analytic'), indent=2))


if __name__ == '__main__':
    main()
