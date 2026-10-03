#!/usr/bin/env python3
"""Critical amplification in an unforced mixing flow and its nonlinear payment.

Exact algebra for the Fourier moments, viscosity-error constants, physical
parent return and all-time allowance. The stochastic representation, PDE
comparison and stability to three-dimensional perturbations are analytic
arguments in README.md, not certified by this finite checker.
"""

import json
import sympy as sp
from helicity_renewal import (
    f, pm, Q, add, scale, eqv, velocity_time_jets, zero, conjugate,
    coefficient, modes, sobolev_pair,
)
from helical_second_return import padd, diffuse, nonlinear


def initial(amplitude, perturbation):
    """(A sin y+eps cos z, eps sin z, A cos x)."""
    u = [{}, {}, {}]
    for k, v in [((0, 1, 0), [-f.II*amplitude, 0, 0]),
                 ((1, 0, 0), [0, 0, amplitude]),
                 ((0, 0, 1), [perturbation, -f.II*perturbation, 0])]:
        for j in range(3):
            a = f.QQ_I.convert(v[j])/2
            u[j][k] = a
            u[j][tuple(-x for x in k)] = conjugate(a)
    return [f.clean(p) for p in u]


def evaluate(p, amplitude, perturbation, viscosity):
    return add(*(scale(amplitude**a*perturbation**e*viscosity**n, v)
                 for (a, e, n), v in p.items()))


def parent_return():
    # Entire amplitude/perturbation/viscosity polynomials of full PDE jets.
    u = {(1, 0, 0): initial(Q(1), Q(0)), (0, 1, 0): initial(Q(0), Q(1))}
    j1 = padd(diffuse(u), nonlinear(u, u))
    j2 = padd(diffuse(j1), nonlinear(j1, u), nonlinear(u, j1))
    k = (0, 1, 0)
    expected = {(1, 0, 2): [-f.II/2, f.ZERO, f.ZERO],
                (1, 2, 0): [f.II/4, f.ZERO, f.ZERO]}
    for key in j2.keys() | expected.keys():
        actual = coefficient(j2.get(key, [{}, {}, {}]), k)
        if actual != expected.get(key, [f.ZERO]*3):
            raise ArithmeticError(('Complete original shear return changed', key, actual))
    cases = []
    for A, eps, nu in [(Q(2), Q(0), Q(1)), (Q(2), Q(1, 2), Q(3, 2)),
                       (Q(3), Q(-1, 3), Q(2))]:
        v = initial(A, eps)
        jets, pressures = velocity_time_jets(v, nu, 2)
        eqv(jets[1], evaluate(j1, A, eps, nu), 'first complete advective NS jet')
        eqv(jets[2], evaluate(j2, A, eps, nu), 'second complete advective NS jet')
        resource = sp.Rational(A*A+eps*eps)
        zero(sobolev_pair(v, v)-resource, 'initial critical mass')
        zero(sp.Rational(pm.mean(f.dot(v, v)))-resource, 'initial kinetic energy')
        zero(sobolev_pair(v, v, 2)-resource, 'all initial frequencies have length one')
        h = initial(Q(0), eps)
        h3_squared = sum(sp.binomial(3, j)*sobolev_pair(h, h, 2*j) for j in range(4))
        zero(h3_squared-8*sp.Rational(eps)**2, 'initial Fourier H3 difference')
        zero(sp.Rational(2*pm.mean(f.dot(v, jets[1])))+2*sp.Rational(nu)*resource,
             'actual unforced kinetic energy balance')
        if eps and (sp.Matrix(modes(v)).rank() != 3 or not any(pressures)):
            raise ArithmeticError('Three-dimensional perturbation must retain pressure')
        if not eps and any(pressures):
            raise ArithmeticError('Triangular reference has zero pressure')
        cases.append(dict(A=str(A), epsilon=str(eps), viscosity=str(nu),
                          jet_modes=[len(modes(j)) for j in jets],
                          pressure_modes=[len(p) for p in pressures]))
    return dict(cases=cases, shear_amplitude='A exp(-nu t)-A epsilon^2 t^2/4+O(t^3)',
                scope='initial return only; all other generated modes retained')


def mixing_moments():
    y, z = sp.symbols('y z', real=True)
    wave = sp.exp(-sp.I*z*sp.sin(y))
    mean = lambda g: sp.simplify(sp.integrate(sp.expand_trig(sp.simplify(g)),
                                           (y, 0, 2*sp.pi))/(2*sp.pi))
    d1, d2 = sp.diff(wave, y), sp.diff(wave, y, 2)
    second, fourth = mean(d1*sp.conjugate(d1)), mean(d2*sp.conjugate(d2))
    lap_squared = mean((d2-wave)*sp.conjugate(d2-wave))/2
    zero(second-z*z/2, 'second vertical Fourier moment')
    zero(fourth-z*z/2-3*z**4/8, 'fourth vertical Fourier moment')
    zero(lap_squared-sp.Rational(1, 2)-3*z*z/4-3*z**4/16,
         'transport reference Laplacian norm squared divided by B^2')
    zero((1+z*z)**2/2-lap_squared-z*z/4-5*z**4/16,
         'viscosity-error integrand upper bound')
    probability = sp.cancel((second-z*z/4)**2/fourth)
    zero(probability-z*z/(8+6*z*z), 'high-frequency mass lower bound')
    zero(probability-sp.Rational(1, 14)-8*(z*z-1)/(14*(8+6*z*z)),
         'mass fraction at least one over14 when z>=1')
    c = sp.Rational(1, 10)
    error = c+c**3/3
    if not (error < sp.Rational(1, 8) and sp.Rational(1, 14) > sp.Rational(1, 16)):
        raise ArithmeticError('Positive-viscosity comparison margin failed')
    return dict(second_moment=str(second), fourth_moment=str(fourth),
        normalized_Laplacian_squared=str(lap_squared), high_band_probability=str(probability),
        viscosity_error_relative_upper=str(error),
        time='(1/(10nu)) Re^(-2/3)', phase_lower='Re^(1/3)/20',
        actual_critical_mass_lower='B^2 Re^(1/3)/5120',
        scope='moment algebra and error constants; spectral comparison is analytic')


def full_history_payment():
    A, B, nu, t, kappa = sp.symbols('A B nu t kappa', positive=True)
    Re = A/nu
    phase = Re*(1-sp.exp(-nu*t))
    moment = sp.integrate(phase*sp.exp(-3*nu*t), (t, 0, sp.oo))
    zero(moment-Re/(12*nu), 'total gradient work of the original decaying shear')
    int_Z = B**2/(4*nu)
    int_D = B**2/(4*nu)+A*B**2*moment/(2*nu)
    zero(int_D-B**2/(4*nu)*(1+Re**2/6), 'complete gradient-dissipation payment')
    int_L = B**2/(4*nu)*sp.sqrt(1+Re**2/6)
    zero(int_Z*int_D-int_L**2, 'time-integrated critical interpolation')
    Mmax = A**2/2+B**2*sp.sqrt(1+Re**2)/2
    M0 = (A**2+B**2)/2
    allowance = B**2*(sp.sqrt(1+Re**2)-1)/2
    allowance += kappa*(A**2+B**2*sp.sqrt(1+Re**2/6))/2
    zero(Mmax-M0+2*kappa*nu*(A**2/(4*nu)+int_L)-allowance,
         'same sufficient critical-history target, all times')
    delta, eps = sp.symbols('delta epsilon', nonnegative=True)
    coupled = A**2+2*allowance.subs(B, A)+(2+4*kappa)*delta
    triangle_bound = 2*Mmax.subs(B, A)+2*delta-A**2-eps**2
    triangle_bound += 4*kappa*nu*(A**2/(4*nu)+int_L.subs(B, A))+4*kappa*delta
    zero(coupled-triangle_bound-eps**2, 'coupled all-history allowance retains initial mass')
    return dict(scalar_integrated_dissipation=str(int_D),
        allowance=str(allowance), coupled_allowance=str(coupled),
        scope='triangular history at all amplitudes; coupled history under the stated H3 stability bound',
        OPEN='a full-data allowance for unrestricted mutually amplifying parents')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed',
        physical_return=parent_return(), mixing=mixing_moments(),
        payment=full_history_payment(),
        scope='analytic PDE and stochastic claims with exact algebra; no new Lean certificate'), indent=2))
