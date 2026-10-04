#!/usr/bin/env python3
"""Exact fixtures for a two-observer fluid-history relaxation.

Every instantaneous rate is from the full unforced NS vector field.
The concentrating observer curve is NOT an unforced solution: its lift
requires a nonzero force invisible to both observed moment balances.
Whole-space localization, the characteristic argument and its coercivity
consequence are analytic in README.md, not certified by these fixtures.
"""

import ast
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from generated_fourth_moment import target_field, fourth_work, vector_pair
from heat_remainder_pressure import require


def zero(expression, label):
    require(s.simplify(expression) == 0, label)


def source_hashes():
    """Hash the transitive local Python imports, excluding external packages."""
    root = Path(__file__).resolve().parent
    pending, seen = [Path(__file__).resolve()], set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        tree = ast.parse(path.read_text())
        for node in ast.walk(tree):
            names = ([a.name for a in node.names] if isinstance(node, ast.Import)
                     else [node.module] if isinstance(node, ast.ImportFrom) and node.level == 0
                     else [])
            for name in names:
                if name:
                    dependency = root / (name.split('.')[0] + '.py')
                    if dependency.is_file():
                        pending.append(dependency)
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(seen)}


def fourier_fixture():
    u = target_field()
    f.equal(f.trace(f.jac(u)), {}, 'The complete periodic seed is divergence free')
    require(all(f.ORIGIN not in a for a in u), 'The seed has zero mean')
    p, d, y = fourth_work(u)
    e = vector_pair(u, u)
    z = -vector_pair(u, [f.lap(a) for a in u])
    require((e, y, z, d, p) ==
            (Q(579, 128), Q(924955, 32768), Q(387, 64), Q(627867, 16384), Q(51, 320)),
            'Exact original kinetic, quartic, derivative, diffusion and pressure observations')
    require(min(e, y, z, d, p) > 0, 'The seed has strictly positive pressure work')
    n = velocity_time_jets(u, Q(0), 1)[0][1]
    receiver = [f.mul(f.dot(u, u), a) for a in u]
    require(vector_pair(u, n) == 0, 'The complete nonlinearity conserves kinetic energy')
    require(vector_pair(receiver, n) == p, 'The quartic receiver identifies full pressure work')
    input_modes, output_modes = set().union(*u), set().union(*n)
    k = (-1, -2, 0)
    require(k not in input_modes and k in output_modes, 'An actual generated mode lies outside the input support')
    coefficient = [a.get(k, f.ZERO) for a in n]
    require(coefficient == [f.QQ_I(1)/80, -f.QQ_I(1)/160, f.ZERO],
            'The missing mode has a nonzero complete Leray coefficient')
    require(sum((k[j]*coefficient[j] for j in range(3)), f.ZERO) == f.ZERO,
            'The missing mode is solenoidal and cannot be removed by pressure')
    opposite_work = fourth_work([f.scale(-1, a) for a in u])[0]
    require(opposite_work == -p, 'Reversing the seed reverses its signed pressure work')
    rows = []
    for nu in (Q(1), Q(2, 7)):
        tangent = velocity_time_jets(u, nu, 1)[0][1]
        erate, yrate = 2*vector_pair(u, tangent), 4*vector_pair(receiver, tangent)
        require(erate == -2*nu*z and yrate == 4*p-4*nu*d,
                'Both rates include full transport, pressure and positive viscosity')
        rows.append(dict(viscosity=str(nu), energy_rate=str(erate), quartic_rate=str(yrate)))
    return dict(energy=str(e), fourth_moment=str(y), gradient_energy=str(z),
                quartic_diffusion=str(d), pressure_work=str(p), input_modes=len(input_modes),
                full_source_modes=len(output_modes), missing_mode=list(k),
                missing_coefficient=[str(f.QQ_I.to_sympy(a)) for a in coefficient],
                physical_tangents=rows,
                scope='Periodic algebraic seed; its numbers are not the constants of the localized whole-space field.')


def scale_characteristic():
    e, y, z, d, p, nu, a, ell = s.symbols('e y z d p nu a ell', positive=True)
    E, Y, q = s.symbols('E Y q', positive=True)
    a0 = s.sqrt(e*Y/(y*E))
    ell0 = (e**2*Y/(y*E**2))**s.Rational(1, 3)
    kinetic, quartic = e*a*a/ell**3, y*a**4/ell**3
    zero(kinetic.subs({a:a0, ell:ell0})-E, 'Amplitude and scale reconstruct the prescribed energy')
    zero(quartic.subs({a:a0, ell:ell0})-Y, 'Amplitude and scale reconstruct the prescribed fourth moment')
    Z, D, P = z*a*a/ell, d*a**4/ell, p*a**5/ell**2
    adot = a*(2*a*ell*p/y + nu*ell**2*(z/e-2*d/y))
    ldot = ell*s.Rational(4, 3)*(a*ell*p/y + nu*ell**2*(z/e-d/y))
    edot, ydot = -2*nu*Z, 4*P-4*nu*D
    zero(s.diff(kinetic,a)*adot+s.diff(kinetic,ell)*ldot-edot,
         'The two parameter velocities realize the full kinetic rate')
    zero(s.diff(quartic,a)*adot+s.diff(quartic,ell)*ldot-ydot,
         'The same parameter velocities realize the full quartic rate')
    zero((adot/a-s.Rational(3,2)*ldot/ell)*kinetic+nu*Z,
         'The reconstructed force has zero integrated kinetic work')
    zero((adot/a-s.Rational(3,4)*ldot/ell)*quartic+nu*D-P,
         'The reconstructed force has zero integrated quartic work')

    cz = z*e**s.Rational(1,3)/y**s.Rational(2,3)
    alpha = p*e**s.Rational(5,6)/(3*z*y**s.Rational(7,6))
    beta = d*e/(3*z*y)
    erate = s.simplify(edot.subs({a:a0, ell:ell0}))
    yrate = s.simplify(ydot.subs({a:a0, ell:ell0}))
    zero(erate+2*nu*cz*Y**s.Rational(2,3)*E**s.Rational(-1,3),
         'The whole-space kinetic scaling retains the volume factor')
    dq_dE = s.simplify((-Y**s.Rational(-7,6)*yrate/(6*erate)).subs(Y,q**-6))
    zero(dq_dE-(alpha/nu*E**s.Rational(-5,6)-beta*q/E),
         'The complete observer characteristic is a linear equation for Y^(-1/6)')

    A, B, Estar, E0 = s.symbols('alpha beta E_star E0', positive=True)
    kappa = A/(B+s.Rational(1,6))
    qcurve = kappa/nu*(E**s.Rational(1,6)-Estar**(B+s.Rational(1,6))*E**(-B))
    zero(s.diff(qcurve,E)+B*qcurve/E-A/nu*E**s.Rational(-5,6),
         'Independent differentiation checks the concentrating characteristic')
    zero(qcurve.subs(E,Estar), 'The characteristic reaches zero at positive energy')
    zero(s.diff(qcurve,E).subs(E,Estar)-A/nu*Estar**s.Rational(-5,6),
         'The zero is simple with positive derivative')
    clock_density = E**s.Rational(1,3)*q**4/(2*nu*cz)
    zero(clock_density+1/erate.subs(Y,q**-6),
         'The clock is the actual instantaneous kinetic-loss clock')
    upper = s.integrate(s.simplify(clock_density.subs(q,kappa/nu*E**s.Rational(1,6))), (E,0,E0))
    zero(upper-kappa**4*E0**2/(4*nu**5*cz), 'Exact finite upper bound for the characteristic clock')

    force_scale = s.simplify((a*a/ell**s.Rational(1,2)).subs({a:a0,ell:ell0}).subs(Y,q**-6))
    zero(force_scale-e**s.Rational(2,3)/(y**s.Rational(5,6)*E**s.Rational(2,3)*q**5),
         'The generated packet gives the exact force L2 scaling')
    force_clock = s.simplify(force_scale*clock_density)
    zero(force_clock-e**s.Rational(2,3)/(2*nu*cz*y**s.Rational(5,6)*E**s.Rational(1,3)*q),
         'The missing packet requires a logarithmically divergent integrated force norm')
    eps = s.symbols('epsilon', nonnegative=True)
    amplitude_drift = 2*p/y+eps*(z/e-2*d/y)
    dilation_drift = s.Rational(4,3)*(p/y+eps*(z/e-d/y))
    zero((adot/(a*a*ell)).subs(nu,eps*a/ell)-amplitude_drift,
         'The exact normalized amplitude drift retains viscosity')
    zero((ldot/(a*ell*ell)).subs(nu,eps*a/ell)-dilation_drift,
         'The exact normalized dilation drift retains viscosity')
    zero(-2*eps*z-2*amplitude_drift*e+3*dilation_drift*e,
         'The normalized full equation preserves the fixed kinetic observation')
    zero(4*p-4*eps*d-4*amplitude_drift*y+3*dilation_drift*y,
         'The normalized full equation preserves the fixed quartic observation')
    turnover_clock = s.simplify((a*ell).subs({a:a0,ell:ell0}).subs(Y,q**-6)*clock_density)
    zero(turnover_clock-e**s.Rational(7,6)/(2*nu*cz*y**s.Rational(5,6)*E**s.Rational(5,6)*q),
         'The concentrating curve has an infinite nonlinear turnover clock')
    return dict(scale=dict(energy=str(kinetic), fourth_moment=str(quartic), gradient_energy=str(Z),
                           quartic_diffusion=str(D), pressure_work=str(P)),
                parameter_rates=dict(amplitude=str(adot), spatial_scale=str(ldot)),
                observer_rates=dict(energy=str(erate), fourth_moment=str(yrate)),
                constants=dict(c_z=str(cz), alpha=str(alpha), beta=str(beta)),
                characteristic=str(qcurve), clock_density=str(clock_density), clock_upper=str(upper),
                force_L2_scale=str(force_scale), force_clock_density=str(force_clock),
                normalized_equation=dict(amplitude_drift=str(amplitude_drift),
                                         dilation_drift=str(dilation_drift),
                                         turnover_clock_density=str(turnover_clock)),
                near_endpoint_powers=dict(time_in_q=5, amplitude_in_q=-3, frequency_in_q=-2,
                                          fourth_moment_in_q=-6, gradient_energy_in_q=-4,
                                          force_L2_lower_in_q=-5),
                scope='Positive constants are those of one fixed localized whole-space field. The concentrating curve solves the two-observer relaxation, not unforced NS.')


def checks():
    return dict(fourier=fourier_fixture(), whole_space=scale_characteristic(),
                source_sha256=source_hashes(),
                certification='Exact algebra only. Localization, the forced lift, coercivity obstruction and divergence conclusions are analytic; no Lean certification or unforced singularity is claimed.')


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
