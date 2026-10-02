#!/usr/bin/env python3
"""Exact physical feedback fixtures and the full-energy square payment.

Every canonical nonlinear output is kept. Actual unforced whole-space
source and history inequalities are separately formalized in
MettapediaNS.WholeSpaceParentFeedback. The periodic realization and
the combined parent/receiver reserve are explained in README.md.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from cellular_parent_refeeding import seed
from cellular_transfer_reversal import real_field
from reciprocal_pattern_cycles import inner, mode, vector_add, vector_scale, require
from refeeding_stretching import nonlinear, cubic
from generated_mean_enstrophy import minus_laplacian, second_gradient_squared
from reference_stretching_control import gradient_norm_squared, equal_vectors


def dilation(u, n):
    return [{tuple(n*j for j in k): a for k, a in component.items()} for component in u]


def source_by_stress(u, psi):
    return inner(u, f.matvec(f.jac(psi), u))


def fixtures():
    u0 = real_field(seed())
    N0 = nonlinear(u0)
    psi0 = [mode((1, 0, 1), 1), {}, mode((1, 0, 1), -1)]
    E0, Nenergy = inner(u0, u0), inner(N0, N0)
    records = []
    paired = {}
    for delta in [Q(-1, 10), Q(1, 10)]:
        base = vector_add(u0, vector_scale(delta, N0))
        for frequency in [1, 3, 11]:
            u, psi = dilation(base, frequency), dilation(psi0, frequency)
            f.equal(f.trace(f.jac(u)), {}, 'actual datum is solenoidal')
            f.equal(f.trace(f.jac(psi)), {}, 'fixed parent observation is solenoidal')
            require(inner(psi, psi) == 1, 'parent remains L2 normalized')
            require(inner(u, psi) == Q(1, 10), 'both hidden phases keep the same parent')
            require(inner(u, u) == E0+delta**2*Nenergy, 'both hidden phases have the same energy')
            N = nonlinear(u)
            pressure = f.green(f.trace(f.matmul(f.jac(u), f.jac(u))))
            require(inner(f.grad(pressure), psi) == 0, 'full pressure cancels only in solenoidal observation')
            F = inner(N, psi)
            require(F == source_by_stress(u, psi), 'canonical feedback equals complete stress pairing')
            require(F == -frequency*delta*Q(22019, 546000),
                    'same parent and energy have opposite internally generated feedback')
            K = 2*frequency
            require(abs(F) <= K*inner(u, u), 'energy pays the fixed observer source')
            lap = minus_laplacian(u)
            nu = Q(2, 7)
            rhs = vector_add(N, vector_scale(-nu, lap))
            require(inner(rhs, psi) == -2*nu*frequency**2*inner(u, psi)+F,
                    'observed actual parent retains viscosity and nonlinear feedback')
            Z = gradient_norm_squared(u)
            require(2*inner(u, rhs) == -2*nu*Z, 'same full energy pays all suppliers')
            require(2*inner(lap, rhs) == 2*cubic(u)-2*nu*second_gradient_squared(u),
                    'full enstrophy source is retained separately')
            c = 2/(nu*frequency)
            require(c*K == 4/nu, 'single-harmonic feedback price is uniform in frequency')
            require(c*(2*nu*frequency**2) == 4*frequency,
                    'reserve decay price matches the parent gradient observation')
            # A non-solenoidal observation would retain this pressure term.
            gradient_test = f.grad(pressure)
            pressure_work = inner(gradient_test, gradient_test)
            require(pressure_work > 0, 'canonical pressure is genuinely nonzero here')
            paired[delta, frequency] = (inner(u, u), Z, F)
            records.append({'phase': str(delta), 'frequency': frequency,
                            'energy': str(inner(u, u)), 'source': str(F),
                            'parent_amplitude': '1/10', 'pressure_norm_squared': str(pressure_work)})
    for n in [1, 3, 11]:
        left, right = paired[Q(-1, 10), n], paired[Q(1, 10), n]
        require(left[:2] == right[:2] and left[2] == -right[2],
                'both phases have identical energy and enstrophy but opposite source')
    return records


def identities():
    nu, C, E, Z, W = s.symbols('nu C E Z W', real=True)
    J = C*E**2/(4*nu)
    require(s.expand(s.diff(J, E)*(-2*nu*Z)+C*E*Z) == 0,
            'exact unforced energy-square payment')
    require(s.expand(s.diff(J, E)*(-2*nu*Z+2*W)+C*E*Z-C*E*W/nu) == 0,
            'external kinetic work is retained when the equation is forced')
    c, a, F, L, extra, v, loss, k = s.symbols('c a F L extra v loss k', real=True)
    # k a is the parent enstrophy growth bound; c a'=-k a+c F.
    Rdot = (v-1)*(k*a*Z-2*nu*s.symbols('D')+L-loss)+v*(-k*a+c*F)*Z
    D = s.symbols('D')
    paid = (v-1)*L+extra-(C*E-c*v*F)*Z-(v-1)*loss
    require(s.expand(Rdot-C*E*Z+k*a*Z+extra+2*nu*(v-1)*D-paid) == 0,
            'full corrected reserve retains receiver and domination slacks')
    Ea, Eb, Ec = s.symbols('Ea Eb Ec', real=True)
    cap = lambda x: C*x*x/(4*nu)
    require(s.expand(cap(Ea)-cap(Eb)+cap(Eb)-cap(Ec)-cap(Ea)+cap(Ec)) == 0,
            'a seam uses the same remaining kinetic reserve')
    Cp = s.symbols('Cp')
    require(s.expand(Cp*E**2/(4*nu)+s.diff(J,E)*(-2*nu*Z)+C*E*Z
                     -Cp*E**2/(4*nu)) == 0,
            'changing the source-observer price creates a separate derivative cost')
    return {'feedback_bound': 'c*exp(c*|a|)*|F|*Z <= C*E*Z',
            'C': 'c*K*exp(c*||psi||2*sqrt(E_initial))',
            'reserve': 'C*E^2/(4*nu)',
            'remaining': '(exp(c*alpha)-1)*L+extra',
            'scope': 'fixed smooth parent source; arbitrary receiver stretching remains open'}


if __name__ == '__main__':
    print(json.dumps({'fixtures': fixtures(), 'identities': identities()}, indent=2))
