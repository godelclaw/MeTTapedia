#!/usr/bin/env python3
"""Exact checks for physical-kernel entropy and directional score balances.

Kernel bounds, entropy limits, and actual positive-time statements are
analytic in README.md. No controlled-law bound is inferred from an
uncontrolled first moment, and all NS Fourier products are retained.
"""

import json

import sympy as sp

import passive_parent_bellman as parent
from metric_loss_bellman import zero
from cyclic_pressure_history import velocity_time_jets

f, Q, r = parent.f, parent.Q, parent.r


def entropy_checks():
    t, nu = sp.symbols("t nu", positive=True)
    entropy = -sp.Rational(3, 2)*(1+sp.log(4*sp.pi*nu*t))
    fisher = sp.Rational(3, 2)/(nu*t)
    zero(sp.diff(entropy, t)+nu*fisher, "exact Gaussian entropy dissipation")
    primitive = -sp.Rational(3, 2)*t*sp.log(4*sp.pi*nu*t)
    zero(sp.diff(primitive, t)-entropy, "Gaussian entropy time primitive")
    zero(-t*entropy+primitive-sp.Rational(3, 2)*t,
         "point-source weighted Fisher identity")
    a = sp.symbols("a", positive=True)  # The positive density uses 0<a<1.
    root = sp.sqrt(1-a*a)
    periodic_entropy = sp.log((1+root)/2)+1-root
    periodic_fisher = 1-root
    zero(-nu*a*sp.diff(periodic_entropy, a)+nu*periodic_fisher,
         "positive periodic heat density q=1+a cos x, a'= -nu a")
    C = sp.symbols("C", positive=True)
    zero((sp.log(2*C)+sp.Rational(3, 2))/nu
         +(2*C-1)/(2*nu)-(sp.log(2*C)+C+1)/nu,
         "periodic early entropy plus Poincare tail")
    B = sp.symbols("B", positive=True)
    zero(t*(sp.log(8*sp.pi*B**3)+1)+primitive
         -t*(sp.log(8*sp.pi)+3*sp.log(B)-sp.Rational(3, 2)*sp.log(4*sp.pi*nu*t)+1),
         "whole-space displacement entropy budget")
    radial = sp.symbols("radial", positive=True)
    norm = sp.integrate(4*sp.pi*radial**2*sp.exp(-radial/B), (radial, 0, sp.oo))
    zero(norm-8*sp.pi*B**3, "normalization of the radial entropy reference")
    heat_area = 2*sp.sqrt(t)/(4*sp.pi*nu)**sp.Rational(3, 2)
    zero(sp.diff(heat_area, t)-t/(4*sp.pi*nu*t)**sp.Rational(3, 2),
         "entire weighted impulse observation is integrable at the point source")


def exact_shear_fisher():
    # Endpoint velocity is 80 nu sin(y) e_x. It belongs to an exact
    # unforced history u(s)=160 nu exp(-nu s) sin(y)e_x at t=log(2)/nu.
    amplitude, nu, decay, y = sp.symbols("amplitude nu decay y", positive=True)
    shear = amplitude*decay*sp.sin(y)
    zero(-nu*decay*sp.diff(shear, decay)-nu*sp.diff(shear, y, 2),
         "exact unforced shear and its original passive field both solve the heat equation")
    # The x component depends only on y: divergence and self-transport vanish.
    k, ell = (1, 0, 1), (1, 1, 1)
    phi = f.add(r.mode(k, 1), r.mode(ell, 1))
    dp, Hp = f.grad(phi), f.hess(phi)
    cos_y = r.mode((0, 1, 0), 1)
    inviscid = f.scale(2, f.mul(cos_y, f.mul(dp[0], dp[1])))
    diffusive = f.scale(2, f.add(*(f.mul(p, p) for row in Hp for p in row)))
    average = lambda p: p.get(f.ORIGIN, f.ZERO).x
    zero(sp.Rational(str(average(inviscid)))-sp.Rational(1, 2), "uniform strain coefficient")
    zero(sp.Rational(str(average(diffusive)))-13, "full three-dimensional receiver Hessian")
    # |phi|<=2, epsilon=1/100. Thus |q0-1| <= exp(1/25)-1 <=1/24.
    # |2 A cos(y) phi_x phi_y -2nu |Hess phi|^2| <=4A+50nu.
    margin = sp.Rational(80, 2)-13-sp.Rational(4*80+50, 24)
    zero(margin-sp.Rational(139, 12), "strict Fisher-production lower bound")
    if margin <= 0:
        raise ArithmeticError("the exact unforced shear must increase this receiver's Fisher information")
    return dict(velocity="160 nu exp(-nu s) sin(y) e_x", endpoint="log(2)/nu",
                receiver="q0=exp(epsilon [cos(x+z)+cos(x+y+z)])/Z, epsilon=1/100",
                fisher_derivative_lower_bound="(139/12) nu epsilon^2 > 0",
                passive_parent="H=u, I=0 for all time",
                scope="smooth positive receiver, not a claim about a point kernel's monotonicity")


def directional_fixture(u, label, point):
    nu = Q(1)
    jets, pressure = velocity_time_jets(u, nu, 1)
    ut = jets[1]
    omega, wt = f.curl(u), f.curl(ut)
    ev = lambda p: r.at(p, point)
    vec = lambda v: sp.Matrix([ev(p) for p in v])
    mat = lambda T: sp.Matrix([[ev(p) for p in row] for row in T])
    # Positive receiver q=exp(L)/Z; all spatial derivatives of log q are literal.
    L = f.scale(Q(1, 5), f.add(r.mode((1, 0, 1), 1), r.mode((1, 1, 1), 1)))
    kp, Kp = f.grad(L), f.hess(L)
    k, K, w, U, B = vec(kp), mat(Kp), vec(omega), vec(u), mat(f.jac(u))
    G = mat(f.jac(omega))
    lapk, lapw = vec([f.lap(p) for p in kp]), vec([f.lap(p) for p in omega])
    # q_r=nu Delta q+u.grad q; omega is evaluated at physical time t-r.
    kr = nu*lapk+2*nu*K*k+B.T*k+K*U
    c = w.dot(k)
    cr = -vec(wt).dot(k)+w.dot(kr)
    dc = G.T*k+K*w
    cross = sum(G[i, j]*K[i, j] for i in range(3) for j in range(3))
    lapc = lapw.dot(k)+2*cross+w.dot(lapk)
    generator_c = cr-U.dot(dc)+nu*lapc
    wanted = 2*nu*(w.dot(lapk)+w.dot(K*k)+cross)
    zero(generator_c-wanted, (label, "actual vorticity and kernel score cancel strain"))
    # Divide the literal local flux div(4nu q c K omega) by q.
    div_flux_over_q = 4*nu*(k.dot(c*K*w)+dc.dot(K*w)
                            +c*(w.dot(lapk)+cross))
    generator_csq = 2*c*generator_c+2*nu*dc.dot(dc)
    positive, negative = (G.T*k).dot(G.T*k), (K*w).dot(K*w)
    zero(generator_csq-div_flux_over_q-2*nu*(positive-negative),
         (label, "complete directional Fisher density and its spatial flux"))
    # Ordinary Fisher's derivative retains its strain production.
    ordinary = sp.factor(2*k.dot(B*k)-2*nu*sum(z*z for z in K))
    generator_ksq = 2*k.dot(kr-K*U+nu*lapk)+2*nu*sum(z*z for z in K)
    fisher_flux = 4*nu*(k.dot(K*k)+lapk.dot(k)+sum(z*z for z in K))
    zero(generator_ksq-fisher_flux-ordinary,
         (label, "ordinary Fisher production with its complete spatial flux"))
    if label == "original_simple_carrier":
        zero(negative, "simple carrier negative directional square vanishes")
        if not sp.simplify(positive).is_positive:
            raise ArithmeticError("simple carrier positive directional defect must be strict")
    return dict(fixture=label, score_pair=str(sp.factor(c)),
                directional_positive_defect=str(sp.factor(positive)),
                directional_negative_square=str(sp.factor(negative)),
                ordinary_fisher_local_production=str(ordinary),
                canonical_pressure_modes=len(pressure[0]),
                scope="literal PDE jets and positive smooth receiver; not a kernel computed by time integration")


def main():
    entropy_checks()
    shear = exact_shear_fisher()
    simple = parent.carrier(r.c.simple_parent(), Q(16), 4, [{}, {}, {}])
    background = r.ns.vector_scale(Q(-20000), r.ns.nonlinear(r.c.resonant_parent()))
    resonant = parent.carrier(r.c.resonant_parent(), Q(200), 4, background)
    cases = [(r.counterstrain_datum(Q(4), Q(8)), "pressure_start", (0, 0, 0)),
             (r.record_datum(Q(4), Q(8)), "original_maximum", (0, 0, 0)),
             (simple, "original_simple_carrier", (1, 1, 1)),
             (resonant, "original_resonant_carrier", (1, 1, 1))]
    fixtures = [directional_fixture(*case) for case in cases]
    print(json.dumps(dict(status="all exact checks passed", shear=shear, fixtures=fixtures,
                         scope="kernel bounds and entropy limits analytic; complete algebra and actual NS initial jets exact"), indent=2))


if __name__ == "__main__":
    main()
