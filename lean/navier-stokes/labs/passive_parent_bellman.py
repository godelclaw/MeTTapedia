#!/usr/bin/env python3
"""Exact Bellman squares and actual original-passive-parent NS jets.

The general passive comparison and stochastic integration are analytic in
README.md. All pressure modes and changing-drift terms are retained here;
the original passive field is initialized once, not at a released descendant.
"""

import json

import sympy as sp

import pressure_impulse_history as ph
import signed_reaction_renewal as r
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f, Q = r.f, r.Q


def original_bound_sq(u):
    # Each component's Fourier l1 majorant bounds its sup norm.
    return Q(1)+sum(sum(Q(str(abs(a.x)+abs(a.y))) for a in row.values())**2 for row in u)


def pointwise_squares():
    nu, theta, M = sp.symbols("nu theta M", positive=True)
    beta = sp.Matrix(sp.symbols("b0:3", real=True))
    H = sp.Matrix(sp.symbols("h0:3", real=True))
    G = sp.Matrix(3, 3, sp.symbols("g0:9", real=True))
    grad_sq = sum(v*v for v in G)
    grad_phi = -theta*G.T*H/(2*M*M)
    production = theta*nu*grad_sq/(2*M*M)
    square_sum = theta*nu*sum((G[:, j]+beta[j]*H/nu).dot(G[:, j]+beta[j]*H/nu)
                             for j in range(3))/(4*M*M)
    remainder = theta*beta.dot(beta)*(1-H.dot(H)/(M*M))/(4*nu)
    zero(production-beta.dot(grad_phi)+theta*beta.dot(beta)/(4*nu)
         -theta*nu*grad_sq/(4*M*M)-square_sum-remainder,
         "all control and derivative cross terms")
    y, c = sp.symbols("y c", real=True)
    zero(theta*nu*y*y/(4*M*M)+c*c*M*M/(theta*nu)-c*y
         -(theta*nu*y-2*c*M*M)**2/(4*M*M*theta*nu), "linear gradient observation")
    phi0, phi1, phi2, dt1, dt2, cost = sp.symbols("phi0 phi1 phi2 dt1 dt2 cost", real=True)
    zero((phi2-phi1+cost*dt2)+(phi1-phi0+cost*dt1)
         -(phi2-phi0+cost*(dt1+dt2)), "one retained potential across compatible seams")


def exact_shear():
    a, nu, theta = sp.symbols("a nu theta", positive=True)
    q, y, beta = sp.symbols("q y beta", real=True)
    # q=exp(-nu t), H=u=(a q sin y,0,0), M=a.
    H = a*q*sp.sin(y)
    phi = theta*(1-q*q*sp.sin(y)**2)/4
    Dt = lambda z: -nu*q*sp.diff(z, q)-nu*sp.diff(z, y, 2)
    gradient_square = a*a*q*q*sp.cos(y)**2
    zero(Dt(phi)-theta*nu*gradient_square/(2*a*a), "complete exact shear potential law")
    lhs = Dt(phi)-beta*sp.diff(phi, y)+theta*beta*beta/(4*nu)-theta*nu*gradient_square/(4*a*a)
    rhs = theta*nu*(sp.diff(H, y)+beta*H/nu)**2/(4*a*a)+theta*beta*beta*(1-H*H/(a*a))/(4*nu)
    zero(lhs-rhs, "full-time controlled shear square")
    return {"passive_parent": "H=u for all time", "pressure_impulse": "0",
            "remaining_reaction": "-2 nu |grad omega|^2/(|omega|^2+delta) <= 0"}


def forced_shear_contrast():
    a, nu = sp.symbols("a nu", positive=True)
    q, y = sp.symbols("q y", real=True)
    u, H = a*sp.sin(y), a*q*sp.sin(y)
    force, impulse = nu*u, H-u
    Dt = lambda v: -nu*q*sp.diff(v, q)-nu*sp.diff(v, y, 2)
    zero(Dt(H), "forced fluid still transports the same passive original parent")
    zero(Dt(impulse)+force, "forced impulse retains minus the actual force")
    omega, curl_force = -sp.diff(u, y), -sp.diff(force, y)
    s = omega*omega+a*a
    full_source = 2*omega*curl_force-2*nu*sp.diff(omega, y)**2
    zero(Dt(s)-full_source, "forced vorticity reaction retains its extra curl source")
    return {"fluid": "stationary forced shear", "force": "nu u", "impulse_source": "-force",
            "extra_reaction": "2 omega.curl(force)/s",
            "scope": "smooth manufactured calibration, not a forced singular solution"}


def actual_history_jets(u0, nu, label, point):
    jets, pressures = velocity_time_jets(u0, nu, 2)
    u, u1, u2 = jets
    H1 = ph.vector_transport(u, u, nu)
    H2 = [f.add(v, f.scale(-1, f.adv(u1, h)))
          for v, h in zip(ph.vector_transport(u, H1, nu), u)]
    I1 = [f.add(v, f.scale(-1, w)) for v, w in zip(H1, u1)]
    I2 = [f.add(v, f.scale(-1, w)) for v, w in zip(H2, u2)]
    ph.vectors_equal(I1, f.grad(pressures[0]), (label, "original pressure impulse first jet"))
    ph.vectors_equal(I2, [f.add(v, w) for v, w in
                         zip(ph.vector_transport(u, I1, nu), f.grad(pressures[1]))],
                     (label, "second impulse jet includes evolving canonical pressure"))
    B, BH1 = f.jac(u), f.jac(H1)
    G0 = f.add(*(f.mul(p, p) for row in B for p in row))
    G1 = f.scale(2, f.add(*(f.mul(p, q) for row, row1 in zip(B, BH1) for p, q in zip(row, row1))))
    n0 = f.dot(u, u)
    n1 = f.scale(2, f.dot(u, H1))
    n2 = f.scale(2, f.add(f.dot(H1, H1), f.dot(u, H2)))
    f.equal(f.add(n1, f.adv(u, n0), f.scale(-nu, f.lap(n0))),
            f.scale(-2*nu, G0), (label, "actual passive squared norm"))
    f.equal(f.add(n2, f.adv(u1, n0), f.adv(u, n1), f.scale(-nu, f.lap(n1))),
            f.scale(-2*nu, G1), (label, "first evolving potential law with changing drift"))
    m2 = original_bound_sq(u0)
    ev = lambda p: r.at(p, point)
    vec = lambda v: sp.Matrix([ev(p) for p in v])
    mat = lambda T: sp.Matrix([[ev(p) for p in row] for row in T])
    theta = sp.Rational(1, 2)
    beta = sp.Matrix([2, -3, 1])
    h, b = vec(u), mat(B)
    ms = sp.Rational(m2.numerator, m2.denominator)
    phi = theta*(ms-h.dot(h))/(4*ms)
    if not (0 <= phi <= theta/4):
        raise ArithmeticError((label, "original Fourier magnitude bound"))
    grad_phi = -theta*b.T*h/(2*ms)
    Dphi = theta*nu*ev(G0)/(2*ms)
    margin = sp.factor(Dphi-beta.dot(grad_phi)+theta*beta.dot(beta)/(4*nu)
                      -theta*nu*ev(G0)/(4*ms))
    if margin < 0:
        raise ArithmeticError((label, "controlled gradient payment failed"))
    # Differentiate the actual remaining pressure-impulse reward from I(0)=0.
    omega, omega1 = f.curl(u), f.curl(u1)
    w, wt, P = vec(omega), vec(omega1), mat(f.hess(pressures[0]))
    delta = original_bound_sq(omega)
    # The two explicit families have a certified sharper initial maximum.
    if label in ("original_maximum", "pressure_start"):
        delta = Q(256)
    s = w.dot(w)+delta
    st = 2*w.dot(wt)
    dw = [vec([f.diff(p, j) for p in omega]) for j in range(3)]
    dwt = [vec([f.diff(p, j) for p in omega1]) for j in range(3)]
    J, Jt = sum(v.dot(v) for v in dw), 2*sum(v.dot(t) for v, t in zip(dw, dwt))
    ri = -2*nu*J/s
    rit = (-2*w.dot(P*w)-2*nu*Jt)/s-ri*st/s
    paid0 = 2*w.dot(b*w)/s
    paid1 = 2*(wt.dot(b*w)+w.dot(mat(BH1)*w)+w.dot(b*wt))/s-paid0*st/s
    ordinary1 = 2*(wt.dot(b*w)+w.dot(mat(f.jac(u1))*w)+w.dot(b*wt)-nu*Jt)/s-(paid0+ri)*st/s
    zero(paid1+rit-ordinary1, (label, "complete physical reaction split at first derivative"))
    if label == "pressure_start":
        zero(ri, "pressure-start remaining reward is initially zero")
        zero(rit-sp.Rational(64, 3), "pressure-start remaining reward genuinely becomes positive")
        zero(paid1, "pressure-start new strain belongs to the impulse channel")
    if label == "original_maximum":
        zero(rit-16, "original maximum pressure-impulse activation")
        zero(paid1+12, "original passive reaction decreases")
    return dict(fixture=label, original_magnitude_bound_squared=str(m2),
                original_vorticity_regularizer=str(delta), potential=str(phi),
                control_square_margin=str(margin), remaining_initial=str(sp.factor(ri)),
                remaining_time_rate=str(sp.factor(rit)), passive_time_rate=str(sp.factor(paid1)),
                complete_original_jets=2)


def carrier(parent, amplitude, n, background):
    return [f.add(f.scale(amplitude*n, f.mul(r.mode((0, 0, n), 1), v)), b)
            for v, b in zip(parent, background)]


def main():
    pointwise_squares()
    shear = exact_shear()
    forced = forced_shear_contrast()
    simple = carrier(r.c.simple_parent(), Q(16), 4, [{}, {}, {}])
    background = r.ns.vector_scale(Q(-20000), r.ns.nonlinear(r.c.resonant_parent()))
    resonant = carrier(r.c.resonant_parent(), Q(200), 4, background)
    cases = [("original_maximum", r.record_datum(Q(4), Q(8)), (0, 0, 0)),
             ("pressure_start", r.counterstrain_datum(Q(4), Q(8)), (0, 0, 0)),
             ("original_simple_carrier", simple, (1, 1, 1)),
             ("original_resonant_carrier", resonant, (1, 1, 1))]
    results = [actual_history_jets(u, Q(1), name, point) for name, u, point in cases]
    print(json.dumps(dict(status="all exact checks passed", exact_shear=shear, forced_contrast=forced, fixtures=results,
                         scope="full original jets and control algebra; comparison and path integration analytic"), indent=2))


if __name__ == "__main__":
    main()
