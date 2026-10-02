#!/usr/bin/env python3
"""Exact gauges for the actual transported-metric loss and its Bellman budget.

PDE comparison, stochastic verification and heat-kernel estimates in README.md
are analytic. These fixtures check independent jets and an exact NS shear.
"""

import json

import sympy as s


def zero(value, label):
    value = s.factor(s.cancel(s.expand(value)))
    if value != 0:
        value = s.simplify(value)
    if value != 0:
        raise AssertionError((label, value))


def gauge_jets():
    x, y, z = s.symbols("x y z", real=True)
    nu, hazard = s.symbols("nu hazard", positive=True)
    kt = s.symbols("k_t", real=True)
    coordinates = (x, y, z)
    origin = {c: 0 for c in coordinates}
    grad = lambda f: s.Matrix([s.diff(f, c) for c in coordinates])
    lap = lambda f: sum(s.diff(f, c, 2) for c in coordinates)
    div = lambda v: sum(s.diff(v[j], c) for j, c in enumerate(coordinates))
    at = lambda f: s.simplify(f.subs(origin))
    u = s.Matrix([1+x+2*y, 2-y+z, -1+x])
    zero(div(u), "physical drift is incompressible")
    h = 3+2*x-y+z+x*x+2*y*y-z*z+x*y
    passive = 5-x+2*y+z+3*x*x+y*z+z*z
    phi = 2-2*x+3*y+x*z+x*x
    k = 1+x-y+z+x*y+2*z*z
    ht = nu*lap(h)-u.dot(grad(h))-hazard*h
    pt = nu*lap(passive)-u.dot(grad(passive))
    w = u-2*nu*grad(h)/h
    ratio = passive/h
    ratio_t = (pt*h-passive*ht)/h**2
    zero(at(ratio_t+w.dot(grad(ratio))-nu*lap(ratio)-hazard*ratio),
         "passive-to-metric ratio from independently differentiated jets")
    # The backward density becomes a killed incompressible diffusion.
    phi_t = -u.dot(grad(phi))-nu*lap(phi)+hazard*phi
    psi = h*phi
    psi_t = ht*phi+h*phi_t
    zero(at(psi_t+div(w*psi)+nu*lap(psi)), "full adjoint density transformation")
    # Keep the reaction when undoing the quotient; it cannot disappear twice.
    Lk = kt+w.dot(grad(k))-nu*lap(k)
    product_rate = ht*k+h*kt+u.dot(grad(h*k))-nu*lap(h*k)
    zero(at(product_rate-h*(Lk-hazard*k)), "full product gauge with its reaction")


def bellman_margin():
    K, g, hazard, nu = s.symbols("K g hazard nu", positive=True)
    power = 2*K/(2*K-1)
    F = 2*g-1
    # 1<=g<=K makes this difference nonnegative.
    zero(2*hazard*g-power*hazard*F-2*hazard*(K-g)/(2*K-1),
         "affine barrier leaves an explicit nonnegative margin")
    zero(2*hazard*g-s.Rational(4, 3)*hazard*F
         -s.Rational(2, 3)*hazard*(2-g), "datum-normalized four-thirds margin")
    zero(1/(4*nu)-s.Rational(3, 16)/nu-s.Rational(1, 16)/nu,
         "control cost is split once, without duplicate payment")
    grad = s.Matrix(s.symbols("d0:3", real=True))
    beta = s.Matrix(s.symbols("beta0:3", real=True))
    zero(grad.dot(beta)-power*nu*grad.dot(grad)-beta.dot(beta)/(4*power*nu)
         +(beta-2*power*nu*grad).dot(beta-2*power*nu*grad)/(4*power*nu),
         "sampling-control square completion")


def exact_shear():
    # q=exp(-2 nu t), c=cos y; derivatives are exact rational functions.
    A, nu, delta, q = s.symbols("A nu delta q", positive=True)
    c = s.symbols("c", real=True)
    time = lambda f: -2*nu*q*s.diff(f, q)
    lap = lambda f: (1-c*c)*s.diff(f, c, 2)-c*s.diff(f, c)
    grad_pair = lambda f, g: (1-c*c)*s.diff(f, c)*s.diff(g, c)
    physical = A*A*q*c*c
    h = delta+physical
    passive = delta+A*A*(1+q*q*(2*c*c-1))/2
    loss = A*A*q*(1-c*c)
    hazard = 2*nu*loss/h
    zero(time(h)-nu*lap(h)+hazard*h, "actual shear metric loss")
    zero(time(passive)-nu*lap(passive), "actual passive original-data scalar")
    zero(passive.subs(q, 1)-h.subs(q, 1), "original gauge starts at one")
    zero(passive-h-A*A*(1-q)*(1-q*(2*c*c-1))/2,
         "nonnegative shear passive-minus-metric gap")
    L = lambda f: time(f)-nu*lap(f)-2*nu*grad_pair(h, f)/h
    g = passive/h
    zero(L(g)-hazard*g, "full-time actual gauge equation")
    F = 2*g-1
    # Independently differentiate Phi=(3/4) log F without exponential simplification.
    phi_time = s.Rational(3, 4)*time(F)/F
    phi_lap = s.Rational(3, 4)*(lap(F)/F-grad_pair(F, F)/F**2)
    phi_drift = -s.Rational(3, 2)*nu*grad_pair(h, F)/(h*F)
    phi_grad_sq = s.Rational(9, 16)*grad_pair(F, F)/F**2
    margin = phi_time-nu*phi_lap+phi_drift-s.Rational(4, 3)*nu*phi_grad_sq-hazard
    zero(margin-hazard*(2-g)/(2*F), "actual four-thirds HJB supersolution margin")
    ordinary = -2*nu*loss/(physical+delta)
    zero(ordinary+hazard, "full shear conversion still equals one")
    return {"passive_scalar": str(passive), "hazard": str(hazard),
            "full_reaction": "0", "gauge_limit": "1 + A^2/(2 delta)"}


def actual_initial_obstruction():
    # The already verified periodic unforced initial datum; this is its
    # curl tangent, not a prescribed time evolution of the initial formula.
    x, y, z = s.symbols("x y z", real=True)
    a, b, nu, delta = s.symbols("a b nu delta", positive=True)
    coordinates = (x, y, z)
    u = s.Matrix([-a*s.sin(x)*s.cos(z)-b*s.sin(y),
                  b*s.sin(x), a*s.cos(x)*s.sin(z)])
    curl = lambda v: s.Matrix([s.diff(v[2], y)-s.diff(v[1], z),
                              s.diff(v[0], z)-s.diff(v[2], x),
                              s.diff(v[1], x)-s.diff(v[0], y)])
    lap = lambda f: sum(s.diff(f, c, 2) for c in coordinates)
    B = u.jacobian(coordinates)
    omega = curl(u)
    tangent = -curl(B*u)+nu*omega.applyfunc(lap)
    origin = {c: 0 for c in coordinates}
    for v in (tangent+omega.jacobian(coordinates)*u-B*omega-nu*omega.applyfunc(lap)):
        zero(s.trigsimp(v), "actual initial vorticity equation")
    physical = omega.dot(omega)
    loss = sum(v*v for v in omega.jacobian(coordinates))  # Original M=I.
    hazard = 2*nu*loss/(physical+delta)
    ordinary = (2*omega.dot(B*omega)-2*nu*loss)/(physical+delta)
    zero(hazard.subs(origin), "metric loss initially vanishes at the symmetry point")
    zero(ordinary.subs(origin)-8*a*b*b/(4*b*b+delta),
         "ordinary stretching remains positive where the paid hazard vanishes")
    # |omega0|^2 <= 4(a^2+b^2) on the entire torus. Thus this example
    # also satisfies the datum-fixed regularizer condition used above.
    datum_regularizer = 4*(a*a+b*b)
    normalized = s.factor(ordinary.subs(origin).subs(delta, datum_regularizer))
    zero(normalized-2*a*b*b/(a*a+2*b*b),
         "unpaid positive strain survives the actual regularizer choice")
    return {"arbitrary_delta": str(s.factor(ordinary.subs(origin))),
            "datum_fixed_delta": str(normalized)}


if __name__ == "__main__":
    gauge_jets()
    bellman_margin()
    shear = exact_shear()
    remaining = actual_initial_obstruction()
    print(json.dumps({
        "status": "all exact checks passed",
        "datum_choice": "delta > 0, delta >= ||omega0||_infinity^2",
        "metric_bellman_allowance": "(3/4) log 3",
        "control_cost_used": "3 |beta|^2/(16 nu)",
        "control_cost_remaining": "|beta|^2/(16 nu)",
        "shear": shear,
        "unpaid_initial_reaction": remaining,
        "scope": "analytic all-prefix physical/Bellman estimate, exact jet and shear checks; no new Lean certification",
    }, indent=2))
