#!/usr/bin/env python3
"""Pressure-impulse boundary flux, receiver entropy, and actual NS jets.

All identities are exact. The actual positive-time and stochastic Taylor
arguments are analytic in README.md; finite time jets are not solutions.
The original passive parent is retained with the full canonical pressure.
"""

import json

import sympy as sp

import passive_parent_bellman as parent
import pressure_impulse_history as ph
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f, Q, r = parent.f, parent.Q, parent.r


def square_identities():
    nu = sp.symbols("nu", positive=True)
    n = sp.Matrix(sp.symbols("n0:3", real=True))
    impulse = sp.Matrix(sp.symbols("i0:3", real=True))
    A = sp.Matrix(3, 3, sp.symbols("a0:9", real=True))
    W = sp.Matrix(3, 3, sp.symbols("w0:9", real=True))
    W[2, 2] = -W[0, 0]-W[1, 1]  # div omega=0, not div n=0.
    psi = sp.symbols("psi", real=True)
    grad_psi = sp.Matrix(sp.symbols("p0:3", real=True))
    gamma = sp.Matrix(sp.symbols("b0:3", real=True))
    d, radius = impulse.dot(n), n.dot(n)
    reflected = impulse-2*d*n
    Dn = W-n*(W.T*n).T
    flux = 2*d*n
    div_flux = 2*((A.T*n+Dn.T*impulse).dot(n)+d*sp.trace(Dn))
    normW = sum(v*v for v in W)
    reward = -2*n.dot(A*n)-2*nu*normW
    zero(reward+div_flux-2*reflected.dot(W*n)+2*nu*normW,
         "complete impulse flux including the soft direction's divergence")
    V = radius*(reflected.dot(reflected)+16*d*d)/nu
    div_weighted_flux = psi*psi*div_flux+2*psi*flux.dot(grad_psi)
    strain_square = 4*nu*sum(v*v for v in
                            (psi*W-psi*reflected*n.T/(2*nu)))
    density_square = nu*(grad_psi-4*psi*d*n/nu).dot(grad_psi-4*psi*d*n/nu)
    zero(2*reward*psi*psi-nu*grad_psi.dot(grad_psi)+2*div_weighted_flux
         -V*psi*psi+strain_square+density_square,
         "exact spatial form and boundary flux")
    entropy_rate = -4*nu*grad_psi.dot(grad_psi)+2*psi*gamma.dot(grad_psi)
    control_square = (psi*gamma-2*nu*grad_psi).dot(psi*gamma-2*nu*grad_psi)/(4*nu)
    zero((2*reward-gamma.dot(gamma)/(4*nu))*psi*psi
         +entropy_rate/2+2*div_weighted_flux-V*psi*psi
         +strain_square+density_square+control_square,
         "joint entropy and control price retain all three squares")
    score = sp.Matrix(sp.symbols("k0:3", real=True))
    relative_gradient = 2*grad_psi-psi*score  # psi grad log(rho/q)
    relative_entropy_rate = -nu*relative_gradient.dot(relative_gradient) + psi*gamma.dot(relative_gradient)
    relative_density_square = nu*(relative_gradient-8*psi*d*n/nu).dot(relative_gradient-8*psi*d*n/nu)/4
    relative_control_square = (psi*gamma-nu*relative_gradient).dot(psi*gamma-nu*relative_gradient)/(4*nu)
    zero((2*reward-gamma.dot(gamma)/(4*nu))*psi*psi
         +relative_entropy_rate/2+2*div_weighted_flux
         -(V+4*d*n.dot(score))*psi*psi
         +strain_square+relative_density_square+relative_control_square,
         "relative entropy retains the actual reference-kernel score")
    gram = radius*impulse.dot(impulse)-d*d
    zero(17*impulse.dot(impulse)-nu*V
         -(1-radius)*(4*radius**2+16*radius+17)*impulse.dot(impulse)
         -radius*(12+4*radius)*gram,
         "amplitude upper bound uses radius <= 1 and the Gram square")


def inversion(poly):
    return {tuple(-j for j in k): a for k, a in poly.items()}


def history_fixture(u0, label, point):
    nu = Q(1)
    jets, pressures = velocity_time_jets(u0, nu, 2)
    u, ut, utt = jets
    Ht = ph.vector_transport(u, u, nu)
    Htt = [f.add(v, f.scale(-1, f.adv(ut, h)))
           for v, h in zip(ph.vector_transport(u, Ht, nu), u)]
    It = [f.add(h, f.scale(-1, v)) for h, v in zip(Ht, ut)]
    Itt = [f.add(h, f.scale(-1, v)) for h, v in zip(Htt, utt)]
    ph.vectors_equal(It, f.grad(pressures[0]), (label, "canonical initial impulse"))
    ph.vectors_equal(Itt, [f.add(v, w) for v, w in
                          zip(ph.vector_transport(u, It, nu), f.grad(pressures[1]))],
                     (label, "changing drift and pressure retained"))
    ev = lambda p: r.at(p, point)
    vec = lambda v: sp.Matrix([ev(p) for p in v])
    mat = lambda rows: sp.Matrix([[ev(p) for p in row] for row in rows])
    omega, wt = f.curl(u), f.curl(ut)
    dw, dwt = f.jac(omega), f.jac(wt)
    J = f.add(*(f.mul(p, p) for row in dw for p in row))
    Jt = f.scale(2, f.add(*(f.mul(p, q) for row, rowt in zip(dw, dwt)
                           for p, q in zip(row, rowt))))
    delta = Q(256) if label in ("pressure_start", "original_maximum") else parent.original_bound_sq(omega)
    s = f.add(f.dot(omega, omega), {f.ORIGIN: f.QQ_I(delta)})
    st = f.scale(2, f.dot(omega, wt))
    w, P, sv, jv = vec(omega), mat(f.hess(pressures[0])), ev(s), ev(J)
    ds, dj = vec(f.grad(s)), vec(f.grad(J))
    ri = -2*nu*jv/sv
    rit = -2*w.dot(P*w)/sv-2*nu*ev(Jt)/sv+2*nu*jv*ev(st)/sv**2
    gradri = -2*nu*(dj/sv-jv*ds/sv**2)
    lapri = -2*nu*(ev(f.lap(J))/sv-jv*ev(f.lap(s))/sv**2
                   -2*dj.dot(ds)/sv**2+2*jv*ds.dot(ds)/sv**3)
    log_second = sp.factor(rit+nu*lapri-vec(u).dot(gradri))
    # The amplitude potential has zero first two Feynman--Kac time jets.
    # Its third jet is 2 |grad p0|^2/nu. At a symmetric centre that also vanishes.
    impulse_rate_sq = f.dot(It, It)
    amplitude_third = 2*ev(impulse_rate_sq)/nu
    amplitude_fourth = (2*ev(f.lap(impulse_rate_sq))
                        -2*vec(u).dot(vec(f.grad(impulse_rate_sq)))/nu
                        +6*vec(It).dot(vec(Itt))/nu)
    if label == "pressure_start":
        for j, field in enumerate(u):
            f.equal(inversion(field), f.scale(-1, field), (label, j, "original odd symmetry"))
        for order, field in enumerate(jets):
            for j, p in enumerate(field):
                f.equal(inversion(p), f.scale(-1, p), (label, order, j, "actual odd velocity jets"))
        for order, field in enumerate((It, Itt)):
            for j, p in enumerate(field):
                f.equal(inversion(p), f.scale(-1, p), (label, order, j, "original odd impulse jets"))
        zero(ri, "remaining reaction initially vanishes at the symmetry centre")
        zero(rit-sp.Rational(64, 3), "actual pressure-start reaction derivative")
        zero(lapri+3, "Brownian sampling sees the full negative diffusion nearby")
        zero(log_second-sp.Rational(55, 3), "positive complete stochastic second coefficient")
        zero(amplitude_third, "impulse-amplitude history has zero cubic coefficient at the centre")
        zero(amplitude_fourth/24-sp.Rational(11008, 9), "quartic amplitude-history coefficient")
    # A polynomial from the two complete original jets is a kinematic probe,
    # not an asserted positive-time solution. Its divergence is still exactly zero.
    eps = Q(1, 17)
    probe = [f.add(p, f.scale(eps, q), f.scale(eps*eps/2, z)) for p, q, z in zip(u, ut, utt)]
    impulse = [f.add(f.scale(eps, p), f.scale(eps*eps/2, q)) for p, q in zip(It, Itt)]
    f.equal(f.trace(f.jac(probe)), {}, (label, "complete jet probe remains solenoidal"))
    wp = vec(f.curl(probe))
    scale = sp.sqrt(wp.dot(wp)+delta)
    n, W = wp/scale, mat(f.jac(f.curl(probe)))/scale
    i, A = vec(impulse), mat(f.jac(impulse))
    d = i.dot(n)
    R = i-2*d*n
    Dn = W-n*(W.T*n).T
    flux_div = 2*((A.T*n+Dn.T*i).dot(n)+d*sp.trace(Dn))
    reward = -2*n.dot(A*n)-2*nu*sum(v*v for v in W)
    zero(reward+flux_div-2*R.dot(W*n)+2*nu*sum(v*v for v in W),
         (label, "nonzero inherited impulse flux with all original outputs"))
    return dict(fixture=label, remaining_initial=str(sp.factor(ri)),
                remaining_time_rate=str(sp.factor(rit)),
                remaining_log_moment_quadratic_coefficient=str(log_second),
                amplitude_moment_cubic_coefficient=str(sp.factor(amplitude_third/6)),
                amplitude_moment_quartic_coefficient=str(sp.factor(amplitude_fourth/24)),
                original_regularizer=str(delta), complete_jets=2,
                spatial_probe="two-jet polynomial only; not a solution at time 1/17")


def main():
    square_identities()
    simple = parent.carrier(r.c.simple_parent(), Q(16), 4, [{}, {}, {}])
    background = r.ns.vector_scale(Q(-20000), r.ns.nonlinear(r.c.resonant_parent()))
    resonant = parent.carrier(r.c.resonant_parent(), Q(200), 4, background)
    cases = [(r.counterstrain_datum(Q(4), Q(8)), "pressure_start", (0, 0, 0)),
             (r.record_datum(Q(4), Q(8)), "original_maximum", (0, 0, 0)),
             (simple, "original_simple_carrier", (1, 1, 1)),
             (resonant, "original_resonant_carrier", (1, 1, 1))]
    results = [history_fixture(*case) for case in cases]
    shear = parent.exact_shear()
    print(json.dumps(dict(status="all exact checks passed", fixtures=results,
                         exact_shear=shear,
                         scope="complete spatial squares and actual initial jets; PDE intervals, path moments and entropy integration analytic"), indent=2))


if __name__ == "__main__":
    main()
