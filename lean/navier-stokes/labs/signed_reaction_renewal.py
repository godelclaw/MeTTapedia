#!/usr/bin/env python3
"""Complete signed-reaction renewal on actual unforced NS initial jets.

Fourier products retain every output, and pressure is the canonical periodic
pressure. Quotients are differentiated independently from the velocity's full
NS tangent. PDE interval arguments and the general identities in README.md
remain analytic; this is neither a time integrator nor a Lean certificate.
"""

import json

import sympy as sp

import covariance_velocity_defect as c
from metric_loss_bellman import zero
from reciprocal_pattern_cycles import mode

f, ns, Q = c.f, c.s, c.Q


def at(poly, eighths):
    root = (1+sp.I)/sp.sqrt(2)
    return sp.simplify(sp.expand(sum(
        (sp.Rational(str(a.x))+sp.I*sp.Rational(str(a.y)))
        * root**(sum(k[j]*eighths[j] for j in range(3)) % 8)
        for k, a in poly.items())))


def record_datum(a, b):
    sx, sy, sz = (mode(tuple(int(i == j) for i in range(3)), 1, True) for j in range(3))
    cx, _, cz = (mode(tuple(int(i == j) for i in range(3)), 1) for j in range(3))
    return [f.add(f.scale(-a, f.mul(sx, cz)), f.scale(-b, sy)),
            f.scale(b, sx), f.scale(a, f.mul(cx, sz))]


def counterstrain_datum(a, b):
    sx, sy, sz = (mode(tuple(int(i == j) for i in range(3)), 1, True) for j in range(3))
    cx, cy, cz = (mode(tuple(int(i == j) for i in range(3)), 1) for j in range(3))
    return [f.add(f.scale(-a, f.mul(sx, cz)), f.scale(-b, sy)),
            f.add(f.scale(b, sx), f.scale(a, f.mul(sy, cz))),
            f.scale(a, f.mul(f.add(cx, f.scale(-1, cy)), sz))]


def reaction_jet(u, nu, delta, eighths, label):
    ev = lambda p: at(p, eighths)
    vec = lambda v: sp.Matrix([ev(p) for p in v])
    mat = lambda M: sp.Matrix([[ev(p) for p in row] for row in M])
    B = f.jac(u)
    omega = f.curl(u)
    pressure = f.green(f.trace(f.matmul(B, B)))
    f.equal(pressure, c.pressure(u), (label, "independent canonical pressure"))
    ut = [f.add(f.scale(nu, f.lap(u[i])), f.scale(-1, f.adv(u, u[i])),
                f.scale(-1, f.diff(pressure, i))) for i in range(3)]
    f.equal(f.trace(B), {}, (label, "divergence free"))
    f.equal(f.trace(f.jac(ut)), {}, (label, "full tangent divergence free"))
    wt, Bt = f.curl(ut), f.jac(ut)
    zeta = f.matvec(B, omega)
    g = f.dot(omega, zeta)
    d = [[f.diff(p, j) for p in omega] for j in range(3)]
    dt = [[f.diff(p, j) for p in wt] for j in range(3)]
    J = f.add(*(f.dot(v, v) for v in d))
    s = f.add(f.dot(omega, omega), {f.ORIGIN: f.QQ_I(delta)})
    st = f.scale(2, f.dot(omega, wt))
    gt = f.add(f.dot(wt, zeta), f.dot(omega, f.matvec(Bt, omega)),
               f.dot(omega, f.matvec(B, wt)))
    Jt = f.scale(2, f.add(*(f.dot(v, w) for v, w in zip(d, dt))))
    U, W, BV, P = vec(u), vec(omega), mat(B), mat(f.hess(pressure))
    sv, gv, jv = ev(s), ev(g), ev(J)
    z = BV*W
    dw = [vec(v) for v in d]
    dB = [mat([[f.diff(p, j) for p in row] for row in B]) for j in range(3)]
    ddw = [[vec([f.diff(p, k) for p in d[j]]) for k in range(3)] for j in range(3)]
    # A and C are the two distinct gradient/transport contractions.
    A = sum(dw[j].dot(dB[j]*W) for j in range(3))
    T = sum(v.dot(BV*v) for v in dw)
    C = sum(BV[k, j]*dw[j].dot(dw[k]) for j in range(3) for k in range(3))
    H = sum(v.dot(v) for row in ddw for v in row)
    def D(poly, tangent):
        return ev(tangent)+U.dot(vec(f.grad(poly)))-nu*ev(f.lap(poly))
    expected_g = z.dot(z)-W.dot(P*W)-2*nu*T-4*nu*A
    expected_J = 2*(A+T-C)-2*nu*H
    zero(D(g, gt)-expected_g, (label, "complete cubic production"))
    zero(D(J, Jt)-expected_J, (label, "complete vorticity-gradient production"))
    v = 2*(gv-nu*jv)/sv
    zero(D(s, st)-v*sv, (label, "ordinary magnitude reaction"))
    ds, ls = vec(f.grad(s)), ev(f.lap(s))
    results = []
    for kappa in (-1, 0, 1, 4):
        N = f.scale(2, f.add(g, f.scale(kappa*nu, J)))
        Nt = f.scale(2, f.add(gt, f.scale(kappa*nu, Jt)))
        nv, ntv, dn = ev(N), ev(Nt), vec(f.grad(N))
        q = nv/sv
        qt = ntv/sv-nv*ev(st)/sv**2
        dq = dn/sv-nv*ds/sv**2
        lq = ev(f.lap(N))/sv-nv*ls/sv**2-2*dn.dot(ds)/sv**2+2*nv*ds.dot(ds)/sv**3
        covariant_rate = qt+(U-2*nu*ds/sv).dot(dq)-nu*lq
        expected = 2*(z.dot(z)-W.dot(P*W))/sv + (
            4*nu*((kappa-2)*A+(kappa-1)*T-kappa*C)-4*kappa*nu**2*H)/sv
        zero(covariant_rate+v*q-expected, (label, kappa, "independent quotient evolution"))
        if kappa >= -1:
            zero(q-v-2*(kappa+1)*nu*jv/sv, (label, kappa, "correction controls reward"))
        results.append(dict(kappa=kappa, corrected=str(sp.factor(q)),
                            time_rate=str(sp.factor(qt)),
                            complete_source=str(sp.factor(expected))))
    return dict(fixture=label, nu=str(nu), delta=str(delta), ordinary=str(sp.factor(v)),
                pressure_work=str(sp.factor(W.dot(P*W))),
                stretching_square=str(sp.factor(z.dot(z))),
                gradient_mixed=str(sp.factor(A)), gradient_strain=str(sp.factor(T)),
                transport_commutator=str(sp.factor(C)), second_gradient_square=str(sp.factor(H)),
                corrections=results)


def symbolic_record_family():
    x, y, z = sp.symbols("x y z", real=True)
    a, nu = sp.symbols("a nu", positive=True)
    kappa = sp.symbols("kappa", real=True)
    coords = (x, y, z)
    origin = {q: 0 for q in coords}
    grad = lambda p: sp.Matrix([sp.diff(p, q) for q in coords])
    lap = lambda p: sum(sp.diff(p, q, 2) for q in coords)
    curl = lambda v: sp.Matrix([sp.diff(v[2], y)-sp.diff(v[1], z),
                               sp.diff(v[0], z)-sp.diff(v[2], x),
                               sp.diff(v[1], x)-sp.diff(v[0], y)])
    u = a*sp.Matrix([-sp.sin(x)*sp.cos(z)-2*sp.sin(y),
                     2*sp.sin(x), sp.cos(x)*sp.sin(z)])
    B, omega = u.jacobian(coords), curl(u)
    p = a*a*(sp.cos(2*x)+sp.cos(2*z))/4-4*a*a*sp.cos(x)*sp.cos(y)
    zero(sp.trigsimp(-lap(p)-sp.trace(B*B)), "family canonical pressure Poisson equation")
    ut = nu*u.applyfunc(lap)-B*u-grad(p)
    wt, Bt = curl(ut), ut.jacobian(coords)
    zero(sp.trigsimp(sp.trace(Bt)), "family actual tangent is solenoidal")
    g = omega.dot(B*omega)
    G = omega.jacobian(coords)
    J = sum(v*v for v in G)
    s = omega.dot(omega)+16*a*a
    gt = wt.dot(B*omega)+omega.dot(Bt*omega)+omega.dot(B*wt)
    Jt = 2*sum(v*w for v, w in zip(G, wt.jacobian(coords)))
    st = 2*omega.dot(wt)
    cx, cy, cz = sp.cos(x), sp.cos(y), sp.cos(z)
    denominator = (1-cx*cx)*(1-cz*cz)+(cx+cy)**2+4
    gradient = 2+cz*cz-cy*cy-2*cx*cx*cz*cz
    zero(sp.trigsimp(s-4*a*a*denominator), "family physical denominator")
    zero(sp.trigsimp(J-4*a*a*gradient), "family physical gradient")
    zero(sp.trigsimp(g-4*a**3*cx*cz*(cx+cy)**2), "family physical stretching")
    numerator = 2*g+2*kappa*nu*J
    qt = ((2*gt+2*kappa*nu*Jt)*s-numerator*st)/s**2
    zero(qt.subs(origin)-a*(a-3*nu), "family full initial time rate for every correction")
    alpha_rate = (gt*omega.dot(omega)-g*st)/omega.dot(omega)**2
    zero(alpha_rate.subs(origin)+2*nu*a,
         "unregularized longitudinal strain initially decays in the maximum example")
    zero(Jt.subs(origin), "derivative correction has zero first time rate at the maximum")
    zero(sp.diff(p, z, 2).subs(origin)+a*a, "actual negative axial pressure Hessian")
    # These are the two certificates used by the Lean whole-domain bound.
    X, Y, Z = sp.symbols("X Y Z", real=True)
    w, t = (X+Y)**2, (1-X*X)*(1-Z*Z)
    H = t+4+(1-2*X*Z)*w
    Jshape = 2+Z*Z-Y*Y-2*X*X*Z*Z
    low = t+(1-w)+(1-Z*Z)+Y*Y+2*X*X*Z*Z+2*(1-X*Z)*w
    high = 3*t+(X-Y)**2+(X-Z)**2+(2-X*X-Y*Y)+2*(1-X*Z)*(w-1)
    zero(H-Jshape-low, "certificate when (X+Y)^2 <= 1")
    zero(H-Jshape-high, "certificate when (X+Y)^2 >= 1")
    return dict(original_delta="16 a^2 = ||omega_0||_infinity^2",
                initial_corrected_maximum="a, when kappa >= 0 and a >= 2 kappa nu",
                initial_time_rate="a (a-3 nu), independent of kappa",
                unregularized_stretching_rate_derivative="-2 nu a; the corrected-rate increase includes regularizer activation",
                all_coefficients="choose a=(2 kappa+4) nu for any kappa>=0, nu>0",
                scope="global initial maximum and actual initial tangent; local PDE time passage analytic")


def symbolic_pressure_start():
    x, y, z = sp.symbols("x y z", real=True)
    a, nu = sp.symbols("a nu", positive=True)
    kappa = sp.symbols("kappa", real=True)
    coords = (x, y, z)
    origin = {q: 0 for q in coords}
    grad = lambda p: sp.Matrix([sp.diff(p, q) for q in coords])
    lap = lambda p: sum(sp.diff(p, q, 2) for q in coords)
    curl = lambda v: sp.Matrix([sp.diff(v[2], y)-sp.diff(v[1], z),
                               sp.diff(v[0], z)-sp.diff(v[2], x),
                               sp.diff(v[1], x)-sp.diff(v[0], y)])
    u = a*sp.Matrix([-sp.sin(x)*sp.cos(z)-2*sp.sin(y),
                     2*sp.sin(x)+sp.sin(y)*sp.cos(z),
                     (sp.cos(x)-sp.cos(y))*sp.sin(z)])
    B, omega = u.jacobian(coords), curl(u)
    p = a*a*(sp.cos(2*x)+sp.cos(2*y)+2*sp.cos(2*z))/4-a*a*sp.cos(x)*sp.cos(y)*(sp.Rational(9, 2)+sp.cos(2*z)/6)
    zero(sp.trigsimp(-lap(p)-sp.trace(B*B)), "counterstrain canonical pressure Poisson equation")
    ut = nu*u.applyfunc(lap)-B*u-grad(p)
    wt, Bt = curl(ut), ut.jacobian(coords)
    for value in u.subs(origin):
        zero(value, "counterstrain stagnation point")
    for value in (B*omega).subs(origin):
        zero(value, "counterstrain initially has no stretching vector at the receiver")
    for value in omega.jacobian(coords).subs(origin):
        zero(value, "counterstrain initially has zero vorticity gradient at the receiver")
    zero(sp.diff(p, z, 2).subs(origin)+4*a*a/3, "counterstrain compressive pressure")
    alpha_t = (omega.dot(Bt*omega)/omega.dot(omega)).subs(origin)
    zero(alpha_t-4*a*a/3, "actual longitudinal strain is generated, not a regularizer effect")
    g = omega.dot(B*omega)
    gt = wt.dot(B*omega)+omega.dot(Bt*omega)+omega.dot(B*wt)
    G, Gt = omega.jacobian(coords), wt.jacobian(coords)
    J, Jt = sum(v*v for v in G), 2*sum(v*w for v, w in zip(G, Gt))
    st = 2*omega.dot(wt)
    s = omega.dot(omega)+16*a*a
    qt = ((2*gt+2*kappa*nu*Jt)*s-(2*g+2*kappa*nu*J)*st)/s**2
    zero(qt.subs(origin)-4*a*a/3, "full counterstrain corrected derivative for every coefficient")
    H = sum(sp.diff(v, q)**2 for v in G for q in coords)
    zero(H.subs(origin)-24*a*a, "counterstrain complete second-gradient square")
    source_at_origin = (-2*omega.dot(sp.hessian(p, coords)*omega)-4*kappa*nu**2*H)/s
    zero(source_at_origin.subs(origin)-(4*a*a/3-3*kappa*nu**2),
         "counterstrain pressure versus full corrected diffusion")
    zero(st.subs(origin)+32*nu*a*a, "vorticity initially decays at this receiver")
    cx, cy, cz = sp.cos(x), sp.cos(y), sp.cos(z)
    shape = (2-cx*cx-cy*cy)*(1-cz*cz)+(cx+cy)**2
    zero(sp.trigsimp(omega.dot(omega)-4*a*a*shape), "counterstrain whole-domain vorticity")
    X, Y, Z = sp.symbols("X Y Z", real=True)
    zero(4-((2-X*X-Y*Y)*(1-Z*Z)+(X+Y)**2)
         -(2*(1-X*Y)+(2-X*X-Y*Y)*Z*Z), "counterstrain original maximum certificate")
    return dict(original_delta="16 a^2 = ||omega_0||_infinity^2", initial_reaction="0",
                initial_pressure_zz="-4 a^2/3", initial_true_strain_rate="4 a^2/3",
                corrected_source="4 a^2/3 - 3 kappa nu^2",
                scope="new positive stretching on a local actual interval, not repeated or unbounded renewal")


def main():
    fixtures = [reaction_jet(record_datum(Q(4), Q(8)), Q(1), Q(256), (0, 0, 0), "original_maximum"),
                reaction_jet(counterstrain_datum(Q(4), Q(8)), Q(1), Q(256), (0, 0, 0), "pressure_start"),
                reaction_jet([mode((0, 1, 0), 2, True), {}, {}], Q(1), Q(4), (0, 2, 0), "heat_shear"),
                reaction_jet(ns.vector_scale(Q(64), ns.nonlinear(c.simple_parent())),
                             Q(1), Q(10**12), (1, 1, 1), "inherited_simple"),
                reaction_jet(ns.vector_scale(Q(-10000), ns.nonlinear(c.resonant_parent())),
                             Q(1), Q(10**12), (1, 1, 1), "inherited_resonant")]
    family = symbolic_record_family()
    pressure_start = symbolic_pressure_start()
    print(json.dumps(dict(status="all exact checks passed", fixtures=fixtures, family=family,
                         pressure_start=pressure_start), indent=2))


if __name__ == "__main__":
    main()
