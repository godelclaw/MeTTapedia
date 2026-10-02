#!/usr/bin/env python3
"""Exact fixtures for a classical vorticity reserve and its conversion limit.

The integral estimate reuses Qian's vorticity--energy argument. Smooth PDE
existence, integration, comparison and the concentration argument are analytic;
these finite checks do not certify those theorems.
"""

import json

import sympy as s


def zero(value, label):
    value = s.factor(s.trigsimp(s.expand(value)))
    if value != 0:
        value = s.simplify(value)
    if value != 0:
        raise AssertionError((label, value))


def vector_zero(value, label):
    for i, entry in enumerate(value):
        zero(entry, (label, i))


def magnitude_jet():
    """Differentiate the norm from independent spatial and temporal jets."""
    t, x = s.symbols("t x", real=True)
    nu, delta = s.symbols("nu delta", positive=True)
    w = s.Matrix([2, -3, 6])
    B = s.Matrix([[1, 2, 3], [-3, 0, 1], [2, -1, -1]])
    first = [s.Matrix([1, 3, -1]), s.Matrix([2, 0, 1]), s.Matrix([-1, 2, 2])]
    second = [s.Matrix([2, -1, 3]), s.Matrix([0, 1, 4]), s.Matrix([3, -2, 0])]
    wt = w + t * (B * w + nu * sum(second, s.zeros(3, 1)))
    temporal = s.diff(s.sqrt(delta + wt.dot(wt)), t).subs(t, 0)
    laplacian = 0
    angular = 0
    for g, h in zip(first, second):
        wx = w + x * g + x**2 * h / 2
        laplacian += s.diff(s.sqrt(delta + wx.dot(wx)), x, 2).subs(x, 0)
        angular += g.dot(g) / s.sqrt(delta + w.dot(w))
        angular -= w.dot(g)**2 / (delta + w.dot(w))**s.Rational(3, 2)
    zero(temporal - nu * laplacian - w.dot(B * w) / s.sqrt(delta + w.dot(w))
         + nu * angular, "regularized magnitude from independent jets")
    n = w / 7
    Q = s.Matrix([[2, 1, 0], [1, 3, 1], [0, 1, 2]]).inv()
    frame_gradients = [s.diag(1, -2, 3), s.ones(3),
                       s.Matrix([[1, 2, 0], [2, 0, -1], [0, -1, 2]])]
    r, dr = s.symbols("r dr", positive=True)
    rad = s.sqrt(delta + r**2)
    conversion = 0
    expanded = 0
    for g, P in zip(first, frame_gradients):
        nj = g - n * n.dot(g)
        gradw = dr * n + r * nj
        A = gradw.dot(gradw) / rad - (r * n).dot(gradw)**2 / rad**3
        zero(A - r**2 / rad * nj.dot(nj) - delta * dr**2 / rad**3,
             "radial and angular diffusion both retained")
        h = n.dot(Q * n)
        d = nj - P * Q * n
        residual = gradw - P * Q * (r * n)
        conversion += residual.dot(Q * residual) / (r**2 * h)
        conversion -= gradw.dot(gradw) / r**2
        expanded += 2 * dr / r * n.dot(Q * d) / h
        expanded += d.dot(Q * d) / h - nj.dot(nj)
    zero(conversion - expanded, "directional conversion retains mixed frame derivatives")


def reserve_slack():
    r, sigma, stretch, delta, Y, nu, D = s.symbols(
        "r sigma stretch delta Y nu D", positive=True)
    slack = (r - s.sqrt(2) * sigma)**2 / (2 * s.sqrt(2))
    slack += r * sigma - stretch / s.sqrt(r**2 + delta)
    zero(slack - (r**2 / (2 * s.sqrt(2)) + sigma**2 / s.sqrt(2)
                  - stretch / s.sqrt(r**2 + delta)), "nonnegative slack decomposition")
    # Integrals of |omega|^2 and |strain|^2 are Y and Y/2.
    production = s.symbols("production", real=True)
    slack_integral = Y / (2 * s.sqrt(2)) + Y / (2 * s.sqrt(2)) - production
    norm_rate = production - nu * D
    energy_rate = -2 * nu * Y
    zero(norm_rate + energy_rate / (2 * s.sqrt(2) * nu) + nu * D
         + slack_integral, "full reserve balance including discarded slack")

    # Local balance uses the pointwise skew/symmetric decomposition, not
    # a weighted version of the integrated strain--vorticity identity.
    w = s.Matrix([2, -3, 6])
    strain = s.Matrix([[1, 2, 3], [2, -4, 1], [3, 1, 3]])
    skew = s.Matrix([[0, -w[2], w[1]], [w[2], 0, -w[0]], [-w[1], w[0], 0]]) / 2
    B = strain + skew
    vector_zero(s.Matrix([B[2, 1]-B[1, 2], B[0, 2]-B[2, 0], B[1, 0]-B[0, 1]])-w,
                "vorticity is the actual skew part of the velocity gradient")
    zero(sum(v*v for v in B)-sum(v*v for v in strain)-w.dot(w)/2,
         "pointwise strain and vorticity decomposition")
    velocity, pressure_gradient = s.Matrix([1, -2, 3]), s.Matrix([2, 1, -4])
    prod = w.dot(B*w)/s.sqrt(w.dot(w)+delta)
    scalar_rate = prod-nu*D
    kinetic_rate = -2*velocity.dot(pressure_gradient)-2*nu*sum(v*v for v in B)
    slack_local = (w.dot(w)/2+sum(v*v for v in strain))/s.sqrt(2)-prod
    zero(scalar_rate+kinetic_rate/(2*s.sqrt(2)*nu)+nu*D+slack_local
         +velocity.dot(pressure_gradient)/(s.sqrt(2)*nu),
         "full local reserve rate retains pressure flux")


def helical_heat():
    """A literal unforced solution with changing spatial vorticity direction."""
    x, y, z, t = s.symbols("x y z t", real=True)
    A, k, nu = s.symbols("A k nu", positive=True)
    coordinates = (x, y, z)
    decay = s.exp(-nu * k**2 * t)
    u = A * decay * s.Matrix([0, s.sin(k*x), s.cos(k*x)])
    B = u.jacobian(coordinates)
    lap = lambda f: sum(s.diff(f, c, 2) for c in coordinates)
    w = s.Matrix([s.diff(u[2], y) - s.diff(u[1], z),
                  s.diff(u[0], z) - s.diff(u[2], x),
                  s.diff(u[1], x) - s.diff(u[0], y)])
    vector_zero(u.diff(t) + B*u - nu*u.applyfunc(lap), "actual NS with zero pressure")
    zero(s.trace(B), "actual incompressibility")
    vector_zero(w - k*u, "physical helical vorticity")
    r = A*k*decay
    n = w / r
    angular = sum(n.diff(c).dot(n.diff(c)) for c in coordinates)
    zero(angular - k**2, "nonzero spatial direction variation")
    zero(w.dot(B*w), "zero stretching of this reference")
    reserve = r + A**2 * decay**2 / (2*s.sqrt(2)*nu)
    zero(s.diff(reserve, t) + nu*r*angular + r**2/s.sqrt(2), "full-time exact payment")
    zero(s.integrate(nu*r*angular, (t, 0, s.oo)) - A*k, "all-time angular price")
    zero(s.integrate(r**2/s.sqrt(2), (t, 0, s.oo))
         - A**2/(2*s.sqrt(2)*nu), "all-time alignment slack price")
    # Holding the same helix steady requires an actual force. Its curl work
    # and kinetic work pay exactly the two costs; it is not an unforced example.
    zero(nu*k**2*(A*k) + nu*k**2*A**2/(s.sqrt(2)*nu)
         - nu*(A*k)*k**2 - (A*k)**2/s.sqrt(2), "forced stationary bill")


def compact_seed_and_scaling():
    x, y, z = s.symbols("x y z", real=True)
    a, b, delta, lam, r = s.symbols("a b delta lam r", positive=True)
    coordinates = (x, y, z)
    u = s.Matrix([-a*x-b*y, b*x, a*z])
    potential = u.cross(s.Matrix(coordinates)) / 3

    def curl(v):
        return s.Matrix([s.diff(v[2], y)-s.diff(v[1], z),
                         s.diff(v[0], z)-s.diff(v[2], x),
                         s.diff(v[1], x)-s.diff(v[0], y)])

    vector_zero(curl(potential) - u, "compact seed potential on its inner ball")
    B = u.jacobian(coordinates)
    w = curl(u)
    wt = -curl(B*u)  # Viscous curl vanishes on this inner ball.
    zero(s.trace(B), "divergence-free linear core")
    vector_zero(wt - B*w, "true initial vorticity tangent, no imposed pressure")
    srate = 2*w.dot(wt)
    erate = srate - w.dot((B+B.T)*w)
    zero(erate, "original metric rate retains its evolution")
    conversion_rate = (srate-erate)/(w.dot(w)+delta)
    zero(conversion_rate - 8*a*b**2/(4*b**2+delta), "strict original conversion growth")
    zero(s.sqrt(lam**4*r**2+delta)/lam**3
         - s.sqrt(delta)/lam**3
         - (s.sqrt(r**2+delta/lam**4)-s.sqrt(delta/lam**4))/lam,
         "regularized reserve scaling with fixed physical regularizer")
    e = s.symbols("e", positive=True)
    zero((delta+lam**4*r**2)/(delta+lam**4*e)
         - (delta/lam**4+r**2)/(delta/lam**4+e), "directional conversion scaling")
    return str(conversion_rate.factor())


def released_direction_checks():
    """Use the existing complete Fourier parents, with their inherited frames."""
    import covariance_velocity_defect as c

    f, ns = c.f, c.s
    cases = [("simple", c.simple_parent(), c.Q(64), c.Q(64)),
             ("resonant_background", c.resonant_parent(), c.Q(-10000), c.Q(10000))]
    output = []
    for name, parent, speed, memory in cases:
        u = ns.vector_scale(speed, ns.nonlinear(parent))
        omega = f.curl(u)
        Mfield = c.tadd(c.matrix_identity(), c.j.tensor_scale(memory, c.j.tensor(parent, parent)))
        # Exact eighth-turn phases use only rational numbers and sqrt(2).
        phase = (1, 1, 1)
        root = (1+s.I)/s.sqrt(2)

        def at(poly):
            return s.simplify(s.expand(sum((s.Rational(str(a.x)) + s.I*s.Rational(str(a.y)))
                                          * root**(sum(k[j]*phase[j] for j in range(3)) % 8)
                                          for k, a in poly.items())))

        vector_at = lambda v: s.Matrix([at(p) for p in v])
        matrix_at = lambda T: s.Matrix([[at(p) for p in row] for row in T])
        om, B, M = vector_at(omega), matrix_at(f.jac(u)), matrix_at(Mfield)
        if om.dot(om) == 0:
            # A different prescribed point for a seed with this symmetry zero.
            phase = (1, 2, 1)
            om, B, M = vector_at(omega), matrix_at(f.jac(u)), matrix_at(Mfield)
        if om.dot(om) == 0:
            raise AssertionError((name, "fixture vorticity must be nonzero"))
        Q = M.inv()
        gradients = [vector_at([f.diff(p, j) for p in omega]) for j in range(3)]
        matrix_gradients = [matrix_at([[f.diff(p, j) for p in row] for row in Mfield])
                            for j in range(3)]
        r2, e = om.dot(om), om.dot(Q*om)
        G = sum(g.dot(g) for g in gradients)
        W = sum((g-P*Q*om).dot(Q*(g-P*Q*om))
                for g, P in zip(gradients, matrix_gradients))
        angular = sum(g.dot(g)/r2-om.dot(g)**2/r2**2 for g in gradients)
        n, r = om/s.sqrt(r2), s.sqrt(r2)
        expansion = 0
        for g, P in zip(gradients, matrix_gradients):
            aj = om.dot(g)/r2
            nj = g/r-aj*n
            dj = nj-P*Q*n
            expansion += 2*aj*n.dot(Q*dj)/n.dot(Q*n)+dj.dot(Q*dj)/n.dot(Q*n)-nj.dot(nj)
        zero(W/e-G/r2-expansion, (name, "complete directional reaction split"))
        zero(s.trace(B), (name, "actual incompressibility"))
        sigma2 = sum(v*v for v in (B+B.T)/2)
        stretching = om.dot(B*om)
        # Positivity of the regularized magnitude diffusion at delta=1.
        d_regularized = G/s.sqrt(1+r2)-sum(om.dot(g)**2 for g in gradients)/(1+r2)**s.Rational(3, 2)
        if s.simplify(d_regularized) < 0 or angular < 0:
            raise AssertionError((name, "nonnegative physical direction cost"))
        output.append({"parent": name, "eighth_turn_point": phase,
                       "angular_gradient_squared": str(s.factor(angular)),
                       "directional_strain": str(s.factor(stretching/r2)),
                       "conversion_diffusion_difference": str(s.factor(W/e-G/r2)),
                       "strain_squared": str(s.factor(sigma2))})
    return output


if __name__ == "__main__":
    magnitude_jet()
    reserve_slack()
    helical_heat()
    rate = compact_seed_and_scaling()
    released = released_direction_checks()
    print(json.dumps({
        "status": "all exact checks passed",
        "reused_reserve": "||omega||_1 + ||u||_2^2/(2 sqrt(2) nu)",
        "paid_cost": "nu integral |omega||grad direction|^2, plus nonnegative strain slack",
        "compact_seed_conversion_rate": rate,
        "inherited_frame_tests": released,
        "concentration": "reserve scales as lambda^-1; positive log-conversion persists at time tau/lambda^2",
        "scope": "analytic physical estimates and local intervals, exact algebra fixtures; no new Lean theorem",
    }, indent=2))
