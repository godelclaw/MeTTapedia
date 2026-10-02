#!/usr/bin/env python3
"""Check the joint metric/sampling change on actual NS coefficient fixtures.

Path measures, comparison, and positive-time solution arguments remain
analytic. The companion Lean file certifies the control-shift algebra.
"""

import json

import sympy as s

from metric_loss_bellman import zero


def independent_gauge_jets():
    x, y, z = s.symbols("x y z", real=True)
    nu, loss = s.symbols("nu loss", positive=True)
    coordinates = (x, y, z)
    origin = {c: 0 for c in coordinates}
    grad = lambda f: s.Matrix([s.diff(f, c) for c in coordinates])
    lap = lambda f: sum(s.diff(f, c, 2) for c in coordinates)
    u = s.Matrix([1+x+2*y, 2-y+z, -1+x])
    h = 3+2*x-y+z+x*x+2*y*y-z*z+x*y
    ht = nu*lap(h)-u.dot(grad(h))-loss*h
    gamma = s.Matrix(s.symbols("gamma0:3", real=True))
    p = grad(h)/h
    log_lap = lap(h)/h-p.dot(p)
    actual_backward_log_rate = -ht/h+(-u+gamma).dot(p)+nu*log_lap
    zero((actual_backward_log_rate-loss+nu*p.dot(p)-gamma.dot(p)).subs(origin),
         "backward log rate from independent time and spatial jets")
    zero((-ht/h-u.dot(p)+nu*lap(h)/h-loss).subs(origin),
         "density with the negative integrated loss is a local martingale")
    beta = gamma-2*nu*p
    zero((loss-beta.dot(beta)/(4*nu)+gamma.dot(gamma)/(4*nu)
          -actual_backward_log_rate).subs(origin), "complete cost shift")
    # Exact endpoint factors, retaining the same middle state.
    h0, h1, h2, z01, z12 = s.symbols("h0 h1 h2 z01 z12", positive=True)
    zero((h0/h1*z01)*(h1/h2*z12)-h0/h2*z01*z12,
         "compatible path factors telescope")


def full_shear_history():
    A, nu, delta, q = s.symbols("A nu delta q", positive=True)
    c, gx, gy, gz = s.symbols("c gx gy gz", real=True)
    time = lambda f: -2*nu*q*s.diff(f, q)
    lap = lambda f: (1-c*c)*s.diff(f, c, 2)-c*s.diff(f, c)
    h = delta+A*A*q*c*c
    hc = s.diff(h, c)
    gradient_square = (1-c*c)*hc**2/h**2
    loss = 2*nu*A*A*q*(1-c*c)/h
    v = -loss
    # gamma=(gx, gy sin y, gz); p=(0,-sin y h_c/h,0).
    gamma_square = gx*gx+(1-c*c)*gy*gy+gz*gz
    beta_square = gx*gx+(1-c*c)*(gy+2*nu*hc/h)**2+gz*gz
    backward_log = -time(h)/h-gy*(1-c*c)*hc/h+nu*(lap(h)/h-gradient_square)
    zero(loss+v-beta_square/(4*nu)
         -(v-gamma_square/(4*nu)+backward_log),
         "complete time-dependent shear cost, arbitrary displayed controls")
    zero(-time(h)+nu*lap(h)-loss*h,
         "shear density martingale including its killing")


def inherited_coefficients():
    import covariance_velocity_defect as c

    f, ns = c.f, c.s
    cases = [("simple", c.simple_parent(), c.Q(64), c.Q(64)),
             ("resonant_background", c.resonant_parent(), c.Q(-10000), c.Q(10000))]
    result = []
    root = (1+s.I)/s.sqrt(2)

    def at(poly):
        return s.simplify(s.expand(sum((s.Rational(str(a.x))+s.I*s.Rational(str(a.y)))
                                      *root**(sum(k) % 8) for k, a in poly.items())))

    vector_at = lambda v: s.Matrix([at(p) for p in v])
    matrix_at = lambda T: s.Matrix([[at(p) for p in row] for row in T])
    for name, parent, speed, memory in cases:
        ufield = ns.vector_scale(speed, ns.nonlinear(parent))
        omega_field = f.curl(ufield)
        Mfield = c.tadd(c.matrix_identity(), c.j.tensor_scale(memory, c.j.tensor(parent, parent)))
        u, omega = vector_at(ufield), vector_at(omega_field)
        B, M = matrix_at(f.jac(ufield)), matrix_at(Mfield)
        zero(s.trace(B), (name, "incompressibility"))
        Q = M.inv()
        dw = [vector_at([f.diff(p, j) for p in omega_field]) for j in range(3)]
        dM = [matrix_at([[f.diff(p, j) for p in row] for row in Mfield]) for j in range(3)]
        ddw = [vector_at([f.diff(f.diff(p, j), j) for p in omega_field]) for j in range(3)]
        ddM = [matrix_at([[f.diff(f.diff(p, j), j) for p in row] for row in Mfield])
               for j in range(3)]
        dQ = [-Q*P*Q for P in dM]
        ddQ = [2*Q*P*Q*P*Q-Q*P2*Q for P, P2 in zip(dM, ddM)]
        e = omega.dot(Q*omega)
        de = s.Matrix([2*omega.dot(Q*g)+omega.dot(Qj*omega) for g, Qj in zip(dw, dQ)])
        le = sum(2*g.dot(Q*g)+2*omega.dot(Q*g2)+4*omega.dot(Qj*g)+omega.dot(Qjj*omega)
                 for g, g2, Qj, Qjj in zip(dw, ddw, dQ, ddQ))
        omega_t = sum(ddw, s.zeros(3, 1))+B*omega-sum((u[j]*dw[j] for j in range(3)), s.zeros(3, 1))
        M_t = sum(ddM, s.zeros(3))+B*M+M*B.T-sum((u[j]*dM[j] for j in range(3)), s.zeros(3))
        et = 2*omega.dot(Q*omega_t)-omega.dot(Q*M_t*Q*omega)
        W = sum((g-P*Q*omega).dot(Q*(g-P*Q*omega)) for g, P in zip(dw, dM))
        zero(et+u.dot(de)-le+2*W, (name, "actual metric equation, all inherited derivatives"))
        values = []
        for delta in (s.Integer(1), s.Integer(10)**12):
            h = e+delta
            p = de/h
            loss = 2*W/h
            v = (2*omega.dot(B*omega)-2*sum(g.dot(g) for g in dw))/(omega.dot(omega)+delta)
            gamma = s.Matrix([2, -1, 3])
            beta = gamma-2*p
            backward_log = -et/h+(-u+gamma).dot(p)+le/h-p.dot(p)
            zero(loss+v-beta.dot(beta)/4-v+gamma.dot(gamma)/4-backward_log,
                 (name, delta, "physical joint cost identity"))
            zero(-et/h-u.dot(p)+le/h-loss, (name, delta, "physical density martingale"))
            values.append({"delta": str(delta), "loss": str(s.factor(loss)), "ordinary": str(s.factor(v))})
        result.append({"fixture": name, "regularizers": values})
    return result


def actual_initial_record():
    x, y, z = s.symbols("x y z", real=True)
    a, b, nu = s.symbols("a b nu", positive=True)
    coords = (x, y, z)
    u = s.Matrix([-a*s.sin(x)*s.cos(z)-b*s.sin(y), b*s.sin(x), a*s.cos(x)*s.sin(z)])
    B = u.jacobian(coords)
    curl = lambda v: s.Matrix([s.diff(v[2], y)-s.diff(v[1], z),
                              s.diff(v[0], z)-s.diff(v[2], x),
                              s.diff(v[1], x)-s.diff(v[0], y)])
    omega = curl(u)
    tangent = -curl(B*u)+nu*omega.applyfunc(lambda f: sum(s.diff(f, q, 2) for q in coords))
    zero(sum(B[j, j] for j in range(3)), "record datum is incompressible")
    zero(s.trigsimp(omega.dot(omega)-4*a*a*s.sin(x)**2*s.sin(z)**2-b*b*(s.cos(x)+s.cos(y))**2),
         "whole-domain magnitude for the initial maximum")
    t = s.symbols("t", real=True)
    zero(4*b*b-(4*a*a*(1-t*t)+b*b*(t+1)**2)
         -(1-t)*((b*b-2*a*a)*(t+3)+2*a*a*(1-t)),
         "global maximum certificate when b^2>=2a^2 and 0<=t<=1")
    origin = {q: 0 for q in coords}
    rate = s.factor((2*omega.dot(tangent)).subs(origin))
    zero(rate-8*b*b*(a-nu), "actual original global maximum has positive rate if a>nu")
    for component in u.subs(origin):
        zero(component, "velocity observation vanishes at the stretching point")
    G = sum(v*v for v in omega.jacobian(coords))
    ordinary = (2*omega.dot(B*omega)-2*nu*G)/(omega.dot(omega)+4*b*b)
    zero(ordinary.subs(origin)-a, "ordinary reaction at the original global maximum")
    return {"initial_max_squared": "4 b^2 when b^2 >= 2 a^2", "actual_rate": str(rate),
            "example_nu_a_b": [1, 2, 3], "example_delta": 36,
            "example_squared_rate": int(rate.subs({nu: 1, a: 2, b: 3})),
            "ordinary_reaction_at_origin": "a", "velocity_at_origin": "0"}


def velocity_allowance_constants():
    nu, E0, coefficient = s.symbols("nu E0 coefficient", positive=True)
    L = 4*s.sqrt(E0)*(8*s.pi*nu)**(-s.Rational(3, 4))
    inverse_block_length = (2*coefficient*L)**4
    zero(inverse_block_length-8*coefficient**4*E0**2/(s.pi**3*nu**3),
         "explicit velocity occupation block length")
    tau = s.symbols("tau", positive=True)
    zero(s.diff(4*tau**s.Rational(1, 4), tau)-tau**(-s.Rational(3, 4)),
         "integrable velocity observation exponent")


if __name__ == "__main__":
    independent_gauge_jets()
    full_shear_history()
    fixtures = inherited_coefficients()
    record = actual_initial_record()
    velocity_allowance_constants()
    print(json.dumps({"status": "all exact checks passed", "inherited_coefficients": fixtures,
                      "initial_record": record,
                      "scope": "physical coefficients and control algebra; path laws and interval arguments analytic"}, indent=2))
