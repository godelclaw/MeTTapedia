#!/usr/bin/env python3
"""Full joint-metric pressure payment and a datum-fixed paid history.

Rational common frames retain every tensor slot and spatial connection.
Complete Fourier jets use the actual unforced PDE on the normalized
period-2*pi torus. The annular-swirl smoothing argument and stochastic
Taylor--Green identification are analytic; their scalar identities are
checked here. No arbitrary-flow history allowance is certified.
"""

import json

import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
import joint_receiver_tensor as jt
from signed_viscous_pressure import interacting_datum


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def vec(A):
    return s.Matrix(list(A))


def partial_trace(W):
    return s.Matrix(3, 3, lambda i, l: sum(W[3*i+j, 3*l+j] for j in range(3)))


def finite_cotangent():
    weights = [s.Rational(1, 3), s.Rational(1, 6), s.Rational(1, 2)]
    frames = [s.Matrix([[1, 2, 0], [0, 1, 1], [0, 0, 1]]),
              s.Matrix([[1, 0, 1], [-2, 1, 0], [0, 0, 1]]),
              s.Matrix([[2, 1, 0], [0, s.Rational(1, 2), 0], [0, 0, 1]])]
    generators = [s.Matrix([[1, 2, 0], [-1, 0, 1], [2, 0, -1]]),
                  s.Matrix([[0, -1, 2], [3, 1, 0], [1, -2, -1]]),
                  s.Matrix([[-1, 0, 3], [1, 2, -1], [0, 1, -1]])]
    require(sum(weights) == 1 and all(F.det() == 1 for F in frames),
            'one normalized determinant-one frame law')
    grams = [F.T*F for F in frames]
    C = sum((w*s.kronecker_product(G, G) for w, G in zip(weights, grams)), s.zeros(9))
    require(all(C[:k, :k].det() > 0 for k in range(1, 10)), 'positive joint moment')
    W = C.inv()
    E = s.Matrix([[1, -2, 3], [-2, 1, -1], [3, -1, 0]])
    e, residuals, flux = vec(E), [], s.zeros(3, 1)
    for j in range(3):
        dF = [F*((j+1)*R+(k-1)*generators[(k+1) % 3].T)
              for k, (F, R) in enumerate(zip(frames, generators))]
        require(all((F.inv()*d).trace() == 0 for F, d in zip(frames, dF)),
                'all spatial frame tangents preserve volume')
        dG = [d.T*F+F.T*d for F, d in zip(frames, dF)]
        dC = sum((w*(s.kronecker_product(d, G)+s.kronecker_product(G, d))
                  for w, G, d in zip(weights, grams, dG)), s.zeros(9))
        dE = (j+1)*(generators[j]+generators[j].T)
        K, dW = dC*W, -W*dC*W
        r = vec(dE)-K*e
        dZ = dW*e+W*vec(dE)
        require(dZ == W*r, ('complete metric derivative and connection', j))
        for i in range(3):
            flux[i] += dZ[3*i+j]
        residuals.append(r)
    R, v, nu = partial_trace(W), s.Matrix([-2, 3, 1]), s.Rational(3, 5)
    slots = [vec(v*s.eye(3)[j, :]) for j in range(3)]
    diffusion = sum((r.T*W*r)[0] for r in residuals)
    pressure = (v.T*R*v)[0]
    work = (v.T*flux)[0]
    square = sum(((nu*r-z).T*W*(nu*r-z))[0] for r, z in zip(residuals, slots))
    require(pressure == sum((z.T*W*z)[0] for z in slots), 'every diagonal spatial slot retained')
    require(work == sum((r.T*W*z)[0] for r, z in zip(residuals, slots)),
            'literal divergence cotangent')
    require(square == nu**2*diffusion-2*nu*work+pressure and square >= 0,
            'full pressure/diffusion completed square')
    require(2*work <= nu*diffusion+pressure/nu, 'half of 2nu diffusion pays the cotangent')
    a = vec(s.Matrix([[1, 2, 3], [-1, 0, 2], [0, 1, -1]]))
    quadratic = lambda w: (w.T*W*w)[0]
    require(2*quadratic(a)+2*quadratic(e)-quadratic(a-e) == quadratic(a+e)
            and quadratic(a+e) >= 0, 'complete normalized physical-gradient comparison')
    require(all(R[:k, :k].det() > 0 for k in range(1, 4)), 'positive induced pressure metric')
    anisotropy = []
    for lam in (1, 2, 4, 8):
        F = s.diag(lam, s.Rational(1, lam), 1)
        H = (F.T*F).inv()
        R = partial_trace(s.kronecker_product(H, H))
        require(R == H.trace()*H, 'one-frame partial trace keeps the trace factor')
        anisotropy.append({'frame_scale': lam, 'extra_factor': str(H.trace())})
    return {'tensor_coordinates': 9, 'spatial_directions': 3,
            'diffusion': str(diffusion), 'induced_pressure_cost': str(pressure),
            'completed_square': str(square), 'one_frame_metric': 'tr(H)*H',
            'anisotropy': anisotropy,
            'scope': 'finite supplied same-frame law; no uniform physical metric bound'}


def fourier_pressure():
    u = interacting_datum()
    B = f.jac(u)
    f.equal(f.trace(B), {}, 'actual solenoidal initial velocity')
    p = f.tensor_pressure(f.tensor(u, u))
    P = f.hess(p)
    S = jt.scale(f.QQ_I(1)/2, jt.add(B, pm.transpose(B)))
    I = [[{f.ORIGIN: f.QQ_I.one} if i == j else {} for j in range(3)] for i in range(3)]
    twice_S = jt.add(B, pm.transpose(B))
    W1 = jt.add(jt.kronecker(twice_S, I), jt.kronecker(I, twice_S))
    metric_leg = jt.metric(jt.flatten(B), W1, jt.flatten(P))
    independent = f.scale(4, pm.pair(jt.multiply(S, S), P))
    f.equal(metric_leg, independent, 'complete first original-metric pressure leg')
    measured = pm.mean(metric_leg)
    require(measured == (f.QQ_I(-391507472)/10405395).x and measured < 0,
            'exact negative weighted-pressure derivative on genuine 3D data')
    require(pm.mean(pm.pair(B, P)) == f.ZERO.x, 'unweighted physical gradient pressure cancellation')
    Z1_flat = f.matvec(W1, jt.flatten(B))
    Z1 = [Z1_flat[3*i:3*i+3] for i in range(3)]
    boundary = pm.mean(f.dot(pm.tensor_divergence(Z1), f.grad(p)))
    require(measured == -boundary, 'weak integration by parts keeps the full induced receiver')
    for nu in (f.QQ_I(1)/10, f.QQ_I.one):
        u1 = [f.add(f.scale(nu, f.lap(q)), f.scale(-1, f.adv(u, q)),
                    f.scale(-1, f.diff(p, i))) for i, q in enumerate(u)]
        f.equal(pm.divergence(u1), {}, 'complete unforced tangent remains solenoidal')
        B1 = f.jac(u1)
        P1 = f.hess(f.tensor_pressure(pm.symmetric_product(u, u1)))
        require(pm.mean(pm.pair(B1, P)) == f.ZERO.x
                and pm.mean(pm.pair(B, P1)) == f.ZERO.x,
                'both evolving physical pressure legs retained before cancellation')
        derivative = pm.mean(f.add(pm.pair(B1, P), pm.pair(B, P1), metric_leg))
        require(derivative == measured, 'full positive-viscosity actual NS derivative')
    return {'weighted_gradient_pressure_at_zero': '0',
            'first_derivative': str(measured), 'weak_receiver_work': str(boundary),
            'formula': 'J_p_prime(0)=4*mean(S^2:Hess p)',
            'scope': 'actual full Fourier initial jets; not the defect source history'}


def swirl_sign():
    r = s.symbols('r', positive=True)
    alpha, beta = s.symbols('alpha beta', real=True)
    V = alpha*r+beta
    dV = s.diff(V, r)
    B = s.Matrix([[0, -V/r, 0], [dV, 0, 0], [0, 0, 0]])
    S = (B+B.T)/2
    radial_pressure = V**2/r
    P = s.diag(s.diff(radial_pressure, r), radial_pressure/r, 0)
    require(s.simplify(P.trace()+s.trace(B*B)) == 0, 'actual radial canonical pressure source')
    require(s.simplify(4*s.trace(S*S*P)-2*(dV-V/r)**2*dV*V/r) == 0,
            'physical quartic pressure work and polar area factor')
    primitive = alpha*beta**2*(alpha*s.log(r)-beta/r)
    require(s.simplify(s.diff(primitive, r)-(s.diff(V, r)-V/r)**2*s.diff(V, r)*V) == 0,
            'exact quartic radial primitive')

    def tent_integral(delta):
        upper = 1+delta
        up = primitive.subs({alpha: 1/delta, beta: -1/delta})
        down = primitive.subs({alpha: -1/(2-delta), beta: 3/(2-delta)})
        value = up.subs(r, upper)-up.subs(r, 1)+down.subs(r, 3)-down.subs(r, upper)
        closed = (s.log(1+delta)-delta/(1+delta))/delta**4
        closed += 9*(s.log(3/(1+delta))-3/(1+delta)+1)/(2-delta)**4
        require(s.simplify(s.expand_log(value-closed, force=True)) == 0, 'both ramp contributions')
        return closed

    positive, negative = tent_integral(s.Rational(1, 10)), tent_integral(s.Integer(1))
    x = s.symbols('x', nonnegative=True)
    require(s.cancel(1/(1+x)-(1-x)-x**2/(1+x)) == 0, 'lower logarithm integrand')
    require(s.cancel((1-x+x**2)-1/(1+x)-x**3/(1+x)) == 0, 'upper logarithm integrand')
    z = s.symbols('z', positive=True)
    require(s.cancel((3-z)/2-1/z+(z-1)*(z-2)/(2*z)) == 0,
            'trapezoid bound for log 2 on [1,2]')
    delta = s.Rational(1, 10)
    lower = (delta-delta**2/2-delta/(1+delta))/delta**4
    lower += 9*(-3/(1+delta)+1)/(2-delta)**4
    upper = s.Rational(3, 4)+9*s.Rational(5, 12)-5
    require(lower == s.Rational(2996550, 75449) and lower > 39,
            'strict positive bound uses only rational inequalities')
    require(upper == -s.Rational(1, 2), 'strict negative bound')
    return {'thin_rise_integral': str(positive), 'thin_rise_lower_bound': str(lower),
            'symmetric_tent_integral': str(negative), 'symmetric_tent_upper_bound': str(upper),
            'normalized_weighted_pressure_derivative': 'I/pi',
            'scope': 'exact Lipschitz radial tents; smooth W^(1,4) passage and actual short-time sign are analytic',
            'excluded_claim': 'no uniform smooth time window, recurrence or singularity'}


def taylor_green_history():
    x, y, z = s.symbols('x y z', real=True)
    a, nu = s.symbols('a nu', positive=True)
    t = s.symbols('t', nonnegative=True)
    coordinates = (x, y, z)
    amplitude = a*s.exp(-2*nu*t)
    u = s.Matrix([amplitude*s.sin(x)*s.cos(y), -amplitude*s.cos(x)*s.sin(y), 0])
    p = amplitude**2*(s.cos(2*x)+s.cos(2*y))/4
    B, gp = u.jacobian(coordinates), s.Matrix([s.diff(p, q) for q in coordinates])
    lap = s.Matrix([sum(s.diff(ui, q, 2) for q in coordinates) for ui in u])
    require(s.simplify(B.trace()) == 0, 'literal incompressibility')
    require(all(s.trigsimp(q) == 0 for q in B*u+gp), 'full nonlinear pressure cancellation')
    require(all(s.trigsimp(q) == 0 for q in lap+2*u), 'actual viscous eigenvalue')
    require(all(s.trigsimp(q) == 0 for q in s.diff(u, t)+B*u+gp-nu*lap),
            'exact unforced NS evolution for all time')
    require(s.trigsimp(sum(s.diff(p, q, 2) for q in coordinates)+s.trace(B*B)) == 0,
            'canonical quadratic pressure, including all parents')

    def mean_xy(q):
        return s.simplify(s.integrate(s.integrate(q, (x, -s.pi, s.pi)),
                                     (y, -s.pi, s.pi))/(4*s.pi**2))

    pressure_square = mean_xy((gp.T*gp)[0])
    require(mean_xy(p) == 0, 'canonical mean-zero pressure')
    energy, enstrophy = mean_xy((u.T*u)[0]), mean_xy(sum(q*q for q in B))
    require(pressure_square == a**4*s.exp(-8*nu*t)/4, 'exact pressure-gradient square')
    require(energy == a**2*s.exp(-4*nu*t)/2
            and enstrophy == a**2*s.exp(-4*nu*t), 'actual physical energy and enstrophy')
    d, h = amplitude*s.cos(x)*s.cos(y), amplitude*s.sin(x)*s.sin(y)
    require(B == s.Matrix([[d, -h, 0], [h, -d, 0], [0, 0, 0]]), 'physical gradient slots')
    require(s.trigsimp(d+h-amplitude*s.cos(x-y)) == 0
            and s.trigsimp(d-h-amplitude*s.cos(x+y)) == 0,
            'singular values bounded by the known decaying amplitude')
    basis = s.Matrix([[1, 1, 0], [1, -1, 0], [0, 0, s.sqrt(2)]])/s.sqrt(2)
    require(basis.T*basis == s.eye(3), 'orthonormal singular basis')
    diagonal = s.diag((d-h)**2, (d+h)**2, 0)
    require(all(s.trigsimp(q) == 0 for q in basis.T*B.T*B*basis-diagonal),
            'operator norm uses the full physical matrix')
    D = s.integrate(amplitude, (t, 0, s.oo))
    require(D == a/(2*nu), 'entire parent history paid from original amplitude and viscosity')
    kappa = s.exp(4*D)
    pressure_upper = 3*kappa*pressure_square/nu
    other_source_upper = 4*a**3*kappa*(s.exp(2*D)+s.exp(-2*nu*t))*s.exp(-4*nu*t)
    reserve = kappa*(3*a**4*s.exp(-8*nu*t)/(32*nu**2)
                    +a**3*s.exp(2*D)*s.exp(-4*nu*t)/nu
                    +2*a**3*s.exp(-6*nu*t)/(3*nu))
    require(s.simplify(s.diff(reserve, t)+pressure_upper+other_source_upper) == 0,
            'nonnegative original-history reserve pays both complete source legs')
    allowance = kappa*(3*a**4/(32*nu**2)+a**3*(s.exp(2*D)+s.Rational(2, 3))/nu)
    require(s.simplify(reserve.subs(t, 0)-allowance) == 0, 'fixed initial payment')
    require(s.simplify(s.integrate(pressure_upper+other_source_upper, (t, 0, s.oo))-allowance) == 0,
            'full all-time source payment, with no seam replenishment')
    require(s.limit(reserve, t, s.oo) == 0, 'remaining reserve exhausts continuously')
    return {'exact_unforced_velocity': 'a*exp(-2nu*t)*(sin x cos y,-cos x sin y,0)',
            'original_parent_integral': str(D), 'metric_upper_bound': 'exp(4D)*I',
            'pressure_gradient_square': str(pressure_square),
            'complete_source_allowance': str(allowance),
            'remaining_original_history_reserve': str(reserve),
            'paid_cost': 'mean(q_E(t))-mean(q_E(s))+nu*integral_s^t mean(F_E)',
            'physical_consumer': 'mean(|grad u|^2)<=2exp(4D)*(a^2+allowance)',
            'scope': 'scalar identities exact; original stochastic frames, weak integration and history inequalities analytic',
            'open': 'datum-fixed pressure/geometry payment for mutually amplifying arbitrary parents'}


def main():
    print(json.dumps({'finite_cotangent': finite_cotangent(),
                      'actual_pressure_jets': fourier_pressure(),
                      'annular_sign': swirl_sign(),
                      'paid_taylor_green_history': taylor_green_history()}, indent=2))


if __name__ == '__main__':
    main()
