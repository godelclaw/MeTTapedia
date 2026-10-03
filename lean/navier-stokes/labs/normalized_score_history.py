#!/usr/bin/env python3
"""Normalized vorticity/score flux and an actual-kernel Bellman test.

The exact checks retain canonical NS pressure and every Fourier output.
The physical point-kernel factorization and small-time estimates are
analytic in README.md. Smooth receiver fixtures are identified separately.
"""

import json

import sympy as sp

import passive_parent_bellman as parent
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f, Q, r = parent.f, parent.Q, parent.r


def vector(prefix):
    return sp.Matrix(sp.symbols(prefix+"0:3", real=True))


def matrix(prefix):
    return sp.Matrix(3, 3, sp.symbols(prefix+"0:9", real=True))


def normsq(v):
    return sum(x*x for x in v)


def pair(a, b):
    return sum(x*y for x, y in zip(a, b))


def general_identities():
    nu, age, theta = sp.symbols("nu age theta", positive=True)
    alpha, beta, growth = sp.symbols("alpha beta growth", real=True)
    n, impulse, k, lapk, gp, gamma = [vector(s) for s in ("n", "i", "k", "l", "p", "g")]
    W, A, B = [matrix(s) for s in ("w", "a", "b")]
    entries = sp.symbols("K0:6", real=True)
    K = sp.Matrix([[entries[0], entries[1], entries[2]],
                   [entries[1], entries[3], entries[4]],
                   [entries[2], entries[4], entries[5]]])
    j = W.T*n
    N = W-n*j.T
    d, z = impulse.dot(n), n.dot(k)
    gd, gz = A.T*n+N.T*impulse, N.T*k+K*n
    chi = growth/2+nu*j.dot(j)
    Lz = chi*z-2*nu*k.dot(N*j)+2*nu*(n.dot(lapk)+n.dot(K*k)+pair(N, K))
    Ld = -n.dot(gp)-impulse.dot(B*n)+chi*d-2*nu*impulse.dot(N*j)+2*nu*pair(A, N)
    Lzz = 2*z*Lz+2*nu*gz.dot(gz)
    fluxzz = 4*nu*(z*k.dot(K*n)+gz.dot(K*n)+z*(n.dot(lapk)+pair(N, K)))
    reflected_k = k-2*z*n
    T = growth*z*z+2*nu*normsq(W.T*reflected_k)-2*nu*normsq(K*n)
    zero(Lzz-fluxzz-T, "normalized directional flux retains growth and its geometric defect")
    Ldz = d*Lz+z*Ld+2*nu*gd.dot(gz)
    fluxdz = 2*nu*(d*k.dot(K*n)+gd.dot(K*n)+d*(n.dot(lapk)+pair(N, K)))
    M = (2*chi*d*z-2*nu*d*k.dot(N*j)
         +z*(-n.dot(gp)-impulse.dot(B*n)-2*nu*impulse.dot(N*j)+2*nu*pair(A, N))
         +2*nu*gd.dot(N.T*k))
    zero(Ldz-fluxdz-M, "mixed impulse and score retain pressure and normalization")
    quadratic = impulse.dot(impulse)/nu+2*beta*d*z+alpha*nu*z*z
    positive_form = ((impulse.dot(impulse)-d*d)/nu
                     +(d/sp.sqrt(nu)+beta*sp.sqrt(nu)*z)**2+(alpha-beta*beta)*nu*z*z)
    zero(quadratic-positive_form, "positive joint quadratic when alpha>=beta^2 and |n|<=1")
    Lii = -2*impulse.dot(gp)+2*nu*normsq(A)
    LQ = Lii/nu+2*beta*Ldz+alpha*nu*Lzz
    bulk = Lii/nu+2*beta*M+alpha*nu*T
    zero(LQ-(2*beta*fluxdz+alpha*nu*fluxzz)-bulk,
         "full quadratic generator and its boundary flux")
    # Complete the control square without replacing a controlled law by q.
    dq = vector("dq")
    zero(age*gamma.dot(dq)-theta*gamma.dot(gamma)/(4*nu)-nu*age*age*dq.dot(dq)/theta
         +theta*(gamma-2*nu*age*dq/theta).dot(gamma-2*nu*age*dq/theta)/(4*nu),
         "pointwise Bellman optimization retains its assigned sampling-price share")
    return dict(normalized_flux=True, mixed_pressure_flux=True, full_quadratic=True,
                scope="algebra of the stated PDE generators; inequalities require their physical hypotheses")


def physical_fixture(u, label, point):
    nu = Q(1)
    jets, pressures = velocity_time_jets(u, nu, 1)
    omega, wt = f.curl(u), f.curl(jets[1])
    ev = lambda p: r.at(p, point)
    vec = lambda v: sp.Matrix([ev(p) for p in v])
    mat = lambda T: sp.Matrix([[ev(p) for p in row] for row in T])
    U, B, w, wtime, G = vec(u), mat(f.jac(u)), vec(omega), vec(wt), mat(f.jac(omega))
    lapw = vec([f.lap(p) for p in omega])
    delta = Q(256) if label in ("pressure_start", "original_maximum") else parent.original_bound_sq(omega)
    s = w.dot(w)+delta
    h = 1/sp.sqrt(s)
    gradh = -G.T*w/s**sp.Rational(3, 2)
    laph = -(w.dot(lapw)+normsq(G))/s**sp.Rational(3, 2)+3*normsq(G.T*w)/s**sp.Rational(5, 2)
    n, W = h*w, h*G
    N = h*G+w*gradh.T
    ntime = h*wtime-w*w.dot(wtime)/s**sp.Rational(3, 2)
    lapn = h*lapw+2*G*gradh+w*laph
    Ln = -ntime-N*U+nu*lapn
    j = W.T*n
    growth = 2*n.dot(B*n)-2*nu*normsq(W)
    expected = -B*n+(growth/2+nu*j.dot(j))*n-2*nu*N*j
    for i in range(3):
        zero(Ln[i]-expected[i], (label, "literal normalized physical vorticity", i))
    # This prescribed positive smooth receiver is distinct from the shear's
    # actual point-source kernel used in the analytic endpoint argument.
    logq = f.scale(Q(1, 5), f.add(r.mode((1, 0, 1), 1), r.mode((1, 1, 1), 1)))
    k, K = vec(f.grad(logq)), mat(f.hess(logq))
    lapk = vec([f.lap(p) for p in f.grad(logq)])
    kr = nu*lapk+2*nu*K*k+B.T*k+K*U
    z, gz = n.dot(k), N.T*k+K*n
    zr = -ntime.dot(k)+n.dot(kr)
    lapz = lapn.dot(k)+2*pair(N, K)+n.dot(lapk)
    Lz_direct = zr-U.dot(gz)+nu*lapz
    flux = 4*nu*(z*k.dot(K*n)+gz.dot(K*n)+z*(n.dot(lapk)+pair(N, K)))
    defect = 2*nu*(normsq(W.T*(k-2*z*n))-normsq(K*n))
    zero(2*z*Lz_direct+2*nu*gz.dot(gz)-flux-growth*z*z-defect,
         (label, "complete directional rate on actual NS jets"))
    # At physical time zero the ORIGINAL impulse and its gradient vanish.
    # Its actual reversed-time derivative is minus canonical grad p0.
    gp = vec(f.grad(pressures[0]))
    mixed = -z*n.dot(gp)
    return dict(fixture=label, original_regularizer=str(delta),
                normalized_growth=str(sp.factor(growth)),
                normalized_score_square=str(sp.factor(z*z)),
                geometric_defect=str(sp.factor(defect)),
                initial_mixed_pressure_rate=str(sp.factor(mixed)),
                canonical_pressure_modes=len(pressures[0]),
                scope="complete actual NS initial jets, original I=0; prescribed smooth receiver")


def exact_shear_endpoint():
    age, nu, alpha = sp.symbols("age nu alpha", positive=True)
    z, curvature = sp.symbols("z curvature", real=True)
    # At t=log(2)/nu the original flow 2 exp(-nu s) sin(y)e_x has amplitude 1.
    n2 = sp.exp(2*nu*age)/(sp.exp(2*nu*age)+4)
    zero(sp.limit(n2, age, 0)-sp.Rational(1, 5), "original-datum normalization at the endpoint")
    heat_score = -z/(2*nu*age)
    P = alpha*nu*age*n2*heat_score**2
    L = sp.diff(P, age)+nu*sp.diff(P, z, 2)
    at_centre = sp.factor(L.subs(z, 0))
    zero(at_centre-alpha*n2/(2*age), "leading Gaussian centre generator")
    zero(sp.limit(age*at_centre, age, 0)-alpha/10,
         "nonintegrable pointwise source for every positive alpha")
    # The exact periodic kernel is even. At its centre score=0, so only
    # the z Laplacian contributes, whatever its exact log curvature is.
    exact_centre = 2*alpha*nu**2*age*n2*curvature**2
    zero(exact_centre.subs(curvature, -1/(2*nu*age))-at_centre,
         "periodic curvature has the heat leading coefficient")
    # This is the Gaussian leading coefficient. Averaging the y-dependent
    # normalization and passing from the periodic kernel are analytic limits.
    rho_second_moment = 2*nu*age
    entrance = alpha*nu*age*n2*rho_second_moment/(4*nu**2*age**2)
    zero(sp.limit(entrance, age, 0)-alpha/10,
         "the stochastic entrance cost is not its value on the centre line")
    # Analytic image-sum estimate for b=pi^2/(nu age)>=8:
    # sum_{m!=0} m^2 exp(-b m^2) <=2h(1+h)/(1-h)^3, h=exp(-b).
    h = sp.Rational(1, 256)
    if not (1+h)/(1-h)**3 < 2:
        raise ArithmeticError("periodic image-tail rational bound")
    zero(2*sp.Rational(1, 32)*2-sp.Rational(1, 8), "b times image-moment upper bound")
    # Thus |curvature|>=1/(4nu age), n2>=1/5 gives alpha/(40 age).
    zero(exact_centre.subs(curvature, -1/(4*nu*age))/n2-sp.Rational(1, 8)*alpha/age,
         "explicit centre lower-bound coefficient")
    # Gaussian conditional-score Jensen gives the periodic endpoint bound.
    # At alpha=theta=1/2 and |n|^2<=1/2, its exponential moment is <=sqrt(2).
    xi = sp.symbols("xi", real=True)
    gaussian_moment = sp.integrate(sp.exp(-xi*xi/4)/sp.sqrt(2*sp.pi), (xi, -sp.oo, sp.oo))
    zero(gaussian_moment-sp.sqrt(2), "finite Gaussian exponential moment for the terminal cost")
    zero(sp.log(gaussian_moment)/2-sp.log(2)/4,
         "terminal score cost paid with half the original sampling action")
    return dict(fluid="2 exp(-nu s) sin(y)e_x, pressure=0, H=u, I=0, delta=4",
                endpoint="t=log(2)/nu", density="actual point kernel, independent periodic heat factor in z",
                centre_generator_limit="lim_{r->0} r [2r_I+L P+nu|grad P|^2]=alpha/10",
                lower_bound="alpha/(40r) for 0<r<min(t,pi^2/(8nu))",
                entrance_limit="lim E P=alpha/10, not zero",
                controlled_terminal_payment="E_gamma P(r,X_r) - (1/2) E_gamma integral |gamma|^2/(4nu) <= log(2)/4, alpha=1/2",
                scope="factorization, image-sum asymptotics and endpoint limits analytic; coefficients exact")


def main():
    identities = general_identities()
    simple = parent.carrier(r.c.simple_parent(), Q(16), 4, [{}, {}, {}])
    background = r.ns.vector_scale(Q(-20000), r.ns.nonlinear(r.c.resonant_parent()))
    resonant = parent.carrier(r.c.resonant_parent(), Q(200), 4, background)
    cases = [(r.counterstrain_datum(Q(4), Q(8)), "pressure_start", (0, 0, 0)),
             (r.record_datum(Q(4), Q(8)), "original_maximum", (0, 0, 0)),
             (simple, "original_simple_carrier", (1, 1, 1)),
             (resonant, "original_resonant_carrier", (1, 1, 1))]
    fixtures = [physical_fixture(*case) for case in cases]
    shear = exact_shear_endpoint()
    print(json.dumps(dict(status="all exact checks passed", identities=identities,
                         fixtures=fixtures, exact_shear=shear,
                         scope="analytic PDE and actual-kernel statements with exact algebra; no regularity claim"), indent=2))


if __name__ == "__main__":
    main()
