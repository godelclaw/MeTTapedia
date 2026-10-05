#!/usr/bin/env python3
"""Exact joint strain source and coarse-parent algebra for unforced NS.

Continuum estimates and continuation are analytic arguments in README.md.
The fixtures keep every Fourier output, including transfer into the actual
coarse fluid. They are not closed finite-mode evolutions.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

import optimal_cubic_gauge as og
import helical_parent_response as hr

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require = og.require


def metric(v):
    return [f.add(a, f.lap(a), f.lap(f.lap(a))) for a in v]


def low(v):
    return [{k: a for k, a in row.items() if sum(j*j for j in k) <= 1} for row in v]


def high(v):
    return wh.addv(v, wh.scalev(-1, low(v)))


def pair(a, b):
    return am.pairing([a], [b])


def sum_fields(fields):
    return f.add(*fields)


def strain_work(v):
    gradient = f.jac(v)
    lap = [f.lap(a) for a in v]
    hess = [f.hess(a) for a in v]
    strain = [[f.scale(Q(1)/2, f.add(gradient[i][j], gradient[j][i]))
               for j in range(3)] for i in range(3)]
    stress = [[f.add(sum_fields(f.mul(gradient[i][k], gradient[j][k]) for k in range(3)),
                     f.scale(-1, f.mul(lap[i], lap[j])),
                     f.scale(-2, sum_fields(f.mul(lap[k], hess[k][i][j]) for k in range(3))))
               for j in range(3)] for i in range(3)]
    for i in range(3):
        for j in range(3):
            f.equal(stress[i][j], stress[j][i], "the complete derivative stress is symmetric")
    full = sum((pair(strain[i][j], stress[i][j]) for i in range(3) for j in range(3)), f.ZERO)
    anti = sum((pair(f.scale(Q(1)/2, f.add(gradient[i][j], f.scale(-1, gradient[j][i]))),
                     stress[i][j]) for i in range(3) for j in range(3)), f.ZERO)
    require(anti == f.ZERO, "antisymmetric velocity gradient cancels in the joint work")
    return full


def source_audit(v):
    pressure = f.tensor_pressure(f.tensor(v, v))
    rows = []
    for i in range(3):
        w = v[i]
        q = f.scale(-1, f.lap(w))
        cq = f.add(q, f.scale(-1, w))
        transport = f.scale(-1, f.adv(v, q))
        first = f.adv([f.lap(a) for a in v], w)
        second = f.scale(2, sum_fields(f.adv([f.diff(a, j) for a in v], f.diff(w, j))
                                      for j in range(3)))
        ppart = f.diff(f.lap(pressure), i)
        f.equal(f.scale(-1, f.lap(hr.nonlinear(v)[i])),
                f.add(transport, first, second, ppart), "complete directional source identity")
        values = [pair(cq, field) for field in (transport, first, second, ppart)]
        rows.append(values)
    require(sum((row[3] for row in rows), f.ZERO) == f.ZERO,
            "pressure redistributes directional work but cancels in the complete sum")
    return [[str(a) for a in row] for row in rows]


def check_flow(u, label, directional=False):
    U, v = low(u), high(u)
    for field in (u, U, v):
        f.equal(f.trace(f.jac(field)), {}, "actual split preserves incompressibility")
    Av = metric(v)
    nv = hr.nonlinear(v)
    nu = hr.nonlinear(u)
    nU = hr.nonlinear(U)
    linear = wh.scalev(-1, wh.project(wh.addv(og.adv(U, v), og.adv(v, U))))
    wh.same_vectors(nu, wh.addv(nU, linear, nv), "full nonlinear decomposition")
    require(am.pairing(Av, high(nu)) == am.pairing(Av, nu),
            "the actual high-pass tangent has exactly the retained metric work")
    require(am.pairing(Av, f.grad(f.tensor_pressure(f.tensor(v, v)))) == f.ZERO,
            "canonical pressure cancels against the solenoidal joint observer")
    production = am.pairing(Av, nv)
    require(production == strain_work(v), "joint nonlinear work is the explicit strain contraction")
    stock = am.pairing(Av, v)
    dissipation = -am.pairing(Av, [f.lap(a) for a in v])
    require(dissipation.x >= stock.x >= 0 and dissipation.y == stock.y == 0,
            "high-frequency joint metric and complete diffusion are positive")
    row = {"label": label, "energy": str(am.pairing(u, u)), "stock": str(stock),
           "diffusion": str(dissipation), "internal_strain_work": str(production),
           "parent_self_work": str(am.pairing(Av, nU)),
           "parent_linear_work": str(am.pairing(Av, linear)),
           "generated_coarse_modes": len(set().union(*(a.keys() for a in low(nu))))}
    if directional:
        row["directional_transport_commutator1_commutator2_pressure"] = source_audit(v)
    return row


def scalar_checks():
    x, K = s.symbols("x K", nonnegative=True)
    z = K*K-K+1
    require(s.expand(4*z-3*K*K-(K-2)**2) == 0, "second derivatives are controlled by the joint metric")
    require(s.expand(z-K-(K-1)**2) == 0, "joint stock controls the continuation gradient")
    require(s.expand(z-1-K*(K-1)) == 0, "on K>=1 the stock controls kinetic energy")
    require(s.expand(13-z-(4-K)*(K+3)) == 0, "parent self-interaction has metric multiplier at most thirteen")
    require(all(c >= 0 for c in s.Poly(s.expand(((K-1)*z).subs(K, x+1)), x).coeffs()),
            "high-pass diffusion dominates the stock")
    require(s.Rational(2)+4+5*s.Rational(4, 3) < 13,
            "the complete coarse linear estimate has coefficient below thirteen")
    H, t, M, E, nu, Z, D, P = s.symbols("H t M E nu Z D P", positive=True)
    c, C0 = 26*M, 169*M*M*E/nu
    weight = s.exp(c*(H-t))
    allowance = C0*(weight-1)/c
    rhs = c*Z+C0+2*P-nu*D
    Rprime = s.diff(weight, t)*Z+weight*rhs+s.diff(allowance, t)
    require(s.simplify(Rprime+nu*weight*D-2*weight*P) == 0,
            "one original deadline pays every complete coarse term")
    require(s.simplify(Rprime+nu*weight*D/2-2*weight*(P-nu*D/4)) == 0,
            "the open signed budget retains half of the full remaining diffusion")
    A = s.symbols("A", positive=True)
    adverse_excess = A**3*s.Rational(17, 12)-nu*A**2*s.Rational(19, 4)
    require(s.simplify(adverse_excess.subs(A, 4*nu)-s.Rational(44, 3)*nu**3) == 0,
            "the pressure-free adverse source beats its quarter diffusion at A=4nu")
    return {"metric": "A=I+Delta+Delta^2", "coarse_derivative_bound": "M=3*sqrt(E0)",
            "linear_rate": "26*M", "coarse_source_rate": "169*M^2*E0/nu",
            "reserve": "exp(26*M*(H-t))*Z+C0*(exp(26*M*(H-t))-1)/(26*M)",
            "OPEN": "2*integral_0^t exp(26*M*(H-s))*(P(v)-nu*D(v)/4) ds <= one finite original-data K",
            "adverse_threshold": "A>57*nu/17", "adverse_excess_at_A_4nu": "44*nu^3/3"}


if __name__ == "__main__":
    waves = [(1, 1, 0), (1, -1, 1), (2, 0, 1)]
    adverse = wh.addv(*(wh.project([og.cosine(k) if j < 2 else og.vd.sine(k), {}, {}])
                        for j, k in enumerate(waves)))
    swapped = [{(k[2], k[1], k[0]): a for k, a in adverse[j].items()} for j in (2, 1, 0)]
    balanced = wh.addv(adverse, wh.scalev(-1, swapped))
    base = [og.vd.sine((0, 1, 0)), og.vd.sine((0, 0, 1)), og.vd.sine((1, 0, 0))]
    resonant = wh.addv(wh.project([og.cosine((1, 1, 0)), {}, {}]),
                       wh.project([{}, {}, og.cosine((1, 1, 1))]))
    fields = [("adverse triad", adverse), ("opposite triad", wh.scalev(-1, adverse)),
              ("orientation balanced", balanced), ("complete cyclic parents", base),
              ("parents with high receiver", wh.addv(base, adverse)),
              ("parents with opposite receiver", wh.addv(base, wh.scalev(-1, adverse))),
              ("retained generated modes", wh.addv(base, wh.scalev(Q(1)/4, hr.nonlinear(base)))),
              ("nonzero parent linear work", wh.addv(base, resonant))]
    rows = [check_flow(v, name, i < 3) for i, (name, v) in enumerate(fields)]
    require(rows[0]["stock"] == "311/60" and rows[0]["diffusion"] == "19"
            and rows[0]["internal_strain_work"] == "17/12", "exact adverse constants")
    require(rows[2]["internal_strain_work"] == "0", "balanced orientation has zero net nonlinear work initially")
    require(any(row["parent_self_work"] != "0" for row in rows),
            "a full fixture exercises the paid coarse self-interaction")
    require(any(row["parent_linear_work"] != "0" for row in rows),
            "a full fixture exercises the changing-parent linear work")
    require(any(row["generated_coarse_modes"] > 0 for row in rows),
            "the actual nonlinear tangent includes feedback into coarse parents")
    comparison = scalar_checks()
    dependencies = [Path(__file__), Path(og.__file__), Path(hr.__file__),
                    Path(f.__file__), Path(wh.__file__), Path(am.__file__)]
    print(json.dumps({"fixtures": rows, "comparison": comparison,
                      "scope": "A single pressure-free strain source remains after an original-data exponential reserve pays every coarse contribution on R3 and T3. Its arbitrary-history bound remains open. No continuum or Lean theorem is certified by these finite identities.",
                      "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies}},
                     indent=2), flush=True)
