#!/usr/bin/env python3
"""Complete first returns from spectrally balanced unforced NS data.

All Fourier outputs and pressure tangents are retained. The uniform shell
law and physical positive-time consequences are analytic in README.md;
these fixtures are not a closed shell-model evolution or a Lean proof.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

import joint_strain_source as js

og, f, wh, am, Q, hr = js.og, js.f, js.wh, js.am, js.Q, js.hr
require = og.require


def differential(v, h):
    convection = wh.addv(og.adv(v, h), og.adv(h, v))
    pressure_tangent = f.tensor_pressure(am.matrix_add(f.tensor(v, h), f.tensor(h, v)))
    tangent = wh.scalev(-1, wh.addv(convection, f.grad(pressure_tangent)))
    wh.same_vectors(tangent, wh.scalev(-1, wh.project(convection)),
                    "nonlinear differential includes the complete canonical pressure tangent")
    return tangent


def energy_pair(v, h, order):
    weighted = v
    for _ in range(order):
        weighted = [f.scale(-1, f.lap(a)) for a in weighted]
    return am.pairing(weighted, h)


def source(v):
    return am.pairing(js.metric(v), hr.nonlinear(v))


def source_derivative(v, h):
    return (am.pairing(js.metric(h), hr.nonlinear(v)),
            am.pairing(js.metric(v), differential(v, h)))


def dilation(v, n):
    return [{tuple(n*j for j in k): a for k, a in row.items()} for row in v]


def shell_energy(v, radius_squared):
    selected = [{k: a for k, a in row.items() if sum(j*j for j in k) == radius_squared}
                for row in v]
    return am.pairing(selected, selected)


def shell_test(v, n, label):
    k0 = 2*n*n
    require(all(sum(j*j for j in k) == k0 for row in v for k in row),
            "initial physical velocity lies on its stated shell")
    f.equal(f.trace(f.jac(v)), {}, "shell datum is divergence free")
    nv = hr.nonlinear(v)
    h = js.high(nv)
    wh.same_vectors(h, nv, "every generated output is retained by the high projection")
    require(all(sum(j*j for j in k) in (2*n*n, 4*n*n, 6*n*n) for row in nv for k in row),
            "complete daughter support includes only the three analytically allowed shells")
    energy = am.pairing(v, v)
    daughters = {j: shell_energy(nv, j*n*n) for j in (2, 4, 6)}
    nv2 = sum(daughters.values(), f.ZERO)
    require(nv2 == am.pairing(nv, nv), "daughter shell accounting is exhaustive")
    require(source(v) == f.ZERO and energy_pair(v, nv, 1) == f.ZERO,
            "both joint strain work and physical stretching vanish initially")
    first, back = source_derivative(v, h)
    heat = sum(source_derivative(v, [f.lap(a) for a in v]), f.ZERO)
    require(heat == f.ZERO, "the complete first source return is independent of viscosity")
    b0 = k0*k0-k0+1
    require(back == -Q(b0)*nv2, "all parent feedback is fixed by the differentiated energy identity")
    require(am.pairing(v, differential(v, nv)) == -nv2,
            "generated kinetic energy is paid by the original waves")
    predicted = Q(2*n*n*(6*n*n-1))*daughters[4]+Q(4*n*n*(8*n*n-1))*daughters[6]
    require(first+back == predicted, "complete joint first-return shell formula")
    stretch_return = energy_pair(h, nv, 1)+energy_pair(v, differential(v, h), 1)
    predicted_stretch = Q(2*n*n)*daughters[4]+Q(4*n*n)*daughters[6]
    require(stretch_return == predicted_stretch, "complete physical vorticity-stretching return")
    require((first+back).x >= (6*n*n-1)*stretch_return.x
            and (first+back).x <= (8*n*n-1)*stretch_return.x,
            "uniform relation between derivative-stock creation and enstrophy creation")
    return {"label": label, "frequency_dilation": n, "initial_energy": str(energy),
            "initial_stock": str(am.pairing(js.metric(v), v)),
            "initial_stock_diffusion": str(-am.pairing(js.metric(v), [f.lap(a) for a in v])),
            "initial_enstrophy_diffusion": str(energy_pair(v, v, 2)),
            "daughter_energy_by_squared_frequency": {str(j*n*n): str(a) for j, a in daughters.items()},
            "positive_response_term": str(first), "complete_parent_return": str(back),
            "joint_source_return": str(first+back), "stretching_return": str(stretch_return),
            "heat_source_derivative": str(heat), "generated_modes": len(set().union(*(a.keys() for a in nv)))}


def balanced_test():
    waves = [(1, 1, 0), (1, -1, 1), (2, 0, 1)]
    v = wh.addv(*(wh.project([og.cosine(k) if j < 2 else og.vd.sine(k), {}, {}])
                  for j, k in enumerate(waves)))
    swapped = [{(k[2], k[1], k[0]): a for k, a in v[j].items()} for j in (2, 1, 0)]
    v = wh.addv(v, wh.scalev(-1, swapped))
    nv = hr.nonlinear(v)
    h = js.high(nv)
    first, back = source_derivative(v, h)
    heat = sum(source_derivative(v, [f.lap(a) for a in v]), f.ZERO)
    require(source(v) == heat == f.ZERO, "reflection balance cancels the initial work and its heat derivative")
    require(first+back == Q(2894587)/138600, "full balanced nonlinear return is strictly positive")
    # Independent cubic polarization checks the differential via the strain formula.
    plus, minus = wh.addv(v, h), wh.addv(v, wh.scalev(-1, h))
    polarized = (js.strain_work(plus)-js.strain_work(minus))/2-js.strain_work(h)
    require(polarized == first+back, "independent strain-tensor polarization agrees with the physical differential")
    return {"initial_source": "0", "heat_source_derivative": "0",
            "positive_response_term": str(first), "complete_parent_return": str(back),
            "full_return": str(first+back),
            "initial_coarse_tangent_energy": str(am.pairing(js.low(nv), js.low(nv)))}


def physical_jet(v, nu):
    """Check heat comparisons from full NS time jets, independently of SR4."""
    u1 = wh.addv(wh.scalev(nu, [f.lap(a) for a in v]), hr.nonlinear(v))
    u2 = wh.addv(wh.scalev(nu, [f.lap(a) for a in u1]), differential(v, u1))
    u3 = wh.addv(wh.scalev(nu, [f.lap(a) for a in u2]), differential(v, u2),
                 wh.scalev(2, hr.nonlinear(u1)))
    # The original seed has -Delta v=2v; heat energies decay as exp(-4*nu*t).
    joint2 = am.pairing(js.metric(u1), u1)+am.pairing(js.metric(v), u2)
    joint2 -= 8*nu*nu*am.pairing(js.metric(v), v)
    enstrophy2 = energy_pair(u1, u1, 1)+energy_pair(v, u2, 1)
    enstrophy2 -= 8*nu*nu*energy_pair(v, v, 1)
    energy3 = am.pairing(u1, u2)+am.pairing(v, u3)/3
    heat_energy3 = -Q(32)/3*nu*nu*nu*am.pairing(v, v)
    require(joint2 == Q(7)/2 and enstrophy2 == Q(1)/2,
            "full NS second time jets reproduce both excesses over heat")
    require(heat_energy3-energy3 == nu/3,
            "full NS third time jet loses more kinetic energy than heat")
    return {"viscosity": str(nu), "joint_stock_excess_t2": str(joint2),
            "enstrophy_excess_t2": str(enstrophy2),
            "heat_minus_actual_kinetic_energy_t3": str(heat_energy3-energy3)}


def scalar_checks():
    n, e4, e6 = s.symbols("n e4 e6", nonnegative=True)
    joint = 2*n*n*(6*n*n-1)*e4+4*n*n*(8*n*n-1)*e6
    stretching = 2*n*n*e4+4*n*n*e6
    require(s.expand(joint-(6*n*n-1)*stretching-8*n**4*e6) == 0,
            "lower comparison retains the sixth-shell contribution")
    require(s.expand((8*n*n-1)*stretching-joint-4*n**4*e4) == 0,
            "upper comparison retains the fourth-shell contribution")
    L = s.Rational(9, 7)
    require(s.Rational(7, 2)*L*L-s.Rational(9, 4)*L == s.Rational(81, 28),
            "complete initially negative joint budget has a later positive leading integral")
    require(s.Rational(1, 2)*12**2-3*12 == 36,
            "ordinary signed-renewal excess also becomes positive with diffusion retained")
    return {"joint_budget_time": "t=9*nu/(7*A^2)",
            "joint_budget_leading_excess": "exp(39*sqrt(3)*A*H)*81*nu^2/28",
            "ordinary_budget_time": "t=12*nu/A^2", "ordinary_budget_leading_excess": "36*nu^2",
            "scope": "The asymptotics hold as A/nu tends to infinity for fixed viscosity and a fixed positive horizon, with uniform local remainders established analytically."}


if __name__ == "__main__":
    seed = wh.addv(wh.project([og.cosine((1, 1, 0)), {}, {}]),
                   wh.project([{}, og.vd.sine((0, 1, 1)), {}]),
                   wh.project([{}, {}, og.cosine((1, 0, 1))]))
    fourth = wh.addv(wh.project([og.cosine((1, 1, 0)), {}, {}]),
                     [{}, {}, og.vd.sine((1, -1, 0))])
    mixed = wh.addv(seed, wh.scalev(Q(1)/3, fourth),
                    wh.project([og.vd.sine((1, 0, -1)), og.cosine((0, 1, -1)), {}]))
    rows = [shell_test(dilation(seed, n), n, "genuinely 3D seed") for n in (1, 2, 4)]
    rows += [shell_test(fourth, 1, "fourth-shell receiver"),
             shell_test(mixed, 1, "mixed polarizations and phases"),
             shell_test(wh.project([og.cosine((1, 1, 0)), {}, {}]), 1, "zero-interaction wave")]
    require(rows[0]["joint_source_return"] == "7/2" and rows[0]["stretching_return"] == "1/2",
            "explicit three-dimensional physical source coefficients")
    result = {"shell_fixtures": rows, "reflection_balanced": balanced_test(),
              "full_physical_jets": [physical_jet(seed, nu) for nu in (Q(1)/3, Q(2))],
              "integrated_cost": scalar_checks(),
              "scope": "Initial spectral balance can generate strictly positive stretching through actual internal energy transfer. The uniform first-return law and positive-viscosity intervals do not establish repeated indefinite renewal or refute a finite full-datum allowance.",
              "status": "Exact full Fourier and rational checks passed. Uniform shell, PDE interval and small-viscosity-clock arguments remain analytic, not Lean-certified."}
    dependencies = [Path(__file__), Path(js.__file__), Path(og.__file__), Path(hr.__file__),
                    Path(f.__file__), Path(wh.__file__), Path(am.__file__)]
    result["source_sha256"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies}
    print(json.dumps(result, indent=2), flush=True)
