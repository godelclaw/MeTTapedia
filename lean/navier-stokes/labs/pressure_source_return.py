#!/usr/bin/env python3
"""Complete pressure-production returns on actual NS initial jets.

The Eulerian parabolic source and the material parabolic source are distinct.
Both comparisons retain every Fourier output, viscosity and canonical pressure.
The short physical intervals and source-to-clock estimate are analytic in
README.md, not numerical PDE enclosures or Lean certificates.
"""

import json
from math import comb

import sympy as s
import pressure_history_source as f
from pressure_adaptive_storage import avg, datum
from pressure_impulse_return import NU, require, specialize, viscosity_jets
from pressure_oblique_return import cubic_forecast_jets


def parabolic_source(pressure):
    return [f.add(pressure[n+1], f.scale(-NU, f.lap(pressure[n])))
            for n in range(3)]


def material_source(velocity, pressure):
    source = parabolic_source(pressure)
    return [f.add(source[n], *(f.scale(comb(n, j),
                    f.adv(velocity[j], pressure[n-j])) for j in range(n+1)))
            for n in range(3)]


def gradient_pair(a, b):
    return avg(f.dot(f.grad(a), f.grad(b)))


def norm_coefficients(source):
    """Coefficients of 1,t,t^2; the source entries are time derivatives."""
    return [gradient_pair(source[0], source[0]),
            2*gradient_pair(source[0], source[1]),
            gradient_pair(source[1], source[1])+gradient_pair(source[0], source[2])]


def source_stress_jets(velocity, pressure):
    """Independent pressure equation, differentiated with every product term."""
    # NS: (partial_t-nu Delta)u=-N, N=u.grad u+grad p.
    # Xi=T[-N tensor u-u tensor N-2nu sum_k partial_k u tensor partial_k u].
    N = [[f.add(f.diff(pressure[n], i), *(f.scale(comb(n, j),
                  f.adv(velocity[j], velocity[n-j][i])) for j in range(n+1)))
          for i in range(3)] for n in range(3)]
    answer = []
    for n in range(3):
        tensor = [[f.add(*(f.scale(-comb(n, j), f.add(
            f.mul(N[j][i], velocity[n-j][ell]),
            f.mul(velocity[j][i], N[n-j][ell]),
            f.scale(2*NU, f.add(*(f.mul(f.diff(velocity[j][i], k),
                                      f.diff(velocity[n-j][ell], k))
                                 for k in range(3)))))) for j in range(n+1)))
                   for ell in range(3)] for i in range(3)]
        answer.append(f.tensor_pressure(tensor))
    return answer


def first_source_split(velocity, pressure):
    """Separate convection and canonical-pressure feedback at zero viscosity."""
    u = velocity[0]
    tangent = [specialize(a, 0) for a in velocity[1]]
    convection = [f.adv(u, a) for a in u]
    tangent_convection = [f.add(f.adv(tangent, a), f.adv(u, b))
                          for a, b in zip(u, tangent)]
    C = f.tensor_pressure([[f.scale(-1, f.add(
        f.mul(tangent_convection[i], u[j]), f.mul(convection[i], tangent[j]),
        f.mul(tangent[i], convection[j]), f.mul(u[i], tangent_convection[j])))
        for j in range(3)] for i in range(3)])
    gp = f.grad(pressure[1])
    P = f.tensor_pressure([[f.scale(-1, f.add(f.mul(gp[i], u[j]),
                                              f.mul(u[i], gp[j])))
                           for j in range(3)] for i in range(3)])
    return C, P


EXPECTED = {
    0: (s.Rational(-21, 8), s.Rational(-39, 8)),
    1: (s.Rational(-4793, 2310), s.Rational(-14899, 3696)),
    2: (s.Rational(21933, 33880), s.Rational(-829, 6776)),
    4: (s.Rational(309716579, 747358920), s.Rational(96960167, 448415352)),
    8: (s.Rational(26424288654209, 659937034454040),
        s.Rational(-3371825506417, 131987406890808)),
}


def check_fixture(m):
    u = datum(m)
    f.equal(f.trace(f.jac(u)), {}, 'Smooth solenoidal original datum')
    require(all(avg(a) == 0 for a in u), 'Fixed zero-mean frame')
    velocity, pressure = viscosity_jets(u, 4)
    forecast = cubic_forecast_jets(u)
    require(not pressure[0] and not forecast[0], 'Both pressures initially vanish')
    z, zb = parabolic_source(pressure), parabolic_source(forecast)
    for a, b in zip(z, source_stress_jets(velocity, pressure)):
        f.equal(a, b, 'Full evolving pressure source agrees with the NS stress equation')
    actual, reference = norm_coefficients(z), norm_coefficients(zb)
    delta = [s.factor(a-b) for a, b in zip(actual, reference)]
    require(delta == [0, 0, EXPECTED[m][0]], 'Complete Eulerian comparison at every viscosity')
    dz = [f.add(a, f.scale(-1, b)) for a, b in zip(z, zb)]
    require(not dz[0], 'Same original pressure-producing capacity')
    f.equal(dz[1], specialize(dz[1], 0), 'First new source has no discarded viscosity terms')
    parts = [gradient_pair(dz[1], dz[1]), gradient_pair(z[0], dz[2]),
             2*gradient_pair(zb[1], dz[1])]
    require(s.expand(sum(parts)-delta[2]) == 0 and parts[2] == 0,
            'New-source square and complete signed return account for the difference')
    require(parts[0] > 0 and parts[1] < 0,
            'Generated source is positive while the old-source pairing is depleting')

    # The exact source energy balance retains its complete diffusion.
    W = [f.add(z[n+1], f.scale(-NU, f.lap(z[n]))) for n in range(2)]
    D0 = avg(f.mul(f.lap(z[0]), f.lap(z[0])))
    D1 = 2*avg(f.mul(f.lap(z[0]), f.lap(z[1])))
    nu = s.Symbol('nu')
    require(s.expand(actual[1]+2*nu*D0-2*gradient_pair(z[0], W[0])) == 0,
            'Complete source-energy identity at the initial time')
    require(s.expand(2*actual[2]+2*nu*D1-2*gradient_pair(z[1], W[0])
                     -2*gradient_pair(z[0], W[1])) == 0,
            'The first source-energy return retains the differentiated dissipation')

    # Use the same actual drift on both pressures. This reference is a
    # diagnostic, not an independently paid or physically reconstructed flow.
    y, yb = material_source(velocity, pressure), material_source(velocity, forecast)
    ma, mr = norm_coefficients(y), norm_coefficients(yb)
    md = [s.factor(a-b) for a, b in zip(ma, mr)]
    require(md == [0, 0, EXPECTED[m][1]], 'Complete material comparison at every viscosity')
    transport = [2*gradient_pair(f.adv(u, pressure[1]), dz[1]),
                 gradient_pair(z[0], f.adv(u, dz[1]))]
    require(s.expand(delta[2]+sum(transport)-md[2]) == 0,
            'Retained advective-gradient terms explain the changed comparison')

    C, P = first_source_split(velocity, pressure)
    f.equal(f.add(C, P), dz[1], 'New source includes convection and pressure feedback')
    creation_parts = [gradient_pair(C, C), gradient_pair(P, P), 2*gradient_pair(C, P)]
    require(s.expand(sum(creation_parts)-parts[0]) == 0,
            'Joint convection-pressure correlation is retained')
    if m == 2:
        require(len(z[0]) == 8 and len(dz[1]) == 28 and not set(z[0]) & set(dz[1]),
                'New source modes are outside the original pressure-source support')
        original = [{k: a for k, a in field.items() if k in z[0]} for field in z]
        generated = [{k: a for k, a in field.items() if k not in z[0]} for field in z]
        require([s.factor(a-b) for a, b in zip(norm_coefficients(original), reference)]
                == [0, 0, parts[1]], 'Original source modes retain the depleting return')
        require(norm_coefficients(generated) == [0, 0, parts[0]],
                'The disjoint generated modes supply exactly the new positive cost')
        require(actual == [s.Rational(21, 22), -179*nu/11,
                            4655*nu**2/33+s.Rational(21933, 33880)],
                'Explicit viscous source-resource expansion')
        require(parts[:2] == [s.Rational(33821, 12705), -s.Rational(204769, 101640)],
                'Explicit depleting return is outweighed by generated source')
    return dict(m=m, eulerian_actual=list(map(str, actual)),
                eulerian_forecast=list(map(str, reference)), eulerian_difference=list(map(str, delta)),
                original_source_modes=len(z[0]), new_source_modes=len(dz[1]),
                source_supports_disjoint=not bool(set(z[0]) & set(dz[1])),
                new_source_square=str(parts[0]), old_source_return=str(parts[1]),
                thermal_cross=str(parts[2]),
                convection_pressure_parts=list(map(str, creation_parts)),
                material_actual=list(map(str, ma)), material_reference=list(map(str, mr)),
                material_difference=list(map(str, md)), transport_corrections=list(map(str, transport)))


def rebound_algebra():
    d, k = s.Rational(179, 11), s.Rational(21933, 33880)
    c = 2*d/k
    require(c == s.Rational(1102640, 21933) and -d*c+k*c*c == k*c*c/2,
            'Later source rebound outweighs the initial viscous loss')
    return dict(d=str(d), k=str(k), c=str(c),
                normalized_time='tau=c*mu, mu<=min(1,T0/c,k/(4*B*c))',
                physical_time='t=c*nu/lambda^2, lambda>=nu/mu_star',
                physical_gain='Q(t)-Q(0)>=(k*c^2/4)*nu^2*lambda^4',
                limitation='T0 and B come from uniform local H14 theory; not numerically evaluated')


if __name__ == '__main__':
    print(json.dumps(dict(status='All exact checks passed',
                          fixtures=[check_fixture(m) for m in (0, 1, 2, 4, 8)],
                          rebound=rebound_algebra(),
                          scope='Complete NS jets and algebra; short physical intervals and continuation consumer analytic',
                          limitation='No arbitrary-data payment, singularity construction, numerical PDE enclosure or new Lean certificate'), indent=2))
