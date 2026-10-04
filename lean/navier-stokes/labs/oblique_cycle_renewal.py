#!/usr/bin/env python3
"""Full pressure-work renewal laws for an unbounded oblique cyclic family.

Phase coordinates retain the ordinary Euclidean derivatives and inverse
Laplacian. All convolution outputs are kept. Independent physical Fourier
specializations check the coordinate calculation. Actual local NS intervals
and the general short-age asymptotics are analytic in README.md.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import heat_work_reserve as h
from heat_remainder_pressure import require, plus, times
from generated_fourth_moment import fourth_work
from cyclic_pressure_history import velocity_time_jets


K = f.QQ_I.frac_field('m')
R = K.poly_ring('a', 'b', 'c', 'x', 'y', 'z')
M = R.ring.ground_new(K.gens[0])
A, B, C, X, Y, Z = R.gens
m, a, b, c, x, y, z = s.symbols('m a b c x y z')


def wave(j):
    key = tuple(int(i == j) for i in range(3))
    return {key: R.convert(-f.II/2), tuple(-k for k in key): R.convert(f.II/2)}


def frequency(k):
    # Phase order is (y,z,x+m*y); components remain physical (x,y,z).
    return k[2], k[0]+M*k[2], k[1]


def diff(field, j):
    return f.clean({k: R.convert(f.II)*frequency(k)[j]*value for k, value in field.items()})


def grad(field):
    return [diff(field, j) for j in range(3)]


def lap(field):
    return f.clean({k: -sum(q*q for q in frequency(k))*value for k, value in field.items()})


def green(field):
    return {k: value/sum(q*q for q in frequency(k)) for k, value in field.items() if k != f.ORIGIN}


def jac(v):
    return [grad(row) for row in v]


def pressure(v):
    return green(f.add(*(diff(diff(f.mul(v[i], v[j]), i), j) for i in range(3) for j in range(3))))


def pressure_variation(v, tangent):
    tensor_form = green(f.add(*(diff(diff(f.add(f.mul(v[i], tangent[j]),
                        f.mul(tangent[i], v[j])), i), j) for i in range(3) for j in range(3))))
    gradient_form = green(f.scale(2, f.trace(f.matmul(jac(v), jac(tangent)))))
    f.equal(tensor_form, gradient_form, 'Independent complete pressure-variation formulas')
    return tensor_form


def nonlinear(v):
    return [f.scale(-1, f.add(f.dot(v, grad(row)), gp)) for row, gp in zip(v, grad(pressure(v)))]


def heat(v):
    # x=exp(-s), y=exp(-(m-1)^2*s), z=exp(-2*m*s).
    # Every heated input here is an original mode or a complete quadratic
    # output, so the indicated exponents are nonnegative. Only the shear
    # enters denominators; strengths and heat weights remain polynomial.
    result=[]
    for row in v:
        require(all(k[2]**2+k[0]*k[2]>=0 for k in row), 'The stated complete inputs have polynomial heat weights')
        result.append({k:value*X**(k[0]**2+k[1]**2)*Y**(k[2]**2)*Z**(k[2]**2+k[0]*k[2])
                       for k,value in row.items()})
    return result


def average(field):
    value = s.factor(R.to_sympy(R.convert(field.get(f.ORIGIN, f.ZERO))))
    require(not value.has(s.I), 'Every complete spatial average is real')
    return value


def variation(v, tangent):
    magnitude, cross = f.dot(v, v), f.dot(v, tangent)
    receiver = [f.mul(magnitude, row) for row in v]
    receiver_change = [f.add(f.mul(magnitude, tangent[j]), f.scale(2, f.mul(cross, v[j]))) for j in range(3)]
    pt = pressure_variation(v, tangent)
    result = -average(f.add(f.dot(receiver_change, grad(pressure(v))), f.dot(receiver, grad(pt))))
    divergence = f.add(*(diff(receiver[j], j) for j in range(3)))
    alternative = -average(f.dot(receiver_change, grad(pressure(v))))+average(f.mul(divergence, pt))
    require(s.cancel(result-alternative) == 0, 'Pressure work retains its exact integration by parts')
    return result


def symbolic_family():
    U = [f.add(f.scale(A, wave(0)), f.scale(-M*B, wave(1))),
         f.scale(B, wave(1)), f.scale(C, wave(2))]
    matrix = jac(U)
    f.equal(f.trace(matrix), {}, 'Incompressibility for every shear and all amplitudes')
    f.equal(pressure(U), {}, 'The original pressure is zero')
    heated = heat(U)
    f.equal(pressure(heated), {}, 'The entire physical free-heat pressure is zero')
    source = nonlinear(U)
    f.equal(f.trace(jac(source)), {}, 'The complete nonlinear source is solenoidal')
    determinant = f.add(*(f.scale(sign, f.mul(matrix[0][p[0]], f.mul(matrix[1][p[1]], matrix[2][p[2]])))
                         for p, sign in [((0,1,2),1),((1,2,0),1),((2,0,1),1),
                                         ((2,1,0),-1),((1,0,2),-1),((0,2,1),-1)]))
    cubic_trace = f.trace(f.matmul(f.matmul(matrix, matrix), matrix))
    f.equal(cubic_trace, f.scale(3, determinant), 'The three-component loop is the gradient determinant')
    pt = pressure_variation(U, source)
    f.equal(pt, green(f.scale(-6, determinant)), 'The actual first pressure source is the complete cubic loop')
    f.equal(pressure_variation(U, [lap(row) for row in U]), {},
            'Positive viscosity does not alter this first pressure derivative')

    full = variation(heated, heat(source))
    intrinsic = variation(heated, nonlinear(heated))
    base = m*m+3
    dm, dp = base-2*m, base+2*m
    strength = a*a*b*b*c*c
    expected_full = m*strength*x**4*y**2/s.Integer(4)*(2*(1/dm-1/dp)*z*z+z/dm-z**3/dp)
    expected_intrinsic = 3*m*m*strength*x**4*y**2*z*z/(dm*dp)
    require(s.cancel(full-expected_full) == 0, 'Exact full heat-history renewal for all family members')
    require(s.cancel(intrinsic-expected_intrinsic) == 0, 'Exact intrinsic renewal of the heated geometry')
    covariance = s.factor(full-intrinsic)
    positive_covariance = m*strength*x**4*y**2*z*(1-z)/s.Integer(4)*(1/dm+z/dp)
    require(s.cancel(covariance-positive_covariance) == 0,
            'Both covariance contributions have favorable sign for renewal, not depletion')
    full_int = m*strength/s.Integer(4)*((1/dm-1/dp)/base
                     +1/(2*dm*(base-m))-1/(2*dp*(base+m)))
    intrinsic_int = 3*m*m*strength/(2*base*dm*dp)
    covariance_int = s.factor(full_int-intrinsic_int)
    expected_covariance_int = m*m*strength*(m**4+8*m*m+9)/(4*base*dm*dp*(base-m)*(base+m))
    require(s.cancel(covariance_int-expected_covariance_int) == 0, 'Positive exact covariance payment deficit')
    slope = s.factor((-x*s.diff(covariance,x)-(m-1)**2*y*s.diff(covariance,y)
                     -2*m*z*s.diff(covariance,z)).subs({x:1,y:1,z:1}))
    require(s.cancel(slope-m*m*base*strength/(dm*dp)) == 0, 'Covariance begins one heat-age order later')
    ratio=s.cancel(covariance_int/full_int)
    denominator=7*m**4+38*m*m+63
    require(s.cancel(ratio-s.Rational(1,7)-18*m*m/(7*denominator))==0,
            'The exact covariance fraction exceeds one seventh')
    require(s.cancel(s.Rational(7,40)-ratio-9*(m*m-3)**2/(40*denominator))==0,
            'The exact covariance fraction is at most seven fortieths')

    # Exact complete viscosity cost for the equal-amplitude subfamily.
    unit = [{k: value.subs(A,1).subs(B,1).subs(C,1) for k,value in row.items()} for row in U]
    mag = f.dot(unit,unit)
    J = jac(unit)
    diffusion = average(f.add(f.mul(mag, f.add(*(f.mul(v,v) for row in J for v in row))),
          f.scale(2, f.add(*(f.mul(f.dot(unit,[diff(row,j) for row in unit]),
                                f.dot(unit,[diff(row,j) for row in unit])) for j in range(3))))))
    require(s.cancel(diffusion-(5*m**4+29*m*m+21)/8)==0, 'Complete quartic diffusion for all shears')
    require(s.cancel(average(f.mul(mag,mag))-(3*m**4+22*m*m+21)/8)==0,
            'Fourth moment of the same actual initial field')
    u, r = s.symbols('u r')
    margin_num=32*u*(1+u)**4*(7*u*u+38*u+63)-(5*u*u+29*u+21)*(u+3)*(u*u+2*u+9)*(u*u+5*u+9)
    coefficients=s.Poly(s.expand(margin_num.subs(u,1+r)),r).all_coeffs()
    require(all(c>0 for c in coefficients), 'An explicit amplitude pays the full positive-viscosity growth threshold')
    return dict(full=str(s.factor(full)), intrinsic=str(s.factor(intrinsic)),
                covariance=str(covariance), positive_covariance=str(positive_covariance),
                full_integral=str(s.factor(full_int)), intrinsic_integral=str(s.factor(intrinsic_int)),
                covariance_integral=str(covariance_int), covariance_fraction=str(s.factor(ratio)),
                covariance_initial_slope=str(slope),
                diffusion=str(s.factor(diffusion)), threshold_shift_coefficients=list(map(str,coefficients)))


def physical_specializations(symbolic):
    rows=[]
    for shear, strengths in ((0,(1,1,1)),(1,(1,1,1)),(2,(1,1,1)),
                              (4,(1,1,1)),(-2,(2,-1,3)),(2,(1,0,1))):
        U=h.weighted_datum(shear,strengths)
        heatU=h.heat(U)
        require(h.profile(heatU)==0,'Independent ordinary Fourier heat-work profile')
        full=h.variation(heatU,h.heat(h.nonlinear(U)))
        intrinsic=h.variation(heatU,h.nonlinear(heatU))
        substitution={m:shear,a:strengths[0],b:strengths[1],c:strengths[2],
                      x:h.q,y:h.q**((shear-1)**2),z:h.q**(2*shear)}
        for actual,key in ((full,'full'),(intrinsic,'intrinsic')):
            require(s.cancel(actual-s.sympify(symbolic[key]).subs(substitution))==0,
                    'Physical metric, source and all retained output modes agree with the symbolic law')
        nu=Q(2,7)
        tangent, pressures=velocity_time_jets(U,nu,2)
        pressure_t=pressures[1]
        matrix=f.jac(U)
        expected=f.green(f.scale(-2,f.trace(f.matmul(f.matmul(matrix,matrix),matrix))))
        f.equal(pressure_t,expected,'Independent full viscous pressure derivative')
        physical=h.variation(heatU,h.heat(tangent[1]))
        require(s.expand(physical-full)==0,'The actual positive-viscosity initial renewal keeps every parent')
        if shear and all(strengths):
            require(h.integrate(full)>0,'The selected full renewal is strictly positive')
        else:
            require(full==intrinsic==0,'The orthogonal or missing-parent branch has zero initial work renewal')
        rows.append(dict(shear=shear,strengths=list(strengths),viscosity=str(nu),
                         full_integral=str(h.integrate(full)),diffusion=str(fourth_work(U)[1])))
    return rows


def checks():
    symbolic=symbolic_family()
    result=dict(symbolic=symbolic,physical=physical_specializations(symbolic),
                scope='Exact complete family identities and positive-viscosity initial tangents. Actual local intervals and short-age asymptotics are analytic, not Lean-certified.')
    root=Path(__file__).resolve().parent
    names=['oblique_cycle_renewal.py','heat_work_reserve.py','pressure_history_source.py',
           'heat_remainder_pressure.py','generated_fourth_moment.py','cyclic_pressure_history.py',
           'pressure_gradient_stock.py','pressure_quadratic_storage.py']
    result['source_sha256']={name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    return result


if __name__=='__main__':
    print(json.dumps(checks(),indent=2))
