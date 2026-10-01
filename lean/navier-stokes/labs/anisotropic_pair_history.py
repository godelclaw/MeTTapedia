#!/usr/bin/env python3
"""Complete sixth mixed stretching at arbitrary positive parent frequencies.

The symbolic recurrence uses exact rational functions of squared frequencies,
retains canonical pressure and every generated mode, and checks both energy
ledgers. Independent rational recurrences use literal physical curl stretching.
The all-time sign certificate is in MettapediaNS.AnisotropicCycleHistory;
identification with continuous NS derivatives is analytic, not Lean-certified.
Higher interaction orders and an arbitrary-data history bound remain open.
"""
import json
import math
import time
import itertools
from collections import defaultdict
import paired_stretching_history as p
import sympy as s
from sympy.polys.fields import field
F, a, b, c = field('a,b,c', s.QQ)
A, B, C = s.symbols('a b c')
axis = (C, A, B)
# In coordinates with base integer wavevector k, put v_i=r_i*u_i,
# where r_i^2=(c,a,b). Advection is v.grad(v); Leray projection uses
# diag(c,a,b), and physical energy uses diag(1/c,1/a,1/b).
# All initial v amplitudes are one. The mixed sixth coefficient is
# multiplied by a*b*c to recover unit physical u amplitudes.

def Q(x=0, y=1):
    def coerce(z):
        if isinstance(z, s.Basic):
            return F.from_expr(z)
        return F(z)
    return coerce(x)/coerce(y)


require = p.require

def clean(a):
    return {k: v for k, v in a.items() if v}

def scale(c, a):
    return clean({k: Q(c)*v for k, v in a.items()})

def add(*arrays):
    result = defaultdict(Q)
    for a in arrays:
        for k, v in a.items():
            result[k] += v
    return clean(result)

def multiply(a, b):
    result = defaultdict(Q)
    for (i, j), v in a.items():
        for (k, ell), w in b.items():
            result[i+k, j+ell] += v*w
    return clean(result)

def heat_convolution(a, damping):
    """Integral_0^t exp[-damping*(t-r)] a(r) dr, including resonance."""
    result = defaultdict(Q)
    for (i, j), v in a.items():
        if i == damping:
            result[i, j+1] += v/Q(j+1)
            continue
        beta = damping-i
        for k in range(j+1):
            result[i, j-k] += v*Q((-1)**k*math.factorial(j),
                                    math.factorial(j-k)*beta**(k+1))
        result[damping, 0] -= v*Q((-1)**j*math.factorial(j), beta**(j+1))
    return clean(result)

def jet(a, order):
    for _ in range(order):
        a = derivative(a)
    return sum((v for (_, j), v in a.items() if j == 0), Q(0))

def dot(a, b):
    return add(*(multiply(x, y) for x, y in zip(a, b)))

def vector_scale(c, a):
    return tuple(scale(c, z) for z in a)

def vector_add(a, b):
    return tuple(add(x, y) for x, y in zip(a, b))

def field_add(arrays):
    result = {}
    for u in arrays:
        for k, a in u.items():
            result[k] = vector_add(result.get(k, ({}, {}, {})), a)
    return {k: a for k, a in result.items() if any(a)}

def advection(u, v):
    # Write the odd real velocity coefficient as u_hat(k)=i*a(k).
    # Then -u.grad(v) has coefficient i*sum (a(p).q)*b(q).
    result = {}
    for p, a in u.items():
        for q, b in v.items():
            k = tuple(x+y for x, y in zip(p, q))
            factor = add(*(scale(q[i], a[i]) for i in range(3)))
            if factor:
                result[k] = vector_add(result.get(k, ({}, {}, {})),
                                       tuple(multiply(factor, z) for z in b))
    return {k: a for k, a in result.items() if any(a)}


def derivative(ep):
    result = defaultdict(Q)
    for (lam, j), v in ep.items():
        if j:
            result[lam, j-1] += j*v
        result[lam, j] -= Q(lam)*v
    return clean(result)


def norm(k):
    return sum(axis[i]*k[i]**2 for i in range(3))


def project(source):
    out, pressure = {}, {}
    for k, v in source.items():
        n = norm(k)
        if n:
            pr = scale(Q(1, n), add(*(scale(k[i], v[i]) for i in range(3))))
            if pr:
                pressure[k] = pr
            z = tuple(add(v[i], scale(-axis[i]*k[i], pr)) for i in range(3))
        else:
            z = v
        if any(z):
            out[k] = z
    return out, pressure


def weighted_pair(u, v, order):
    return add(*(scale(Q(norm(k)**order, axis[i]), multiply(vec[i], v.get(k, ({}, {}, {}))[i]))
                 for k, vec in u.items() for i in range(3)))


def fields(omit=None):
    initial = {}
    for i, j in enumerate((1, 2, 0)):
        if i == omit:
            continue
        k = tuple(int(ell == j) for ell in range(3))
        z = tuple({(norm(k), 0): Q(-1, 2)} if ell == i else {} for ell in range(3))
        initial[k] = z
        initial[tuple(-q for q in k)] = vector_scale(-1, z)
    U, N, P = [{}, initial], [{}, {}], [{}, {}]
    for m in range(2, 6):
        source, pressure = project(field_add(advection(U[i], U[m-i]) for i in range(1, m)))
        N.append(source)
        P.append(pressure)
        U.append({k: tuple(heat_convolution(z, norm(k)) for z in v) for k, v in source.items()})
    for m in range(1, 6):
        require((0, 0, 0) not in U[m], ('zero symbolic mean velocity', m))
        for k, v in U[m].items():
            require(not add(*(scale(k[i], v[i]) for i in range(3))),
                    ('symbolic solenoidality', m, k))
            require(tuple(add(derivative(z), scale(norm(k), z)) for z in v)
                    == N[m].get(k, ({}, {}, {})), ('complete symbolic equation', m, k))
            require(U[m].get(tuple(-q for q in k)) == vector_scale(-1, v),
                    ('symbolic reality', m, k))
            if m > 1:
                require(all(jet(z, 0) == 0 for z in v), ('zero generated datum', m, k))
    if omit is not None:
        require(not any(P), 'complete pair pressure remains zero')
    return U, N, P


def observe(U, N, P):
    G = add(*(weighted_pair(U[i], N[6-i], 1) for i in range(1, 6)))
    Z = add(*(weighted_pair(U[i], U[6-i], 1) for i in range(1, 6)))
    D = add(*(weighted_pair(U[i], U[6-i], 2) for i in range(1, 6)))
    E = add(*(weighted_pair(U[i], U[6-i], 0) for i in range(1, 6)))
    require(not add(derivative(Z), scale(2, D), scale(-2, G)), 'full symbolic enstrophy balance')
    require(not add(derivative(E), scale(2, Z)), 'full symbolic kinetic balance')
    return G, Z, D


def signed_formula():
    """The exact expression certified by AnisotropicCycleHistory in Lean."""
    total = a+b+c
    slope = 2*total/3
    decay = 2*(A+B+C)
    result = {(decay,3): -a*b*c/4}
    for x,y,z,Zexpr in ((a,b,c,C),(b,c,a,A),(c,a,b,B)):
        weight = 3*x*y**2/(32*z**2*total)
        rate = 2*z
        remainder = {(decay-2*Zexpr,0): Q(1), (decay-2*Zexpr,1): -slope,
                     (decay,0): Q(-1), (decay,1): -(rate-slope),
                     (decay,2): -(rate**2-2*slope*rate)/2,
                     (decay,3): -(rate**3-3*slope*rate**2)/6}
        result = add(result,scale(weight,remainder))
    return result


def specialize(ep, radii):
    substitutions = dict(zip((A,B,C),(r*r for r in radii)))
    result = defaultdict(p.Q)
    for (lam,j),value in ep.items():
        result[int(lam.subs(substitutions)),j] += p.Q(str(value.as_expr().subs(substitutions)))
    return p.clean(result)


def rational_check(radii, expected):
    full = p.amplitude_fields((1,1,1),5,radii)
    O = p.observers(*full[:2],6)
    pairs = [p.observers(*p.amplitude_fields(tuple(int(i!=omit) for i in range(3)),5,radii)[:2],6)
             for omit in range(3)]
    mixed = [p.add(o,*(p.scale(-1,pair[j]) for pair in pairs)) for j,o in enumerate(O)]
    require(all(value == specialize(formula,radii) for value,formula in zip(mixed,expected)),
            ('independent literal-curl coefficients',radii))
    return {'radii':radii, 'twice_integral':str(2*p.integral_infinity(mixed[0])),
            'mode_counts':list(map(len,full[0]))}


def profile_check(formula):
    profiles = (((1,p.Q(1)),(2,p.Q(1,2))),
                ((1,p.Q(2)),(3,p.Q(-1,3))),
                ((1,p.Q(3,2)),(2,p.Q(-2))))
    def initial(omit):
        result = {}
        for i,j in enumerate((1,2,0)):
            if i==omit:
                continue
            for radius,amplitude in profiles[i]:
                k = tuple(radius if ell==j else 0 for ell in range(3))
                v = tuple({(radius**2,0):-amplitude/2} if ell==i else {} for ell in range(3))
                result[k] = v
                result[tuple(-q for q in k)] = p.vector_scale(-1,v)
        return result
    full = p.evolve_amplitudes(initial(None),5)
    full_G = p.observers(*full[:2],6)[0]
    pairs = [p.observers(*p.evolve_amplitudes(initial(omit),5)[:2],6)[0] for omit in range(3)]
    expected = p.add(*(p.scale(math.prod(amplitude**2 for _,amplitude in triple),
                              specialize(formula,tuple(r for r,_ in triple)))
                       for triple in itertools.product(*profiles)))
    require(p.add(full_G,*(p.scale(-1,g) for g in pairs)) == expected,
            'complete multiharmonic history equals nonnegative spectral sum')
    return {'profiles':[[[r,str(v)] for r,v in profile] for profile in profiles],
            'mode_counts':list(map(len,full[0])),
            'complete_stretching':p.encode(expected),
            'twice_integral':str(2*p.integral_infinity(expected))}


def main():
    start = time.monotonic()
    full = fields()
    O = observe(*full)
    pairs = [observe(*fields(i)) for i in range(3)]
    mixed = [scale(a*b*c,add(o,*(scale(-1,v[i]) for v in pairs))) for i,o in enumerate(O)]
    formula = signed_formula()
    require(mixed[0] == formula, 'complete symbolic PDE equals the signed scalar formula')
    require([jet(formula,n) for n in range(4)] == [Q(0),Q(0),Q(0),-3*a*b*c/2],
            'generic initial jets')
    require(not add(derivative(mixed[1]),scale(2,mixed[2]),scale(-2,mixed[0])),
            'complete symbolic mixed signed ledger')
    integrated = sum((v*Q(2*math.factorial(j),lam**(j+1))
                      for (lam,j),v in formula.items()), Q(0))
    numerator, denominator = s.fraction(s.factor(integrated.as_expr()))
    require(all(v < 0 for v in s.Poly(numerator,A,B,C).coeffs()),
            'integrated coefficient has strictly negative numerator coefficients')
    require(all(v > 0 for v in s.Poly(denominator,A,B,C).coeffs()),
            'integrated coefficient has strictly positive denominator coefficients')
    # For a,b,c >= 1 this exact shifted polynomial proves
    # 0 <= -2*integral(gamma6) <= 5/1152, with equality at (1,1,1).
    # Homogeneity then gives 5/[1152*min(a,b,c)] for all positive scales.
    x, y, z = s.symbols('x y z')
    margin = s.Poly(s.expand((5*denominator+1152*numerator).subs(
        {A:1+x,B:1+y,C:1+z})),x,y,z)
    require(all(v >= 0 for v in margin.coeffs()) and margin.coeff_monomial(1) == 0,
            'sharp scale-uniform integrated magnitude bound')
    require(all(sum(m)==9 for m,_ in s.Poly(numerator,A,B,C).terms()) and
            all(sum(m)==10 for m,_ in s.Poly(denominator,A,B,C).terms()),
            'integrated magnitude has frequency-square homogeneity minus one')
    report = {'symbolic_stretching':[[str(lam),j,str(s.factor(v.as_expr()))]
                                    for (lam,j),v in formula.items()],
              'twice_integral_symbolic':str(s.factor(integrated.as_expr())),
              'sharp_integrated_magnitude_bound':{'constant':'5/1152',
                  'scale':'inverse minimum squared frequency',
                  'nonnegative_shifted_monomials':len(margin.terms())},
              'symbolic_mode_counts':list(map(len,full[0])),
              'symbolic_pressure_mode_counts':list(map(len,full[2])),
              'rational_checks':[rational_check(r,mixed) for r in
                                 ((1,1,1),(1,1,2),(1,2,1),(2,1,1),(1,2,3),(1,3,2),
                                  (2,2,2),(1,2,17),(1,17,2),(1,19,20))],
              'profile_check':profile_check(formula),
              'scope':'exact finite amplitude histories; PDE identification analytic; higher-order sum open'}
    report['seconds'] = time.monotonic()-start
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
