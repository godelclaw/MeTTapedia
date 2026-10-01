#!/usr/bin/env python3
"""Exact heat/log-gradient observation test on a divergence-free Fourier frame.

The two composition conventions give different observations. Both start
from zero velocity and have a nonzero projected fluid residual. This is
an obstruction to an unrestricted observation map, not an NS solution
from zero data. Continuous group identification is analytic in README.md.
"""

import json
import sympy as s


def require_zero(value, label):
    if isinstance(value, s.MatrixBase):
        passed = all(s.simplify(v) == 0 for v in value)
    else:
        passed = s.simplify(value) == 0
    if not passed:
        raise ArithmeticError(label + ': ' + str(value))


def delayed_observation(m, nu, t):
    # sin(x)^(2m+1) has a zero of order 2m+1 at the origin.
    # A transverse frame frequency adds kappa to every heat rate.
    coefficients = [(2*j+1, (-1)**j*s.binomial(2*m+1,m-j)/4**m)
                    for j in range(m+1)]
    z = s.symbols('z', real=True)
    require_zero(s.expand_trig(sum(c*s.sin(n*z) for n,c in coefficients))
                 -s.sin(z)**(2*m+1), 'exact odd-power Fourier expansion')
    rows = []
    for kappa in (0,1):
        moments = [s.expand(sum(c*n*(-nu*(n*n+kappa))**r*nu
                               for n,c in coefficients)) for r in range(m+1)]
        for r in range(m):
            require_zero(moments[r], 'matching initial velocity jets')
        require_zero(moments[m]-s.factorial(2*m+1)*nu**(m+1),
                     'first nonzero observed velocity jet')
        a = nu*sum(c*n*s.exp(-(n*n+kappa)*nu*t) for n,c in coefficients)
        require_zero(s.diff(a,t,m).subs(t,0)-moments[m], 'independent time derivative')
        rows.append({'kappa':kappa,'zero_time_jets':list(range(m)),
                     'first_nonzero_order':m,'first_nonzero_value':str(moments[m])})
    return {'m':m,'initial_profile':'2+sin(x)^(2m+1)',
            'positive_lower_bound':1, 'observations':rows}


def main():
    x = s.symbols('x y z', real=True)
    t = s.symbols('t', real=True)
    nu = s.symbols('nu', positive=True)
    lap = lambda f: sum(s.diff(f, q, 2) for q in x)
    origin = dict.fromkeys(x, 0)
    frame = []
    for j in range(3):
        for k in range(3):
            if j == k:
                continue
            for trig in (s.cos, s.sin):
                e = s.zeros(3, 1)
                e[j] = trig(x[k])/s.sqrt(2)
                frame.append(e)
    require_zero(sum((e*e.T for e in frame), s.zeros(3))-s.eye(3),
                 'pointwise tight frame')
    require_zero(sum((e.jacobian(x)*e for e in frame), s.zeros(3, 1)),
                 'zero frame transport drift')
    for e in frame:
        require_zero(sum(s.diff(e[j], x[j]) for j in range(3)), 'solenoidal frame')
    kernel_column = sum((e[0].subs(origin)*e for e in frame), s.zeros(3, 1))
    expected = s.Matrix([(s.cos(x[1])+s.cos(x[2]))/2, 0, 0])
    require_zero(kernel_column-expected, 'observer kernel column')
    require_zero(kernel_column.subs(origin)-s.Matrix([1, 0, 0]), 'identity covariance')

    phi = 2+s.exp(-nu*t)*s.sin(x[0])-s.exp(-4*nu*t)*s.sin(2*x[0])/2
    W = -2*nu*s.log(phi)
    require_zero(s.diff(phi, t)-nu*lap(phi), 'complete scalar heat equation')
    require_zero(s.diff(W, t)-nu*lap(W)+sum(s.diff(W, q)**2 for q in x)/2,
                 'complete scalar Cole-Hopf HJB')
    require_zero(phi.subs(origin)-2, 'positive fixed observed value')
    require_zero(s.diff(phi, x[0]).subs(origin).subs(t, 0), 'zero initial gradient')
    a_post = nu*(s.exp(-nu*t)-s.exp(-4*nu*t))
    require_zero(-s.diff(W, x[0]).subs(origin)-a_post, 'postcomposition observer')

    # For precomposition, Phi(t,g)=P_t(phi0 composed with g)(0).
    # Its frame derivative is P_t(E_i dot grad phi0)(0), not
    # E_i(0) dot grad P_t(phi0)(0). Check each eigenfunction used.
    pre_coefficients = []
    for e in frame:
        f1 = e[0]*s.cos(x[0])
        f2 = e[0]*s.cos(2*x[0])
        require_zero(lap(f1)+2*f1, 'first precomposition heat eigenfunction')
        require_zero(lap(f2)+5*f2, 'second precomposition heat eigenfunction')
        pre_coefficients.append(nu*(s.exp(-2*nu*t)*f1.subs(origin)
                                   -s.exp(-5*nu*t)*f2.subs(origin)))
    a_pre = nu*(s.exp(-2*nu*t)-s.exp(-5*nu*t))
    require_zero(sum((c*e for c, e in zip(pre_coefficients, frame)), s.zeros(3, 1))
                 -a_pre*kernel_column, 'precomposition observer')

    rows = []
    for name, a in [('postcomposition', a_post), ('precomposition', a_pre)]:
        u = a*kernel_column
        transport = u.jacobian(x)*u
        require_zero(transport, name+' actual convective term')
        require_zero(sum(s.diff(u[j], x[j]) for j in range(3)), name+' incompressibility')
        require_zero(u.subs(t, 0), name+' zero initial velocity')
        force = u.diff(t)+transport-nu*u.applyfunc(lap)
        residual_amplitude = s.simplify(s.diff(a, t)+nu*a)
        require_zero(force-residual_amplitude*kernel_column, name+' full momentum residual')
        require_zero(force.subs(t, 0)-3*nu**2*kernel_column, name+' nonzero initial source')
        require_zero(s.diff(force[0], x[1]).subs({t:0,x[1]:s.pi/2})+3*nu**2/2,
                     name+' nonzero curl component at the initial time')
        # Normalized spatial mean of the kernel's squared norm is 1/4.
        require_zero(s.integrate(s.integrate(kernel_column.dot(kernel_column),
                         (x[1],-s.pi,s.pi)), (x[2],-s.pi,s.pi))/(2*s.pi)**2
                     -s.Rational(1,4), 'exact kinetic coefficient')
        energy = a*a/4
        work = a*residual_amplitude/4
        require_zero(s.diff(energy,t)+2*nu*energy-2*work, 'complete forced energy ledger')
        rows.append({'convention':name, 'amplitude':str(a),
                     'residual_amplitude':str(residual_amplitude),
                     'initial_acceleration':'3*nu**2 * kernel_column',
                     'kinetic_energy':str(energy)})
    print(json.dumps({'frame_fields':len(frame), 'heat_lower_bound':'1/2 for nu,t>=0',
                      'observations':rows,
                      'delayed_observations':[delayed_observation(m,nu,t) for m in range(1,7)],
                      'scope':'exact finite frame and scalar identities; no unforced NS realization'},indent=2))


if __name__ == '__main__':
    main()
