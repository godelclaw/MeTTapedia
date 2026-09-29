#!/usr/bin/env python3
"""Differentiable excess weights and an actual unforced mixing class.

Exact algebra checks the perspective excess, its diffusion payment,
the NS reduction and a sharp-receiver interface. The stochastic solution,
uniform bounds and positive-viscosity interface persistence are analytic
arguments in the README, not numerical evolutions or general regularity.
"""
import json
import sympy as s


def zero(value, label):
    if s.simplify(value) != 0:
        raise ArithmeticError(label)


def check_perspective():
    X, h, b = s.symbols('X h b', positive=True)
    dX, dh, z, dz = s.symbols('dX dh z dz', real=True)
    active = (X-b*h)**2/X
    a = 1-b*b*h*h/(X*X)
    c = 2*b*(1-b*h/X)
    zero(s.diff(active, X)-a, 'pressure receiver weight')
    zero(s.diff(active, h)+c, 'memory payment coefficient')
    Hess = s.hessian(active, (X, h))
    inc = s.Matrix([dX, dh])
    zero((inc.T*Hess*inc)[0]-2*b*b*(h*dX-X*dh)**2/X**3,
         'positive rank-one Hessian')
    zero(2*b*h+active-X-b*b*h*h/X, 'doubled-threshold coercivity')
    zero((X-b*h)-active-b*h*(X-b*h)/X, 'below linear excess')
    for expression in (active, a, c):
        zero(expression.subs(X, b*h), 'C1 threshold matching')

    phi = (z-b)**2/z
    curvature = 2*b*b/z**3
    zero(s.diff(phi, z, 2)-curvature, 'perspective curvature')
    zero(s.diff(1-b*b/z**2, z)-curvature, 'weight gradient')
    zero(2*b-z*z*curvature-2*b*(z-b)/z,
         'curvature scale bound on z>=b')
    zero(2/b-curvature-2*(z-b)*(z*z+z*b+b*b)/(b*z**3),
         'curvature bounded by 2/b on z>=b')
    zero((2/b)*curvature-curvature**2
         -4*b*(z-b)*(z*z+z*b+b*b)/z**6,
         'diffusion controls squared receiver-weight gradient')
    return {'excess': '(X-b*h)_+^2/X', 'regularity': 'C1 and locally C1,1 for X>0',
            'coercivity': 'X<=2*b*h+excess',
            'diffusion': '2*nu*b^2*h/z^3*|grad z|^2 on z>b',
            'weight_gradient_payment': '(nu*b*h/2)*|grad a|^2<=diffusion'}


def check_unforced_reduction():
    x, y, z, t = s.symbols('x y z t', real=True)
    nu, A, B = s.symbols('nu A B', positive=True)
    q = s.exp(-nu*t)
    a = A*q*s.sin(y)
    v = s.Function('v')(x, y, t)
    u = s.Matrix([a, 0, v])
    coords = (x, y, z)
    grad = u.jacobian(coords)
    lap = lambda f: sum(s.diff(f, c, 2) for c in coords)
    zero(s.trace(grad), 'actual fluid is incompressible')
    zero(s.trace(grad*grad), 'canonical fluid pressure is zero')
    residual = u.diff(t)+grad*u-nu*u.applyfunc(lap)
    zero(residual[0], 'autonomous horizontal heat parent')
    zero(residual[1], 'zero transverse velocity')
    zero(residual[2]-(v.diff(t)+a*v.diff(x)-nu*(v.diff(x, 2)+v.diff(y, 2))),
         'literal unforced passive-component equation')

    phi = s.Function('phi')(y, t)
    mode = B*q*s.exp(s.I*x)*phi
    mode_residual = mode.diff(t)+a*mode.diff(x)-nu*lap(mode)
    zero(mode_residual-B*q*s.exp(s.I*x)*(phi.diff(t)-nu*phi.diff(y, 2)+s.I*a*phi),
         'stochastic phase equation including viscous x decay')
    allowance = A*(1-q)/nu
    zero(allowance.diff(t)-A*q, 'complete decaying-parent history')
    zero(allowance.subs(t, 0), 'parent history starts at zero')

    c11 = s.Function('c11')(y, t)
    c13, c33 = s.Function('c13')(x, y, t), s.Function('c33')(x, y, t)
    C = s.Matrix([[c11, 0, c13], [0, 0, 0], [c13, 0, c33]])
    G = grad*grad.T
    for j in range(3):
        zero(G[1, j], 'memory zero row is preserved')
        zero(G[j, 1], 'memory zero column is preserved')
    zero(G[0, 0].diff(x), 'horizontal memory component is x independent')
    zero(sum(s.diff(C[i, j], coords[i], coords[j])
             for i in range(3) for j in range(3)),
         'actual retained memory has zero canonical pressure')
    return {'fluid': '(A exp(-nu t) sin y, 0, v(x,y,t))',
            'initial_vertical_velocity': 'B sin x',
            'equation_for_v': 'v_t+A exp(-nu t)sin(y)v_x=nu(v_xx+v_yy)',
            'phase_history_bound': 'A(1-exp(-nu t))/nu',
            'pressure_and_memory_pressure': 'zero for the complete history',
            'scope': 'exact PDE reduction; Feynman-Kac and comparison are analytic'}


def check_moments():
    a, b, c = s.symbols('a b c', real=True)
    grad = s.Matrix([[0, a, 0], [0, 0, 0], [b, c, 0]])
    S = (grad+grad.T)/2
    omega = s.Matrix([c, -b, -a])
    W = omega.dot(omega)
    zero(s.trace(S*S)-W/2, 'actual mixing strain magnitude')
    zero(omega.dot(S*omega)+a*b*c, 'genuine stretching in the mixing class')
    zero((S*omega).dot(S*omega)-a*a*b*b, 'mixed strain-vorticity moment')
    zero(s.Rational(10, 21)/2+s.Rational(44, 95)-s.Rational(1399, 1995),
         'core coefficient in this class')
    zero(s.Rational(1, 5)-s.Rational(10, 21)/2+s.Rational(4, 105),
         'negative switch gap')
    return {'W': 'a^2+b^2+c^2', 'Q': 'W/2', 'V': '-a*b*c', 'Z': 'a^2*b^2',
            'L_squared': 'A^2+B^2+(A*B/nu)^2',
            'K': '(39/7)*A^2*B^2+(1399/1995)*L^4',
            'all_time_excess_allowance': 'K/(4*nu) with normalized periodic volume',
            'scope': 'analytic full-history estimate for this actual triangular NS class'}


def check_sharp_receiver():
    # The Euler solution is used only to locate a strict regular interface.
    # The README proves persistence for actual positive viscosity and memory
    # by uniform fixed-time perturbation estimates on the linear subsystem.
    x, y, t = s.symbols('x y t', real=True)
    u = s.Matrix([s.sin(y), 0, s.sin(x-t*s.sin(y))])
    coords = (x, y, s.symbols('z', real=True))
    grad = u.jacobian(coords)
    for component in u.diff(t)+grad*u:
        zero(component, 'complete inviscid comparison flow')

    r = s.symbols('r', nonnegative=True)  # cos(x)^2 at y=0,t=1
    W = 1+2*r
    core = 5*r*r/(W+1)+s.Rational(4, 7)*r+s.Rational(1399, 1995)*W*W
    gap = -s.Rational(4, 7)*r-s.Rational(4, 105)*W*W
    Y = 1+core+(gap+s.sqrt(gap*gap+1))/2
    r0 = s.Rational(3, 4)
    threshold = s.sqrt(13)/6+s.Rational(20051, 3192)
    zero(Y.subs(r, r0)-threshold, 'fixed threshold at a regular limiting interface')
    initial_upper = s.Rational(3, 2)+s.Rational(4, 7)+4*s.Rational(1399, 1995)
    if not threshold > initial_upper:
        raise ArithmeticError('threshold must exceed the full initial envelope')
    zero(gap.subs(r, r0)+s.Rational(2, 3), 'interface switch gap')
    derivative_lower = s.diff(core+gap, r).subs(r, r0)
    if not derivative_lower > 0:
        raise ArithmeticError('regular excess interface')

    point = {x: s.pi/6, y: 0, t: 1}
    B0 = s.simplify(grad.subs(point))
    S0 = (B0+B0.T)/2
    w = s.Matrix([-s.sqrt(3)/2, -s.sqrt(3)/2, -1])
    curl = s.Matrix([B0[2, 1]-B0[1, 2], B0[0, 2]-B0[2, 0], B0[1, 0]-B0[0, 1]])
    for component in curl-w:
        zero(component, 'actual vorticity at the interface')
    n = s.Matrix([-1, 1, 0])  # unnormalized interface normal
    theta = (1-2/s.sqrt(13))/2
    V, W0 = w.dot(S0*w), w.dot(w)
    Sw = S0*w
    receiver = 10*V/(W0+1)*(w*w.T)+(1-theta)*(
        s.Rational(4, 7)*(Sw*w.T+w*Sw.T)+s.Rational(20, 21)*W0*S0)
    nn = s.factor(n.dot(receiver*n))
    zero(nn+s.Rational(25, 21)*(1+2/s.sqrt(13)),
         'nonzero normal-normal jump of the physical strain receiver')
    if not nn < 0:
        raise ArithmeticError('sharp pressure receiver must have a nonzero jump')
    tf_nn = s.simplify(n.dot((receiver-s.trace(receiver)*s.eye(3)/3)*n))
    if not tf_nn < 0:
        raise ArithmeticError('trace-free receiver also has the interface defect')

    aa = s.cos(y)
    bb = s.cos(x-t*s.sin(y))
    cc = -t*aa*bb
    WW, VV, ZZ = aa*aa+bb*bb+cc*cc, -aa*bb*cc, aa*aa*bb*bb
    core_field = 5*VV*VV/(WW+1)+s.Rational(4, 7)*ZZ+s.Rational(1399, 1995)*WW*WW
    gap_field = -s.Rational(4, 7)*ZZ-s.Rational(4, 105)*WW*WW
    gradY = s.Matrix([s.simplify((s.diff(core_field, var)+theta*s.diff(gap_field, var)).subs(point))
                      for var in (x, y)])
    zero(gradY[0]+gradY[1], 'actual level normal is parallel to (-1,1,0)')
    if not gradY[0] < 0:
        raise ArithmeticError('physical level normal is nonzero')

    z = s.symbols('z', real=True)
    ramp = 3*z*z-2*z**3
    zero(s.integrate(s.diff(ramp, z), (z, 0, 1))-1, 'finite sharp-limit diffusion')
    zero(s.integrate(s.diff(ramp, z)**2, (z, 0, 1))-s.Rational(6, 5),
         'receiver derivative cost grows as 6/(5 epsilon)')
    return {'fixed_threshold': str(threshold), 'initial_upper': str(initial_upper),
            'limiting_interface': 't=1,x=pi/6,y=0',
            'normal_receiver_contraction': str(nn),
            'trace_free_normal_contraction': str(tf_nn),
            'sharp_mask_derivative_cost': '6/(5*epsilon) for a unit cubic ramp',
            'physical_memory_pressure_work': 'zero throughout this mixing family',
            'scope': 'exact limiting geometry; actual positive-viscosity persistence '
                     'and infinite sharp dual norm are analytic, not a budget refutation'}


if __name__ == '__main__':
    print(json.dumps({'status': 'all exact checks passed',
                      'perspective': check_perspective(),
                      'actual_reduction': check_unforced_reduction(),
                      'full_history': check_moments(),
                      'sharp_receiver': check_sharp_receiver()}, indent=2))
