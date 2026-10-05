#!/usr/bin/env python3
"""Rotation-preserving covector payment and a physical gauge-work test.

Exact identities and full NS jets support the analytic comparison and
continuation estimates in README.md. The arbitrary fine-history payment
remains open. This checker is not a Lean or continuum certificate.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
import aged_joint_memory_payment as am
import recent_pressure_reconstruction as wh
import viscous_pressure_regeneration as vd
from rotational_curl_reserve import require, zero


def transpose(A):
    return list(map(list, zip(*A)))


def scale_matrix(c, A):
    return [[f.scale(c, a) for a in row] for row in A]


def symmetric(A):
    return scale_matrix(f.QQ_I(1)/2, am.matrix_add(A, transpose(A)))


def skew(A):
    return scale_matrix(f.QQ_I(1)/2, am.matrix_add(A, scale_matrix(-1, transpose(A))))


def algebra():
    t, nu = s.symbols('t nu', real=True)
    x = s.symbols('x0:3', real=True)
    args = (t,)+x
    u = s.Matrix([s.Function('u'+str(i))(*args) for i in range(3)])
    p, chi = [s.Function(a)(*args) for a in ('p', 'chi')]
    grad = lambda a: s.Matrix([s.diff(a, z) for z in x])
    op = lambda a: s.diff(a, t)+sum(u[i]*s.diff(a, x[i]) for i in range(3))-nu*sum(s.diff(a, z, 2) for z in x)
    U, e = u.jacobian(x), u.dot(u)/2
    S, Omega = (U+U.T)/2, (U-U.T)/2
    m = u+grad(chi)
    residual = u.applyfunc(op)+grad(p)+grad(op(chi)-p+e)
    zero(s.expand(m.applyfunc(op)+U.T*m-residual), 'physical Bernoulli lift and full covector equation')
    zero(s.expand(grad(chi).applyfunc(op)-Omega*grad(chi)
                  -grad(op(chi))+S*grad(chi)),
         'rotation-only transport retains strain leakage of gradients')

    w = s.Matrix(s.symbols('w0:3', real=True))
    d = s.Matrix(s.symbols('d0:3', real=True))
    eps = s.symbols('epsilon', positive=True)
    omega = s.Matrix([[0, -s.Symbol('a'), s.Symbol('b')],
                      [s.Symbol('a'), 0, -s.Symbol('c')],
                      [-s.Symbol('b'), s.Symbol('c'), 0]])
    zero(w.dot(omega*w), 'rotation has exactly zero quadratic work')
    squares = sum((w[i]*d[j]-w[j]*d[i])**2 for i in range(3) for j in range(i+1, 3))
    zero((w.dot(w)+eps**2)*d.dot(d)-w.dot(d)**2-squares-eps**2*d.dot(d),
         'regularized norm diffusion is a sum of nonnegative squares')
    return {'lift': 'scriptL chi=p-|u|^2/2, chi(0)=0; m=u+grad chi; scriptL m+U^T m=0; Pi m=u',
            'rotating_operator': 'B=scriptL-Omega, U=S+Omega; Bm=-Sm',
            'domination': '|R_(a,t)v|<=P_(a,t)|v|, by the regularized norm comparison; the PDE comparison is analytic.',
            'gradient_leakage': 'B grad chi=grad(scriptL chi)-S grad chi; R does not independently preserve gradients.'}


def actual_jet(u, label, nu):
    U = f.jac(u)
    S, Omega = symmetric(U), skew(U)
    p = f.tensor_pressure(f.tensor(u, u))
    e = f.scale(f.QQ_I(1)/2, f.dot(u, u))
    b = f.add(p, f.scale(-1, e))
    evolve = lambda a: f.add(f.scale(nu, f.lap(a)), f.scale(-1, f.adv(u, a)))
    ut = [f.add(evolve(u[i]), f.scale(-1, f.diff(p, i))) for i in range(3)]
    Ut, St = f.jac(ut), symmetric(f.jac(ut))
    pt = f.tensor_pressure(am.matrix_add(f.tensor(ut, u), f.tensor(u, ut)))
    bt = f.add(pt, f.scale(-1, f.dot(u, ut)))
    utt = [f.add(evolve(ut[i]), f.scale(-1, f.adv(ut, u[i])), f.scale(-1, f.diff(pt, i))) for i in range(3)]
    chi2 = f.add(bt, evolve(b))
    m1, m2 = wh.addv(ut, f.grad(b)), wh.addv(utt, f.grad(chi2))
    wh.same_vectors(m1, wh.addv([evolve(a) for a in u], wh.scalev(-1, f.matvec(transpose(U), u))), 'actual first covector jet')
    predicted2 = wh.addv([evolve(a) for a in m1],
                         [f.scale(-1, f.adv(ut, a)) for a in u],
                         wh.scalev(-1, f.matvec(transpose(Ut), u)),
                         wh.scalev(-1, f.matvec(transpose(U), m1)))
    wh.same_vectors(m2, predicted2, 'actual second covector jet keeps inherited gradient and changing drift')
    for covector, velocity in ((u, u), (m1, ut), (m2, utt)):
        wh.same_vectors(wh.project(covector), velocity, 'physical velocity reconstruction')
        wh.same_vectors(f.curl(covector), f.curl(velocity), 'physical vorticity reconstruction')

    D0 = am.pairing(u, f.matvec(S, u))
    D1 = 2*am.pairing(m1, f.matvec(S, u))+am.pairing(u, f.matvec(St, u))
    bn = am.pairing(f.grad(b), f.grad(b))
    require(D0 == f.ZERO and D1 == -bn, 'universal first covector strain return equals minus Bernoulli-gradient energy')
    require(bn.y == 0 and bn.x > 0, 'fixture has actual positive returned work')
    for velocity in (u, ut, utt):
        f.equal(f.trace(f.jac(velocity)), {}, 'full physical jet is solenoidal')

    # The high observer does not commute with advection or local rotation.
    hi = lambda v: [am.high(a) for a in v]
    high_u = hi(u)
    B_high_u = wh.addv(hi(m1), [f.adv(u, a) for a in high_u],
                       [f.scale(-nu, f.lap(a)) for a in high_u],
                       wh.scalev(-1, f.matvec(Omega, high_u)))
    comm_adv = wh.addv([f.adv(u, a) for a in high_u],
                      wh.scalev(-1, hi([f.adv(u, a) for a in u])))
    comm_rotation = wh.addv(f.matvec(Omega, high_u), wh.scalev(-1, hi(f.matvec(Omega, u))))
    wh.same_vectors(B_high_u, wh.addv(wh.scalev(-1, hi(f.matvec(S, u))), comm_adv,
                                      wh.scalev(-1, comm_rotation)),
                    'both actual high-observer commutators are retained')
    S_hi = [[am.high(a) for a in row] for row in S]
    S_lo = am.matrix_add(S, scale_matrix(-1, S_hi))
    source_S = am.matrix_add(am.matrix_add(f.matmul(S, S), f.matmul(Omega, Omega)), f.hess(p))
    actual_high_S = [[f.add(am.high(St[i][j]), f.adv(u, S_hi[i][j]),
                            f.scale(-nu, f.lap(S_hi[i][j]))) for j in range(3)] for i in range(3)]
    expected_high_S = [[f.add(f.scale(-1, am.high(source_S[i][j])), f.adv(u, S_hi[i][j]),
                             f.scale(-1, am.high(f.adv(u, S[i][j])))) for j in range(3)] for i in range(3)]
    f.same_matrices(actual_high_S, expected_high_S, 'fine strain keeps rotational-square pressure and transport defects')
    low_u = wh.addv(u, wh.scalev(-1, high_u))
    wh.same_vectors(f.matvec(S, u), wh.addv(f.matvec(S_lo, u), f.matvec(S_hi, low_u), f.matvec(S_hi, high_u)),
                    'critical source split is exact, with the joint fine product retained')
    return {'datum': label, 'nu': str(nu), 'pressure_modes': len(p), 'Bernoulli_modes': len(b),
            'strain_work_at_zero': str(D0), 'strain_work_derivative': str(D1),
            'returned_work_over_t2_limit': str(bn/2),
            'scope': 'Complete NS and canonical covector jets, not a truncated time evolution; interval conclusions use smooth local theory.'}


def shear():
    z = s.symbols('z', real=True)
    A, nu = s.symbols('A nu', positive=True)
    t = s.symbols('t', nonnegative=True)
    u = A*s.exp(-nu*t)*s.sin(z)
    chi = -A*A/(8*nu)*(1-s.exp(-2*nu*t))+A*A/(8*nu)*(s.exp(-2*nu*t)-s.exp(-4*nu*t))*s.cos(2*z)
    g = s.diff(chi, z)
    zero(s.diff(u, t)-nu*s.diff(u, z, 2), 'actual unforced decaying shear')
    zero(s.trigsimp(s.diff(chi, t)-nu*s.diff(chi, z, 2)+u*u/2), 'original Bernoulli scalar on the actual shear')
    zero(s.trigsimp(s.diff(g, t)-nu*s.diff(g, z, 2)+u*s.diff(u, z)), 'complete covector shear equation')
    average = lambda a: s.integrate(s.expand_trig(a), (z, -s.pi, s.pi))/(2*s.pi)
    G = A**4/(32*nu**2)*(s.exp(-2*nu*t)-s.exp(-4*nu*t))**2
    D = -A**4/(16*nu)*(s.exp(-4*nu*t)-s.exp(-6*nu*t))
    zero(average(g*g)-G, 'retained gradient energy')
    zero(average(u*s.diff(u, z)*g)-D, 'positive covector work despite no pressure or vorticity stretching')
    zero(s.diff(G, t)/2+4*nu*G+D, 'all-history work is gradient storage plus gradient diffusion')
    reserve = A**4/(16*nu**2)*(s.exp(-4*nu*t)/4-s.exp(-6*nu*t)/6)
    zero(s.diff(reserve, t)-D, 'explicit remaining reserve pays the entire shear overcharge')
    zero(reserve.subs(t, 0)-A**4/(192*nu**2), 'finite original shear allowance')
    # Positivity follows after factoring exp(-6nu t): exp(2nu t)/4-1/6>=1/12.
    zero(reserve-A**4*s.exp(-6*nu*t)/(16*nu**2)*(s.exp(2*nu*t)/4-s.Rational(1, 6)), 'nonnegative remaining reserve')
    clock = s.symbols('heat_clock', positive=True)
    Em = A*A*clock/2+A**4/(32*nu**2)*(clock-clock**2)**2
    zero(Em.subs({A:16*nu, clock:s.Rational(1, 2)})-192*nu**2,
         'actual covector energy can exceed its initial value by fifty percent')
    return {'actual_velocity': '(A exp(-nu t) sin z,0,0); canonical p=0; vortex stretching=0',
            'chi': str(chi), 'gradient_energy': str(G), 'strain_work_D': str(D),
            'integral_0_infinity_minus_D': 'A^4/(192nu^2)', 'remaining_reserve': str(reserve),
            'finite_example': 'A=16nu, t=log(2)/(2nu): original energy128nu^2, physical energy64nu^2, covector energy192nu^2.',
            'interpretation': 'The positive covector strain work creates and diffuses a gradient removed by velocity reconstruction. It is not dangerous stretching or external forcing.'}


def whole_space_seed():
    x, y, z = s.symbols('x y z', real=True)
    coords = (x, y, z)
    rho, radius2 = x*x+y*y, x*x+y*y+z*z
    velocity = s.Matrix([-y, x, 0])*s.exp(-radius2)
    U = velocity.jacobian(coords)
    e = velocity.dot(velocity)/2
    lap_p = -s.trace(U*U)
    lap_b = lap_p-sum(s.diff(e, a, 2) for a in coords)
    zero(lap_b-2*rho*(5-4*radius2)*s.exp(-2*radius2), 'localized actual Bernoulli source is not spatially constant')
    return {'datum': '(-y,x,0) exp(-|x|^2)',
            'Delta_Bernoulli': '2(x^2+y^2)(5-4|x|^2) exp(-2|x|^2), not identically zero',
            'consequence': 'The actual whole-space covector return has D_prime(0)=-||grad(p0-|u0|^2/2)||2^2<0, at every positive viscosity.',
            'scaling': 'For actual NS concentration, chi_lambda=chi(lambda^2 t,lambda x), m_lambda=lambda m(lambda^2 t,lambda x); the retained gradient is not reset.'}


def constants():
    R = s.Rational
    zero(1+R(1, 18)-R(5, 9)-R(1, 2), 'heat-kernel Young exponents')
    zero(R(5, 9)-R(1, 18)-R(1, 2), 'critical product Holder exponents')
    zero(R(2, 3)-R(1, 2)-R(1, 6), 'finite time inclusion')
    zero(3-R(5, 3)-R(4, 3), 'undifferentiated heat kernel scale')
    zero(4-R(5, 3)-R(7, 3), 'differentiated heat kernel scale')
    h, E, Q, nu, Z, G = s.symbols('h E Q nu Z G', positive=True)
    stock = h*E+Q/(2*nu)
    rate = -s.diff(stock, h)-2*nu*Z*s.diff(stock, E)-2*nu*G*s.diff(stock, Q)
    zero(rate+E+G+2*nu*h*Z, 'joint remaining reserve pays the actual covector squared norm')
    x, y = s.symbols('x y', nonnegative=True)
    zero(R(1, 4)+R(3, 4)*x**4-x**3-(x-1)**2*(3*x*x+2*x+1)/4,
         'fractional remaining-clock reserve pays the three-quarter cost')
    factor = s.div(2*(x**3+y**3)**2-(x*x+y*y)**3, (x-y)**2, x)
    zero(factor[1], 'critical source sum bound has double contact')
    require(all(c >= 0 for c in s.Poly(factor[0], x, y).coeffs()), 'critical source convexity gap is nonnegative')
    return {'P_chi': '(3/2) C_S^(3/4) H^(1/4) E0/(2nu)^(3/4)',
            'M_H_squared': 'H E0+P_chi^2/(2nu), bounding integral ||m||2^2',
            'M_low': 'J_ell sqrt(E0)+K_ell P_chi',
            'paid_critical_source': 'H^(1/6)[K_ell sqrt(E0) M_H+M_low sqrt(E0/(2nu))]',
            'compatible_reserve': 'R_X=(H-t)E+Q_chi/(2nu), R_Z=E/(2nu); R_A=sqrt(2)(H-t)^(1/4)[a^(3/2) R_X^(3/4)+b^(3/2) R_Z^(3/4)], a=K_ell sqrt(E0), b=M_low; R_A_prime+||S_lo m+S_hi m_lo||_(9/5)^(3/2)<=0.',
            'kernels': 'J_ell=||heat_kernel_(ell^2)||_(9/5); K_ell=||grad heat_kernel_(ell^2)||_(9/5)',
            'OPEN': 'Full-datum L3_t L9_x payment of Pi integral R_(a,t)[S_hi m_hi](a)da, with actual joint history retained.'}


if __name__ == '__main__':
    cyclic = [vd.sine((0, 1, 0)), vd.sine((0, 0, 4)), vd.sine((1, 0, 0))]
    data = [(f.fixture(), 'genuine 3D'), (cyclic, 'initially pressure-free cyclic'),
            ([vd.sine((0, 0, 1)), {}, {}], 'pressure-free shear')]
    result = {'algebra': algebra(), 'constants': constants(), 'exact_shear': shear(),
              'whole_space_seed': whole_space_seed(),
              'actual_jets': [actual_jet(u, name, nu) for u, name in data for nu in (f.QQ_I(1), f.QQ_I(2)/7)],
              'status': 'Exact checks passed. Propagator domination, reserve bounds, physical histories and continuation are analytic, not Lean-certified.',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2), flush=True)
