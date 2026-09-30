#!/usr/bin/env python3
"""Cellular stochastic-parent histories and their selected pressure flux.

Exact Fourier algebra identifies a heat-decaying horizontal NS parent.
The vertical component and retained memory obey linear advection-diffusion
PDEs driven by that parent. The finite parent reserve and memory bounds
are analytic in README.md. Optional Fourier prefixes are approximations,
with separate resolution, positivity and balance diagnostics; they do not
certify arbitrary-flow histories or the nonlinear renewal estimate.
"""
import argparse
import json
import time
from fractions import Fraction
import numpy as np
import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
import pressure_diffusion_completion as completion


PACKETS = ((1, 2, Fraction(1, 5)), (2, 1, Fraction(9, 50)), (1, -2, Fraction(4, 25)))


def exact_parent(packets):
    psi = {}
    for i, j, amplitude in packets:
        k = (i, j, 0)
        psi[k] = f.QQ_I(amplitude)/2
        psi[tuple(-q for q in k)] = f.QQ_I(amplitude)/2
    u = [f.scale(-1, f.diff(psi, 1)), f.diff(psi, 0), {}]
    B = f.jac(u)
    p = f.green(f.trace(f.matmul(B, B)))
    P = f.hess(p)
    bernoulli = f.scale(-f.QQ_I(1)/2, f.add(f.dot(u, u), f.scale(5, f.mul(psi, psi))))
    f.equal(f.add(f.lap(psi), f.scale(5, psi)), {}, 'single Laplacian shell')
    for j in range(3):
        f.equal(f.add(f.adv(u, u[j]), f.diff(p, j)), {}, 'actual stationary Euler parent')
        f.equal(f.diff(p, j), f.diff(bernoulli, j), 'canonical Bernoulli pressure')
        f.equal(f.add(f.lap(u[j]), f.scale(5, u[j])), {}, 'actual heat-decaying NS parent')
    bound = sum((abs(z.x)+abs(z.y) for row in P for q in row for z in q.values()), f.ZERO.x)
    return u, p, P, bound


def exact_checks():
    x, y, z, t = s.symbols('x y z t', real=True)
    nu, lam, A1 = s.symbols('nu lam A1', positive=True)
    a = s.exp(-nu*lam*t)
    reserve = A1*a/nu
    if s.simplify(reserve.diff(t)+lam*A1*a) != 0:
        raise ArithmeticError('remaining parent history reserve')
    shear_history = A1*(1-a)/nu
    if s.simplify(shear_history+reserve-A1/nu) != 0:
        raise ArithmeticError('compatible seams do not refill parent reserve')
    # Retain an arbitrary advected vertical component. No feedback from v
    # is dropped: z-independence makes the feedback literally zero.
    psi = s.cos(x+2*y)/5+s.Rational(9, 50)*s.cos(2*x+y)+s.Rational(4, 25)*s.cos(x-2*y)
    uh = s.exp(-5*nu*t)*s.Matrix([-s.diff(psi, y), s.diff(psi, x)])
    v = s.Function('v')(x, y, t)
    velocity = s.Matrix([uh[0], uh[1], v])
    gradient = velocity.jacobian((x, y, z))
    for value in (s.trace(gradient), s.trace(gradient*gradient)-s.trace(uh.jacobian((x, y))**2)):
        if s.simplify(value) != 0:
            raise ArithmeticError('actual passive-component incompressibility and pressure')
    residual = v.diff(t)+uh[0]*v.diff(x)+uh[1]*v.diff(y)-nu*(v.diff(x, 2)+v.diff(y, 2))
    if s.simplify((velocity.diff(t)+gradient*velocity)[2]
                  -nu*(v.diff(x, 2)+v.diff(y, 2))-residual) != 0:
        raise ArithmeticError('literal unforced vertical PDE')
    M = s.symbols('M', positive=True)
    source4 = 4*nu*M**4*(2*M)**4*A1**2
    coefficient4 = 2*M*A1*((1+M)**4-1)
    if s.simplify(source4/(2*nu*lam) - 2*M**4*(2*M)**4*A1**2/lam) != 0:
        raise ArithmeticError('integrated generated horizontal memory source')
    if s.simplify(coefficient4.subs(M, 2)-320*A1) != 0:
        raise ArithmeticError('four-derivative parent commutator coefficient')
    if s.simplify((source4/(2*nu*lam)).subs({M: 2, lam: 5})-s.Rational(8192, 5)*A1**2) != 0:
        raise ArithmeticError('finite initial resource for four memory derivatives')
    if not 13 < 4**2 or 4*18 != 72:
        raise ArithmeticError('periodic pressure observer Sobolev constants')
    u, p, P, bound = exact_parent(PACKETS)
    if bound != f.QQ_I(578).x/125:
        raise ArithmeticError('datum-fixed pressure Hessian majorant')
    localization = pm.weighted_pressure_flux(P, p)
    # A two-parent member has zero total pressure flux defect pointwise;
    # the three-parent member has a genuine nonlocal correction.
    _, p2, P2, _ = exact_parent(PACKETS[:2])
    gp2 = f.grad(f.lap(p2))
    defect2 = f.add(*(pm.pair(pm.matrix_diff(P2, j), pm.matrix_diff(P2, j)) for j in range(3)),
                    f.scale(-1, f.dot(gp2, gp2)))
    f.equal(defect2, {}, 'two-parent pressure gradient identity is pointwise')
    adapter = check_array_derivatives()
    return {'arithmetic': 'Gaussian rational Fourier coefficients and symbolic differential algebra',
            'floating_matrix_adapter': adapter,
            'parent': 'psi=sum a_k cos(k.x), |k|^2=lambda; u_h=exp(-nu lambda t) J grad psi',
            'actual_pressure': '-exp(-2nu lambda t)(|grad psi|^2+lambda psi^2)/2 up to a constant',
            'vertical': 'v_t+u_h.grad v=nu Delta v; arbitrary smooth periodic v0(x,y)',
            'remaining_parent_reserve': 'A1 exp(-nu lambda t)/nu; A1=sum |a_k|',
            'stochastic_gradient_bound': '||grad v(t)||_infty<=||grad v0||_infty exp(A1(1-exp(-nu lambda t))/nu)',
            'memory_derivative_bound': 'M4<=(2/lambda) M^4 (2M)^4 A1^2 exp(2M A1((1+M)^4-1)/(nu lambda))',
            'memory_pressure_bound': '||P_C||_infty<=72 M4 on the normalized 2*pi torus',
            'fixed_pressure_hessian_bound': str(bound),
            'two_parent_pressure_defect': 'zero pointwise',
            'three_parent_pressure_defect': localization,
            'scope': 'exact PDE and coefficient checks; stochastic/memory/history bounds are analytic, not Lean'}


PAIRS = ((0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2))


def matdot(A, B):
    return np.einsum('...ij,...ij->...', A, B)


def matvec(A, v):
    return np.einsum('...ij,...j->...i', A, v)


def curl(B):
    return np.stack((B[..., 2, 1]-B[..., 1, 2], B[..., 0, 2]-B[..., 2, 0],
                     B[..., 1, 0]-B[..., 0, 1]), axis=-1)


class Prefix:
    def __init__(self, n, nu, vertical, packets):
        self.n, self.nu, self.vertical = n, nu, vertical
        x = 2*np.pi*np.arange(n)/n
        X, Y = np.meshgrid(x, x, indexing='ij')
        f = np.fft.fftfreq(n)*n
        self.K = np.stack(np.meshgrid(f, f, indexing='ij'), axis=-1)
        self.k2 = np.sum(self.K**2, axis=-1)
        self.heat = -nu*self.k2
        self.mask = (abs(self.K[..., 0]) < n/3) & (abs(self.K[..., 1]) < n/3)
        self.psi = sum(float(a)*np.cos(k*X+l*Y) for k, l, a in packets)
        self.psi_hat = self.fft(self.psi)
        self.uh0 = np.stack((-self.derivative(self.psi, 1),
                             self.derivative(self.psi, 0)), axis=-1)
        self.Bh0 = np.stack((self.derivative(self.uh0, 0),
                            self.derivative(self.uh0, 1)), axis=-1)
        self.p0 = -(np.sum(self.uh0**2, axis=-1)+5*self.psi**2)/2
        self.P0 = self.hessian(self.p0)
        # Analytic datum-fixed bound, rather than the observed grid maximum.
        rmax = (5*sum(abs(a) for _, _, a in packets))**2+vertical**2
        _, _, _, pbound = exact_parent(packets)
        self.threshold = float(1+76*(float(rmax)+np.sqrt(1+float(pbound)**2))**2)
        self.initial = np.zeros((n, n, 7), dtype=np.complex128)
        self.initial[..., 0] = self.fft(vertical*np.sin(X))
        self.minimum_memory_eigenvalue = 0.0

    def fft(self, a):
        return np.fft.fftn(a, axes=(0, 1))

    def ifft(self, a):
        return np.fft.ifftn(a, axes=(0, 1)).real

    def derivative(self, a, j):
        tail = (1,)*(a.ndim-2)
        return self.ifft((1j*self.K[..., j]).reshape((self.n, self.n)+tail)*self.fft(a))

    def gradient_hat(self, a):
        return [self.ifft(1j*self.K[..., j, None]*a) for j in range(2)]

    def hessian(self, a):
        out = np.zeros((self.n, self.n, 3, 3))
        ah = self.fft(a)
        for i in range(2):
            for j in range(2):
                out[..., i, j] = self.ifft(-self.K[..., i]*self.K[..., j]*ah)
        return out

    def matrix(self, components):
        C = np.zeros((self.n, self.n, 3, 3))
        for j, (a, b) in enumerate(PAIRS):
            C[..., a, b] = components[..., j]
            C[..., b, a] = components[..., j]
        return C

    def observe(self, C):
        ch = self.fft(C)
        numerator = np.einsum('...i,...j,...ij->...', self.K, self.K, ch[..., :2, :2])
        q = -np.divide(numerator, self.k2, out=np.zeros_like(numerator), where=self.k2 != 0)
        return self.hessian(self.ifft(q))

    def fields(self, t, state):
        decay = np.exp(-5*self.nu*t)
        uh = decay*self.uh0
        Bh = decay*self.Bh0
        value = self.ifft(state)
        gradients = self.gradient_hat(state)
        B = np.zeros((self.n, self.n, 3, 3))
        B[..., :2, :2] = Bh
        B[..., 2, 0] = gradients[0][..., 0]
        B[..., 2, 1] = gradients[1][..., 0]
        u = np.concatenate((uh, value[..., :1]), axis=-1)
        C = self.matrix(value[..., 1:])
        return u, B, C, gradients

    def rhs(self, t, state):
        u, B, _, gradients = self.fields(t, state)
        adv = sum(u[..., j, None]*gradients[j] for j in range(2))
        result = -adv
        G = B @ np.swapaxes(B, -1, -2)
        for j, (a, b) in enumerate(PAIRS):
            result[..., j+1] += 2*self.nu*G[..., a, b]
        return self.fft(result)*self.mask[..., None]

    def step(self, t, y, dt):
        E = np.exp(dt*self.heat)[..., None]
        E2 = np.exp(dt*self.heat/2)[..., None]
        a = self.rhs(t, y)
        b = self.rhs(t+dt/2, E2*(y+dt*a/2))
        c = self.rhs(t+dt/2, E2*y+dt*b/2)
        d = self.rhs(t+dt, E*y+dt*E2*c)
        return (E*y+dt*(E*a+2*E2*(b+c)+d)/6)*self.mask[..., None]

    @staticmethod
    def observable(B, P, increments=None):
        S = (B+np.swapaxes(B, -1, -2))/2
        w = curl(B)
        W = np.sum(w*w, axis=-1)
        Sw = matvec(S, w)
        V = np.sum(w*Sw, axis=-1)
        ss = matdot(S, S)
        Z = np.sum(Sw*Sw, axis=-1)
        r = matdot(B, B)
        q = np.sqrt(1+matdot(P, P))
        Q = r+q
        perspective = V*V/(W+1)
        p = 5*perspective+(63/95)*W*W-2*np.sum(w*matvec(P, w), axis=-1)
        c = 5*perspective+(4/7)*Z+(10/21)*ss*W+(44/95)*W*W
        A, A0 = p+48*Q*Q, c+48*Q*Q
        rho = np.sqrt(A*A+A0*A0)
        if increments is None:
            return 1+rho
        E, L = increments
        H = (E+np.swapaxes(E, -1, -2))/2
        v = curl(E)
        dW = 2*np.sum(w*v, axis=-1)
        ddW = 2*np.sum(v*v, axis=-1)
        dV = 2*np.sum(v*Sw, axis=-1)+np.sum(w*matvec(H, w), axis=-1)
        ddV = 2*np.sum(v*matvec(S, v), axis=-1)+4*np.sum(v*matvec(H, w), axis=-1)
        dT = 2*V*dV/(W+1)-V*V*dW/(W+1)**2
        ddT = 2*(dV-V*dW/(W+1))**2/(W+1)+2*V*ddV/(W+1)-(V/(W+1))**2*ddW
        dSw = matvec(H, w)+matvec(S, v)
        dZ = 2*np.sum(Sw*dSw, axis=-1)
        ddZ = 2*np.sum(dSw*dSw, axis=-1)+4*np.sum(Sw*matvec(H, v), axis=-1)
        dss = 2*matdot(S, H)
        ddss = 2*matdot(H, H)
        dwPw = 2*np.sum(v*matvec(P, w), axis=-1)+np.sum(w*matvec(L, w), axis=-1)
        ddwPw = 2*np.sum(v*matvec(P, v), axis=-1)+4*np.sum(v*matvec(L, w), axis=-1)
        dp = 5*dT+(126/95)*W*dW-2*dwPw
        ddp = 5*ddT+(126/95)*(dW*dW+W*ddW)-2*ddwPw
        dc = 5*dT+(4/7)*dZ+(10/21)*(dss*W+ss*dW)+(88/95)*W*dW
        ddc = 5*ddT+(4/7)*ddZ+(10/21)*(ddss*W+2*dss*dW+ss*ddW)+(88/95)*(dW*dW+W*ddW)
        d = matdot(B, E)
        ell = matdot(P, L)/q
        dR = 2*Q*(2*d+ell)
        ddR = 8*d*d+4*Q*matdot(E, E)+8*d*ell+2*matdot(L, L)+2*r/q*(matdot(L, L)-ell*ell)
        dA, dA0 = dp+48*dR, dc+48*dR
        ddA, ddA0 = ddp+48*ddR, ddc+48*ddR
        first = (A*dA+A0*dA0)/rho
        second = (A*ddA+A0*ddA0)/rho+(A0*dA-A*dA0)**2/rho**3
        return first, second

    def diagnostic(self, t, state):
        u, B, C, gc = self.fields(t, state)
        P = np.exp(-10*self.nu*t)*self.P0
        PC = self.observe(C)
        Ph = P+PC
        H = C+np.eye(3)
        eigenvalues = np.linalg.eigvalsh(C)
        mineig = float(np.min(eigenvalues))
        if np.min(np.linalg.eigvalsh(H)) <= 0:
            raise ArithmeticError('memory-capacity tensor loses positive definiteness')
        h = np.linalg.det(H)**(1/3)
        invH = np.linalg.inv(H)
        Psi = self.observable(B, Ph)
        z = Psi/h
        active = z > self.threshold
        a = np.where(active, 1-self.threshold**2/z**2, 0)
        curvature = np.where(active, 2*self.threshold**2/z**3, 0)
        cb = np.where(active, 2*self.threshold*(1-self.threshold/z), 0)
        F = np.where(active, (Psi-self.threshold*h)**2/Psi, 0)
        r = matdot(B, B)
        Pgrad2 = np.zeros_like(r)
        PCgrad2 = np.zeros_like(r)
        sourcegrad2 = np.zeros_like(r)
        parent = np.zeros_like(r)
        observed = np.zeros_like(r)
        fullD = np.zeros_like(r)
        J = np.zeros_like(r)
        flux_pair = np.zeros_like(r)
        G = B @ np.swapaxes(B, -1, -2)
        Qgeom = (2*self.nu/3)*np.trace(invH @ G, axis1=-2, axis2=-1)
        traceP = np.trace(P, axis1=-2, axis2=-1)
        sourcegrad = np.stack((self.derivative(traceP, 0), self.derivative(traceP, 1), np.zeros_like(r)), axis=-1)
        flux = matvec(P, sourcegrad)
        for j in range(2):
            E = self.derivative(B, j)
            L = self.derivative(Ph, j)
            CP = self.derivative(PC, j)
            PP = self.derivative(P, j)
            Cj = self.matrix(gc[j][..., 1:])
            Hj = invH @ Cj
            dh = h*np.trace(Hj, axis1=-2, axis2=-1)/3
            dPsi, ddPsi = self.observable(B, Ph, (E, L))
            dz = (dPsi-z*dh)/h
            da = curvature*dz
            Pgrad2 += matdot(PP, PP)
            PCgrad2 += matdot(CP, CP)
            sourcegrad2 += sourcegrad[..., j]**2
            parent += r*matdot(E, E)
            observed += matdot(L, L)
            fullD += self.nu*ddPsi
            J += self.nu*h*curvature*dz*dz
            flux[..., j] -= matdot(P, PP)
            flux_pair += da*flux[..., j]
            Qgeom += (self.nu/3)*(np.trace(Hj @ Hj, axis1=-2, axis2=-1)
                                        -np.trace(Hj, axis1=-2, axis2=-1)**2/3)
        lowerD = self.nu*(8*parent+(56/5)*observed)
        if np.min(fullD-lowerD) < -1e-7*max(1, np.max(fullD)):
            raise ArithmeticError('physical completed Hessian violates its analytic lower bound')
        stress = np.einsum('...i,...j->...ij', u, u)+C
        gp = np.stack((self.derivative(np.exp(-10*self.nu*t)*self.p0, 0),
                       self.derivative(np.exp(-10*self.nu*t)*self.p0, 1), np.zeros_like(r)), axis=-1)
        sym = np.einsum('...i,...j->...ij', u, gp)+np.einsum('...i,...j->...ij', gp, u)
        comm = sum(u[..., j, None, None]*self.derivative(Ph, j) for j in range(2))
        advstress = sum(u[..., j, None, None]*self.derivative(stress, j) for j in range(2))
        DPh = -self.observe(sym)+comm-self.observe(advstress)
        DB = -B @ B-P
        production, _ = self.observable(B, Ph, (DB, DPh))
        signed = a*production-cb*h*Qgeom-a*fullD-J
        mean = lambda q: float(np.mean(q))
        ratio = lambda q, d: mean(q)/mean(d) if mean(d) > 0 else None
        E = mean(np.sum(u*u, axis=-1))
        memory_mass = mean(np.trace(C, axis1=-2, axis2=-1))
        e0 = mean(np.sum(self.uh0*self.uh0, axis=-1))+self.vertical**2/2
        return {'time': t, 'excess_mass': mean(F), 'active_fraction': mean(active),
                'threshold': self.threshold, 'maximum_ratio': float(np.max(z)),
                'minimum_memory_eigenvalue': mineig,
                'energy_memory_balance_error': E+memory_mass-e0,
                'weighted_pressure_flux_direct': mean(a*(Pgrad2-sourcegrad2)),
                'weighted_pressure_flux_gradient': mean(flux_pair),
                'weighted_pressure_source_ratio': ratio(a*Pgrad2, 4*a*parent),
                'selected_memory_vs_lower_diffusion': ratio(self.nu*a*PCgrad2, a*lowerD),
                'selected_memory_vs_full_diffusion': ratio(self.nu*a*PCgrad2, a*fullD),
                'selected_completed_diffusion': mean(a*fullD), 'weight_gradient_payment': mean(J),
                'signed_excess_production': mean(signed),
                'unweighted_memory_vs_lower_diffusion': ratio(self.nu*PCgrad2, lowerD)}


def check_array_derivatives():
    # The solver's first and full second directional derivatives are checked
    # independently against symbolic differentiation, including zero vorticity.
    # These are calculus fixtures, not independent physical pressure states.
    backgrounds = (s.Matrix([[3, 0, 3], [4, 4, 2], [3, 1, -7]]),
                   s.Matrix([[0, 1, 0], [-1, 0, -1], [0, 1, 0]]), s.zeros(3))
    E = s.Matrix([[0, 0, 3], [0, 0, -3], [0, 0, 0]])
    P = s.Matrix([[2, 1, 0], [1, -1, 2], [0, 2, 3]])
    L = s.Matrix([[1, -2, 3], [-2, 4, 0], [3, 0, -1]])
    t = s.symbols('t', real=True)
    cast = lambda A: np.asarray(A, dtype=float)
    errors = []
    for B in backgrounds:
        Bt, Pt = B+t*E, P+t*L
        p, c = completion.branches(Bt, Pt, s.Integer(1))
        r = s.trace(Bt.T*Bt)
        q = s.sqrt(1+s.trace(Pt.T*Pt))
        R = (r+q)**2
        Psi = 1+s.sqrt((p+48*R)**2+(c+48*R)**2)
        expected = [float(s.diff(Psi, t, order).subs(t, 0).evalf(30)) for order in (1, 2)]
        observed = Prefix.observable(cast(B), cast(P), (cast(E), cast(L)))
        error = max(abs(got-want)/max(1, abs(want)) for got, want in zip(observed, expected))
        if error > 1e-11:
            raise ArithmeticError(('complete matrix derivative adapter', error))
        errors.append(error)
    return {'independent_symbolic_fixtures': len(errors), 'maximum_relative_error': max(errors),
            'scope': 'floating evaluation of symbolic derivatives; not a physical-flow theorem'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run-prefix', action='store_true', help='Run the Fourier PDE approximation after exact checks.')
    parser.add_argument('--n', type=int, default=64)
    parser.add_argument('--nu', type=float, default=.01)
    parser.add_argument('--vertical', type=float, default=2)
    parser.add_argument('--final-time', type=float, default=2)
    parser.add_argument('--dt', type=float, default=.01)
    parser.add_argument('--diagnostic-n', type=int, default=0)
    args = parser.parse_args()
    certificates = exact_checks()
    if not args.run_prefix:
        print(json.dumps(certificates, indent=2))
        return
    if args.n < 16 or args.n % 2 or args.nu <= 0 or args.final_time <= 0 or args.dt <= 0:
        raise ValueError('even n>=16 and positive viscosity, horizon and step are required')
    packets = PACKETS
    flow = Prefix(args.n, args.nu, args.vertical, packets)
    y = flow.initial.copy()
    samples = [flow.diagnostic(0, y)]
    start = time.time()
    t = 0.0
    steps = max(1, int(round(args.final_time/args.dt)))
    dt = args.final_time/steps
    for step in range(steps):
        y = flow.step(t, y, dt)
        t = (step+1)*dt
        if (step+1) % max(1, int(round(.1/dt))) == 0 or step+1 == steps:
            sample = flow.diagnostic(t, y)
            samples.append(sample)
            print(json.dumps(sample), flush=True)
    signed_integral = float(np.trapz([q['signed_excess_production'] for q in samples],
                                    [q['time'] for q in samples]))
    refined = None
    if args.diagnostic_n:
        newn = args.diagnostic_n
        if newn < args.n or (newn-args.n) % 2:
            raise ValueError('diagnostic grid must be an even enlargement')
        pad = (newn-args.n)//2
        newstate = np.fft.ifftshift(np.pad(np.fft.fftshift(y, axes=(0, 1)),
                                 ((pad, pad), (pad, pad), (0, 0))), axes=(0, 1))*(newn/args.n)**2
        refined_flow = Prefix(newn, args.nu, args.vertical, packets)
        refined_flow.threshold = flow.threshold
        refined = refined_flow.diagnostic(t, newstate)
    print(json.dumps({'exact_checks': certificates, 'resolution': args.n, 'dt': dt, 'nu': args.nu, 'vertical': args.vertical,
                      'samples': samples, 'integrated_signed_production': signed_integral,
                      'budget_error': samples[-1]['excess_mass']-samples[0]['excess_mass']-signed_integral,
                      'enlarged_diagnostic_grid': args.diagnostic_n, 'refined_diagnostic': refined,
                      'elapsed_seconds': time.time()-start,
                      'scope': 'Fourier approximation of exact unforced cellular/passive/memory PDE'}, indent=2))


if __name__ == '__main__':
    main()
