#!/usr/bin/env python3
"""Signed internal renewal of cellular parents in actual NS coefficients.

The default check uses exact Gaussian-rational Fourier algebra, retains
all convolution outputs and verifies the full pressure-projected vector
field. Optional prefixes evolve all three velocities and six symmetric
memory entries. They are Fourier-Galerkin approximations, with explicit
positivity and resolution diagnostics, not continuum enclosures.
The torus has period 2*pi and normalized volume.
"""

import argparse
import json
import time
from fractions import Fraction
import numpy as np
from scipy.fft import fftn, ifftn
import cellular_parent_history as cellular
import pressure_history_source as f
import pressure_memory_diffusion as pm


def seed(epsilon, phase=1):
    u, _, _, _ = cellular.exact_parent(cellular.PACKETS)
    u[2] = {(1, 0, 0): -f.II, (-1, 0, 0): f.II}
    for k, a, sign in [((1, 1, 1), (1, -1, 0), 1),
                       ((0, -1, 1), (1, 1, 1), phase)]:
        for j in range(3):
            for q in (k, tuple(-x for x in k)):
                u[j][q] = u[j].get(q, f.ZERO)+f.QQ_I(epsilon)*sign*a[j]/2
    return [f.clean(q) for q in u]


def nonlinear_source(u):
    B = f.jac(u)
    p = f.green(f.trace(f.matmul(B, B)))
    return [f.add(f.scale(-1, f.adv(u, q)), f.scale(-1, f.diff(p, j)))
            for j, q in enumerate(u)], p


def hermitian_work(u, N, k):
    pairs = [(a.get(k, f.ZERO), b.get(k, f.ZERO)) for a, b in zip(u, N)]
    return sum((a.x*b.x+a.y*b.y for a, b in pairs), f.ZERO.x)


def exact_check(epsilon, phase, nu):
    if epsilon < 0 or phase not in (-1, 1) or nu <= 0:
        raise ValueError('nonnegative amplitude, signed phase and positive viscosity required')
    u = seed(epsilon, phase)
    B = f.jac(u)
    f.equal(f.trace(B), {}, '3D incompressible datum')
    N, p = nonlinear_source(u)
    f.equal(p, f.tensor_pressure(f.tensor(u, u)), 'actual canonical pressure')
    f.equal(pm.divergence(N), {}, 'complete Leray-corrected nonlinear source')
    work = pm.mean(f.dot(u, N))
    if work:
        raise ArithmeticError('complete nonlinear kinetic work must vanish')
    q = (1, 2, 0)
    output = [a.get(q, f.ZERO) for a in N]
    expected = [f.II*f.QQ_I(c)*phase*epsilon**2
                for c in (Fraction(-4, 5), Fraction(2, 5), Fraction(1, 4))]
    if output != expected:
        raise ArithmeticError('complete hidden-to-parent source')
    if hermitian_work(u, N, q) != Fraction(1, 5)*phase*epsilon**2:
        raise ArithmeticError('signed parent work')
    parents = {}
    for kx, ky, amplitude in cellular.PACKETS:
        parents[(kx, ky, 0)] = amplitude
        parents[(-kx, -ky, 0)] = amplitude
    parent_work = sum((hermitian_work(u, N, k) for k in parents), f.ZERO.x)
    renewal = sum((2*hermitian_work(u, N, k)/f.QQ_I(5*nu*a).x
                   for k, a in parents.items()), f.ZERO.x)
    shear = Fraction(5, 2)*sum(parents.values())
    if parent_work != Fraction(2, 5)*phase*epsilon**2:
        raise ArithmeticError('complete initial parent energy transfer')
    if renewal != Fraction(4, 5)*phase*epsilon**2/nu:
        raise ArithmeticError('initial parent reserve transfer')
    inputs = set().union(*u)
    donors = inputs-set(parents)
    donor_work = sum((hermitian_work(u, N, k) for k in donors), f.ZERO.x)
    if donor_work+parent_work != 0:
        raise ArithmeticError('parent gain must be paid by the actual donor modes')
    energy = pm.mean(f.dot(u, u))
    if energy != Fraction(449, 200)+Fraction(5, 2)*epsilon**2:
        raise ArithmeticError('equal-energy phase comparison')
    parent_energy = sum((sum((z.get(k, f.ZERO).x**2+z.get(k, f.ZERO).y**2
                              for z in u), f.ZERO.x) for k in parents), f.ZERO.x)
    if parent_energy != Fraction(49, 200):
        raise ArithmeticError('all cellular parent energies retained')
    P = f.hess(p)
    pbound = sum((abs(z.x)+abs(z.y) for row in P for field in row
                  for z in field.values()), f.ZERO.x)
    generated = set().union(*N)-inputs
    return {'epsilon': str(epsilon), 'phase': phase, 'nu': str(nu),
            'energy': str(energy), 'parent_rhs': list(map(str, output)),
            'parent_pair_energy_rate': str(Fraction(4, 5)*phase*epsilon**2-nu),
            'parent_energy_nonlinear_rate': str(2*parent_work),
            'donor_energy_nonlinear_rate': str(2*donor_work),
            'parent_reserve_rate': str(renewal-f.QQ_I(shear).x),
            'pressure_majorant': str(pbound), 'generated_modes': len(generated),
            'full_nonlinear_work': str(work)}


PAIRS = cellular.PAIRS
dot = cellular.matdot
mv = cellular.matvec


class Flow:
    def __init__(self, n, nu, eps, phase):
        self.n, self.nu, self.eps, self.phase = n, nu, eps, phase
        frequencies = np.fft.fftfreq(n)*n
        self.K = np.stack(np.meshgrid(frequencies, frequencies, frequencies, indexing='ij'), axis=-1)
        self.k2 = np.sum(self.K*self.K, axis=-1)
        self.inv = np.divide(1, self.k2, out=np.zeros_like(self.k2), where=self.k2 != 0)
        self.heat = -nu*self.k2
        self.mask = np.all(abs(self.K) < n/3, axis=-1)
        self.initial = np.zeros((n,n,n,9), dtype=np.complex128)
        exact = seed(eps, phase)
        for j, field in enumerate(exact):
            for k, amplitude in field.items():
                self.initial[tuple(q % n for q in k)+(j,)] = complex(float(amplitude.x), float(amplitude.y))*n**3
        self.parents = sorted(set(k for field in exact for k in field if k[2] == 0 and sum(q*q for q in k) == 5))
        self.parent_indices = [tuple(q % n for q in k) for k in self.parents]
        p = f.green(f.trace(f.matmul(f.jac(exact),f.jac(exact))))
        P = f.hess(p)
        bound = sum((abs(a.x)+abs(a.y) for row in P for field in row for a in field.values()), f.ZERO.x)
        self.pbound = float(bound)
        r0 = (np.sqrt(11.29)+2*np.sqrt(6)*float(eps))**2
        self.threshold = 1+76*(r0+np.sqrt(1+self.pbound**2))**2
        self.energy0 = float(pm.mean(f.dot(exact,exact)))
        self.R0, _, self.EP0 = self.parent_values(self.initial)

    @staticmethod
    def fft(a):
        return fftn(a, axes=(0,1,2), workers=1)

    @staticmethod
    def ifft(a):
        return ifftn(a, axes=(0,1,2), workers=1).real

    def derivative(self, a, j):
        dims = (1,)*(a.ndim-3)
        return self.ifft((1j*self.K[...,j]).reshape((self.n,)*3+dims)*self.fft(a))

    def grad_hat(self, a):
        return [self.ifft(1j*self.K[...,j,None]*a) for j in range(3)]

    def project(self, a):
        return a-self.K*self.inv[...,None]*np.sum(self.K*a,axis=-1)[...,None]

    def fields(self, state):
        physical = self.ifft(state)
        grad = self.grad_hat(state)
        u = physical[...,:3]
        B = np.stack([g[...,:3] for g in grad],axis=-1)
        return u, B, self.matrix(physical[...,3:]), grad

    def matrix(self, a):
        C = np.zeros(a.shape[:-1]+(3,3))
        for j,(i,k) in enumerate(PAIRS):
            C[...,i,k] = a[...,j]
            C[...,k,i] = a[...,j]
        return C

    def hessian(self, q):
        qh = self.fft(q)
        return self.ifft(-self.K[..., :,None]*self.K[...,None,:]*qh[...,None,None])

    def observe(self, C):
        Ch = self.fft(C)
        numerator = np.einsum('...i,...j,...ij->...',self.K,self.K,Ch)
        qh = -self.inv*numerator
        return self.ifft(-self.K[..., :,None]*self.K[...,None,:]*qh[...,None,None]), self.ifft(qh)

    def parent_values(self, state):
        coeff = np.stack([state[k][...,:3]/self.n**3 for k in self.parent_indices])
        norm = np.linalg.norm(coeff,axis=-1)
        return float(np.sum(norm)/(self.nu*np.sqrt(5))), float(np.sqrt(5)*np.sum(norm)), float(np.sum(norm*norm))

    def parent_rates(self, state, nonlinear):
        coeff = np.stack([state[k][...,:3]/self.n**3 for k in self.parent_indices])
        forcing = np.stack([nonlinear[k][...,:3]/self.n**3 for k in self.parent_indices])
        norms = np.linalg.norm(coeff,axis=-1)
        work = np.real(np.sum(np.conj(coeff)*forcing,axis=-1))
        quotient = np.divide(work, norms, out=np.linalg.norm(forcing,axis=-1), where=norms > 0)
        _, shear, energy = self.parent_values(state)
        return np.array([shear,np.sum(quotient)/(self.nu*np.sqrt(5)),2*np.sum(work),10*self.nu*energy])

    def rhs(self, state):
        u,B,_,grad = self.fields(state)
        adv = sum(u[...,j,None]*grad[j] for j in range(3))
        result = -adv
        G = B @ np.swapaxes(B,-1,-2)
        for j,(a,b) in enumerate(PAIRS):
            result[...,3+j] += 2*self.nu*G[...,a,b]
        rhs = self.fft(result)*self.mask[...,None]
        rhs[...,:3] = self.project(rhs[...,:3])
        return rhs, self.parent_rates(state,rhs)

    def step(self, state, dt):
        E = np.exp(dt*self.heat)[...,None]
        E2 = np.exp(dt*self.heat/2)[...,None]
        a,ra = self.rhs(state)
        b,rb = self.rhs(E2*(state+dt*a/2))
        c,rc = self.rhs(E2*state+dt*b/2)
        d,rd = self.rhs(E*state+dt*E2*c)
        nextstate = (E*state+dt*(E*a+2*E2*(b+c)+d)/6)*self.mask[...,None]
        return nextstate, dt*(ra+2*rb+2*rc+rd)/6

    def padded(self, state, n):
        if n < self.n or (n-self.n)%2:
            raise ValueError('even diagnostic enlargement required')
        pad = (n-self.n)//2
        newstate = np.fft.ifftshift(np.pad(np.fft.fftshift(state,axes=(0,1,2)),
                           ((pad,pad),(pad,pad),(pad,pad),(0,0))),axes=(0,1,2))*(n/self.n)**3
        flow = Flow(n,self.nu,self.eps,self.phase)
        flow.threshold = self.threshold
        return flow,newstate

    def diagnostic(self, t, state, ledger, diagnostic_n):
        original_state = state
        flow,state = self.padded(state,diagnostic_n)
        u,B,C,gc = flow.fields(state)
        P,p = flow.observe(np.einsum('...i,...j->...ij',u,u))
        PC,_ = flow.observe(C)
        Ph = P+PC
        H = C+np.eye(3)
        eig = np.linalg.eigvalsh(C)
        if np.min(eig) <= -1:
            raise ArithmeticError('capacity matrix loses positive definiteness')
        h = np.linalg.det(H)**(1/3)
        invH = np.linalg.inv(H)
        Psi = cellular.Prefix.observable(B,Ph)
        z = Psi/h
        active = z > self.threshold
        a = np.where(active,1-self.threshold**2/z**2,0)
        curv = np.where(active,2*self.threshold**2/z**3,0)
        cb = np.where(active,2*self.threshold*(1-self.threshold/z),0)
        F = np.where(active,(Psi-self.threshold*h)**2/Psi,0)
        r = dot(B,B)
        Pgrad2 = np.zeros_like(r);PCgrad2 = np.zeros_like(r)
        parent = np.zeros_like(r);observed = np.zeros_like(r)
        fullD = np.zeros_like(r);J = np.zeros_like(r);flux_pair = np.zeros_like(r)
        G = B @ np.swapaxes(B,-1,-2)
        Qgeom = (2*self.nu/3)*np.trace(invH @ G,axis1=-2,axis2=-1)
        traceP = np.trace(P,axis1=-2,axis2=-1)
        sourcegrad = np.stack([flow.derivative(traceP,j) for j in range(3)],axis=-1)
        flux = mv(P,sourcegrad)
        for j in range(3):
            E = flow.derivative(B,j);L = flow.derivative(Ph,j)
            PP = flow.derivative(P,j);CP = flow.derivative(PC,j)
            Cj = flow.matrix(gc[j][...,3:]);Hj = invH @ Cj
            dh = h*np.trace(Hj,axis1=-2,axis2=-1)/3
            dPsi,ddPsi = cellular.Prefix.observable(B,Ph,(E,L))
            dz = (dPsi-z*dh)/h
            Pgrad2 += dot(PP,PP);PCgrad2 += dot(CP,CP)
            parent += r*dot(E,E);observed += dot(L,L)
            fullD += self.nu*ddPsi
            J += self.nu*h*curv*dz*dz
            flux[...,j] -= dot(P,PP)
            flux_pair += curv*dz*flux[...,j]
            Qgeom += (self.nu/3)*(np.trace(Hj @ Hj,axis1=-2,axis2=-1)
                                      -np.trace(Hj,axis1=-2,axis2=-1)**2/3)
        lowerD = self.nu*(8*parent+(56/5)*observed)
        if np.min(fullD-lowerD)<-1e-7*max(1,np.max(fullD)):
            raise ArithmeticError('completed Hessian violates physical lower bound')
        stress = np.einsum('...i,...j->...ij',u,u)+C
        gp = np.stack([flow.derivative(p,j) for j in range(3)],axis=-1)
        sym = np.einsum('...i,...j->...ij',u,gp)+np.einsum('...i,...j->...ij',gp,u)
        advstress = sum(u[...,j,None,None]*flow.derivative(stress,j) for j in range(3))
        advPh = sum(u[...,j,None,None]*flow.derivative(Ph,j) for j in range(3))
        DPh = -flow.observe(sym)[0]+advPh-flow.observe(advstress)[0]
        production,_ = cellular.Prefix.observable(B,Ph,(-B @ B-P,DPh))
        signed = a*production-cb*h*Qgeom-a*fullD-J
        source2 = np.sum(sourcegrad*sourcegrad,axis=-1)
        mean = lambda q:float(np.mean(q))
        ratio = lambda q,d:mean(q)/mean(d) if mean(d)>0 else None
        R,S,EP = self.parent_values(original_state)
        nonlinear,_ = self.rhs(original_state)
        rates = self.parent_rates(original_state,nonlinear)
        amplitude_density = np.sum(abs(original_state[...,:3]/self.n**3)**2,axis=-1)
        high = np.any(abs(self.K)>.8*self.n/3,axis=-1)
        canonical_source = np.trace(B @ B,axis1=-2,axis2=-1)
        source_error = mean((traceP+canonical_source)**2)
        return {'time':t,'excess_mass':mean(F),'active_fraction':mean(active),'threshold':self.threshold,
                'maximum_ratio':float(np.max(z)),'minimum_memory_eigenvalue':float(np.min(eig)),
                'memory_capacity_minimum':float(np.min(h)),'energy':mean(np.sum(u*u,axis=-1)),
                'energy_memory_balance_error':mean(np.sum(u*u,axis=-1)+np.trace(C,axis1=-2,axis2=-1))-self.energy0,
                'parent_reserve':R,'parent_shear_bound':S,'parent_energy':EP,
                'parent_renewal_rate':float(rates[1]),'parent_reserve_rate':float(rates[1]-rates[0]),
                'parent_reserve_ledger_error':float(R-self.R0+ledger[0]-ledger[1]),
                'parent_energy_ledger_error':float(EP-self.EP0-ledger[2]+ledger[3]),
                'parent_renewal_integral':float(ledger[1]),'parent_shear_integral':float(ledger[0]),
                'canonical_pressure_source_error_l2sq':source_error,
                'high_velocity_energy_fraction':float(np.sum(amplitude_density[high])/np.sum(amplitude_density)),
                'high_enstrophy_fraction':float(np.sum((amplitude_density*self.k2)[high])/np.sum(amplitude_density*self.k2)),
                'weighted_pressure_flux_direct':mean(a*(Pgrad2-source2)),
                'weighted_pressure_flux_gradient':mean(flux_pair),
                'selected_memory_vs_lower_diffusion':ratio(self.nu*a*PCgrad2,a*lowerD),
                'selected_memory_vs_full_diffusion':ratio(self.nu*a*PCgrad2,a*fullD),
                'selected_completed_diffusion':mean(a*fullD),'weight_gradient_payment':mean(J),
                'signed_excess_production':mean(signed)}


def initial_operator_check():
    """Compare every retained coefficient with the exact full initial RHS.

    This tiny grid contains every quadratic output of this particular
    datum. It is an operator check, not a solution-resolution claim.
    """
    nu, epsilon = Fraction(1, 100), Fraction(1, 5)
    maximum_error = 0.
    for phase in (-1, 1):
        flow = Flow(24, float(nu), epsilon, phase)
        rhs, _ = flow.rhs(flow.initial)
        u = seed(epsilon, phase)
        N, _ = nonlinear_source(u)
        B = f.jac(u)
        G = f.matmul(B, list(map(list, zip(*B))))
        fields = N+[f.scale(2*f.QQ_I(nu), G[i][j]) for i, j in PAIRS]
        exact = np.zeros_like(rhs)
        for j, field in enumerate(fields):
            for k, amplitude in field.items():
                exact[tuple(q % flow.n for q in k)+(j,)] = complex(
                    float(amplitude.x), float(amplitude.y))*flow.n**3
        error = float(np.max(abs(rhs-exact))/flow.n**3)
        maximum_error = max(maximum_error, error)
    if maximum_error > 2e-13:
        raise ArithmeticError('full initial velocity/memory operator mismatch')
    return maximum_error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true', help='evolve a numerical 3D prefix')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=.01)
    parser.add_argument('--epsilon', type=Fraction, default=Fraction(1, 5))
    parser.add_argument('--phase', type=int, choices=(1, -1), default=1)
    parser.add_argument('--final-time', type=float, default=2)
    parser.add_argument('--dt', type=float, default=.005)
    parser.add_argument('--sample-interval', type=float, default=.5)
    parser.add_argument('--diagnostic-n', type=int, default=0)
    parser.add_argument('--save-state', help='save final Fourier state for diagnostic refinement')
    args = parser.parse_args()
    if not args.prefix:
        checks = [exact_check(epsilon, phase, Fraction(1, 100))
                  for epsilon in (Fraction(0), Fraction(1, 5), Fraction(2, 5))
                  for phase in (1, -1)]
        print(json.dumps({'exact_checks': checks,
                          'initial_operator_maximum_error': initial_operator_check()}, indent=2))
        return
    if (args.n < 18 or args.n % 2 or args.nu <= 0 or args.epsilon < 0
            or args.final_time <= 0 or args.dt <= 0 or args.sample_interval <= 0):
        parser.error('an even grid >=18, positive times/viscosity and nonnegative amplitude are required')
    flow = Flow(args.n, args.nu, args.epsilon, args.phase)
    state = flow.initial.copy()
    ledger = np.zeros(4)
    samples = []
    diag = args.diagnostic_n or 2*args.n
    if diag < 2*args.n:
        parser.error('diagnostic grid must be at least twice the evolution grid')
    print(json.dumps({'initial_exact': exact_check(args.epsilon, args.phase,
                                                   Fraction(str(args.nu))),
                      'initial_parent_reserve': flow.R0,
                      'datum_fixed_threshold': flow.threshold}), flush=True)
    samples.append(flow.diagnostic(0, state, ledger, diag))
    print(json.dumps(samples[-1]), flush=True)
    steps = max(1, int(round(args.final_time/args.dt)))
    dt = args.final_time/steps
    stride = max(1, int(round(args.sample_interval/dt)))
    start = time.monotonic()
    for k in range(steps):
        state, rates = flow.step(state, dt)
        ledger += rates
        if (k+1) % stride == 0 or k+1 == steps:
            samples.append(flow.diagnostic((k+1)*dt, state, ledger, diag))
            print(json.dumps(samples[-1]), flush=True)
    if args.save_state:
        np.savez(args.save_state, state=state, ledger=ledger,
                 n=args.n, nu=args.nu, epsilon=str(args.epsilon), phase=args.phase,
                 time=args.final_time, dt=dt, threshold=flow.threshold)
    print(json.dumps({'resolution': args.n, 'nu': args.nu, 'epsilon': str(args.epsilon),
                      'phase': args.phase, 'dt': dt, 'diagnostic_n': diag,
                      'samples': samples, 'elapsed_seconds': time.monotonic()-start,
                      'scope': 'full unforced Fourier-Galerkin velocity/memory approximation; '
                               'canonical pressure on padded field, not a continuum enclosure'}, indent=2))


if __name__ == '__main__':
    main()
