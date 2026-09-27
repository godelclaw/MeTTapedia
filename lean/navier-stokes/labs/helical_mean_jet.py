#!/usr/bin/env python3
"""First permitted fast angular mean: a finite Galerkin Euler time jet.

The two complex parents have cylindrical labels (m, 1), (-(m+2), -1),
where the axial wave number is twice the second label. Their normalized
horizontal streamfunctions are w^m exp(-r^2)/sqrt(d_m) and its degree-m+2
counterpart conjugated, with d_j=(j+1)!/2^(j+1).

For even m=2k, all binary ancestry branches of the word (k+1, k) are
retained. Its velocity coefficient multiplies t^(2k), with no factorial.
This is the highest parent-amplitude degree in that time coefficient;
background interactions and viscosity cannot contribute at that degree.
For real parents of amplitude epsilon, the word and its conjugate give
epsilon^(2k+1)/2^(2k) times Re(U exp(2iz)) t^(2k).

Horizontal Fourier Galerkin discretization uses a periodic square and
strict two-thirds dealiasing. Axial labels are exact. Angular labels
describe the continuum parents; the square only approximates rotational
symmetry. Every intermediate Leray projection is retained.

The calibration uses the independently known cubic example. The two RHS
forms provide a separate advective/vorticity check. Grid and box studies
are diagnostics, not a continuum error enclosure, a positive-time bound,
or a recurrent cascade. Requires NumPy and SciPy.
"""
import argparse
import json
import math
import time

import numpy as np
from scipy.fft import fftn, ifftn
from scipy.special import j1


def cross(a, b):
    return np.stack([a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2],
                     a[0]*b[1]-a[1]*b[0]])


class Jet:
    def __init__(self, n, box, m, calibration=False):
        self.n, self.box, self.m = n, box, m
        self.calibration = calibration
        x = (np.arange(n)/n-.5)*box
        xx, yy = np.meshgrid(x, x, indexing='ij')
        r2 = xx*xx+yy*yy
        w = xx+1j*yy
        kh = 2*np.pi*np.fft.fftfreq(n, box/n)
        self.kx, self.ky = np.meshgrid(kh, kh, indexing='ij')
        self.kh2 = self.kx**2+self.ky**2
        labels = np.fft.fftfreq(n, 1/n)
        a, b = np.meshgrid(labels, labels, indexing='ij')
        self.mask = (np.abs(a)<n/3) & (np.abs(b)<n/3)
        self.high = (np.abs(a)>.8*n/3) | (np.abs(b)>.8*n/3)
        self.area = box**2/n**4/(2*np.pi)
        if calibration:
            first = w**2*np.exp(-r2)
            second = np.conj(w)**4*(1-.4*r2)*np.exp(-r2)
        else:
            first = w**m*np.exp(-r2)/math.sqrt(math.factorial(m+1)/2**(m+1))
            second = (np.conj(w)**(m+2)*np.exp(-r2)
                      /math.sqrt(math.factorial(m+3)/2**(m+3)))
        self.fields, self.values, self.curls, self.divergences = {}, {}, {}, {}
        for label, psi in [((1, 0), first), ((0, 1), second)]:
            ph = self.fft(psi)*self.mask
            self.store(label, np.array([1j*self.ky*ph, -1j*self.kx*ph,
                                        np.zeros_like(ph)]))
        self.radii = np.array([.5, .75, 1., 1.25, 1.5, 1.75, 2., 2.5, 3.])
        kr = self.radii[:, None, None]*np.sqrt(self.kh2)
        bessel = np.divide(j1(kr), kr, out=np.full_like(kr, .5), where=kr>0)
        shift = np.exp(.5j*box*(self.kx+self.ky))/n**2
        # Exact circular average of the retained Fourier polynomial's r*u_theta.
        self.circle_kernel = 1j*self.radii[:, None, None]**2*bessel*shift

    @staticmethod
    def fft(v):
        return fftn(v, axes=(-2, -1), workers=1)

    @staticmethod
    def ifft(v):
        return ifftn(v, axes=(-2, -1), workers=1)

    def wave(self, label):
        return np.array([self.kx, self.ky,
                         np.full_like(self.kx, 2*(label[0]-label[1]))])

    def project(self, v, label):
        k = self.wave(label)
        ksq = (k*k).sum(axis=0)
        inv = np.divide(1, ksq, out=np.zeros_like(ksq), where=ksq>0)
        return self.mask*(v-k*(inv*(k*v).sum(axis=0)))

    def store(self, label, u):
        k = self.wave(label)
        self.fields[label] = u
        self.values[label] = self.ifft(u)
        self.curls[label] = self.ifft(1j*cross(k, u))
        self.divergences[label] = float(np.sqrt(
            self.area*np.sum(np.abs((k*u).sum(axis=0))**2)))

    def compute(self, form='vorticity'):
        k = self.m//2
        target = (k+1, k)
        started = time.monotonic()
        for degree in range(2, sum(target)+1):
            for ia in range(target[0]+1):
                ib = degree-ia
                if not 0 <= ib <= target[1]:
                    continue
                label = (ia, ib)
                raw = np.zeros((3, self.n, self.n), complex)
                for ja in range(ia+1):
                    for jb in range(ib+1):
                        left, right = (ja, jb), (ia-ja, ib-jb)
                        if left not in self.fields or right not in self.fields:
                            continue
                        if form == 'vorticity':
                            raw += cross(self.values[left], self.curls[right])
                        else:
                            kr = self.wave(right)
                            for axis in range(3):
                                raw -= self.values[left][axis]*self.ifft(
                                    1j*kr[axis]*self.fields[right])
                # Differentiate t^(degree-1); all ordered partitions were summed.
                self.store(label, self.project(self.fft(raw), label)/(degree-1))
        u = self.fields[target]
        density = np.sum(np.abs(u)**2, axis=0)
        circles = np.einsum('rij,ij->r', self.circle_kernel,
                            -self.ky*u[0]+self.kx*u[1])
        r1 = circles[2]
        total = np.sum(density)
        result = {
            'target_word': target, 'time_power': sum(target)-1,
            'angular_label': self.m*target[0]-(self.m+2)*target[1],
            'axial_label': target[0]-target[1],
            'recipient_norm': float(np.sqrt(self.area*total)),
            'circulation_r1_real': float(r1.real),
            'circulation_r1_imag': float(r1.imag),
            'circulation_samples': [[float(r), float(z.real), float(z.imag)]
                                    for r, z in zip(self.radii, circles)],
            'recipient_high_fraction': float(np.sum(density[self.high])/total)
                if total else 0.,
            'max_divergence_l2': max(self.divergences.values()),
            'states': len(self.fields), 'wall_seconds': time.monotonic()-started}
        if self.calibration:
            exact = -16/(5*math.e**3)
            result['exact_cubic_circulation_r1'] = exact
            result['cubic_relative_error'] = float(abs(r1-exact)/abs(exact))
        return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--n', type=int, default=192)
    p.add_argument('--box', type=float, default=14.)
    p.add_argument('--m', type=int, default=6)
    p.add_argument('--calibration', action='store_true')
    p.add_argument('--form', choices=['vorticity', 'advection'], default='vorticity')
    args = p.parse_args()
    if args.calibration:
        args.m = 2
    if args.m < 2 or args.m % 2 or args.n < 32:
        p.error('even m>=2 and n>=32 required')
    if not np.isfinite(args.box) or args.box <= 0:
        p.error('box must be finite and positive')
    model = Jet(args.n, args.box, args.m, args.calibration)
    print(json.dumps({'configuration': vars(args),
                      'result': model.compute(args.form)}), flush=True)


if __name__ == '__main__':
    main()
