"""Real sine/cosine representation of the Kida--Pelz reflection symmetries.

The three velocity components are odd in their own coordinate and even
in the other two. These symmetries are preserved by the real unforced
Navier--Stokes equation. A midpoint grid on (0,pi)^3 therefore represents
the full 2*pi-periodic cube. ``n`` denotes the equivalent full grid size;
each stored dimension has n/2 entries. The retained modes satisfy k_j<n/3,
exactly the same strict Galerkin truncation as the full-cube implementation.

Orthonormal DCT-II and DST-II coefficients share wave-number indices.
The unused sine zero mode is zero, and the sine Nyquist mode is discarded.
This avoids complex coefficients and redundant reflected octants. It
imposes no axisymmetry, angular averaging, or change to the nonlinearity.
"""
import numpy as np
from scipy.fft import dctn, dstn, idctn, idstn

if __package__:
    from .full_history import FullFlow, cross
else:
    from full_history import FullFlow, cross


class ReflectionFlow(FullFlow):
    velocity_parities = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    vorticity_parities = ((0, 1, 1), (1, 0, 1), (1, 1, 0))

    def __init__(self, n, viscosity, self_cutoffs):
        if n % 2:
            raise ValueError('even full-cube grid size required')
        self.n = self.nz = n
        self.reduced_n = n // 2
        self.box = 2 * np.pi
        self.viscosity = viscosity
        labels = np.arange(self.reduced_n, dtype=float)
        self.k = np.array(np.meshgrid(labels, labels, labels, indexing='ij'))
        self.ksq = np.sum(self.k**2, axis=0)
        self.inv = np.divide(1, self.ksq, out=np.zeros_like(self.ksq), where=self.ksq > 0)
        self.mask = np.all(self.k < n / 3, axis=0)
        self.high = np.any(self.k > .8 * n / 3, axis=0)
        self.tail_cutoffs = np.array([0., 4., 8., 12., 16., 24.])
        self.tail_bins = np.searchsorted(self.tail_cutoffs**2, self.ksq, side='right')
        self.self_cutoffs = np.array(self_cutoffs, dtype=float)
        self.area = (2 * np.pi)**3 / self.reduced_n**3
        x = (np.arange(self.reduced_n) + .5) * np.pi / self.reduced_n
        s, c, c3 = np.sin(x), np.cos(x), np.cos(3 * x)
        velocity = np.array([
            s[:, None, None] * (c3[None, :, None] * c[None, None, :]
                                - c[None, :, None] * c3[None, None, :]),
            s[None, :, None] * (c3[None, None, :] * c[:, None, None]
                                - c[None, None, :] * c3[:, None, None]),
            s[None, None, :] * (c3[:, None, None] * c[None, :, None]
                                - c[:, None, None] * c3[None, :, None])])
        self.initial = self.project(self.encode_vector(velocity, self.velocity_parities))

    @staticmethod
    def encode(v, parity):
        even = tuple(j - 3 for j, p in enumerate(parity) if not p)
        odd = tuple(j - 3 for j, p in enumerate(parity) if p)
        a = dctn(v, type=2, axes=even, norm='ortho', workers=1) if even else v.copy()
        if odd:
            # Uniform sqrt(2/n) sine modes; the discarded Nyquist mode
            # requires no endpoint renormalization.
            a = dstn(a, type=2, axes=odd, norm='ortho', orthogonalize=False, workers=1)
        for axis in odd:
            a = np.roll(a, 1, axis=axis)
            selector = [slice(None)] * a.ndim
            selector[axis] = 0
            a[tuple(selector)] = 0
        return a

    @staticmethod
    def decode(a, parity):
        even = tuple(j - 3 for j, p in enumerate(parity) if not p)
        odd = tuple(j - 3 for j, p in enumerate(parity) if p)
        v = a.copy()
        for axis in odd:
            selector = [slice(None)] * v.ndim
            selector[axis] = 0
            v[tuple(selector)] = 0
            v = np.roll(v, -1, axis=axis)
        if odd:
            v = idstn(v, type=2, axes=odd, norm='ortho', orthogonalize=False, workers=1)
        return idctn(v, type=2, axes=even, norm='ortho', workers=1) if even else v

    def encode_vector(self, v, parities):
        return np.array([self.encode(c, p) for c, p in zip(v, parities)])

    def decode_vector(self, v, parities):
        return np.array([self.decode(c, p) for c, p in zip(v, parities)])

    def ifft(self, u):
        return self.decode_vector(u, self.velocity_parities)

    def self_stretching(self, u, cutoffs):
        kx, ky, kz = self.k
        answer = []
        for cutoff in cutoffs:
            v = u * (self.ksq >= cutoff**2)
            aa, bb = self.decode(np.array([kx * v[0], ky * v[1]]), (0, 0, 0))
            dd = self.decode(-.5 * (ky * v[0] + kx * v[1]), (1, 1, 0))
            ee = self.decode(-.5 * (kz * v[0] + kx * v[2]), (1, 0, 1))
            ff = self.decode(-.5 * (kz * v[1] + ky * v[2]), (0, 1, 1))
            cc = -aa - bb
            determinant = aa * bb * cc + 2 * dd * ee * ff - aa * ff**2 - bb * ee**2 - cc * dd**2
            answer.append(-4 * self.area * float(np.sum(determinant)))
        return np.array(answer)

    def rhs(self, u):
        velocity = self.ifft(u)
        omega = self.decode_vector(-cross(self.k, u), self.vorticity_parities)
        source = self.project(self.encode_vector(cross(velocity, omega), self.velocity_parities))
        density = np.sum(u**2, axis=0)
        energy_loss = self.viscosity * self.area * np.sum(self.ksq * density)
        enstrophy_loss = self.viscosity * self.area * np.sum(self.ksq**2 * density)
        p = self.area * self.ksq * np.sum(u * source, axis=0)
        d = self.viscosity * self.area * self.ksq**2 * density
        rates = np.concatenate([[energy_loss, np.sum(p), enstrophy_loss],
            self.tail_sums(p), self.tail_sums(d), self.self_stretching(u, self.self_cutoffs)])
        work = self.area * np.sum(u * source)
        return source - self.viscosity * self.ksq * u, rates, work

    def resolution(self, u):
        density = np.sum(u**2, axis=0)
        pal = self.ksq**2 * density
        v = self.ifft(u)
        omega = self.decode_vector(-cross(self.k, u), self.vorticity_parities)
        return {
            'high_palinstrophy_fraction': float(np.sum(pal[self.high]) / np.sum(pal)),
            'high_enstrophy_fraction': float(np.sum((self.ksq * density)[self.high])
                                               / np.sum(self.ksq * density)),
            'max_velocity': float(np.max(np.sqrt(np.sum(v**2, axis=0)))),
            'max_vorticity': float(np.max(np.sqrt(np.sum(omega**2, axis=0)))),
            'divergence_l2': float(np.sqrt(self.area * np.sum(np.sum(self.k * u, axis=0)**2))),
            'max_reality_error': 0.}
