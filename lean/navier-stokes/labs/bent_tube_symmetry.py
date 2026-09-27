"""Two-plane reflection representation of a periodic bent vortex-tube pair.

Fourier transform in x; cosine/sine transforms in y,z on midpoint nodes.
Velocity has parities (even,even),(odd,even),(even,odd) in y,z, preserved
by the unforced Navier--Stokes equation. All retained modes obey the same
strict two-thirds rule as a full cube. The mixed representation requires
separate spectral and physical volume factors.

The analytic datum has eta(y)=distance-bend*cos(mode*y),
Fplus=exp((cos(x)+cos(z-eta(y))-2)/radius**2), and similarly Fminus
with z+eta(y). Its vorticity is (0,Fplus-Fminus,eta'*(Fplus+Fminus)).
The y and z derivatives cancel exactly, and all three means vanish.
Thus curl(-Delta)^(-1) recovers a periodic solenoidal velocity. A common
factor normalizes its kinetic energy. This is an explicit test family,
not a reproduction of a named vortex-tube dataset.
"""
import numpy as np
from scipy.fft import fftn, ifftn, dctn, dstn, idctn, idstn

if __package__:
    from .full_history import FullFlow, cross
else:
    from full_history import FullFlow, cross


def bent_vorticity(x, y, z, radius=.2, distance=.5, bend=.15, mode=2):
    eta = distance - bend * np.cos(mode * y)
    derivative = mode * bend * np.sin(mode * y)
    plus = np.exp((np.cos(x) + np.cos(z - eta) - 2) / radius**2)
    minus = np.exp((np.cos(x) + np.cos(z + eta) - 2) / radius**2)
    return np.array([np.zeros_like(plus), plus - minus, derivative * (plus + minus)])


class TwoReflectionFlow(FullFlow):
    velocity_parities = ((0, 0), (1, 0), (0, 1))
    vorticity_parities = ((1, 1), (0, 1), (1, 0))

    def __init__(self, n, viscosity, self_cutoffs, radius=.2, distance=.5,
                 bend=.15, mode=2, kinetic_energy=3*np.pi**3, workers=1):
        if n % 2:
            raise ValueError('even full-cube size required')
        self.n = self.nz = n
        self.reduced_n = n // 2
        self.viscosity = viscosity
        self.workers = workers
        labels = np.rint(np.fft.fftfreq(n, 1/n))
        positive = np.arange(self.reduced_n, dtype=float)
        self.k = np.array(np.meshgrid(labels, positive, positive, indexing='ij'))
        self.ksq = np.sum(self.k**2, axis=0)
        self.inv = np.divide(1, self.ksq, out=np.zeros_like(self.ksq), where=self.ksq > 0)
        self.mask = np.all(np.abs(self.k) < n/3, axis=0)
        self.high = np.any(np.abs(self.k) > .8*n/3, axis=0)
        self.tail_cutoffs = np.array([0., 4., 8., 12., 16., 24.])
        self.tail_bins = np.searchsorted(self.tail_cutoffs**2, self.ksq, side='right')
        self.self_cutoffs = np.array(self_cutoffs, dtype=float)
        self.area = (2*np.pi)**3 / (n**2 * self.reduced_n**2)
        self.volume_element = self.area * n
        self.x = 2*np.pi*np.arange(n)[:, None, None]/n
        self.y = (np.arange(self.reduced_n)[None, :, None]+.5)*np.pi/self.reduced_n
        self.z = (np.arange(self.reduced_n)[None, None, :]+.5)*np.pi/self.reduced_n
        omega = bent_vorticity(self.x, self.y, self.z, radius, distance, bend, mode)
        encoded = self.encode_vector(omega, self.vorticity_parities)
        self.initial = self.project(self.curl_vorticity(encoded) * self.inv)
        self.normalization = np.sqrt(kinetic_energy/self.energies(self.initial)[0])
        self.initial *= self.normalization

    def encode(self, v, parity):
        even = tuple(j-2 for j,p in enumerate(parity) if p == 0)
        odd = tuple(j-2 for j,p in enumerate(parity) if p == 1)
        a = fftn(v, axes=(-3,), workers=self.workers)
        if even:
            a = dctn(a, type=2, axes=even, norm='ortho', workers=self.workers)
        if odd:
            a = self.sine_transform(dstn, a, odd)
        for axis in odd:
            a = np.roll(a, 1, axis=axis)
            selector = [slice(None)]*a.ndim
            selector[axis] = 0
            a[tuple(selector)] = 0
        return a

    def sine_transform(self, transform, a, axes):
        # Apply the real transform to each part so that the requested uniform
        # sine normalization is respected by older SciPy complex wrappers.
        kwargs = dict(type=2, axes=axes, norm='ortho', orthogonalize=False,
                      workers=self.workers)
        if np.iscomplexobj(a):
            return transform(a.real, **kwargs) + 1j*transform(a.imag, **kwargs)
        return transform(a, **kwargs)

    def decode(self, a, parity):
        even = tuple(j-2 for j,p in enumerate(parity) if p == 0)
        odd = tuple(j-2 for j,p in enumerate(parity) if p == 1)
        v = a.copy()
        for axis in odd:
            selector = [slice(None)]*v.ndim
            selector[axis] = 0
            v[tuple(selector)] = 0
            v = np.roll(v, -1, axis=axis)
        if odd:
            v = self.sine_transform(idstn, v, odd)
        if even:
            v = idctn(v, type=2, axes=even, norm='ortho', workers=self.workers)
        return ifftn(v, axes=(-3,), workers=self.workers)

    def encode_vector(self, v, parities):
        return np.array([self.encode(a,p) for a,p in zip(v,parities)])

    def decode_vector(self, v, parities):
        return np.array([self.decode(a,p) for a,p in zip(v,parities)])

    def ifft(self, u):
        return self.decode_vector(u, self.velocity_parities)

    def divergence(self, u):
        kx,ky,kz = self.k
        return 1j*kx*u[0] + ky*u[1] + kz*u[2]

    def project(self, u):
        kx,ky,kz = self.k
        normal = np.array([-1j*kx,ky,kz])
        return self.mask * (u - normal*(self.inv*self.divergence(u)))

    def curl_velocity(self, u):
        kx,ky,kz = self.k
        return np.array([-ky*u[2]+kz*u[1], -kz*u[0]-1j*kx*u[2],
                         1j*kx*u[1]+ky*u[0]])

    def curl_vorticity(self, w):
        kx,ky,kz = self.k
        return np.array([ky*w[2]-kz*w[1], kz*w[0]-1j*kx*w[2],
                         1j*kx*w[1]-ky*w[0]])

    def self_stretching(self, u, cutoffs):
        kx,ky,kz = self.k
        values=[]
        for cutoff in cutoffs:
            v = u*(self.ksq >= cutoff**2)
            aa,bb = self.decode(np.array([1j*kx*v[0], ky*v[1]]),(0,0)).real
            dd = self.decode(.5*(-ky*v[0]+1j*kx*v[1]),(1,0)).real
            ee = self.decode(.5*(-kz*v[0]+1j*kx*v[2]),(0,1)).real
            ff = self.decode(-.5*(kz*v[1]+ky*v[2]),(1,1)).real
            cc = -aa-bb
            determinant=aa*bb*cc+2*dd*ee*ff-aa*ff**2-bb*ee**2-cc*dd**2
            values.append(-4*self.volume_element*np.sum(determinant))
        return np.array(values)

    def rhs(self, u):
        velocity = self.ifft(u)
        omega = self.decode_vector(self.curl_velocity(u), self.vorticity_parities)
        source = self.project(self.encode_vector(cross(velocity,omega),self.velocity_parities))
        density = np.sum(np.abs(u)**2,axis=0)
        work = self.area*np.real(np.sum(np.conj(u)*source,axis=0))
        p = self.ksq*work
        d = self.viscosity*self.area*self.ksq**2*density
        rates = np.concatenate([[self.viscosity*self.area*np.sum(self.ksq*density),
                                  np.sum(p),np.sum(d)],self.tail_sums(p),self.tail_sums(d),
                                 self.self_stretching(u,self.self_cutoffs)])
        return source-self.viscosity*self.ksq*u,rates,float(np.sum(work))

    def resolution(self,u):
        density=np.sum(np.abs(u)**2,axis=0)
        pal=self.ksq**2*density
        v=self.ifft(u)
        w=self.decode_vector(self.curl_velocity(u),self.vorticity_parities)
        return {'high_palinstrophy_fraction':float(np.sum(pal[self.high])/np.sum(pal)),
                'high_enstrophy_fraction':float(np.sum((self.ksq*density)[self.high])
                                               /np.sum(self.ksq*density)),
                'max_velocity':float(np.max(np.sqrt(np.sum(v.real**2,axis=0)))),
                'max_vorticity':float(np.max(np.sqrt(np.sum(w.real**2,axis=0)))),
                'divergence_l2':float(np.sqrt(self.area*np.sum(np.abs(self.divergence(u))**2))),
                'max_reality_error':float(np.max(np.abs(v.imag)))}
