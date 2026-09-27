"""Independent full-Fourier checks of the two-plane bent-tube solver.

Checks evolved fields, the complete RHS, signed rates and their integrals,
Betchov stretching against a filtered RHS, and time-step refinement.
These are numerical consistency checks, not continuum error enclosures.
"""
import json
import numpy as np
if __package__:
    from .bent_tube_symmetry import TwoReflectionFlow, bent_vorticity
    from .kida_pelz_history import KidaPelzFlow
    from .full_history import FullFlow, cross
else:
    from bent_tube_symmetry import TwoReflectionFlow, bent_vorticity
    from kida_pelz_history import KidaPelzFlow
    from full_history import FullFlow, cross


def pair(n, radius):
    reduced = TwoReflectionFlow(n, .001, [4,8,12], radius=radius)
    full = KidaPelzFlow(n, .001, [4,8,12])
    x = 2*np.pi*np.arange(n)/n
    w = bent_vorticity(x[:,None,None], x[None,:,None], x[None,None,:], radius=radius)
    full.initial = full.project(1j*cross(full.k, full.fft(w))*full.inv)
    full.initial *= np.sqrt(3*np.pi**3/full.energies(full.initial)[0])
    return full,reduced


def evolve(m,dt,count):
    u=m.initial.copy()
    total=np.zeros_like(m.rhs(u)[1])
    for _ in range(count):
        u,di,_=m.step(u,dt)
        total+=di
    return u,total


def check(n=64,radius=.35,dt=.001,count=20):
    f,r=pair(n,radius)
    phase=np.exp(1j*(f.k[1]+f.k[2])*np.pi/n)
    def quarter(u):return f.ifft(u*phase)[:,:,:n//2,:n//2]
    def relative(x,y):return float(np.linalg.norm(x-y)/np.linalg.norm(x))
    initial_error=relative(quarter(f.initial),r.ifft(r.initial))
    if np.max(np.abs(f.energies(f.initial)-r.energies(r.initial)))>1e-9:
        raise ArithmeticError('initial physical energy mismatch')
    fu,fi=evolve(f,dt,count)
    ru,ri=evolve(r,dt,count)
    rf,fr,_=f.rhs(fu);rr,rrates,_=r.rhs(ru)
    result=dict(n=n,radius=radius,time=dt*count,
                initial_relative_field=initial_error,
                relative_evolved_field=relative(quarter(fu),r.ifft(ru)),
                relative_evolved_rhs=relative(quarter(rf),r.ifft(rr)),
                max_rate_difference=float(np.max(np.abs(fr-rrates))),
                max_integral_difference=float(np.max(np.abs(fi-ri))),
                resolution=r.resolution(ru),stretching=[])
    for k in [0,4,8,12]:
        v=fu*(f.ksq>=k*k)
        independent=FullFlow.rhs(f,v)[1][1]
        physical=f.self_stretching(fu,[k])[0]
        reduced=r.self_stretching(ru,[k])[0]
        error=float(max(abs(independent-physical),abs(independent-reduced)))
        result['stretching'].append(dict(cutoff=k,filtered_rhs=float(independent),
            full_betchov=float(physical),reduced_betchov=float(reduced),max_error=error))
        if error>1e-8:raise ArithmeticError(result)
    if (initial_error>1e-10 or result['relative_evolved_field']>1e-10
        or result['relative_evolved_rhs']>1e-9 or result['max_rate_difference']>1e-7
        or result['max_integral_difference']>1e-8):raise ArithmeticError(result)
    # Step refinement has a different error source from the transform comparison.
    coarse,ci=evolve(r,2*dt,count//2)
    result['relative_step_refinement']=relative(ru,coarse)
    result['step_self_integral_difference']=(ci[-3:]-ri[-3:]).tolist()
    if result['relative_step_refinement']>1e-7:raise ArithmeticError(result)
    return result


if __name__=='__main__':
    print(json.dumps([check(),check(96,.2,.0005,4)],indent=2),flush=True)
