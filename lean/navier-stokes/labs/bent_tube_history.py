#!/usr/bin/env python3
"""Signed tail history of an explicit periodic antiparallel bent-tube pair.

The unforced equation, physical energy normalization and tail split match
kida_pelz_history.py. This family uses only two reflection planes, leaving
the third direction as a full complex Fourier transform. Every nonlinear
input evolves. The initial vorticity formula is in bent_tube_symmetry.py.

The output is a finite Fourier--Galerkin computation. Grid refinement and
small balance errors do not constitute a continuum error enclosure or a
bound through a possible singular endpoint.
"""
import argparse
import json
import time

import numpy as np

if __package__:
    from .bent_tube_symmetry import TwoReflectionFlow, bent_vorticity
else:
    from bent_tube_symmetry import TwoReflectionFlow, bent_vorticity


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,default=128,
                        help='equivalent full-cube grid size')
    parser.add_argument('--viscosity',type=float,default=.001)
    parser.add_argument('--radius',type=float,default=.2)
    parser.add_argument('--distance',type=float,default=.5)
    parser.add_argument('--bend',type=float,default=.15)
    parser.add_argument('--mode',type=int,default=2)
    parser.add_argument('--kinetic-energy',type=float,default=3*np.pi**3)
    parser.add_argument('--time',type=float,default=.5)
    parser.add_argument('--step',type=float,default=.001)
    parser.add_argument('--report-every',type=float,default=.05)
    parser.add_argument('--self-cutoffs',nargs='+',type=float,default=[4.,8.,12.])
    parser.add_argument('--max-high-palinstrophy',type=float,default=.005)
    parser.add_argument('--workers',type=int,default=1)
    parser.add_argument('--checkpoint',help='optional final NumPy checkpoint')
    parser.add_argument('--check-only',action='store_true')
    a=parser.parse_args()
    if a.n<64 or a.n%2 or a.workers<1 or a.mode<1:
        parser.error('even n>=64 and positive mode and worker counts required')
    if any(not np.isfinite(v) or v<=0 for v in [a.viscosity,a.radius,a.distance,
            a.kinetic_energy,a.time,a.step,a.report_every,a.max_high_palinstrophy]):
        parser.error('positive finite physical and time parameters required')
    if not np.isfinite(a.bend) or a.bend<0 or not a.bend<a.distance<np.pi-a.bend:
        parser.error('require 0<=bend<distance<pi-bend')
    if len(set(a.self_cutoffs))!=len(a.self_cutoffs) or any(
            k not in [0,4,8,12,16,24] for k in a.self_cutoffs):
        parser.error('self cutoffs must be distinct members of 0,4,8,12,16,24')
    m=TwoReflectionFlow(a.n,a.viscosity,a.self_cutoffs,a.radius,a.distance,
                        a.bend,a.mode,a.kinetic_energy,a.workers)
    u=m.initial.copy()
    initial=m.energies(u);initial_tails=m.tail_enstrophy(u)
    nt=len(m.tail_cutoffs)
    indices=np.array([list(m.tail_cutoffs).index(k) for k in a.self_cutoffs])
    _,rates,work=m.rhs(u)
    analytic=m.normalization*bent_vorticity(m.x,m.y,m.z,a.radius,a.distance,a.bend,a.mode)
    reconstructed=m.decode_vector(m.curl_velocity(u),m.vorticity_parities)
    reconstruction=float(np.linalg.norm(analytic-reconstructed)/np.linalg.norm(analytic))
    del analytic,reconstructed
    if abs(initial[0]/a.kinetic_energy-1)>1e-12:
        raise ArithmeticError('kinetic normalization failed')
    if abs(m.self_stretching(u,[0.])[0]-rates[1])>1e-10*initial[1]:
        raise ArithmeticError('initial Betchov identity failed')
    initial_resolution=m.resolution(u)
    initial_stop=(initial_resolution['high_palinstrophy_fraction']>a.max_high_palinstrophy)
    print(json.dumps({'configuration':vars(a),'vorticity_factor':float(m.normalization),
        'initial_energy':initial.tolist(),'initial_tail_enstrophy':initial_tails.tolist(),
        'initial_vorticity_reconstruction_relative_error':reconstruction,
        'initial_production':float(rates[1]),'initial_resolution':initial_resolution,
        'stop_reason':'initial_resolution_limit' if initial_stop else None}),flush=True)
    if a.check_only or initial_stop:return
    integrated=np.zeros_like(rates);maxima=np.zeros(len(indices))
    started=time.monotonic();t=0.;steps=0
    next_report=min(a.report_every,a.time);reason='requested_time'
    while t<a.time-1e-13:
        velocity=m.ifft(u).real
        cfl_rate=(a.n/3)*float(np.max(np.sum(np.abs(velocity),axis=0)))
        dt=min(a.step,.5/max(cfl_rate,1e-30),
               2/(a.viscosity*np.max(m.ksq[m.mask])),next_report-t)
        del velocity
        u,di,dw=m.step(u,dt);integrated+=di;work=max(abs(work),dw)
        steps+=1;t+=dt
        ps=integrated[3+2*nt:];ds=integrated[3+nt:3+2*nt][indices]
        maxima=np.maximum(maxima,ps-.5*ds)
        if not np.all(np.isfinite(u)):raise ArithmeticError('nonfinite velocity')
        if t>=next_report-1e-13:
            energy=m.energies(u);tails=m.tail_enstrophy(u)
            _,rates,_=m.rhs(u)
            pfull=integrated[3:3+nt];dfull=integrated[3+nt:3+2*nt]
            resolution=m.resolution(u)
            reason=('resolution_limit' if resolution['high_palinstrophy_fraction']
                    >a.max_high_palinstrophy else 'requested_time')
            print(json.dumps({'time':t,'steps':steps,'last_step':dt,'energy':energy.tolist(),
                'integrated_production':float(integrated[1]),
                'integrated_dissipation':float(integrated[2]),
                'kinetic_ledger':float(energy[0]-initial[0]+integrated[0]),
                'enstrophy_ledger':float(energy[1]-initial[1]-integrated[1]+integrated[2]),
                'tail_ledger_max':float(np.max(np.abs(tails-initial_tails-pfull+dfull))),
                'tails':[dict(cutoff=float(k),enstrophy=float(tails[i]),
                    integrated_self=float(ps[j]),integrated_low_input=float(pfull[i]-ps[j]),
                    integrated_dissipation=float(ds[j]),half_excess=float(ps[j]-.5*ds[j]),
                    sampled_prefix_max=float(maxima[j]),
                    instantaneous_self=float(rates[3+2*nt+j]),
                    instantaneous_low_input=float(rates[3+i]-rates[3+2*nt+j]),
                    instantaneous_dissipation=float(rates[3+nt+i]))
                    for j,(k,i) in enumerate(zip(a.self_cutoffs,indices))],
                'resolution':resolution,'max_nonlinear_kinetic_work':float(work),
                'stop_reason':reason if reason=='resolution_limit' or t>=a.time-1e-13 else None,
                'wall_seconds':time.monotonic()-started}),flush=True)
            if reason=='resolution_limit':break
            next_report=min(next_report+a.report_every,a.time)
    if a.checkpoint:
        np.savez(a.checkpoint,velocity=u,integrated=integrated,time=t,
                 configuration=json.dumps(vars(a)),sampled_prefix_max=maxima,stop_reason=reason)


if __name__=='__main__':main()
