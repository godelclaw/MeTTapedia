#!/usr/bin/env python3
"""Exact stress-transport and pressure-redistribution identities.

Complete periodic Fourier products identify the actual unforced tangent.
The separated whole-space fifth kernel is checked independently by
differentiating the Newtonian kernel. No bound on the cost of following
a changing region is supplied.
"""
import json
import sympy as s
import pressure_history_source as f


def zero(expr,label):
    rem=s.factor(expr)
    if rem!=0:raise ArithmeticError((label,rem))


def check_stress(nu):
    u=f.fixture();B=f.jac(u)
    f.equal(f.trace(B),{},'solenoidal datum')
    q=f.trace(f.matmul(B,B))
    if q.get(f.ORIGIN,f.ZERO):raise ArithmeticError('pressure source mean')
    p=f.green(q)
    ut=[f.add(f.scale(nu,f.lap(u[i])),f.scale(-1,f.adv(u,u[i])),
              f.scale(-1,f.diff(p,i))) for i in range(3)]
    f.equal(f.trace(f.jac(ut)),{},'actual tangent remains solenoidal')
    stress=f.tensor(u,u)
    stress_t=[[f.add(f.mul(ut[i],u[j]),f.mul(u[i],ut[j])) for j in range(3)] for i in range(3)]
    cubic=[[f.add(*(f.diff(f.mul(u[k],stress[i][j]),k) for k in range(3)))
            for j in range(3)] for i in range(3)]
    pressure_flux=[[f.add(f.diff(f.mul(p,u[j]),i),f.diff(f.mul(p,u[i]),j))
                    for j in range(3)] for i in range(3)]
    redistribution=[[f.mul(p,f.add(B[i][j],B[j][i])) for j in range(3)] for i in range(3)]
    loss=[[f.scale(2*nu,f.add(*(f.mul(B[i][k],B[j][k]) for k in range(3))))
           for j in range(3)] for i in range(3)]
    expected=[[f.add(f.scale(-1,cubic[i][j]),f.scale(-1,pressure_flux[i][j]),
                     redistribution[i][j],f.scale(nu,f.lap(stress[i][j])),f.scale(-1,loss[i][j]))
               for j in range(3)] for i in range(3)]
    f.same_matrices(stress_t,expected,'full stress balance')
    f.equal(f.trace(redistribution),{},'pressure redistributes without trace work')
    if not any(redistribution[i][j] for i in range(3) for j in range(3)):
        raise ArithmeticError('nonzero anisotropic pressure redistribution required')
    p_t=f.tensor_pressure(stress_t)
    pp_flux=f.tensor_pressure(pressure_flux)
    f.equal(pp_flux,f.scale(-2,f.adv(u,p)),'full pressure-flux projection')
    material_p=f.add(p_t,f.adv(u,p),f.scale(-nu,f.lap(p)))
    wanted=f.add(f.scale(-1,f.tensor_pressure(cubic)),f.scale(3,f.adv(u,p)),
                 f.tensor_pressure(redistribution),f.scale(-1,f.tensor_pressure(loss)))
    f.equal(material_p,wanted,'full material pressure history after flux split')
    # A positive anisotropic observer with 0<=M<=I, changing in time:
    # M(t,x)=chi(x,z)e(t)e(t)^T,
    # chi=(3+cos(2z)+cos(2x+2z))/5, so 1/5<=chi<=1,
    # e(t)=(sin t,0,cos t). At t=0 retain its rotation, advection,
    # diffusion and pressure boundary flux independently.
    ez=(0,0,2);mz=(0,0,-2)
    chi={f.ORIGIN:f.QQ_I(3)/5,ez:f.QQ_I(1)/10,mz:f.QQ_I(1)/10,
         (2,0,2):f.QQ_I(1)/10,(-2,0,-2):f.QQ_I(1)/10}
    chigrad=f.grad(chi)
    component=f.mul(chi,stress[2][2])
    component_t=f.add(f.mul(chi,stress_t[2][2]),f.scale(2,f.mul(chi,stress[0][2])))
    observed_work=f.mul(chi,redistribution[2][2])
    observed_loss=f.mul(chi,loss[2][2])
    rotation=f.scale(2,f.mul(chi,stress[0][2]))
    transport=f.mul(f.adv(u,chi),stress[2][2])
    diffusion=f.scale(nu,f.mul(f.lap(chi),stress[2][2]))
    pressure_boundary=f.scale(2,f.mul(p,f.mul(u[2],chigrad[2])))
    observer=f.add(rotation,transport,diffusion,pressure_boundary)
    avg=lambda a:a.get(f.ORIGIN,f.ZERO)
    if avg(component_t)!=avg(f.add(observed_work,observer,f.scale(-1,observed_loss))):
        raise ArithmeticError('complete moving positive observer balance')
    if not avg(pressure_boundary):raise ArithmeticError('pressure boundary term must be active')
    if nu and not avg(diffusion):raise ArithmeticError('observer diffusion must be active')
    for i in range(3):
        if avg(stress_t[i][i])!=avg(f.add(redistribution[i][i],f.scale(-1,loss[i][i]))):
            raise ArithmeticError('fixed global direction balance')
    if avg(f.trace(stress_t))!=-avg(f.trace(loss)):
        raise ArithmeticError('actual kinetic balance')
    # An external force can do zero total kinetic work while doing
    # nonzero work on this localized directional observer. This checks
    # the force term in the identity; it is not a singularity construction.
    force=f.curl(u)
    if avg(f.dot(u,force)):raise ArithmeticError('diagnostic force must have zero total work')
    force_work=f.scale(2,f.mul(chi,f.mul(u[2],force[2])))
    if not avg(force_work):raise ArithmeticError('localized force work must be active')
    # Changing u to -u keeps the pressure and kinetic energy, but reverses
    # the pressure redistribution. This is a parity check, not a claim
    # of an energy-only impossibility over an actual time interval.
    v=[f.scale(-1,a) for a in u];bb=f.jac(v)
    pv=f.green(f.trace(f.matmul(bb,bb)))
    f.equal(pv,p,'pressure is unchanged under velocity sign reversal')
    for i in range(3):
        for j in range(3):
            f.equal(f.mul(pv,f.add(bb[i][j],bb[j][i])),f.scale(-1,redistribution[i][j]),
                    'signed anisotropic redistribution reverses')
    return {'nu':str(nu),'velocity_modes':len(set().union(*(set(a) for a in u))),
            'redistribution_modes':len(set().union(*(set(a) for row in redistribution for a in row))),
            'trace_work':'zero','anisotropic_work':'nonzero, changes sign with u',
            'moving_observer':{name:str(avg(a)) for name,a in
                [('component',component),('rate',component_t),('pressure_work',observed_work),
                 ('loss',observed_loss),('rotation',rotation),('transport',transport),
                 ('diffusion',diffusion),('pressure_boundary',pressure_boundary),
                 ('diagnostic_force_work',force_work)]}}


def check_fifth_kernel():
    x,y,z,a,b=s.symbols('x y z a b',real=True)
    r=s.sqrt(x*x+y*y+z*z)
    velocity=s.Matrix([a,0,b]);e=s.Matrix([0,0,1]);n=s.Matrix([x,y,z])/r
    en=e.dot(n);vn=velocity.dot(n);ev=e.dot(velocity)
    ee=e.dot(e);vv=velocity.dot(velocity)
    numerator=(-945*en**2*vn**3
               +105*(ee*vn**3+6*en*ev*vn**2+3*en**2*vv*vn)
               -15*(6*ev*vv*en+3*ee*vv*vn+6*ev**2*vn))
    direct=s.diff(1/r,z,2)
    for _ in range(3):direct=a*s.diff(direct,x)+b*s.diff(direct,z)
    zero(direct-numerator/r**6,'fifth directional Newtonian derivative')
    zero(numerator.subs({x:0,y:0,z:1,a:0,b:1})+120,'radial fifth derivative')
    # Each scalar product is bounded by the relevant norm. The following
    # conservative coefficient therefore bounds |numerator| by 2220|e|^2|v|^3.
    total=945+105*(1+6+3)+15*(6+3+6)
    if total!=2220:raise ArithmeticError('fifth-kernel triangle coefficient')
    # With 0<=chi<=1 and |chi'|<=2, chi(r/R) adds at most
    # (2/R)|v| times the earlier fourth-kernel bound 6|e|^2|v|^2/(pi r^5).
    zero(s.Rational(total,4)+12-567,'smooth cutoff transport coefficient')
    return {'angular_coefficient':total,'smooth_cutoff_bound':'567/(pi R^6)',
            'cutoff':'chi=0 on [0,1], chi=1 on [2,infinity), 0<=chi<=1, |chi_prime|<=2',
            'scope':'unit observation direction; derivative identifies the spatial transport kernel'}


if __name__=='__main__':
    print(json.dumps({'status':'all exact checks passed',
                      'stress':[check_stress(f.QQ_I(0)),check_stress(f.QQ_I(2)/7)],
                      'fifth_kernel':check_fifth_kernel(),
                      'scope':'exact NS stress identity and separated cubic flux; '
                              'no moving-region or arbitrary-data regularity bound'},indent=2))
