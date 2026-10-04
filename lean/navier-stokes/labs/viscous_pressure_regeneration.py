#!/usr/bin/env python3
"""Unequal viscous parent decay defeats joint-pressure source absorption.

Exact checks retain every canonical-pressure mode and the complete initial
NS tangent. The asymptotic and actual-interval arguments are analytic in
README.md. Optional quadrature is diagnostic, not a rigorous enclosure.
"""

import argparse
import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
from rotational_curl_reserve import require, zero


def cosine(k):
    return {k: f.QQ_I(1)/2, tuple(-x for x in k): f.QQ_I(1)/2}


def sine(k):
    return {k: -f.II/2, tuple(-x for x in k): f.II/2}


def datum(n, A=3, B=2):
    sx, cx = sine((n, 0, 0)), cosine((n, 0, 0))
    sx2, cx2 = sine((2*n, 0, 0)), cosine((2*n, 0, 0))
    sy, cy = sine((0, 1, 0)), cosine((0, 1, 0))
    return [f.add(f.scale(f.QQ_I(A)/n, f.mul(sx, cy)),
                  f.scale(-f.QQ_I(B)/(2*n), f.mul(sx2, sy))),
            f.add(f.scale(-A, f.mul(cx, sy)), f.scale(-B, f.mul(cx2, cy))), {}]


def pressure_formula(n, A=3, B=2):
    return f.add(f.scale(f.QQ_I(A*A)/(4*n*n), cosine((2*n, 0, 0))),
                 f.scale(f.QQ_I(B*B)/(16*n*n), cosine((4*n, 0, 0))),
                 f.scale(f.QQ_I(A*A-B*B)/4, cosine((0, 2, 0))),
                 f.scale(-f.QQ_I(9*A*B)/(4*(n*n+4)),
                         f.mul(cosine((n, 0, 0)), sine((0, 2, 0)))),
                 f.scale(f.QQ_I(A*B)/(4*(9*n*n+4)),
                         f.mul(cosine((3*n, 0, 0)), sine((0, 2, 0)))))


def symbolic_formulas():
    X, y = s.symbols('X y', real=True)
    n, nu = s.symbols('n nu', positive=True)
    A, B = s.symbols('A B', real=True)
    u = s.Matrix([A*s.sin(X)*s.cos(y)/n-B*s.sin(2*X)*s.sin(y)/(2*n),
                  -A*s.cos(X)*s.sin(y)-B*s.cos(2*X)*s.cos(y)])
    grad = lambda v: s.Matrix([n*s.diff(v, X), s.diff(v, y)])
    lap = lambda v: n*n*s.diff(v, X, 2)+s.diff(v, y, 2)
    J = s.Matrix(2, 2, lambda i, j: grad(u[i])[j])
    p = (A*A*s.cos(2*X)/(4*n*n)+B*B*s.cos(4*X)/(16*n*n)
         +(A*A-B*B)*s.cos(2*y)/4
         +A*B*s.sin(2*y)*(-9*s.cos(X)/(n*n+4)+s.cos(3*X)/(9*n*n+4))/4)
    # Clear the positive frequency denominators, then reduce polynomially
    # using the two unit-circle identities. No heuristic factor search.
    residual=s.together(s.expand_trig(-lap(p)-s.trace(J*J))).as_numer_denom()[0]
    sx,cx,sy,cy=s.symbols('sx cx sy cy')
    residual=s.expand(residual.xreplace({s.sin(X):sx,s.cos(X):cx,s.sin(y):sy,s.cos(y):cy}))
    residual=s.Poly(residual,cx).rem(s.Poly(cx*cx+sx*sx-1,cx)).as_expr()
    residual=s.Poly(residual,cy).rem(s.Poly(cy*cy+sy*sy-1,cy)).as_expr()
    require(s.expand(residual)==0,'canonical pressure formula for every n, A and B')
    rates = [-nu*(n*n+1)*A, -nu*(4*n*n+1)*B]
    for v in u:
        zero(s.diff(v, A)*rates[0]+s.diff(v, B)*rates[1]-nu*lap(v),
             'complete viscous tangent has the two claimed rates')
    low = (A*A-B*B)/4
    low_rate = s.diff(low, A)*rates[0]+s.diff(low, B)*rates[1]
    zero(low_rate.subs({A:3, B:2})-nu*(7*n*n-5)/2,
         'opposing parents produce increasing low pressure under viscosity')
    energy = (A*A+B*B)/4+A*A/(4*n*n)+B*B/(16*n*n)
    enstrophy = (n*n+1)*A*A*(1+1/(n*n))/4+(4*n*n+1)*B*B*(1+1/(4*n*n))/4
    zero(s.diff(energy, A)*rates[0]+s.diff(energy, B)*rates[1]+2*nu*enstrophy,
         'original kinetic energy decreases')
    return {'pressure':str(p), 'low_pressure_rate':str(s.factor(low_rate.subs({A:3,B:2}))),
            'energy':str(s.factor(energy.subs({A:3,B:2}))),
            'enstrophy':str(s.factor(enstrophy.subs({A:3,B:2})))}


def exact_tangents():
    rows = []
    for n in (1, 2, 3, 7, 16, 32):
        u = datum(n)
        p = f.tensor_pressure(f.tensor(u, u))
        f.equal(f.trace(f.jac(u)), {}, 'divergence-free datum')
        f.equal(p, pressure_formula(n), 'independent full Fourier pressure')
        require(all(k[1] % 2 for v in u for k in v), 'velocity is y-antiperiodic')
        require(all(k[1] % 2 == 0 for k in p), 'pressure is y-periodic by pi')
        for nu in (f.QQ_I(1), f.QQ_I(2)/7):
            visc = [f.scale(nu, f.lap(v)) for v in u]
            euler = [f.scale(-1, f.add(f.adv(u, u[j]), f.diff(p, j))) for j in range(3)]
            G = [[f.add(*(f.mul(f.diff(u[i], k), f.diff(u[j], k)) for k in range(3)))
                  for j in range(3)] for i in range(3)]
            tangent_tensor = lambda v: [[f.add(f.mul(v[i], u[j]), f.mul(u[i], v[j]))
                                         for j in range(3)] for i in range(3)]
            pvis = f.tensor_pressure(tangent_tensor(visc))
            peuler = f.tensor_pressure(tangent_tensor(euler))
            f.equal(pvis, f.add(f.scale(nu, f.lap(p)),
                               f.scale(-2*nu, f.tensor_pressure(G))),
                    'viscous pressure source includes all derivative parents')
            f.equal(f.trace(f.jac(euler)), {}, 'Euler tangent is solenoidal')
            require(all(k[1] % 2 == 0 for v in euler for k in v), 'Euler velocity tangent is even')
            require(all(k[1] % 2 for k in peuler), 'Euler pressure tangent is odd')
            E = f.dot(u,u).get(f.ORIGIN, f.ZERO)
            Z = sum((f.dot(f.grad(v),f.grad(v)).get(f.ORIGIN,f.ZERO) for v in u), f.ZERO)
            require(E == f.QQ_I(13)/4+f.QQ_I(5)/(2*n*n), 'full kinetic energy')
            require(Z == f.QQ_I(25*n*n)/4+f.QQ_I(13)/2+f.QQ_I(5)/(2*n*n), 'full enstrophy')
            require(2*f.dot(u,visc).get(f.ORIGIN,f.ZERO) == -2*nu*Z,
                    'actual initial energy law')
            rows.append({'n':n,'nu':str(nu),'pressure_modes':len(p),
                         'viscous_pressure_modes':len(pvis),'Euler_pressure_modes':len(peuler)})
    return rows


def limiting_constants():
    kappa = s.symbols('kappa',positive=True)
    b = 5*kappa/8
    mean_sin3 = s.Rational(4,3)/s.pi
    mean_sincos2 = s.Rational(2,3)/s.pi
    theta=s.symbols('theta',real=True)
    zero(2*s.integrate(s.sin(theta)**3,(theta,0,s.pi/2))/s.pi-mean_sin3,
         'exact cubic sine mean')
    zero(2*s.integrate(s.sin(theta)*s.cos(theta)**2,(theta,0,s.pi/2))/s.pi-mean_sincos2,
         'exact weighted gradient mean')
    stock = b**3*mean_sin3
    diffusion = 24*b**3*mean_sincos2
    source = s.Rational(42,5)*stock
    zero(source/diffusion-s.Rational(7,10), 'unbounded source/diffusion ratio constant')
    # Bounds obtained from the complete finite pressure formula, h(d)<=1/d.
    beta_x = s.Rational(9,8)+s.Rational(1,16)+s.Rational(27,2)+s.Rational(1,18)
    beta_y = 27+s.Rational(1,27)
    hxx = s.Rational(9,4)+s.Rational(1,4)+s.Rational(27,2)+s.Rational(1,6)
    hxy = 27+s.Rational(1,9)
    hyy = 54+s.Rational(2,27)
    lap_x = s.Rational(9,2)+1+s.Rational(27,2)+s.Rational(1,2)
    lap_y = 27+s.Rational(1,3)
    require(beta_x+beta_y < 43, 'uniform beta remainder constant')
    require(hxx+2*hxy+hyy < 125, 'uniform gradient beta remainder constant')
    require(lap_x+lap_y < 47, 'uniform Laplacian beta remainder constant')
    require(10*43+47 < 500, 'uniform scaled source remainder constant')
    return {'kappa':'1-exp(-4L^2)', 'limiting_beta':'(0,-5kappa sin(2y)/8,0)',
            'limiting_Svis_over_nu_n2':'(0,-7kappa sin(2y)/4,0)',
            'pressure_cubic_stock':str(stock),'pressure_cubic_diffusion_over_nu':str(diffusion),
            'source_over_nu_n2':str(source),
            'ratio':'lim_(n->infinity) n^(-2) lim_(c->infinity) F_vis(c u_n)/D(c u_n)=7/10',
            'remainders':'||beta-beta_bar||inf<=43/n^3; ||grad(beta-beta_bar)||inf<=125/n^2; ||Delta(beta-beta_bar)||inf<=47/n',
            'source_remainder':'||S_vis/(nu n^2)-s_bar||inf<=5/(4n^2)+500/n^3',
            'interpretation':'No finite universal multiple of D absorbs this viscous source on all actual data. The smooth actual evolution preserves each strict initial gap for a positive interval.',
            'OPEN':'A finite allowance depending on the full original datum for complete generated-pressure histories remains open.'}


def explicit_gap():
    # L=nu=1. Elementary exp(4)>16 and pi<4 give kappa>15/16.
    # All quantities below are rational bounds, not quadrature values.
    n,c=16,1000
    b=s.Rational(5,8)
    eps=s.Rational(43,n**3)
    eps_grad=s.Rational(125,n*n)
    eps_source=s.Rational(5,4*n*n)+s.Rational(500,n**3)
    eta=s.Rational(6,c)  # ||u_n||inf/(sqrt(2)c) <= 6/c.
    M=b+eps
    base=s.Rational(175,256)*s.Rational(15,16)**3
    source_error=3*(2*M*eps*s.Rational(7,4)+M*M*eps_source)
    finite_amplitude_error=3*eta*M*(s.Rational(7,4)+eps_source)
    lower=n*n*(base-source_error-finite_amplitude_error)
    upper=12*(M+eta)*(s.Rational(8*n,c)**2+(2*b+eps_grad)**2)
    require(25+s.Rational(16,n*n)<36,'uniform velocity bound on explicit datum')
    require(49*n*n+50+s.Rational(16,n*n)<64*n*n,'uniform gradient bound on explicit datum')
    require(lower>81,'explicit source lower bound')
    require(upper<24,'complete diffusion upper bound')
    require(lower-3*upper>11,'explicit strict source/diffusion margin')
    return {'n':n,'c':c,'nu':1,'L':1,'normalization':'nu (sqrt(2)/nu)^3 c^6',
            'F_vis_lower':str(lower),'D_upper':str(upper),'F_vis_minus_3D_lower':str(lower-3*upper),
            'bounds':'F_vis>81 times normalization, D<24 times normalization, F_vis-3D>11 times normalization',
            'physical_consequence':'At t=0 the Euler entropy derivative and cross diffusion vanish by the exact y-shift symmetry. Thus the complete NS entropy derivative is positive although kinetic energy decreases.',
            'history_consequence':'Continuity on the actual smooth NS prefix preserves F_vis>3D and positive entropy growth for some positive interval; no interval length or indefinite renewal is claimed.'}


def quadrature(n, c, grid):
    import numpy as np
    X,y=np.meshgrid(2*np.pi*np.arange(grid)/grid,2*np.pi*np.arange(grid)/grid,indexing='ij')
    u=datum(n); p=f.tensor_pressure(f.tensor(u,u))
    vis=[f.lap(v) for v in u]
    pvis=f.tensor_pressure([[f.add(f.mul(vis[i],u[j]),f.mul(u[i],vis[j]))
                            for j in range(3)] for i in range(3)])
    def evaluate(field, derivative=(), primitive=False):
        out=np.zeros((grid,grid),dtype=complex)
        for k,a in field.items():
            require(k[0] % n == 0 and k[2] == 0,'rescaled Fourier grid retains all modes')
            coefficient=complex(float(a.x),float(a.y))
            for j in derivative: coefficient*=1j*k[j]
            d=sum(v*v for v in k)
            if primitive: coefficient*= -np.expm1(-d)/d if d else 0
            out+=coefficient*np.exp(1j*((k[0]//n)*X+k[1]*y))
        require(np.max(np.abs(out.imag))<1e-10*max(1,np.max(np.abs(out.real))), 'real Fourier evaluation')
        return out.real
    uu=c*np.array([evaluate(v) for v in u])
    beta=c*c*np.array([evaluate(p,(j,),True) for j in range(3)])
    bvis=c*c*np.array([evaluate(pvis,(j,),True) for j in range(3)])
    blap=c*c*np.array([evaluate(f.lap(p),(j,),True) for j in range(3)])
    yy=np.sqrt(2)*beta; zz=np.concatenate((uu,yy)); r=np.sqrt(np.sum(zz*zz,axis=0))
    inv=np.divide(1,r,out=np.zeros_like(r),where=r>0)
    D=Ddiag=0.0
    for j in range(3):
        du=c*np.array([evaluate(v,(j,)) for v in u])
        db=c*c*np.array([evaluate(p,(i,j),True) for i in range(3)])
        dz=np.concatenate((du,np.sqrt(2)*db))
        v=dz.copy(); v[:3]+=dz[3:]/np.sqrt(2)
        zd=np.sum(zz*dz,axis=0)
        D+=float(np.mean(3*r*np.sum(dz*v,axis=0)+3*inv*zd*np.sum(zz*v,axis=0)))
        Ddiag+=float(np.mean(3*r*np.sum(dz*dz,axis=0)+3*inv*zd*zd))
    Fvis=float(3*np.sqrt(2)*np.mean(r*np.sum(yy*(bvis-blap),axis=0)))
    Juvis=float(3*np.mean(r*(np.sum(uu*c*np.array([evaluate(v) for v in vis]),axis=0)
                              +np.sqrt(2)*np.sum(yy*bvis,axis=0))))
    scale=max(abs(D),abs(Fvis),abs(Juvis),1)
    require(abs(D-Ddiag)/scale<1e-11,'cross diffusion pairs to zero by symmetry')
    require(abs(Fvis-D-Juvis)/scale<2e-5,'quadrature agrees with viscous entropy balance')
    return {'n':n,'c':c,'grid':grid,'nu':1,'L':1,'F_vis':Fvis,'D':D,
            'ratio':Fvis/D,'ratio_over_n2':Fvis/D/n**2,'J_prime':Juvis,
            'balance_relative_error':abs(Fvis-D-Juvis)/scale,
            'status':'numerical diagnostic, not an enclosure'}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--quadrature',action='store_true')
    parser.add_argument('--grid',type=int,default=256)
    args=parser.parse_args()
    result={'formulas':symbolic_formulas(),'exact_tangents':exact_tangents(),
            'limits':limiting_constants(),'explicit_gap':explicit_gap(),
            'certification':'Exact symbolic/Fourier checks; asymptotics and actual NS interval transfer are analytic, not Lean-certified.',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if args.quadrature:
        result['quadrature']=[quadrature(n,1000,args.grid) for n in (2,4,8,16,32)]
    print(json.dumps(result,indent=2),flush=True)
