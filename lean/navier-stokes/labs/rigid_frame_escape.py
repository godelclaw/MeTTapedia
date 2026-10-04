#!/usr/bin/env python3
"""Exact rigid-frame checks for the generated-packet escape estimate.

The continuous whole-space slice, its nonsingular Gram matrix and the
uniform actual-flow residence bound are proved analytically in README.md.
The finite computations certify the carrier stabilizer and check full
NS equivariance and every rigid coordinate term, not an unforced blowup.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
from generated_fourth_moment import target_field, fourth_work, vector_pair
from cyclic_pressure_history import velocity_time_jets
from heat_remainder_pressure import require
from two_observer_bellman import source_hashes


def zero(expression, label):
    require(s.expand(expression) == 0, label)


def matrix_strings(matrix):
    return [[str(x) for x in row] for row in matrix.tolist()]


def carrier_stabilizer(u):
    modes = sorted(set().union(*u))
    first = s.Matrix(modes[0])
    second = next(s.Matrix(k) for k in modes if first.cross(s.Matrix(k)) != s.zeros(3,1))
    basis = s.Matrix.hstack(first,second,first.cross(second))
    require(basis.det() != 0, 'Two noncollinear carriers determine a proper rotation')
    gram = first.dot(first), second.dot(second), first.dot(second)
    rows, accepted = [], []
    for k in modes:
        for ell in modes:
            a,b = s.Matrix(k),s.Matrix(ell)
            if (a.dot(a),b.dot(b),a.dot(b)) != gram:
                continue
            rotation = s.Matrix.hstack(a,b,a.cross(b))*basis.inv()
            require(rotation.T*rotation == s.eye(3) and rotation.det() == 1,
                    'Each Gram-compatible image pair gives exactly one proper rotation')
            bad = next((q for q in modes if tuple(rotation*s.Matrix(q)) not in modes), None)
            rows.append(dict(first_image=list(k), second_image=list(ell),
                             rotation=matrix_strings(rotation), rejected_carrier=list(bad) if bad else None))
            if bad is None:
                accepted.append(rotation)
    require(len(rows) == 6 and accepted == [s.eye(3)],
            'Exhaustive carrier permutations leave only the identity rotation')
    return dict(carriers=[list(k) for k in modes], first=list(map(int,first)), second=list(map(int,second)),
                candidates=rows, stabilizer_order=1)


def rotate(u, rotation):
    result=[{}, {}, {}]
    for k in set().union(*u):
        target=tuple(Q(x) for x in rotation*s.Matrix(k))
        for i in range(3):
            value=sum((Q(rotation[i,j])*u[j].get(k,f.ZERO) for j in range(3)),f.ZERO)
            if value:
                result[i][target]=value
    return result


def translate_quarters(u, direction):
    """Translation by pi*direction/2, before any rational rotation."""
    result=[]
    for component in u:
        row={}
        for k,value in component.items():
            exponent=sum(k[j]*direction[j] for j in range(3))
            require(int(exponent) == exponent, 'The exact phase has an integral quarter-turn exponent')
            row[k]=value*(-f.II)**(int(exponent)%4)
        result.append(f.clean(row))
    return result


def same(a,b,label):
    for x,y in zip(a,b):
        f.equal(x,y,label)


def equivariance(u):
    rz=s.Matrix([[s.Rational(3,5),-s.Rational(4,5),0],
                 [s.Rational(4,5),s.Rational(3,5),0],[0,0,1]])
    rx=s.Matrix([[1,0,0],[0,s.Rational(5,13),-s.Rational(12,13)],
                 [0,s.Rational(12,13),s.Rational(5,13)]])
    require(rx*rz != rz*rx, 'The two tested spatial rotations do not commute')
    source=velocity_time_jets(u,Q(0),1)[0][1]
    observations=fourth_work(u)
    e=vector_pair(u,u)
    rows=[]
    for rotation,direction in [(rz,(1,2,3)),(rx,(3,-1,2)),(rx*rz,(-1,1,2))]:
        require(rotation.T*rotation == s.eye(3) and rotation.det() == 1,
                'The coordinate map is a proper Euclidean isometry')
        moved=rotate(translate_quarters(u,direction),rotation)
        moved_source=velocity_time_jets(moved,Q(0),1)[0][1]
        expected=rotate(translate_quarters(source,direction),rotation)
        same(moved_source,expected,'All generated Leray outputs transform with the same frame and phases')
        same([f.lap(a) for a in moved],rotate(translate_quarters([f.lap(a) for a in u],direction),rotation),
             'Viscosity transforms with the same frame')
        require(fourth_work(moved) == observations and vector_pair(moved,moved) == e,
                'All scalar physical observations retain their exact values')
        for nu in (Q(1),Q(2,7)):
            actual=velocity_time_jets(moved,nu,1)[0][1]
            expected=rotate(translate_quarters(velocity_time_jets(u,nu,1)[0][1],direction),rotation)
            same(actual,expected,'The entire positive-viscosity tangent is equivariant')
        missing=tuple(Q(x) for x in rotation*s.Matrix([-1,-2,0]))
        require(missing not in set().union(*moved) and missing in set().union(*moved_source),
                'The produced mode stays outside the input support after frame transport')
        norm=sum((s.conjugate(f.QQ_I.to_sympy(a.get(missing,f.ZERO)))*
                  f.QQ_I.to_sympy(a.get(missing,f.ZERO)) for a in moved_source),s.Integer(0))
        zero(norm-s.Rational(1,5120),'The full generated coefficient keeps its exact nonzero norm')
        rows.append(dict(rotation=matrix_strings(rotation), translation_quarters=list(direction),
                         missing_mode=list(map(str,missing)), missing_coefficient_squared=str(norm)))
    same(rotate(rotate(u,rz),rx),rotate(u,rx*rz),
         'Composition transports the same interior Fourier witness')
    return rows


def coordinate_identities():
    x=s.Matrix(s.symbols('x y z',real=True))
    p,q,r=x
    potential=s.Matrix([p*p*q+q*r**3,q*q*r+r*p**3,r*r*p+p*q**3])
    def curl(v):
        return s.Matrix([s.diff(v[2],q)-s.diff(v[1],r),
                         s.diff(v[0],r)-s.diff(v[2],p),
                         s.diff(v[1],p)-s.diff(v[0],q)])
    def lap(v):
        return v.applyfunc(lambda a:sum(s.diff(a,b,2) for b in x))
    def div(v):
        return sum(s.diff(v[j],x[j]) for j in range(3))
    w=curl(potential)
    test=s.Matrix([p*q+r*r,q*r+p*p,r*p+q*q])
    om=s.Matrix(s.symbols('omega0:3',real=True))
    omega=s.Matrix([[0,-om[2],om[1]],[om[2],0,-om[0]],[-om[1],om[0],0]])
    def angular(v):
        return omega*v-v.jacobian(x)*omega*x
    zero(div(w),'The independent coordinate fixture is incompressible')
    zero(div(angular(w)),'Rigid vector rotation preserves incompressibility')
    for value in lap(angular(w))-angular(lap(w)):
        zero(value,'The complete rotation generator commutes with viscosity')
    zero(test.dot(angular(w))+angular(test).dot(w)+div(omega*x*test.dot(w)),
         'The angular generator is skew-adjoint after spatial integration')
    magnitude=w.dot(w)
    zero(magnitude*w.dot(angular(w))+div(omega*x*magnitude**2)/4,
         'Rigid rotation contributes zero integrated fourth-moment work')
    for j in range(3):
        zero(test.dot(w.diff(x[j]))+test.diff(x[j]).dot(w)-s.diff(test.dot(w),x[j]),
             'The translation generator is skew-adjoint after integration')
        zero(magnitude*w.dot(w.diff(x[j]))-s.diff(magnitude**2,x[j])/4,
             'Rigid translation contributes zero integrated fourth-moment work')

    center=s.Matrix(s.symbols('center0:3',real=True))
    speed=s.Matrix(s.symbols('speed0:3',real=True))
    nonlinear=s.Matrix(s.symbols('nonlinear0:3',real=True))
    eps,A,L=s.symbols('epsilon A L',real=True)
    laboratory=nonlinear+eps*lap(w)-A*w-L*w.jacobian(x)*(x+center)
    differentiated=laboratory-omega*w+w.jacobian(x)*(omega*x+speed)
    body=nonlinear+eps*lap(w)-A*w-L*w.jacobian(x)*x
    expected=body+w.jacobian(x)*(speed-L*center)-angular(w)
    for value in differentiated-expected:
        zero(value,'The moving-frame equation retains center/dilation and angular terms')
    return dict(frame_translation='R^T (center_theta - L center)',
                frame_rotation='-omega, where R^T R_theta x = omega cross x',
                slice_equation='M(w)c=-h(w,epsilon)',
                skew_adjoint_generators=6,
                scope='Polynomial differential identities check coordinate signs; no polynomial fixture is a finite-energy fluid solution.')


def checks():
    u=target_field()
    result=dict(carrier=carrier_stabilizer(u), equivariance=equivariance(u),
                coordinates=coordinate_identities(),
                scope='The whole-space localized-seed Gram bound, nearest-orbit slice and actual orbit residence theorem are analytic. No new Lean certificate or arbitrary-history payment is claimed.')
    hashes=source_hashes()
    path=Path(__file__).resolve()
    hashes[path.name]=hashlib.sha256(path.read_bytes()).hexdigest()
    result['source_sha256']=dict(sorted(hashes.items()))
    return result


if __name__=='__main__':
    print(json.dumps(checks(),indent=2))
