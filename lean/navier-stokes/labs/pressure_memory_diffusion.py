#!/usr/bin/env python3
"""Exact spatial pressure payment and joint memory-reaction checks.

All Fourier outputs are retained on the 2*pi torus. The memory source
G=grad(u) grad(u)^T is C_t/(2*nu) at C=0 along actual unforced NS
with positive viscosity.
Using G as a tensor tests spatial identities; it does not assert that
C=G occurs at a finite time. The spatial whole-space pressure identities
are also certified in WholeSpacePressureDiffusion.lean.

The joint receiver test uses the leading polynomial coefficients of the
completed observable, with an unselected weight. Its boost-dependent
fragment is exactly compensated in the full pressure production.
It is not a counterexample to a finite datum-fixed excess allowance.
"""

import json
import pressure_history_source as f


def transpose(a):
    return [list(row) for row in zip(*a)]


def matrix_add(*arrays):
    return [[f.add(*(a[i][j] for a in arrays)) for j in range(3)] for i in range(3)]


def matrix_scale(c, a):
    return [[f.scale(c, a[i][j]) for j in range(3)] for i in range(3)]


def matrix_scalar(c, a):
    return [[f.mul(c, a[i][j]) for j in range(3)] for i in range(3)]


def pair(a, b):
    return f.add(*(f.mul(a[i][j], b[i][j]) for i in range(3) for j in range(3)))


def matrix_diff(a, j):
    return [[f.diff(q, j) for q in row] for row in a]


def matrix_adv(u, a):
    return [[f.adv(u, q) for q in row] for row in a]


def observe(a):
    return f.hess(f.tensor_pressure(a))


def symmetric_product(u, v):
    return matrix_add(f.tensor(u, v), f.tensor(v, u))


def divergence(u):
    return f.add(*(f.diff(u[j], j) for j in range(3)))


def tensor_divergence(a):
    return [f.add(*(f.diff(a[i][j], j) for j in range(3))) for i in range(3)]


def mean(a):
    value = a.get(f.ORIGIN, f.ZERO)
    if value.y:
        raise ArithmeticError('nonreal spatial mean')
    return value.x


def mode_norm_sq(a, k):
    values = [a[i][j].get(k, f.ZERO) for i in range(3) for j in range(3)]
    return sum((v.x*v.x+v.y*v.y for v in values), f.ZERO.x)


def spectral_memory_bound(PC, mass, memory_gradient, diffusion):
    modes = set().union(*(q.keys() for row in PC for q in row))
    total = sum((mode_norm_sq(PC, k) for k in modes), f.ZERO.x)
    if total != mean(pair(PC, PC)):
        raise ArithmeticError('pressure-memory Parseval identity')
    for k in modes:
        k2 = sum(x*x for x in k)
        if mode_norm_sq(PC, k) > k2*k2*mass*mass:
            raise ArithmeticError(('positive memory mass controls low mode', k))
    checks = []
    for cutoff in (1, 2, 3):
        k2cut = cutoff*cutoff
        lattice_cost = sum((i*i+j*j+l*l)**2
                           for i in range(-cutoff, cutoff+1)
                           for j in range(-cutoff, cutoff+1)
                           for l in range(-cutoff, cutoff+1)
                           if 0 < i*i+j*j+l*l <= k2cut)
        low = sum((mode_norm_sq(PC, k) for k in modes
                   if sum(x*x for x in k) <= k2cut), f.ZERO.x)
        high = total-low
        if low > lattice_cost*mass*mass or k2cut*high > memory_gradient:
            raise ArithmeticError(('memory-pressure low/high split', cutoff))
        if k2cut*total > k2cut*lattice_cost*mass*mass + f.QQ_I(33).x/56*diffusion:
            raise ArithmeticError(('mass and strict diffusion payment', cutoff))
        checks.append({'cutoff': cutoff, 'low_pressure_square': str(low),
                       'high_pressure_square': str(high), 'lattice_cost': lattice_cost})
    return checks


def weighted_pressure_flux(P, p):
    source_gradient = f.grad(f.lap(p))
    pressure_gradient_square = f.add(*(pair(matrix_diff(P, k), matrix_diff(P, k))
                                       for k in range(3)))
    source_gradient_square = f.dot(source_gradient, source_gradient)
    flux = [f.add(v, f.scale(-f.QQ_I(1)/2, g)) for v, g in
            zip(f.matvec(P, source_gradient), f.grad(pair(P, P)))]
    residual = f.add(pressure_gradient_square, f.scale(-1, source_gradient_square))
    f.equal(residual, f.scale(-1, divergence(flux)), 'physical pressure localization flux')
    mode = next((k for k in sorted(residual) if k != f.ORIGIN), None)
    if mode is None:
        raise ArithmeticError('weighted pressure fixture needs a nonzero localization defect')
    coefficient = residual[mode]
    opposite = tuple(-x for x in mode)
    if coefficient.x:
        a = {f.ORIGIN: f.QQ_I.one, mode: f.QQ_I(1)/4, opposite: f.QQ_I(1)/4}
        weight = '1+cos(k.x)/2'
    else:
        a = {f.ORIGIN: f.QQ_I.one, mode: -f.II/4, opposite: f.II/4}
        weight = '1+sin(k.x)/2'
    direct = mean(f.mul(a, residual))
    boundary = mean(f.dot(f.grad(a), flux))
    if direct != boundary or not direct:
        raise ArithmeticError('nonzero weighted pressure boundary term')
    return {'weight': weight, 'mode': list(mode), 'localization_defect': str(direct),
            'scope': 'smooth positive test weight; not the actual excess selector'}


def pressure_commutator(u, a):
    return matrix_add(matrix_adv(u, observe(a)),
                      matrix_scale(-1, observe(matrix_adv(u, a))))


def check_pressure(u):
    f.equal(divergence(u), {}, 'solenoidal velocity')
    B = f.jac(u)
    r = pair(B, B)
    source = f.trace(f.matmul(B, B))
    p = f.green(source)
    f.equal(p, f.tensor_pressure(f.tensor(u, u)), 'canonical pressure source')
    P = f.hess(p)
    if mean(pair(P, P)) != mean(f.mul(source, source)):
        raise ArithmeticError('pressure Hessian L2 identity')
    if mean(pair(P, P)) > mean(f.mul(r, r)):
        raise ArithmeticError('pressure Hessian quartic bound')

    # G is the actual generated memory source, rather than a freely chosen
    # pressure matrix. The integrated inequality applies to any observed
    # smooth pressure gradient; no memory trajectory is assumed here.
    G = f.matmul(B, transpose(B))
    PC = observe(G)
    observed = matrix_add(P, PC)
    parent = f.ZERO.x
    actual_pressure = f.ZERO.x
    memory = f.ZERO.x
    observed_cost = f.ZERO.x
    for k in range(3):
        E = matrix_diff(B, k)
        Pk = matrix_diff(P, k)
        Sk = f.diff(source, k)
        parent_k = mean(f.mul(r, pair(E, E)))
        pressure_k = mean(pair(Pk, Pk))
        if pressure_k != mean(f.mul(Sk, Sk)) or pressure_k > 4*parent_k:
            raise ArithmeticError(('pressure derivative payment', k))
        parent += parent_k
        actual_pressure += pressure_k
        memory += mean(pair(matrix_diff(PC, k), matrix_diff(PC, k)))
        observed_cost += mean(pair(matrix_diff(observed, k), matrix_diff(observed, k)))
    diffusion = 8*parent + f.QQ_I(56).x/5*observed_cost
    if memory > f.QQ_I(33).x/56*diffusion:
        raise ArithmeticError('33/56 memory-pressure diffusion payment')
    spectral = spectral_memory_bound(PC, mean(f.trace(G)), memory, diffusion)
    localized = weighted_pressure_flux(P, p)
    return {'pressure_square': str(mean(pair(P, P))),
            'velocity_quartic': str(mean(f.mul(r, r))),
            'pressure_derivative_square': str(actual_pressure),
            'local_parent_derivative_cost': str(parent),
            'memory_source_pressure_derivative_square': str(memory),
            'completed_diffusion_lower': str(diffusion),
            'strict_payment_coefficient': '33/56',
            'memory_mass_and_diffusion_split': spectral,
            'weighted_pressure_flux': localized}, (B, P, G)


def check_joint(u, B, P, G):
    S = matrix_scale(f.QQ_I(1)/2, matrix_add(B, transpose(B)))
    omega = f.curl(u)
    W = f.dot(omega, omega)
    r = pair(B, B)
    Sw = f.matvec(S, omega)
    # sqrt(2) is divided out. These are the cubic strain-slot and quadratic
    # pressure-slot coefficients at eta_env=sigma=1 of Psi(alpha*u).
    M = matrix_add(matrix_scalar(f.scale(192, r), S),
                   matrix_scale(f.QQ_I(2)/7, symmetric_product(Sw, omega)),
                   matrix_scalar(f.scale(f.QQ_I(10)/21, W), S))
    N = matrix_add(matrix_scale(96, P), matrix_scale(-1, f.tensor(omega, omega)))
    KN = observe(N)
    qC = f.tensor_pressure(G)
    PC = f.hess(qC)
    qgradient = f.grad(qC)
    joint = mean(f.add(pair(M, PC), pair(N, observe(symmetric_product(u, qgradient)))))
    qeff = f.add(f.tensor_pressure(M),
                 f.scale(-2, f.green(divergence(f.matvec(KN, u)))))
    if joint != mean(pair(G, f.hess(qeff))):
        raise ArithmeticError('joint Hessian pressure receiver')
    if joint != -mean(f.dot(tensor_divergence(G), f.grad(qeff))):
        raise ArithmeticError('joint pressure integration by parts')
    boost_coefficients = [2*mean(f.dot(KN[j], qgradient)) for j in range(3)]

    p = f.green(f.trace(f.matmul(B, B)))
    gp = f.grad(p)
    stress = matrix_add(f.tensor(u, u), G)
    comm = pressure_commutator(u, stress)
    production = matrix_add(matrix_scale(-1, observe(symmetric_product(u, gp))), comm)
    for j in range(3):
        U = [{f.ORIGIN: f.QQ_I(int(i == j))} if i == j else {} for i in range(3)]
        boosted = [f.add(u[i], U[i]) for i in range(3)]
        stressU = matrix_add(f.tensor(boosted, boosted), G)
        f.same_matrices(observe(stressU), observe(stress), 'boost invariant pressure observer')
        commU = pressure_commutator(boosted, stressU)
        correction = observe(symmetric_product(U, gp))
        f.same_matrices(commU, matrix_add(comm, correction), 'transport commutator compensation')
        productionU = matrix_add(matrix_scale(-1, observe(symmetric_product(boosted, gp))), commU)
        f.same_matrices(productionU, production, 'full Galilean invariant pressure production')
        fragmentU = mean(f.add(pair(M, PC), pair(N, observe(symmetric_product(boosted, qgradient)))))
        if fragmentU-joint != boost_coefficients[j]:
            raise ArithmeticError(('isolated memory fragment boost', j))
    return {'joint_memory_source_pairing': str(joint),
            'isolated_fragment_boost_coefficients': list(map(str, boost_coefficients)),
            'full_pressure_production': 'boost invariant with exact commutator compensation',
            'scope': 'unselected leading receivers; generated initial memory source; no history refutation'}


def main():
    u = f.fixture()
    pressure, (B, P, G) = check_pressure(u)
    joint = check_joint(u, B, P, G)
    expected = ['-256/33', '256/33', '0']
    if joint['isolated_fragment_boost_coefficients'] != expected:
        raise ArithmeticError('informative nonzero receiver boost fixture')
    # Add a separated parent with a different phase and exact transverse
    # polarization. The memory pressure is no longer the base fixture's
    # same-size special case; all new interactions are retained.
    extra = [{}, {}, {}]
    k, polarization, phase = (3, -2, 1), (1, 2, 1), f.QQ_I(1, 3)/13
    for j in range(3):
        extra[j][k] = phase*polarization[j]
        extra[j][tuple(-x for x in k)] = f.QQ_I(phase.x, -phase.y)*polarization[j]
    separated, _ = check_pressure([f.add(u[j], extra[j]) for j in range(3)])
    print(json.dumps({'pressure_payment': pressure, 'joint_history': joint,
                      'separated_parent_payment': separated,
                      'arithmetic': 'Gaussian rational; every convolution output retained'}, indent=2))


if __name__ == '__main__':
    main()
