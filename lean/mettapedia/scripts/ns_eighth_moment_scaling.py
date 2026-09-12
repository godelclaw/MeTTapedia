"""Exact Gaussian initial-data diagnostic for an instantaneous L8 source bound.

Requires SymPy. This is a symbolic calculation, not a Lean verification or
a constructed time-evolving Navier--Stokes solution. All polynomial and
normalized Gaussian-moment arithmetic below is rational.

The velocity is curl(exp(-|x|^2) * (0, x*z, 3*x*y)). For r > 0,
u_r(x) = r^3 u(r^2*x) preserves kinetic energy. Its vorticity and strain
scale by r^5, and each spatial derivative adds r^2. Thus S8 scales by
r^39, while G8, R8 and Z2*E8 scale by r^38. Positive S8 rules out a
universal instantaneous bound S8 <= nu*(G8+6*R8) + C(K2,nu)*Z2*E8.
It does not rule out a time-integrated estimate with initial-data terms.
"""

from functools import lru_cache
import json

import sympy as sp


X, Y, Z = sp.symbols("x y z")
COORDINATES = (X, Y, Z)


def derivative(polynomial, coordinate, gaussian_rate=1):
    """Polynomial factor of a derivative of p*exp(-rate*|x|^2)."""
    x = COORDINATES[coordinate]
    return sp.diff(polynomial, x) - 2 * gaussian_rate * x * polynomial


def curl(vector, gaussian_rate=1):
    return tuple(
        sp.expand(
            derivative(vector[(i + 2) % 3], (i + 1) % 3, gaussian_rate)
            - derivative(vector[(i + 1) % 3], (i + 2) % 3, gaussian_rate)
        )
        for i in range(3)
    )


def poly(expression):
    return sp.Poly(expression, *COORDINATES, domain=sp.QQ)


@lru_cache(maxsize=None)
def normalized_moment(exponent, gaussian_rate):
    """Integral x^n exp(-m*x^2) divided by sqrt(pi/m)."""
    if exponent % 2:
        return sp.S.Zero
    degree = exponent // 2
    return sp.factorial2(2 * degree - 1) / (2 * gaussian_rate) ** degree


def normalized_integral(polynomial, gaussian_rate):
    """Rational integral factor; multiply by (pi/rate)^(3/2)."""
    return sum(
        coefficient
        * sp.prod(normalized_moment(n, gaussian_rate) for n in exponents)
        for exponents, coefficient in polynomial.terms()
    )


def main():
    potential = (sp.S.Zero, X * Z, 3 * X * Y)
    velocity = curl(potential)
    vorticity = curl(velocity)
    assert sp.expand(sum(derivative(velocity[i], i) for i in range(3))) == 0
    assert sp.expand(sum(derivative(vorticity[i], i) for i in range(3))) == 0

    # Check the derivative scaling for a symbolic positive concentration parameter.
    r = sp.symbols("r", positive=True)
    substitution = {x: r**2 * x for x in COORDINATES}
    scaled_velocity = tuple(r**3 * p.subs(substitution, simultaneous=True) for p in velocity)
    scaled_vorticity = curl(scaled_velocity, r**4)
    for i in range(3):
        assert sp.expand(scaled_vorticity[i] - r**5 * vorticity[i].subs(substitution, simultaneous=True)) == 0
        for j in range(3):
            assert sp.expand(
                derivative(scaled_velocity[i], j, r**4)
                - r**5 * derivative(velocity[i], j).subs(substitution, simultaneous=True)
            ) == 0
            assert sp.expand(
                derivative(scaled_vorticity[i], j, r**4)
                - r**7 * derivative(vorticity[i], j).subs(substitution, simultaneous=True)
            ) == 0

    gradient = sp.Matrix(3, 3, lambda i, j: derivative(velocity[i], j))
    strain = (gradient + gradient.T) / 2
    omega = sp.Matrix(vorticity)
    omega_square = poly(omega.dot(omega))
    quadratic_stretch = poly(omega.dot(strain * omega))
    assert quadratic_stretch == poly(omega.dot(gradient * omega))

    kinetic = poly(sum(component**2 for component in velocity))
    eighth = omega_square**4
    weighted_gradient = omega_square**3 * poly(
        sum(derivative(vorticity[i], j) ** 2 for i in range(3) for j in range(3))
    )
    radial_gradient = omega_square**2 * poly(
        sum(
            sum(vorticity[i] * derivative(vorticity[i], j) for i in range(3)) ** 2
            for j in range(3)
        )
    )
    stretching = omega_square**3 * quadratic_stretch

    # Independent integration-by-parts consistency checks at the polynomial level.
    velocity_gradient = poly(sum(entry**2 for entry in gradient))
    assert normalized_integral(velocity_gradient, 2) == normalized_integral(omega_square, 2)
    diffusion_pair = omega_square**3 * poly(
        sum(
            vorticity[i] * derivative(derivative(vorticity[i], j), j)
            for i in range(3)
            for j in range(3)
        )
    )
    assert normalized_integral(diffusion_pair + weighted_gradient + 6 * radial_gradient, 8) == 0
    energy_laplacian = poly(
        sum(derivative(derivative(eighth.as_expr(), j, 8), j, 8) for j in range(3))
    )
    assert normalized_integral(energy_laplacian, 8) == 0

    moments = {
        "K2": (kinetic, 2, 0),
        "Z2": (omega_square, 2, 4),
        "E8": (eighth, 8, 34),
        "G8": (weighted_gradient, 8, 38),
        "R8": (radial_gradient, 8, 38),
        "S8": (stretching, 9, 39),
    }
    expected = {
        "K2": sp.Rational(27, 8),
        "Z2": sp.Rational(243, 8),
        "E8": sp.Rational(519989274358265835, 2199023255552),
        "G8": sp.Rational(5029854531845428305, 8796093022208),
        "S8": sp.Rational(9959571879362560, 282429536481),
    }
    result = {}
    for name, (polynomial, rate, scaling_power) in moments.items():
        value = normalized_integral(polynomial, rate)
        assert value > 0
        if name in expected:
            assert value == expected[name]
        result[name] = {
            "rational_factor": str(value),
            "gaussian_factor": f"(pi/{rate})^(3/2)",
            "scaling_power": scaling_power,
        }
    assert moments["Z2"][2] + moments["E8"][2] == moments["G8"][2]
    assert moments["S8"][2] > moments["G8"][2]
    print(json.dumps({
        "velocity_polynomial": [str(p) for p in velocity],
        "vorticity_polynomial": [str(p) for p in vorticity],
        "moments": result,
        "exact_consistency_checks": "passed",
        "status": "symbolic initial-data diagnostic, not Lean-verified",
    }, indent=2))


if __name__ == "__main__":
    main()
