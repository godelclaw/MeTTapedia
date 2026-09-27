#!/usr/bin/env python3
"""Exact finite data for the delayed helical mean example.

Integer phase counts are also certified by MettapediaNS.HelicalPhaseSelection.
This script checks the two Gaussian energy normalizations with rational
arithmetic. The local PDE estimates are analytic, not proved here.
"""
import json
from fractions import Fraction as F
from math import factorial


def moment(j):
    """Integral of r^(2j+1) exp(-2r^2), by the Gaussian moment identity."""
    return F(factorial(j),2**(j+2))


energies=[]
peak_velocities=[]
for m,denominator,expected in [(6,8,F(315,512)),(8,32,F(2835,4096))]:
    # The real horizontal curl of r^m exp(-r^2) exp(i m phi),
    # divided by denominator, has this energy after division by pi.
    energy=(2*m*m*moment(m-1)-4*m*moment(m)+4*moment(m+1))/denominator**2
    closed=F(factorial(m+1),2**(m+1)*denominator**2)
    if energy != closed or energy != expected:
        raise ArithmeticError('Gaussian energy normalization')
    energies.append(energy)
    peak_velocities.append(-F(m-2,denominator))
if sum(energies)!=F(5355,4096) or sum(peak_velocities)!=-F(11,16):
    raise ArithmeticError('combined initial normalization')

print(json.dumps({
    'horizontal_energies_divided_by_pi':[str(q) for q in energies],
    'total_horizontal_energy_divided_by_pi':str(sum(energies)),
    'azimuthal_velocities_at_radius_one_in_units_of_exp_minus_one':
        [str(q) for q in peak_velocities],
    'phase_labels':[[6,1],[-6,-1],[8,1],[-8,-1]],
    'scope':'finite exact normalizations; phase-counting theorem is in Lean, PDE application is analytic'
},indent=2))
