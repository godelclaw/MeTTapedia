# Navier–Stokes interaction labs

The current geometric question is whether repeated interactions among
coherent vorticity structures admit a signed history bound determined by
the full initial datum. Two recent results delimit that question:
[a common polarized belt](#all-frequency-renewal-in-a-polarized-belt)
admits an all-frequency caloric renewal estimate, whereas
[different axes in adjacent shells](#different-axes-in-adjacent-shells)
can produce mixed renewal that defeats an energy-only extension.
The latter is an actual short unforced burst, not an indefinitely repeated
cascade. Both whole-space arguments are analytic; the accompanying programs
check finite algebra. The distinction between the auxiliary caloric renewal
and the physical cubic stretching is essential throughout these labs.

`fourier_interactions.py` checks explicit trigonometric examples against the
complete unforced Navier–Stokes quadratic source. It uses Python's standard
library and exact rational arithmetic. All generated convolution modes are
retained, including modes outside the input family. It does not integrate a
truncated dynamical system.

From this package directory:

```sh
python3 labs/fourier_interactions.py
python3 labs/fourier_interactions.py --case chain --generations 12
```

The program prints JSON after all selected checks pass and raises an error on
failure. Checks remain enabled with `python3 -O`. There are no input files,
network requests or generated files. The `matched`, `chain`, `cyclic`,
`crossing` and `remainder` cases can also be run separately.

These are reproducible algebra calculations, **not Lean certificates**.
The jet calculations identify derivatives of a smooth solution at time zero;
they supply no uniform Taylor remainder, time window, or global regularity
bound. Sample checks of a formula indexed by an integer are distinguished
below from polynomial identities certified by a degree bound and enough
exact samples.

## Conventions and equation

The domain is the torus of period `2π`, with normalized spatial measure. Write
`u(x) = Σ_k û(k) exp(i k·x)` and `A = -Δ`, so `A` multiplies each coefficient
by `|k|²`. The stored vector at `k` is the real rational amplitude `a(k)` in
`û(k) = i a(k)`. Each velocity obeys `a(-k) = -a(k)` and `k·a(k) = 0`.
This is a closed subclass for the source and time-jet operations used here;
it is not a representation of every real Fourier field.

For `P_k z = z - k(k·z)/|k|²`, with `P_0` the identity, the stored amplitude of
`B(u,v) = -P[(u·∇)v]` is

```text
B(u,v)(k) = P_k Σ_(p+q=k) (a(p)·q) b(q).
u_t = -ν A u + N(u),          N(u) = B(u,u).
```

The positive sign in this amplitude formula accounts for all three factors
of `i` in the advection term. Projection happens after the complete sum.
The zero mode is retained by the operator and checked to vanish for the
solenoidal data. There is no Fourier cutoff.

For the formal expansion `u(t) = Σ_r u_r t^r`, the program applies

```text
(r+1) u_(r+1) = -ν A u_r + Σ_(i=0)^r B(u_i,u_(r-i)).
```

At every computed order it checks reality, zero mean, incompressibility,
the kinetic-energy identity and the enstrophy identity. In particular, with
`E = ||u||₂²/2`, `Y = ||∇u||₂²/2` and `Π = <Au,N(u)>`,

```text
E' = -2νY,                  Y' = Π - ν||Au||₂².
```

These conventions differ from the period-one Fourier normalization in the
Lean lane. A bridge must retain the corresponding factors of `2π`.

## Equal initial sources, opposite later corrections

The two initial velocities are

```text
u_s = (-sin y-sin z, -sin x-sin z, -sin x-sin y),
u_a = ( sin y-sin z, -sin x+sin z,  sin x-sin y).
```

Both have squared velocity norm `3`, satisfy `Au=u`, and have the same
**complete** source

```text
n = N(u) = -(sin(y+z), sin(x+z), sin(x+y)),
An = 2n,                    ||n||₂² = 3/2.
```

Their unprojected stretching fields `(curl u·∇)u` also agree. The program
checks this directly, checks `curl A⁻¹P[(curl u·∇)u] = n/2`, and checks the
vanishing heat commutator `DN(u)[Au] - AN(u)`. Since both inputs occupy the
same Laplacian eigenspace, their sources under heat evolution also agree.

The first Picard approximation is
`v(t) = exp(-νt)u + t exp(-2νt)n`. Its production is exactly
`Π(v(t)) = (3/2)t exp(-4νt)`. The actual solution's production has coefficients

```text
Π_s(t) = (3/2)t - 6νt² + (12ν² - 1/12)t³ + O(t⁴),
Π_a(t) = (3/2)t - 6νt² + (12ν² + 3/4 )t³ + O(t⁴).
```

Thus the cubic corrections to first Picard production have opposite signs.
The leading production itself is positive for both fields. These examples
exclude a determination of that correction from their common initial source
and heat-source history alone; they do not exclude rules using the full
initial velocity or the subsequent nonlinear history.

The coefficient of `t^r` is a polynomial in `ν` of degree at most `r`:
this follows inductively from the displayed recurrence. The production
coefficients through `t³` therefore have degree at most three. The four exact
viscosity samples `0, 1, 3/2, 2` determine them for every viscosity. This finite
polynomial argument does not assert a viscosity-uniform Taylor remainder.

## A quadratic chain and its mixed outputs

Let `S=(1,1,1)`, `b_n=(-1)^n`, `a_n=(2^n-b_n)/3`, and, for `i=1,2,3`, set

```text
k_(n,i) = a_n S + b_n e_i,
v_(n,i) = (a_n+b_n)S - (3a_n+b_n)e_i,
r_n = |k_(n,i)|² = (4^n+2)/3,
U_n = Σ_i v_(n,i) sin(k_(n,i)·x),     ||U_n||₂² = 3r_n.
```

The program checks the full diagonal identity
`N(U_n) = γ_n U_(n+1)`, where
`γ_n = b_n 2^n r_n/r_(n+1)`. With `W_n=U_n/sqrt(3r_n)`, its normalized
multiplier has square `β_n² = 4^n/(4^(n+1)+2)`.

This diagonal identity does **not** make the family invariant. For
`C_n = B(W_n,W_(n+1)) + B(W_(n+1),W_n)`, the full mixed source has 24 modes:
six return to `W_n`, and eighteen lie outside the chain. Writing `r=4^n`,
the squared norms checked against the complete convolution are

| Part of the mixed source | Squared norm |
| --- | --- |
| Retained, equal to `-β_n W_n` | `r/(4r+2)` |
| Escaping sums, 12 modes | `r/[2(r+2)]` |
| Escaping differences, 6 modes | `9r³/[2(r+2)(r+8)(2r+1)]` |
| Total | `3r(4r²+9r+8)/[2(r+2)(r+8)(2r+1)]` |

Normalization uses ratios of squared rational norms, so the program needs
no floating-point square roots. It also checks the exact reverse vector
field and kinetic-energy cancellation, not just the norms.

The displayed rational expressions give limiting total squared norm `3`
and escaping squared norm `11/4`; their ratio tends to `11/12`. The program
checks these expressions for the requested finite set of generations
(eight by default). That sample calculation alone is not a proof of the
formulas for every generation. It does establish explicit failures of
closure. The escaping fraction concerns the mixed **source**, not a fraction
of kinetic energy lost by a solution or a persistent leakage rate in time.

## Cyclic shears: a cancellation that ends at the next order

For `u=(sin(cz),sin(ax),sin(by))`, with positive integer radii, put
`T=DN(u)[N(u)]`. The squared norm of the part of `T` whose wavevectors have
all three coordinates nonzero is

```text
[a²(b²-c²)² + b²(c²-a²)² + c²(a²-b²)²] / [2(a²+b²+c²)].
```

The code checks the full vector formula at all eight signed wavevectors
`(±a,±b,±c)`, and then the norm, for five radius triples. Equal radii cancel
this part under the Leray projection. For example, `(1,1,2)` gives `3/2`
and `(2,3,4)` gives `946/29`.

Even at `(a,b,c)=(1,1,1)`, this is not an invariant absence of such modes.
The coefficient `u_3` of `t³` has 24 of them, with squared norm `31/1152`.
At wavevector `(2,1,1)` its stored imaginary amplitude is
`(-5/288, 1/144, 1/36)`. Four exact viscosity samples, together with the
degree bound at most three, check that this entire part of `u_3` is
independent of viscosity. Again this is an initial-derivative statement,
not a quantitative lower bound at a specified positive time.

## Generated modes can return positive work to their parents

The `crossing` case uses three boxes of positive input wavevectors. In box
`i`, coordinate `k_i` is either `2` or `3`, and the other coordinates belong
to `{-1,0,1}`. Their stored amplitudes are respectively
`(-k₂,k₁,0)`, `(0,-k₃,k₂)` and `(k₃,0,-k₁)`; reflection supplies the negative
wavevectors. The resulting field `u₀` has 108 modes and squared norm `774`.
These are finite, relatively wide boxes, not an asymptotically narrow-cone
claim.

Let `P` retain the original frequencies, `p(t)=Pu(t)`, `c(t)=(I-P)u(t)` and
`g=(I-P)N(u₀)`. The complete initial source has 852 modes, of which 756 lie
outside `P`. Since the viscous term preserves the original support,
`c(0)=0` and `c'(0)=g` for every viscosity. Consequently

```text
<p(t), N(c(t))>  = (7481477195560 / 2909907) t² + O(t³),
<Ap(t), N(c(t))> = (3185491560402752 / 140645505) t² + O(t³).
```

Both leading coefficients are positive. Normalizing the initial norm to
`α` multiplies them by `α⁵/774^(5/2)`. The code evaluates each source pairing
by summing every input pair that meets the receiver support; transversality
removes the final Leray projection. It checks this pairing against full
convolution on smaller fields, and also checks the companion cancellation
`<g,B(u₀,g)>=0`, `<g,B(g,u₀)>=-<u₀,N(g)>`.

Thus two previously generated inputs can contribute positive signed work
at the parent frequencies. The mixed terms still conserve total kinetic
energy. This is one source channel, not net parent-energy growth, a closed
energy-transfer model, a uniform positive-time bound, or a refutation of a
data-dependent signed budget.

## Subtracting the complete pair histories does not fix the stretching sign

For `s=±1`, take the cyclic initial velocity `u₀=(c(z),a(x),b(y))`, where

```text
a(x)=s(sin x+sin 2x),    b(y)=sin y+(sin 2y)/2,
c(z)=sin 2z+sin 4z.     ||u₀||₂²=21/8.
```

Write the three separate axis fields as `v₁,v₂,v₃`, and let `U_I(t)` be
the actual solution with initial value `Σ_(i∈I) v_i`. Each single field
follows heat flow. Each pair is globally described by a heat-evolved shear
and a linear passive scalar; for example the pair in `x,y` is
`(0,a(x,t),θ(x,y,t))` with `θ_t+a θ_y=νΔθ` and `θ(0)=b(y)`.

Subtract those complete pair histories by defining

```text
Q(t)=U_{123}(t)-U_{12}(t)-U_{23}(t)-U_{31}(t)+U_1(t)+U_2(t)+U_3(t).
```

This is a difference of actual flows, not a Fourier projection. On the
smooth interval of the full solution, `Q(0)=Q'(0)=0`. The code computes
`Q(t)=t²q₂+O(t³)`, where `q₂` has 56 modes and is independent of viscosity:

```text
||q₂||₂²=845/56,    ||∇q₂||₂²=2331/8,    ||Aq₂||₂²=47115/8,
Π(Q(t))=-(243/56)s t⁶+O(t⁷),             Π(v)=<Av,N(v)>.
```

Three distinct exact viscosity samples determine `q₂`, since its degree
in `ν` is at most two. Reversing `a` reverses `q₂` and its cubic production,
while preserving the displayed squared norms. Thus a zero initial
remainder, even after all pair histories are subtracted, does not force
nonpositive self-stretching. The code certifies the initial coefficients
by rational calculation; it supplies no uniform time window or bound on
the later signed integral. A data-dependent allowance remains possible.

## Angular mean and Reynolds stress

`reynolds_stress.py` uses Sympy to check the differential algebra behind
[the symmetry-defect criterion](../../../papers/ns_symmetry_defect.pdf)
([TeX source](../../../papers/ns_symmetry_defect.tex)). Run it from this
package directory with:

```sh
python3 labs/reynolds_stress.py
```

For the rotation-equivariant angular average `P`, set `v=P u` and `w=u-v`.
The program constructs an explicit divergence-free polynomial velocity,
computes its continuous angular average by exact circle moments, and checks

```text
P[(u·∇)u] = (v·∇)v + P[(w·∇)w],
F = -P[(w·∇)w] = -div P(w⊗w).
```

All six cylindrical stress entries are nonzero in the example. The
cylindrical divergence formula and its lifted potential-vorticity source
are checked against the Cartesian calculation. A second calculation
verifies the lifted identity for arbitrary symbolic stress components.
The program also checks the stretching difference as an exact divergence
plus terms with an undifferentiated `w`. For arbitrary component symbols
it checks the cylindrical stretching identity used in the mean's enstrophy
estimate; for arbitrary functions it checks the local radial integration
identity and the ancient circulation equation. An additional scalar check
verifies a weighted Hardy constant on a power profile. Errors raise
exceptions even under `python3 -O`.

The note also proves a necessary stress input for persistent nonzero
rescaled mean swirl. With `e=P(w_r w_theta)`, `f=P(w_z w_theta)` and
`τ=-t`, some fixed `T>1` and `ε>0` then obey

```text
τ^h ∫[-Tτ,-τ] (||e||∞ + τ^h ||f||∞) dt ≥ ε
```

at every sufficiently late time where the rescaled swirl exceeds a fixed
positive threshold. In particular the interval average of `||w||∞²` is
at least a constant times `τ^(-1-h)`. The proof retains the same uniform
mean geometry and uses the ancient circulation comparison. It gives no
bound on this stress from initial data. Before taking norms, the signed
stress pairs with a test density `ψ` as
`e(R ∂Rψ-ψ) + δ f R ∂Zψ`; the script checks this integration by parts
and the full circulation adjoint identity for arbitrary coefficient
functions. A global adjoint kernel construction is not claimed.

The polynomial fields test local identities; they are not finite-energy
whole-space data or Navier–Stokes solutions. The script does not certify
the analytic proof in the note. Its main regularity criterion assumes
prescribed anisotropic second-order bounds on the angular mean and only
the critical amplitude history

```text
∫ ||w(t)||∞² dt < ∞.
```

No derivative or torque integral of the defect is assumed. The proof first
eliminates swirl in the ancient limit, then controls the mean's stretching
using derivatives smaller than `1/(T-t)`. It uses the full second-order
mean swirl bounds. For the defect amplitude, every power `β<1/2` suffices;
the borderline `τ^(-1/2) log(e/τ)^(-p)` suffices when `p>1/2`.
Neither the mean geometry nor the critical history has been established
for arbitrary data. The note and the symbolic calculations are separate
from the kernel-checked Lean lane.

For a smooth whole-space flow with a uniform energy bound and canonical
pressure, a separate estimate controls the additional gradient history
`∫ √(T-t) ||w||∞ ||∇w||∞ dt`, and therefore the averaged torque history,
under the stronger condition

```text
∫₀ᵃ τ^(-h/2) √log(e/τ) ||w(-τ)||∞² dτ < ∞,       τ = -t.
```

This estimate only needs the mean's velocity and Cartesian gradient bounds
stated in the note, with `0<h<1/2`; it does not need the full second-order
anisotropic geometry of the regularity criterion.
The proof follows the mean over short viscous intervals and retains the
nonlocal pressure kernel. For this additional gradient estimate, a power
bound `||w(-τ)||∞ ≤ C τ^(-β)` suffices for `β < 1/2-h/4`. This is an
analytic smoothing argument, not a result checked by the symbolic script.
The stronger weight is not required by the main regularity criterion.

### Finite-energy angular transfer

The same script checks a separate pair of Schwartz initial data. Let
`ρ=x²+y²+z²`, `r²=x²+y²`, `σ=±1`, and set

```text
V  = curl(exp(-ρ) e_z),
Wσ = curl((x²-y²+2σxy r²) exp(-ρ) e_z),
P V=V,             P Wσ=0.
```

Writing `g_a=(π/a)^(3/2)`, their exact integrals are

```text
||V||₂² = 2 g₂,               ||Wσ||₂² = (9/2) g₂,
||∇h Wσ||₂² = 30 g₂,          ||∂z Wσ||₂² = (9/2) g₂,
∫ Wσ·(Wσ·∇)V = -σ (16/9) g₃.
```

These are Gaussian moments, evaluated exactly without spatial truncation.
The script also checks the work of the complete convection term for
`u=V+εWσ`. For the actual unforced equation, pressure does no work on the
divergence-free defect, and

```text
(1/2) d_t ||w||₂² + ν||∇w||₂² = -∫ w·(w·∇)v.
```

Thus opposite phases have identical defect energy and dissipation but
opposite nonlinear transfer. The paper normalizes the anisotropically
concentrated data `A(V+εWσ)(λx,λy,λ^(2/3)z)` to unit squared velocity norm.
Their relative defect norm is `3ε/2`; the positive transfer divided by
its viscous cost grows like `λ^(1/3)/ν`. The mean also obeys the paper's
spatial geometry bounds at the initial slice with `h=1/6`, uniformly in
the concentration parameter. Persistence of those bounds through a
fixed horizon is not asserted.

This excludes automatic viscous damping from small relative angular defect.
It concerns kinetic transfer, not vorticity stretching, and does not exclude
a data-dependent history allowance or establish a singular solution. The
script checks the initial energy identities, not a time interval of evolution.

It also checks the actual mean circulation source
`r Fθ = 4σ r⁴(2r²-3) exp(-2ρ)`. For the scaled data, at the initial
circulation maximum `r=1/λ, z=0`,

```text
Γ_t = -4νA(2λ²+μ²)/(eλ) - 4σ ε²A²/e²,       μ=λ^(2/3).
```

The phase `σ=-1` therefore increases the maximum when
`ε²A/(νλ) > e[2+(μ/λ)²]`, with energy transferred out of the defect.
The script also checks the initial motion of that peak. In variables
`s=Aλt`, `R=λr`, `Z=μz`, put `δ=μ/λ` and `η=νλ/A`. Then

```text
∂s Γ̃_peak = 4ε²/e² - 4η(2+δ²)/e,
d_s R_peak = 2η - 2ε²/e.
```

Both growth and inward motion hold for sufficiently large `λ`.
The note proves that these signs persist for `0≤s≤c₀`, with `c₀>0`
independent of the concentration. It uses the full projected equation:
the anisotropic Leray multiplier has Sobolev norm at most one, yielding
uniform local bounds and time-derivative control. The exact defect equation
keeps its `H⁸` norm and the `H⁶` norm of its time derivative proportional
to `ε`, so the Reynolds stress and its time derivative stay of order `ε²`.
At the interval's end
the circulation has increased and the radius has decreased by relative
amounts at least `c₁ε²`. This concerns a branch of meridional local maxima
starting at the global maximum; its later global maximality is not assumed.

More generally, choose any `0<h≤1/6`, set `μ=λ^(1-2h)` and
`A=λ^(1+2h)/√C_ε`. The initial squared energy is `λ^(-1+6h)≤1`,
equal to one for `h=1/6`. The full mean geometry with this `h` holds
throughout the interval.
Its radial gain follows from actual incompressibility,
`v_r=-(δ/R)∫₀ᴿ q ∂Z v_z dq`, and uniform Sobolev bounds. The script
checks the radial derivative identities used for that gain; the uniform
existence and persistence argument is analytic, not a symbolic certificate.
The actual critical defect history also obeys

```text
∫[0,c₀/(Aλ)] ||u-Pu||∞(B1)² dt ≥ c₂ ε² λ^(2h).
```

Thus bounded-energy unforced data, including unit-energy data at `h=1/6`,
can produce an arbitrarily large value on a shrinking smooth interval,
while the displayed mean geometry holds.
Initial higher norms grow with `λ`. This is one finite concentrating event;
it does not establish repeated events from one fixed datum, an infinite
cascade, or failure of a history bound depending on that datum's higher norms.

### Fast axial seeds and mean geometry

Run `python3 -O labs/axial_seed_geometry.py` from the NS workspace.
This checker compares two Schwartz horizontal solenoidal defects whose
physical axial phase is `α=λz`. Write

```text
Ψ_α = exp(-R²-Z²)[R² cos(2φ+α) - R⁴ sin(2φ+α)],
W_α = curl_h(Ψ_α e_z).
```

The standing seed is `W₀ cos α`; the helical seed is `W_α`.
Their exact mean radial–azimuthal stresses are respectively

```text
-2R⁴ exp(-2R²-2Z²) cos²α,
-2R⁴ exp(-2R²-2Z²).
```

The helical cancellation persists in the full nonlinear evolution on
a common local interval. The note constructs an extended solution with
an independent periodic phase and axial derivative `δ∂Z+∂α`, then
restricts it to `α=Z/δ`. Its joint symmetry under horizontal rotation
by `β` and phase shift by `-2β` makes the angular mean independent of
the fast phase. Uniform Sobolev bounds on this extended solution give
the actual unforced flow, including its pressure and all generated modes.

Consequently the inward-growth and critical-history conclusions above
also hold with these fast helical seeds. The meridional maximum may
move axially; no fixed axial coordinate is asserted. The full mean
geometry persists for a common normalized interval, with a relative
circulation gain and inward motion of order `ε²`.

The standing seed instead creates fast axial curvature in the mean.
For `G=R(PU)_θ`, `J=δ∂Z+∂α` and `F(s)=J²G(1,0,0,s)`, the checker gives

```text
F(0)  = -4δ²/e,
F'(0) = ηδ²(16+24δ²)/e - ε²(16δ²+8)/e².
```

The note's uniform bound on `F''` proves, at `s*=cε²`, the actual estimate
`|∂zz (Pu)_θ| ≥ c ε⁴ Aλ²`. Its size relative to the stated mean bound
grows as `ε⁴ λ^(4h)`. Both families have the same initial mean, bounded
kinetic energy and arbitrarily small relative defect. Thus those initial
controls do not alone propagate the mean geometry uniformly.

The script also checks the joint symmetry, restriction derivatives on
all bivariate polynomials through degree four, the Gaussian energy
factor and the angular mean of the initial pressure source. Persistence
is an analytic argument, not a symbolic or Lean certificate. Different
helical families need not share the preserved symmetry, and no estimate
over a recurrent sequence or all smooth prefixes is proved here.

### A physical mean mode generated by two helical parents

Run `python3 -O labs/mixed_helical_parent.py` from the NS workspace.
For `q=x+iy` and `a=|q|²`, the complex parent potentials are

```text
ψ₂ = q² exp(-a),
ψ₄ = q⁴(1-2a/5) exp(-a).
```

Their real horizontal curls have phases `(m,n)=(2,1)` and `(4,1)`,
with actual axial derivative `2in`. The first mean mode with phase
`n=1` requires the three parents `2+2-4`; it is absent from every
single-parent and two-parent term. The intermediate pressures are exact:

```text
p₂₂ = -q⁴ exp(-2a),
p₂₄̄ = (conj(q)²/5)(4a³+18a²-62a+9) exp(-2a).
```

The checker verifies their pressure equations, transverse quadratic
velocity sources and all outer convection terms, including axial pressure
and transport. The final pressure does not change azimuthal mean circulation.
Its cubic coefficient is

```text
CΓ(R) = (8/5)R⁴(8R⁸-110R⁶+346R⁴-275R²+27) exp(-3R²),
CΓ(1) = -32/(5e³).
```

The real-field cosine coefficient is `ε³ CΓ/4`. Base and viscous terms
cannot reach this recipient in the second time derivative, by their
phase labels. This is an actual nonlinear generation calculation.

The note uses a fixed Schwartz axial envelope with Fourier support in
`[-1,1]`. After rescaling, the recipient is the physical orthogonal
projection onto the angular mean and `λ≤|k_z|≤3λ`. Its initial velocity
and first time derivative are exactly zero. Finite parameter derivatives
and phase selection control the remainder uniformly on a common time
interval, even at the critical relative amplitude `ε=λ^(-h)`.
High frequencies created in the slow zero phase are estimated by Sobolev
decay; continued compact spectral support is not assumed.

For `0<h≤1/6`, bounded-energy actual unforced data then produce:

```text
recipient kinetic energy           comparable to λ⁻¹,
integrated signed enstrophy work    at least cλ,
integrated recipient dissipation    at most Cν λ^(1-2h),
normalized mean axial curvature    at least cλ^h.
```

The initial energy is exactly one for `h=1/6`; the relative angular
defect tends to zero, and its critical amplitude history on this interval
stays uniformly bounded. The mean geometry nevertheless loses any uniform
constant based on these controls. The persistence and physical estimates
are analytic, not Lean or symbolic certificates.

The signed work here is for the receiving angular-mean sector. The parents
lie in the same axial band outside that sector. Their signed work remains
essential to the full high-frequency budget; this example does not refute
that budget, a data-dependent allowance, or regularity. No infinite sequence
of such events from one fixed datum is constructed.

### Total signed work with the parent response included

Run `python3 -O labs/helical_total_stretching.py` from the NS workspace.
This separate test uses one helical quadrupole about the Gaussian swirl
and includes the full signed enstrophy response. Initially the total
stretching is zero. Its next response has a positive quadratic coefficient
in the perturbation amplitude, with all pressure contributions retained.

For a carrier `κ>0`, the linear pressure has radial source
`32R²(R²-1) exp(-2R²)` and operator `-L₂+κ²`. Its pairing with the
vorticity reduces to a heat integral. The exact heat integrand changes
sign, but has the positive primitive

```text
B(t) = t(128t⁴+160t³+112t²+28t+5) / [2(1+4t)⁵].
```

The full quadratic coefficient is therefore
`2πκ⁴ ∫₀∞ exp(-κ²t) B(t) dt > 0`. The checker verifies the radial
pressure source, the source-square and base-pressure terms, the complete
linear-pressure pairing, the Gaussian heat equation, and the positive
primitive. In particular, the vertical perturbation vorticity cancels
an apparent extra pressure term; omitting it changes the answer.

Proposition 11 of the note proves a uniform time interval for actual
finite-energy unforced data with relative amplitude `ε=bλ^(-h)`,
`0<h≤1/6`. For fixed viscosity one can choose a fixed `b` so that the
**total** enstrophy increases by at least `cλ^(1+4h)` after subtracting
viscosity. The initial kinetic energy stays at most one, and is one
for `h=1/6`. The joint helical symmetry preserves the displayed mean
geometry on this interval, and the fluctuation history stays bounded
independently of `λ`.

Thus at every fixed Fourier cutoff, the full signed tail work minus
any fraction at most one of its dissipation is unbounded across this
family. This excludes an allowance based only on those uniformly bounded
controls. An allowance or cutoff depending on the full datum is still
possible: the initial enstrophy grows faster than the proved increment.
The uniform evolution argument is analytic, not a Lean or symbolic
certificate. This is a finite event from different data, with no asserted
recurrent cascade or failure of the conditional regularity theorem.

### Does the generated seed couple to linear growth?

Run `python3 -O labs/generated_mode_coupling.py` from the NS workspace.
This checker needs only the Python standard library. It uses exact
fractions throughout, with no numerical eigensolver or quadrature.

The mixed-parent seed has three velocity components. The updated
`mixed_helical_parent.py` checks the full radial and axial sources as
well as the azimuthal source. The final Leray projection leaves an
imaginary radial coefficient, a real azimuthal coefficient, and a real
axial coefficient in the axisymmetric carrier-2 mode.

For the inviscid linearization about the fixed Gaussian swirl, radial
motion obeys `A a_tt = -Φ a`, with `A=I-L₁/4` and
`Φ=16(1-r²) exp(-2r²)`. The coupling checker supplies a 32-term rational
Laguerre polynomial `f`. Its exact residual at `μ=21/200` verifies

```text
<f,Af>              < 101/100
<h,f>              > 27/100
||h||²             < 28
||-Φf - μAf||²     < 1/160000,
```

where `h` is the radial acceleration source induced by the generated
azimuthal seed. These inequalities force a nonzero projection onto the
positive spectrum above `1/20`; the proof uses the bounded self-adjoint
operator `-A^(-1/2) Φ A^(-1/2)`. No discrete-spectrum assumption is needed.
Proposition 12 of the note gives the resulting lower bound
`sqrt(20)/40 * sinh(t/sqrt(20))` for the meridional norm of the unscaled
complex mode in this fixed inviscid linearization. The other generated
components cannot cancel this contribution because they have the opposite
complex phase in the radial equation.

This establishes coupling, not amplification in the actual nonlinear
solution. The evolving parents supply an inhomogeneous forcing history;
later contributions could offset the initial one. Viscosity, the slow
envelope and a controlled longer nonlinear interval remain to be handled.
The spectral argument is analytic and the finite certificate is rational
arithmetic; neither is a new Lean theorem.

### Evolving cubic forcing history

Run `python3 labs/cubic_history.py` from the NS workspace; NumPy and SciPy
are required. A longer refinement run is
`python3 labs/cubic_history.py --n 384 --box 14 --time 3 --step .005`.

The first-order parents, both quadratic descendants and the cubic recipient
all evolve under the full projected linearization and their prescribed
interactions. These are all ancestry branches for the recipient at cubic
amplitude order in the continuum. The horizontal square is periodic and
only approximates rotational symmetry. This is a Fourier Galerkin
calculation about the fixed inviscid Gaussian column, **not** the full
nonlinear viscous evolution or a finite-energy whole-space background.
The reported recipient is unscaled; its contribution to the real datum
at this order is `ε³ Re(C exp(2iz))/4`.

The rational test from `generated_mode_coupling.py` defines a complex
observable `q`. Its operator residual is retained in the signed identity

```text
q' - sqrt(μ) q = test(evolving forcing) + residual(recipient).
```

RK4 advances both integrals at the same stages as the fields. The output
includes the independent initial-jet comparison, both signed integrals,
their ledger error, every field's norm and high-frequency fraction, and
the divergence defect. These diagnostics do not give a rigorous continuum
error enclosure.

At normalized time 3:

| Horizontal grid | Side length | Time step | Recipient norm | Real q | Imaginary q |
| --- | --- | --- | --- | --- | --- |
| 256 | 14 | .01 | 42.91325951 | -1.21208574 | 3.95253213 |
| 256 | 14 | .005 | 42.91326024 | -1.21208576 | 3.95253214 |
| 384 | 14 | .005 | 42.91326093 | -1.21208576 | 3.95253214 |
| 512 | 20 | .005 | 42.91325937 | -1.21208472 | 3.95253107 |

The real discounted forcing integral changes sign between times 1.8 and
2.1. Its value at time 3 in the larger box is approximately
`-0.45855706 + 1.49483206i`; the residual integral is included separately.
The displayed observables differ by less than `2e-6` across these runs.
The complete discrete ledger errors are below `4e-11`. This is finite-time
evidence that the initial real sign does not describe the subsequent
history. It establishes neither an infinite-time forcing tail nor control
of an actual nonlinear remainder.

Continuing the side-14 calculation to time 6 with step `.005` gives
recipient norm `850.70874132` and
`q=-11.95861001+38.87926611i` on grid 512. Refinement from grid 384
changes the norm by `5.9e-5`, the two components of `q` by less than
`1.5e-8`, and the signed discounted forcing components by less than
`2.1e-9`. The recipient's upper-frequency velocity fraction decreases
from `6.49e-5` to `2.10e-9`; the grid-512 ledger error is `1.63e-10`.
Both parents evolve throughout. A large unscaled cubic response does
not justify continuing a truncated amplitude expansion after its
contribution becomes comparable to the full field.

### Full nonlinear viscous history

`full_history.py` evolves the complete retained velocity, with both parents,
the mean and all generated Fourier modes free to change. Its initial
streamfunction is `exp(-r²) + ε Re((q² + q⁴(1-2r²/5)) exp(-r²) exp(2iz))`,
where `q=x+iy`, and the initial velocity is its horizontal curl. The domain
is a periodic horizontal square times an axial circle of period `π`.
This remains a finite Galerkin diagnostic, not a continuum enclosure or
a finite-energy whole-space construction.

From the NS workspace, with NumPy and SciPy installed:

```sh
python3 labs/full_history.py --n 256 --nz 32 --box 14 --time 3 --step .005
python3 labs/full_history.py --n 384 --nz 32 --box 14 --time 3 --step .005
```

The defaults are `ε=.1` and viscosity `.001`. Norms use the horizontal
integral divided by `2π` and the average over the axial period. Initial
kinetic energy is `.2545` and enstrophy is `1.0825`. RK4 integrates the
kinetic dissipation, signed enstrophy production and enstrophy dissipation
at the same stages as the field. At time 3:

| Horizontal grid | Enstrophy | Integrated signed production | Integrated enstrophy dissipation |
| --- | --- | --- | --- |
| 256 | 1.09416368675 | .07344871143 | .06178502469 |
| 384 | 1.09416462772 | .07345183378 | .06178720607 |

Thus the observed total production exceeds dissipation by about `.011665`.
At grid 384 the energy-ledger errors are below `1e-11`, and the fraction
of palinstrophy above 80% of any retained coordinate cutoff is about
`1.12e-4` (versus `8.65e-3` at grid 256). These fractions are diagnostics,
not estimates of the omitted modes. No rigorous PDE error bound follows.

The earlier cubic test, applied to the full axial mode and multiplied by
`8/ε³`, is approximately `-1.01349505 + 2.95094567i` at time 3 on grid 384.
It includes all retained amplitude orders; it is not the cubic variation
itself. The program also reports circulation at radius one over the axial
grid. That observable is not a maximization over radius. Neither this
finite history nor the earlier cubic calculation establishes recurrence
or a uniform allowance for arbitrary data.

The option `--tail-cutoffs 0 2 4 8 16 32` also integrates the signed
production and dissipation above each listed physical wave number. Only
the receiving modes with `|k|≥K` are selected; their nonlinear source uses
the complete field. Each tail has its own balance
`Y_K(t)-Y_K(0)=∫P_K-∫D_K`, with viscosity included in `D_K`.
The output records `∫(P_K-D_K/2)` and its maximum sampled at integration
steps. That sampled maximum is not an upper bound over intermediate
times. A cutoff beyond the finite grid gives a zero tail, so the existence
of a harmless cutoff in this diagnostic says nothing about a cutoff
uniform as the resolution increases.

```sh
python3 labs/full_history.py --n 96 --nz 24 --time .05 --step .0025 \
  --tail-cutoffs 0 2 4 8 16 32
```

Enabling these ledgers leaves the computed velocity and the existing
global integrals unchanged. Direct frequency-mask sums independently check
the binned tail sums and their instantaneous rate identities. The short
run above checks their time-integrated balances; this is an implementation
check, not a bound for the continuum equation.

### Matching the amplitude expansion to the viscous flow

`amplitude_history.py` evolves the complete Taylor hierarchy through
amplitude degree three about the evolving zero-amplitude Galerkin solution.
It uses the same datum, viscosity and domain as `full_history.py`. The
stored `(amplitude degree, axial index)` sectors are
`(0,0), (1,1), (2,0), (2,2), (3,1), (3,3)`; conjugates supply the negative
indices. Every ordered partition, Leray projection and viscous term is
retained. Coefficients multiply `ε^j`, without factorial. The full solver's
axial cutoff must include indices `-3` through `3`, as it does for `nz≥12`.

```sh
python3 labs/amplitude_history.py --n 192 --check-only --check-full-rhs
python3 labs/amplitude_history.py --n 256 --box 14 --viscosity .001 --time 3
python3 labs/full_history.py --n 256 --nz 48 --box 14 --viscosity .001 --time 3
```

The independent RHS check evaluates the full three-dimensional equation
at seven complex amplitudes and extracts its polynomial coefficients.
At grid 192, all six sectors agree within `5.7e-13` in maximum coefficient
error; the largest relative sector error is below `4.6e-14`. The initial
cubic second-time derivative agrees with the independent analytic source
within `8.6e-12`.

The second-order energy coefficients include the pairing of the base with
the generated mean, as well as the squared first variation. They obey
`K2'=-2νY2` and `Y2'=P2-D2`. These are signed coefficients, not positive
energies of separate solutions; in particular `D2` need not be positive.
Initial `(K0,Y0,K2,Y2)=(.25,1,.45,8.25)`. At time 3, with `ε=.1`,
viscosity `.001`, grid 256 and step `.005`:

| Quantity | Quadratic amplitude prediction | Full nonlinear flow |
| --- | --- | --- |
| Enstrophy | 1.08865852248 | 1.09416368675 |
| Integrated signed production | .06369319526 | .07344871144 |
| Integrated enstrophy dissipation | .05753467279 | .06178502470 |
| Production minus half the dissipation | .03492585887 | .04255619909 |

The second-order enstrophy ledger error is below `1.2e-9`. For the fixed
radial test, the scaled cubic prediction is `q_cubic+q_linear/ε²`, approximately
`-1.10743655+3.29226722i`; the full observable is
`-1.01349806+2.95094315i`. Thus suppression of this selected observable
coexists with larger total signed production. The linear term is retained
to expose angular leakage on the periodic square. This test is not an
eigenmode identity for the evolving viscous base.

At time 6, with the same amplitude, viscosity and step, the ordering
changes. The amplitude calculation below uses grid 384. The full runs
use either grid 256 throughout, or its time-3 state padded with zero
coefficients to grid 384 and continued there; both use 48 axial points.

| Quantity | Quadratic prediction | Full grid 256 | Refined continuation |
| --- | --- | --- | --- |
| Enstrophy | 1.2985301083 | 1.2509926620 | 1.2509870179 |
| Integrated signed production | .4426154463 | .4102815673 | .4104244787 |
| Integrated enstrophy dissipation | .2265853380 | .2417889054 | .2419374610 |

Both less production and more dissipation now contribute to the smaller
full enstrophy. The upper-frequency palinstrophy fraction at the endpoint
falls from `.03785` to `.0007433`. This refines only the interval from
time 3 to 6; it is not an independent calculation on grid 384 throughout.
The full-flow enstrophy ledger error is below `1.2e-10`.

The earlier five-branch `cubic_history.py` uses an inviscid stationary
column and continuum angular ancestry. Its difference from a viscous full
flow cannot be attributed solely to nonlinear feedback. Even at zero
viscosity the complete and five-branch calculations differ slightly on a
periodic square: at time one their `q` difference is `6.61e-5` for box 14
and grid 256, versus `1.59e-5` for box 20 and grid 384. Refining box 14 from
grid 128 to 256 does not remove that discrepancy. This is consistent with
the boundary breaking continuous angular symmetry; it is not a certified
boundary-error estimate.

These calculations provide neither an amplitude-remainder bound nor a
continuum error enclosure. They test a finite history and do not establish
an arbitrary-data stretching budget.

### A three-component positive-stretching seed

`triaxial_history.py` starts the full unforced Galerkin equation from the
periodized Gaussian curl

```text
V = curl((0,x*z,2*x*y) exp(-rho)),  rho=x²+y²+z².
```

For the whole-space field, put `g_j=(π/j)^(3/2)`. The exact checker
`python3 -O labs/reynolds_stress.py` gives

```text
E=||V||₂²=13 g₂/8,
||∇V||₂²=9E,   ||∇²V||₂²=99E,
∫ curl(V) · strain(V) curl(V) = 32 g₃/27 > 0.
```

It independently computes the last integral as `-4∫det(strain(V))`.
More generally the potential `(a*y*z,b*z*x,c*x*y) exp(-rho)` has production
`-16(a-b)(a-c)(b-c)g₃/27`. These are spatial identities, not a time estimate.

`python3 -O labs/triaxial_jet.py` separately evaluates the initial rate
of change of the total production in the actual unforced equation:

```text
Pi'(0) = (56064597/82001920) π^(3/2) - ν (128/3) g₃.
```

It keeps the whole-space Leray projection. The pressure contribution is
positive, `(4610503/20500480) π^(3/2)`; the heat contribution is negative.
The proof and the resulting initial interval of increasing production
appear in `papers/ns_symmetry_defect.tex`, in the subsection
"Pressure can initially increase total stretching". The checker uses
Gaussian Fourier moments, including the `1/|k|²` denominator, and verifies
the derivative through both vorticity and strain-determinant formulas.
It gives no uniform interval length or integrated history allowance.

The numerical datum is the Fourier periodization of `A V(κx)` on the
`π`-periodic cube, with `κ=14/π` and `A=κ^(3/2)/sqrt(E)` by default.
The initial Fourier moments are checked against the whole-space formulas.
Energies use physical volume integrals, unlike the axial-average
normalization of the earlier mixed-parent test. The initial squared
velocity norm is one to floating-point accuracy. Time arguments use
`s=Aκt`; the output also gives physical time. Listed cutoffs are in units
of `κ`, and the viscosity argument is the physical viscosity.

```sh
python3 labs/triaxial_history.py --n 96 --check-only
python3 labs/triaxial_history.py --n 128 --time .5 --self-cutoffs 4 6
```

For selected cutoffs the program integrates the tail's own stretching
at every RK stage. This filters all three factors. Full tail production
filters only the recipient, so subtracting self-stretching retains the
work with at least one lower-frequency input. Both are signed; neither
is replaced by its absolute value. The full tail energy balances are
recorded separately. Positive initial stretching or a finite excess does
not refute a history allowance depending on the complete initial datum.
Resolution diagnostics and sampled prefix maxima give no continuum
error enclosure or bound between integration steps.

For the default parameters, at normalized time `.5` on grid 128, the
cutoff-4 self-production integral is `.24783179` and its dissipation
integral is `.29316509`. The excess over half the dissipation is therefore
positive, about `.10124925`. The instantaneous self-production rate at
this time changes from `30.29994` on grid 96 to `30.59047` on grid 128.
This tests absorption at a selected cutoff without an initial allowance.
It does not refute the sufficient budget with a datum-dependent cutoff
and allowance. At normalized time 1, the upper-frequency palinstrophy
fractions are `.1054` and `.07522`; the later history still needs spatial
resolution before its finer-scale behavior can be interpreted.

### Adversarial signed-tail tests

[The forced-tail note](../../../papers/ns_forced_tail_budget.pdf)
([source](../../../papers/ns_forced_tail_budget.tex)) applies the exact
self-stretching / lower-frequency feeding / dissipation split to OpenAI's
constructed forced singularities. At every fixed Fourier cutoff, both
direct force work and lower-frequency feeding have finite absolute time
integrals. The accumulated self-stretching minus even full viscous
dissipation therefore has unbounded upper supremum. The full-field
obstruction is kernel checked in `MettapediaNS.ForcedSignedBudget`; the
Fourier-projector extension in the note is an analytic proof. The force
changes the realized history despite its bounded direct work. This is no
bound on an unforced solution.

The note also treats the quartic caloric functional
`K(u)=(1/nu)*integral_0^infinity ||M(exp(nu*s*Delta)u)||_2^2 ds`, with
`M(u)=curl*(-Delta)^(-1)*P[(curl u.grad)u]`. For the effective force `g=P f`,
its derivative obeys the whole-space estimate

```text
|DK(u)[g]| <= (8*pi)^(-3/4)/nu^2 *
  [(32/3)*||g||_infinity*E^(3/4)*Y^(3/4)
        +16*||curl g||_infinity*E^(5/4)*Y^(1/4)],
E=||u||_2^2, Y=||grad u||_2^2.
```

The velocity energy bound and its integrated enstrophy therefore pay this
force term absolutely on a finite horizon, without an order-two velocity
bound. This shows that the signed caloric nonlinear renewal itself exceeds
every uniform allowance relative to its positive cost on the forced
construction. The analytic proof retains both differentiated parents and
uses Sobolev bounds on the original smooth force; it does not assume that
the Leray projector is bounded on `L_infinity`.
Run `python3 -O labs/caloric_force.py` for exact rational checks of the
complete forced caloric identity on the periodic cube, including forces
with a gradient part. Those checks do not certify the whole-space heat
inequality or a physical-time evolution, and no unforced renewal estimate
is proved.

The caloric return also has an explicit split isolating high-frequency
parents. Let `v=P_(>=K)u`, `T(u)=DK(u)[N(u)]` and
`T_K(u)=DK(v)[P_(>=K)N(v)]`. All three discarded terms are retained in
the exact ledger:

```text
T(u) = T_K(u)
       + DK(u)[N(u)-N(v)]
       + (DK(u)-DK(v))[N(v)]
       + DK(v)[P_(<K)N(v)].
```

The first two corrections obey
`|T(u)-T(v)| <= epsilon*nu*D + C2*Y^2 + C32*Y^(3/2)` for every
`epsilon>0`, with explicit constants fixed by the kinetic-energy cap,
viscosity and cutoff. Since `G=(Y+K(u))/2 >= Y/2`, their contribution is
controlled by an energy-integrable Gronwall coefficient and an arbitrarily
small part of the positive cost. The last correction has an absolute
energy-paid time integral. A bound on the remaining `T_K` with a fixed
initial-data allowance and fraction below one would therefore suffice;
no such high-frequency history bound is established.

The proof uses the bounded ordered quartic heat kernel, with all heat-rate
interference kept. Fourier absolute values are used only for these lower
frequency corrections. It assumes neither a general `L_p` bound for the
sharp ball multiplier nor pointwise domination by a Fourier projection.
The checker verifies the split for four cutoffs and its signed reversal,
including the nonzero low-output contribution `-1937/14400` at `K^2=3/2`.
This is the quintic caloric return, distinct from ordinary tail stretching
and from positive Wiener feeding. On the actual forced construction its
high-frequency budget fails for every fixed cutoff and fraction `<1`;
the corresponding unforced bound remains the open target.

Low outputs of the stretching source `M` have a separate history payment.
They differ from low outputs of the nonlinear direction `N`. Let `K_-`
be the caloric capacity with only stretching outputs below a fixed `J`,
and `Z_-=||P_(<J)M(u)||_2^2/nu`. In the whole space,

```text
K_-(u) <= c_J^2 E^2/(4 nu^2),   Z_-(u) <= c_J^2 E Y/nu,
c_J^2 = J^3/(6 pi^2).
```

The exact physical-time identity `d K_-/dt = -Z_- + DK_-[N] + DK_-[g]`
therefore bounds every signed renewal prefix using energy and smooth
force norms. Arbitrarily high parents remain included. This does not
bound the integral of the absolute renewal.

For an unforced history the kinetic-energy equality improves this to
`K_-(u(t)) + integral Z_- <= c_J^2 E(a)^2/(4 nu^2)`: the remaining
capacity and the spent cost are paid together from the initial energy.
Hence every signed low-output renewal prefix is at most that initial
allowance minus `K_-(u(a))`, independently of the horizon. The factor
`c_J^2` grows with the fixed output cutoff.

Equivalently, set `K_+=K-K_-` and `G_+=(Y+K_+)/2`. Its exact equation is
`2 G_+' + W = DK_+[N] + Z_- + DK_+[g] + 2<Au,f>`, with the original
full positive cost `W`. Combining the two frequency splits leaves
`DK_+(v)[P_(>=K)N(v)]`, where all five velocity parents and both internal
outputs are high when `J=K`. Its history estimate remains open. The
forced construction violates a uniform strict-fraction budget for this
term at every fixed pair of cutoffs as well.

The checker verifies this additional balance, both output splits, and
the periodic bounds with the full low lattice count. A reversed fixture
has positive low stretching renewal `118763/443520`; the history payment
does not assume a favorable instantaneous sign. Nearly opposite parents
with frequency parameters up to one million exercise nonzero low
stretching outputs. These are exact algebra checks, not PDE enclosures.

### Caloric renewal of modes generated by the equation

Run `python3 -O labs/generated_caloric_renewal.py --kida --fft-check`.
The rational checks use the standard library; the optional independent
physical-space checks use NumPy.

Let the three positive parent frequencies be
`p=(3,1,1)`, `q=(1,3,1)`, `r=(1,-1,3)`. Their imaginary Fourier amplitudes
are `alpha*Jp`, `beta*Jq`, `gamma*Jr`, where `Jk=(-k_y,k_x,0)`, with
the corresponding reality partners. All parents lie on squared radius
11, have zero axial velocity, and depend on all three spatial coordinates.
The tail above squared radius 16 is initially empty. Its actual first
derivative is `v1=P_(>=4)N(u0)`; viscosity contributes nothing to that
initial tail derivative.

The program expands the complete degree-ten polynomial in the parent
weights for `T_(4,4)(v1)`. Both internal outputs are high, all parent
orders are retained, and every heat-rate cross term is included.
The polynomial is computed by monomial enumeration, without fitting
sampled values. At viscosity one:

| Parent weights `(alpha,beta,gamma)` | Fully high renewal coefficient | Child enstrophy production |
| --- | ---: | ---: |
| `(1/2,1/2,1/2)` | `-6.976497785277...` | `512/5` |
| `(1/2,1,1/2)` | `164.207550346566...` | `2048/5` |

Thus even planar monochromatic parents do not impose a fixed renewal
sign on their generated children. On the actual smooth evolution,
`P_(>=4)u(t)=t*v1+O(t^2)`. The caloric return is a continuous homogeneous
quintic on smooth Sobolev fields, so its leading physical-time term is
`t^5*T_(4,4)(v1)`. Each nonzero coefficient determines the sign for
sufficiently small positive time, at that fixed datum and viscosity.
The first generated Kida tail, with 96 modes, also has a positive fully
high coefficient; the exact rational value is included in the output.

The checker verifies the actual unforced RHS, exact quartic polarization,
and viscosity dependence. Independent physical convection, stretching
and heat quadrature on grids 32 and 48 agree with the two displayed
renewal coefficients within `4.7e-14` relative error. These are checks of
the leading coefficients, not numerical time enclosures.

Run `python3 -O labs/thin_caloric_renewal.py` for an arbitrarily thin
version. Its parents are

```text
p_m=(m,3,1), q_m=(3,m,1), r_m=(m,1,3),
u_hat(k)=i * weight(k) * Jk/m,  weights=(2,1,1),
Q_m^2=3*m^2/2.
```

They share squared radius `m^2+10`, have axial ratio at most `3/m`, and
have squared velocity norm `E_m=12+92/m^2`. Normalize the initial datum
by `sqrt(E_m)`. For every sufficiently large `m` the initially empty
tail has positive leading fully high renewal:

```text
T_(Q_m,Q_m)(u_m(t))
  = (t^5/nu^2) * [17/(2025*m^3) + O(m^-4)] + O_(m,nu)(t^6).
```

The checker computes this asymptotic by exact rational power series,
retaining affine frequency labels when their leading vectors coincide.
All denominators have nonzero constant terms; every truncated division
is checked by multiplication. Reality, transversality, kinetic transport
cancellation and the stretching/source pairing are also checked.
The scaled-frequency return vanishes through order eight, and its next
two coefficients are `52224/25` and `-7422976/375`. Frequency and amplitude
scaling multiply this series by `m^6`: the first generated velocity gains
one factor of `m`, while renewal is quintic in velocity and has one net
frequency derivative. Dividing by `E_m^5` gives the stated normalization.
Direct rational calculations at
`m=16,64,256,1000000` check the positive sign and the limiting coefficient.

The limits have an order: first fix a sufficiently large `m`, then take
time sufficiently small. No time window uniform in `m` is established.
This refutes automatic nonpositive renewal from generated or arbitrarily
thin planar parents. The coefficient decreases as the family thins, so a
quantitative depletion estimate remains possible. No excess over viscous
cost, failure of the allowed full-datum initial allowance, or obstruction
to arbitrary-data regularity follows. These calculations are not Lean
certificates and do not close the recurrent high-frequency budget.

### Whole-space concentration of generated renewal

Run `python3 -O labs/caloric_localization.py`. The standard-library
checker verifies a strict spectral gap, an exact slowly varying
streamfunction envelope, and the scaling of the complete viscous cost.
The analytic whole-space argument is in the unforced-activation section
of [the tail-budget paper](../../../papers/ns_forced_tail_budget.pdf).

The positive three-parent coefficient above is unchanged when the
squared cutoff is moved from 16 to 14, which avoids every internal
frequency center. For the envelope `phi(X)=1+cos(X)/2`, use
`u_L=(-partial_y,partial_x,0)[phi(x/L)*psi]`, including the derivative of
the envelope. It has 18 initial modes and 58 first generated high modes.
The predicted renewal limit is the original coefficient times
`mean(phi^10)=3308407/262144`. Exact rational computations at `L=16,64`
give relative differences `6.96e-4` and `4.36e-5`, respectively. The
calculations form all outputs and retain every heat-rate cross term.
This is a periodic-envelope check, not a certificate of the continuum
localization limit.

For that limit, replace the periodic envelope by a nonnegative Schwartz
function with compact Fourier support. The strict gaps make the retained
multiplier symbols smooth near each packet. After dividing by the
localization volume, the degree-ten coefficient tends to the positive
periodic coefficient times `integral(phi^10)`. Fix a sufficiently wide
envelope and normalize the initial squared `L2` norm to one. Uniform local
smooth estimates for effective viscosities `delta in [0,1]` then yield a
fixed short interval with positive integrated fully high renewal.

The actual unforced rescaling

```text
u_lambda(t,x) = lambda^(3/2) w_delta(lambda^(5/2)*t, lambda*x),
delta = nu/sqrt(lambda),   Q_lambda = lambda*Q
```

preserves initial energy. On the corresponding shrinking physical prefix,
renewal is at least `c*lambda^3/nu^2`, while the integral of the **original
full cost** is at most `C*lambda^(5/2)/nu`. Consequently, even with an
initially empty tail, no energy-only allowance can work uniformly over
the data and these prescribed cutoffs. The thin family above allows the
initial data to remain planar polarized in an arbitrarily thin Fourier
belt. The order is: fix thinness, then localization, then concentrate.

The cutoff varies with the data. This does **not** exclude a
cutoff-dependent or full-datum allowance, or the existence of a different
cutoff for the same datum. The common local interval is an analytic
existence argument, without a certified numerical endpoint. The script
checks finite Fourier algebra and homogeneities; the localization and
actual-time argument are not Lean theorems. The sufficient recurrent
budget remains open.

### Uniform absorption of separated stretching parents

Run `python3 -O labs/separated_caloric.py`. This standard-library checker
accompanies the separated-parent proposition in
[the tail-budget paper](../../../papers/ns_forced_tail_budget.pdf).
With `A=-Delta` and `M(u)=curl A^-1 P[(curl u . grad)u]`, fix integers
`J>=0`, `r>=3` and the output cutoff `K=2^J`. At an output frequency in
shell `j`, a pair is separated when its maximal parent shell `n` obeys

```text
n >= ceil(3j/2)+r.
```

The mask acts on ordered pairs before their sum. On the whole space,
with `E=||u||_2^2`, `Y=||grad u||_2^2` and `D=||Delta u||_2^2`,
the analytic estimate is

```text
||M_far(u)||_2 <= 10 * 2^(-r) * sqrt(E D),
K_far(u)      <= 50 * 2^(-2r) * E Y / nu^2.
```

Here `K_far=(1/nu) integral_0^infinity ||M_far(exp(-nu s A)u)||_2^2 ds`.
The proof sums the output-to-parent matrix before using total energy.
Both its row and column sums are at most `2^(1-r)`; the enlarged
parent bands have fourth-order overlap at most `17`. The bound has no
factor counting occupied shells. Taking `r` large enough from the
initial energy and viscosity absorbs this source's enstrophy work into
any prescribed positive fraction of the dissipation.

Remove the low-output source and the separated pairs from `M`, giving
`M_keep`, and build its own capacity `K_keep`. The exact balance uses

```text
G_keep = (Y+K_keep)/2,
W_keep = nu D + ||M_keep-nu Au||_2^2/nu,
T_keep = D K_keep(u)[N(u)],

2 G_keep' + W_keep = T_keep + force terms
                    + 2<Au,M_lo> + 2<Au,M_far>.
```

The derivative direction is the **full actual** Navier–Stokes source.
`W_keep` is a modified cost, and the three capacities do not generally
add to the original capacity. The low-output work is absolutely paid.
The existing low-parent estimate also applies to the retained kernel.
For forces and low nonlinear outputs, Fourier `L1` moments provide the
needed bounds without assuming a sharp pair mask is bounded on `L∞`.

The remaining quintic return has every original input and both internal
outputs above `K`. Its outer stretching pairs satisfy
`max(|p|,|q|) < sqrt(2)*2^r*|p+q|^(3/2)`. This imposes no comparability
on the two additional parents inside the differentiated `N` slot.
The signed history of these remaining interactions is open.

The checker retains every heat-rate cross term, tests the matrix bounds
and band overlap, and checks the source partition and modified balance
at two viscosities. Independent quartic polarization verifies the
derivative. The finite periodic norm checks use the separate conservative
lattice constant `200`, rather than the whole-space constant `10`.
The positive first-generation example above remains in the retained core
at `J=2,r=3`, with exactly the same coefficient. These rational checks
are not a Lean certificate or a physical-time enclosure; the uniform
whole-space estimate is proved analytically in the paper.

### Separating the two parents inside the nonlinear direction

Run `python3 -O labs/inner_caloric.py` for the next split. Expand the
retained return in all five original inputs: three occur directly in
the quartic derivative, and two occur inside its `N` slot. Let `m` be
the maximal shell of the first three and `n` the maximal shell of the
last two. For a fixed integer `rho>=4`, select

```text
n >= ceil(11m/8)+rho.
```

The whole-space analytic estimate is

```text
|T_inner| <= 20 * 2^(-4rho) * E^(3/2) * D / nu^2.
```

It pays this entire sector from a prescribed fraction of `nu D`, after
choosing `rho` from energy and viscosity. Each of the four differentiated
quartic kernels is bounded by `1/(2nu^2)`. The three other frequencies
lie in a ball of radius `2^(m+1)`; Fourier `L1` bounds and divergence
form give a factor `2^(11m/2) E^(3/2) E_n`. Summing the parent columns
before using the fourth-order band overlap proves the bound with no
shell-count factor. The remaining return is `T_core-T_inner`; this
algebraic partition does not change the actual evolution or `W_keep`.

The checker compares the full five-input expansion to the independently
evaluated capacity derivative. In that derivative, `N(u)` is formed
first and then heat-evolved at its **output** frequency. Heating its two
parents separately would give the wrong denominator. Cancelling parents
at frequencies `128,8192,2097152` feed the same lower mode and give the
same positive separated return `166548224/(167049575*nu^2)`. Reversing
the velocity reverses this quintic sign. The program also checks the
exact separation boundary and a conservative periodic bound, with
constant `10^6` instead of the whole-space constant `20`.

The previous positive first-generated-mode coefficient survives both
separations unchanged. This estimate pays very unequal parent scales;
it gives neither comparability of all remaining frequencies nor control
of their repeated positive renewal. The sufficient signed history
bound, with full-datum allowances and fixed cutoffs, remains open.

### Paying an isolated pair among all five inputs

Run `python3 -O labs/paired_caloric.py`. In each ordered quintic term,
let `n` be the largest original input shell and `m` the third largest.
After removing the inner-parent sector above, select the terms with

```text
n >= ceil(3m/2)+sigma,     sigma>=4.
```

The analytic whole-space bound is

```text
|T_pair| <= 100 * 2^(-3sigma) * E^(3/2) * D / nu^2.
```

The estimate permits the two high inputs to occupy any of the ten
possible pairs of positions. Frequency conservation places both in one
enlarged high band. Cauchy–Schwarz pays them from that band's energy;
the other three inputs are paid by Fourier `L1` bounds on their smaller
ball. The parent-column sum is at most `(8/7)*2^(-3sigma)`, followed
by the same fourth-order overlap bound `17`. A fixed choice of `sigma`
from energy and viscosity absorbs the result into dissipation.

The selection excludes the already paid inner-parent terms, so the
three-part decomposition has no overlap. The checker retains both
parent-shell labels inside `N`, compares the full sum to the capacity
derivative, and independently checks its inner sector. Sign reversal
and doubling the high amplitudes test the signs and the number of high
inputs. Periodic norm checks use the separate constant `10^7`.

Every remaining term has at least three original input frequencies
above a fixed multiple of the largest frequency to the power `2/3`.
This does not make all five frequencies comparable. The positive
generated-child example lies wholly in this remaining sector, and its
signed physical-time budget remains open. The estimates retain the
full actual equation and provide no autonomous evolution for a group
of modes.

The same checker includes the regular pressure-free shear
`u=(sin y,0,sin x+sin(x+y))`. At `J=0,r=3,rho=sigma=4`, its coupled
return is `161/(19200nu^2)`, while its physical enstrophy production is
`-1/4` and the Euler derivative of `integral |u|^4` is zero. Reversing
the sign of the last sine reverses the two nonzero signs. The actual
viscous evolution is a heat shear transporting a passive scalar and
is globally regular. Positive coupled renewal therefore measures more
than instantaneous amplification or pressure work; the full-datum
history allowance is still essential.

### Repeated positive renewal with a bounded signed primitive

Run `python3 -O labs/shear_caloric_cycles.py`, or add `--fft-check`
for independent physical products, inverse curl and heat quadrature.
The construction uses the normalized `2*pi` torus and the full caloric
stretching functional. It does not construct a singularity.

Choose a smooth shear `U(y)` with flat regions of speeds `+1` and `-1`,
and smooth scalar packets `phi_+`, `phi_-` supported strictly inside
those respective regions. The actual Euler solution is

```text
v(tau) = (U(y), 0, phi_+(y) sin(x-tau) + phi_-(y) sin(x+tau)).
```

Its physical vorticity stretching vanishes. Artificial heat mixes the
separate regions, and the caloric capacity is

```text
K^1(v(tau)) = K_+ + K_- + 2 C cos(2 tau),
T^1(v(tau)) = -4 C sin(2 tau),                  C > 1/512.
```

The analytic construction proves the strict cross-pairing bound first
for step profiles, then transfers it to smooth flat profiles with an
explicit heat-map continuity estimate. Step profiles are not used as
PDE data. Each period contributes `4C` to the positive-part integral
and zero to the signed integral.

The actual unforced viscous flow is a heat-evolved shear transporting
a diffusing scalar. With fixed physical viscosity `nu` and initial
data `alpha*v(0)`, its normalized history stays close to the periodic
Euler reference for `gamma*log(alpha)` turnover times. The comparison
is an analytic Sobolev estimate, not a numerical time enclosure. At
physical time `gamma*log(alpha)/alpha`, for sufficiently large `alpha`,

```text
integral positive_part(T^nu) >= c_nu alpha^4 log(alpha),
abs(integral T^nu)           <= C_nu alpha^4,
integral W^nu               <= C_nu (alpha^2 + alpha^4).
```

The last two bounds hold on every time prefix. Thus the positive-part
budget cannot be paid by any fixed initial allowance homogeneous of
degree at most four, even when the positive cost is also allowed.
The signed budget is paid by the initial shear supremum and scalar
energy. A general full-datum allowance with faster growth is not refuted.

With input/output floor `J=0` and data-selected separations, the same
distinction persists for `T_coupled`: the separated returns and modified
positive cost remain quartically bounded, while positive coupled renewal
accumulates the logarithmic factor. This does not exclude a separately
selected input cutoff. The example has repeated cycles at fixed spatial
scales; it does not supply a frequency cascade.

The checker verifies the rational constants and finite heat pairings.
Its finite Fejer profiles have a checked nonzero plateau-equation
residual and are used only to test the heat formulas. The smooth
construction, viscous comparison and all-prefix bounds in
`papers/ns_forced_tail_budget.tex` remain analytic, not Lean-certified.

### Instantaneous stretching capacity and its viscous defect

Run `python3 -O labs/instantaneous_stretching.py`, or add `--fft-check`
for independent physical products and Fourier derivatives. All means
are normalized on the `2*pi` torus. Write `A=-Delta`,
`M=curl A^-1 P[(curl u.grad)u]` and

```text
Q(u) = <M(u), A^-1 M(u)>/(2 nu^2),
C_grad(u) = sum_j ((partial_j curl u).grad)(partial_j u),
V(u) = -(2/nu) <A^-1 M(u), curl A^-1 P C_grad(u)>.
```

The actual unforced balance for this alternative capacity is

```text
2 G_out' + W = DQ(u)[N(u)] + V(u),   G_out = (Y+Q)/2.
```

Here `W` is the original positive cost. The extra quartic viscous term
cannot be omitted. For the globally regular shear datum
`u_*=(sin y,0,(-1+cos(2y))sin x)`,

```text
Q(u_*)                      = 67/(16000 nu^2),
caloric_capacity(u_*)        = 23/(2400 nu^2),
DQ(u_*)[-nu A u_*]           = 49/(4000 nu) > 0,
DQ(u_*)[N(u_*)]              = 0,
V(u_*)                      = 67/(2000 nu).
```

At `nu=1`, initial data `40*u_*` give `2 G_out'=8160`, `W=77600`
and `V=85760`, while physical enstrophy initially decreases. This
excludes pointwise absorption of `V` by any fraction at most one of
`W`. It does not exclude a signed time-integrated allowance.

The analytic heat-minimality argument in `papers/ns_forced_tail_budget.tex`
also constrains replacements. Every functional vanishing at infinite
heat time and paying at least `||M||^2/nu` along heat dominates the
caloric capacity. Exact payment uniquely determines that capacity.
Thus a quantity depending only on instantaneous stretching, vanishing
when that stretching is zero, cannot provide this heat payment on all
smooth data. A larger initial parent reserve remains possible; the
velocity fourth moment is an example, with signed pressure work left
to control along the actual evolution.

The checker retains all Fourier outputs and both differentiated parents.
Exact rational identities and independent FFT values support the explicit
example; the analytic heat comparison and local PDE implication are not
Lean-certified.

### All-frequency renewal in a polarized belt

Run `python3 -O labs/belt_caloric.py`. Proposition 17 of
`papers/ns_forced_tail_budget.tex` bounds the full quintic caloric renewal
when all original inputs above `K≥1` satisfy, for one real unit axis `n`,

```text
|k·n| ≤ β sqrt(|k|),
|v_hat(k)·n| ≤ β |v_hat(k)| / sqrt(|k|).
```

With `E=||v||₂²` and `D=||Δv||₂²`, the analytic estimate is

```text
|T^ν(v)| ≤ C* β² (β+1)^(3/2) K^(-1/4) E^(3/2) D / ν²,
C* = 30,000,000,000.
```

It holds on the normalized `2π` torus and on `R³`, uniformly over the
number of shells and the axis. Increasing a fixed cutoff therefore
absorbs this class into any prescribed positive fraction of `νD`, for
fixed energy, viscosity and `β`. The constant is conservative.

Both parent orders are paired before estimating. The full generated
velocity, including pressure-generated axial components, is retained.
The nonlinear slot is heat-evolved at its output frequency. Neither
nearly cancelling outputs nor highly separated inner parents are omitted.
Scalar masks imposed after pairing permit the earlier high-output and
separated-sector restrictions.

The exact checker compares the five-input expansion with the existing
derivative and independent quartic polarization. Its 18 finite cases
include initially planar and approximately planar velocities, unequal
frequencies, cancelling outputs and both signs. In one case, full
renewal is approximately `0.131857`, but projecting the generated direction
onto its planar polarization gives `-0.840536`. Incorrectly heat-evolving
its two parents gives `-0.077101`. Thus either shortcut can reverse the
sign. Constant checks and the fixture norm inequalities use rational
arithmetic; a separate intermediate kernel diagnostic uses floating point.

For an actual high field split as `v=w+d`, the estimate pays the quintic
term with all five original inputs from a coherent Fourier selection
`w`. Its generated `N(w)` is still complete. All terms containing an
original defect input `d` remain. This algebraic partition does not
differentiate the selection, so the common axis may change with time.
There is no claim that support or polarization persists, that all
scales may use different axes, or that the remaining signed history
is bounded. The infinite-shell proof is analytic, not Lean-certified.

### Different axes in adjacent shells

Run `python3 -O labs/crossed_belt_caloric.py`. The quantity here is the
quintic caloric renewal. Its two parent families have imaginary Fourier
coefficients `i*(-k_y,k_x,0)` at

```text
(3,1,0), (2,1,0), (1,2,0),
```

and `i*(k_z,0,-k_x)` at

```text
(5,0,4), (-1,0,-4),
```

including their reality partners. The first family occupies shell `(2,4)`
and the second `(4,8)`. Each has exact planar polarization and zero
stretching on its own, while their combined renewal is

```text
T_(2,2)^1(s*A+t*B) = s^3 t^2 * 5469265097437563/230433883895600.
```

The coefficient is positive and survives both high-output masks. The
checker expands every original input by its plane, compares with the
complete derivative and an independent quartic polarization, and retains
all generated modes. Finite normal and common-coordinate envelopes check
the associated resonant moments, with envelope derivatives included.

Proposition 18 in `papers/ns_forced_tail_budget.tex` localizes these two
plane profiles and concentrates them on `R³`. The resulting Schwartz data
have squared velocity norm one. Initially, every occupied dyadic shell has
one exactly planar belt satisfying the preceding square-root-width
condition, with different axes in the two shells. On an actual short
unforced interval at fixed physical viscosity,

```text
integrated fully high renewal >= c lambda^(1/2) / nu^2,
integrated full cost          <= C (nu + 1/nu) lambda^(1/4),
physical interval length      ~ lambda^(-15/4).
```

This excludes a uniform energy-only allowance for these data and prescribed
cutoffs. It also excludes an instantaneous extension of the common-axis
payment to independently oriented shells, even without a decaying cutoff
factor. The whole-space localization and actual time window are analytic
proofs; the executable checks finite Fourier algebra and scaling identities.
No new Lean declarations or axioms are used.

The spectral geometry is an initial property; its preservation is not
asserted. The cutoff varies with the data, and their initial gradient
energy grows as `lambda²`. A full-datum allowance, a different chosen
cutoff, and the signed history of repeated interactions remain open.
This family is proved smooth on the constructed interval; its global
smoothness or a finite-time singularity is not established.

### Kida–Pelz evolution

`kida_pelz_history.py` evolves the real Kida–Pelz initial field

```text
u_x = sin(x) [cos(3y) cos(z) - cos(y) cos(3z)],
u_y, u_z by cyclic permutation,
```

on the `2π`-periodic cube with constant positive viscosity. This is the
explicit three-dimensional singularity-search datum given, for example,
in [Siegel–Caflisch, Physica D 238 (2009)](https://doi.org/10.1016/j.physd.2009.09.016).
Only the real initial field is used; the solver evolves the complete
unforced Navier–Stokes nonlinearity. Its initial physical energies are
`K = 3π³`, `Y = 33π³`, `D = 726νπ³`, and its initial total production is zero.

```sh
python3 -O labs/kida_pelz_check.py
python3 -O labs/kida_pelz_history.py --n 48 --check-only
python3 labs/kida_pelz_history.py --n 384 --backend reflections --time 1.5
python3 labs/kida_pelz_history.py --n 512 --backend reflections --time 1.5
```

The `reflections` backend stores real sine/cosine coefficients on a
midpoint grid in `(0,π)³`. Velocity is odd in its own coordinate and even
in the other two, a symmetry preserved by the equation. `--n` always
means the equivalent **full-cube** grid size. Both backends retain exactly
`|k_j| < n/3`; neither uses hyperviscosity, a moving cutoff, or an averaged
nonlinearity. The reflection representation retains all dynamics in this
symmetry class.

The crosscheck compares both evolved fields on the same shifted nodes,
their complete right-hand sides, signed rates, and integrals through
`t = 0.1` at `n = 48`. Relative field and RHS differences were below
`5e-15`; the largest absolute rate difference was below `3e-12`.
An independent filtered-RHS calculation agrees with the Betchov
self-stretching formula within `9e-14`. Halving the time step from `.004`
to `.002` changes velocity relatively by `1.6e-10`.

Selected cutoffs `4, 8, 12` have self-stretching integrals evaluated at
every RK stage, alongside full tail production and dissipation. Their
difference is the lower-frequency feeding. The output also reports
sampled prefix maxima, energy-balance errors, divergence, peak vorticity,
and the fraction of palinstrophy in the highest retained frequency band.
The default run stops when that fraction exceeds `.005`. This is a
resolution warning, not a continuum error bound. Larger histories require
comparison across grids and time steps; the short consistency checks
establish no endpoint-independent budget.

At `ν = .001`, the prefix through `t = .6` has a positive accumulated
self-stretching excess at cutoff 4. The physical integrals are:

| Full grid | Maximum step | Self-stretching | Half dissipation | Excess | Upper-band palinstrophy fraction |
| --- | --- | --- | --- | --- | --- |
| 128³ | .004 | 9.172723 | 6.231699 | 2.941024 | 1.061e-4 |
| 128³ | .002 | 9.172723 | 6.231699 | 2.941024 | 1.061e-4 |
| 192³ | .002 | 9.172741 | 6.231703 | 2.941039 | 1.141e-6 |

The time-step change shifts the excess by `1.64e-8`; the spatial change
shifts it by `1.45e-5` (about `.00049%`). On the finer grid, the excesses
at cutoffs 8 and 12 are `-2.967180` and `-.870214`, respectively. Most
cutoff-4 tail growth comes from lower-frequency feeding: its integral is
`652.749645`, compared with `9.172741` from self-stretching. Reproduce the
prefix with:

```sh
python3 -O labs/kida_pelz_history.py --n 128 --backend reflections --time .6 --step .004 --report-every .05
python3 -O labs/kida_pelz_history.py --n 128 --backend reflections --time .6 --step .002
python3 -O labs/kida_pelz_history.py --n 192 --backend reflections --time .6 --step .002
```

This is numerical evidence against **zero-allowance** half absorption at
this particular cutoff. The regularity target permits a finite allowance
and a data-dependent cutoff, so this finite positive episode does not
refute it. The comparisons are not rigorous continuum error bounds.

The larger reflection runs both reached their requested endpoint `t = 1.5`
at `ν = .001`, with maximum step `.004`. At cutoff 4 they give:

| Full grid | Steps | Self-stretching | Half dissipation | Excess | Upper-band palinstrophy fraction |
| --- | --- | --- | --- | --- | --- |
| 384³ | 930 | 1393.376317 | 567.953505 | 825.422811 | 2.294e-3 |
| 512³ | 1239 | 1393.383182 | 567.957063 | 825.426119 | 1.002e-4 |

The accumulated excess changes by `.0033073`, about `.000401%` of the
512³ value. At that resolution the cutoff-8 and cutoff-12 excesses are
`-377.905298` and `-370.914789`. Cutoff-4 lower-frequency feeding is
`3537.286275`; it remains larger than the self-stretching integral.
The 512³ final enstrophy-balance residual is `7.59e-8` in absolute value,
and the largest tail-balance residual is `8.76e-8`.

```sh
python3 -O labs/kida_pelz_history.py --n 384 --backend reflections --time 1.5 --step .004
python3 -O labs/kida_pelz_history.py --n 512 --backend reflections --time 1.5 --step .004
```

Neither run triggered the resolution stop. This is a matched spatial
comparison of a finite episode; the endpoint has no separate time-step
refinement or rigorous continuum enclosure. It supplies no uniform
all-prefix allowance and no claim about later evolution.

`kida_pelz_birth.py` checks the first self-interactions in these initially
empty tails with exact rational Fourier arithmetic. It expands the actual
unforced equation in powers of time and viscosity, retaining every
convolution output. For the Taylor coefficients `c_j = u^(j)(0)/j!`,
the recurrence is

```text
(j+1)c_(j+1) = sum_(a+b=j) B(c_a,c_b) - nu*(-Delta)c_j,
B(v,w) = -P[(v.grad)w].
```

The initial 24 modes all have squared radius 11. The complete first
nonlinear source has 96 modes, 24 each at squared radii 20, 24, 36 and 40.
Write `Pi_K = <(-Delta)u_K, B(u_K,u_K)>` and
`D_K = nu*||Delta u_K||_2^2`. **This exact check uses normalized volume**;
multiply its coefficients by `(2*pi)^3` for the physical integrals above.

| Cutoff | First tail velocity | First self-production | First dissipation |
| --- | --- | --- | --- |
| 4 | order `t` | `(67/80)t^3` | `(1773/4)nu*t^2` |
| 8 | order `t^2` | `(731793808705302506334191/520336916998778880000000)t^7` | `(288862741/307200)nu*t^4` |
| 12 | order `t^3` | `-(3373/31850496)t^9` | `(13119731/691200)nu*t^6` |

The displayed self-production coefficients are independent of viscosity.
At cutoff 8, the coefficient of `t^6` vanishes: all modes of the first
tail coefficient have odd coordinates, so three of them cannot sum to
zero. The `t^7` term retains all three placements of the next coefficient
in the cubic pairing. The script checks that its viscosity corrections
vanish. Positive self-stretching can therefore arise entirely from modes
generated by the unforced dynamics. The negative first coefficient at
cutoff 12 gives no sign bound at later times.

```sh
python3 -O labs/kida_pelz_birth.py
python3 -O labs/kida_pelz_birth.py --fft-check
```

The optional check independently builds the first four Euler coefficients
with the full physical-space Lamb product and evaluates stretching by
the strain determinant on grids 48 and 64. Field differences are below
`1.2e-13` relatively, and the three production coefficients agree within
`8e-12` relatively. The rational calculation is not a Lean certificate.
These Taylor coefficients give no certified turnover window, remainder
bound, or allowance for repeated production; the fixed-datum signed
history estimate remains open.

The Lean module `FourierGeneratedTailStretch` supplies a smaller exact
companion example. Its initial support is the six modes
`±(3,1,1), ±(1,3,1), ±(1,-1,3)`, with coefficient
`u_hat(k) = i*(-k_y,k_x,0)/2`. All have squared radius 11, so its entire
initial tail above radius 4 is zero. The complete projected nonlinear
source has five conjugate pairs; its high tail `v` consists of the four
pairs at `±(4,4,2), ±(4,0,4), ±(2,2,4), ±(0,4,-2)`.

With normalized Fourier sums and the common derivative factors omitted,
the kernel certificates give

```text
sum |k|^2 Re(conj(v_hat(k)) . N(v)_hat(k)) = 512/5 > 0,
sum |k|^2 |v_hat(k)|^2 = 1472,
sum |k|^4 |v_hat(k)|^2 = 40704.
```

Both fields are real and transverse. `complete_source` covers every
output, and `actual_generated_tail` identifies the entire high part of
the **infinite unforced velocity right-hand side** as `2*pi*v`, for every
viscosity. The tail's own convection retains all eight input modes and
every output; the pairing needs only its receiving modes because the
tail is zero elsewhere. This certifies positive production of the first
generated tail coefficient. It does not certify the larger Kida Taylor
calculation, a physical-time remainder, or a cumulative-history estimate.

### Escape from a Fourier family over a fixed interval

`escape_history.py --check` tests a quantitative limitation of finite-support
rigidity. [Kishimoto--Yoneda, Theorem 5.1](https://arxiv.org/abs/2110.08039)
classify mean-zero unforced Navier--Stokes flows whose Fourier support stays
finite on an interval: their projected nonlinearity vanishes and they evolve
linearly.
This is a statement about the entire interval, not one instantaneous source.

For a **fixed** finite symmetric family `S`, an energy cap, viscosity and
interval, compactness consequently gives the following qualitative fact.
Among Galerkin trajectories in `S` with net enstrophy growth at least a
fixed positive amount, the time integral of the squared nonlinear source
outside `S` has a positive lower bound. Indeed, zero escaping source makes
the Galerkin trajectory an actual finite-support solution, which can only
lose enstrophy; continuous dependence and compactness then give the bound.
The bound can depend on `S`. The example below first treats projections of
one actual solution. The finite-section comparison at the end also gives
Galerkin trajectories with the same fixed datum and interval, showing that
the dependence on `S` cannot be dropped in the compactness statement.

On the normalized `2*pi` torus take `nu=1/1000`, `0<=t<=1`, and the exact
unforced class

```text
u(t,x,y,z) = (U(t)*sin(y), 0, Re(exp(i*x)*a(t,y))),  U(t)=exp(-nu*t),
a_t = nu*(a_yy-a) - i*U(t)*sin(y)*a,                 a(0,y)=1.
```

The pressure is zero. These are full three-component Navier--Stokes
solutions, independent of `z`; they are not genuinely three-dimensional
singularity candidates. The scalar equation constructs a globally smooth
solution and retains every generated Fourier mode. Writing
`a(t,y)=sum a_j(t)*exp(i*j*y)` gives real coefficients with

```text
a'_j = -nu*(1+j^2)*a_j - (U/2)*(a_(j-1)-a_(j+1)),
a_(-j)=(-1)^j*a_j,              |a_j(t)| <= exp(t)*t^|j|/|j|!.
```

The last bound follows from the convergent iterated Duhamel series: heat
is a contraction on coefficient `l1`, each interaction shifts the index by
one, and the sum of the two shift magnitudes is at most one. This also gives
convergence in every spatial Sobolev norm on each finite time interval.

Let `S_M` contain `(0,+/-1,0)` and every `(1,j,0),(-1,-j,0)` with `|j|<=M`.
Set `v_M=P_(S_M)u`, `N(v)=-P((v.grad)v)`,
`Pi(v)=<-Delta v,N(v)>`, and `D(v)=||Delta v||_2^2`. Every `v_M` below
comes from the same actual solution. The complete nonlinear source of `v_M`
has boundary outputs at `j=+/-(M+1)`, and exactly

```text
R_M := integral_0^1 ||P_(S_M complement) N(v_M)||_2^2
     = integral_0^1 U^2*a_M^2/4
     <= exp(2) / (4*(2*M+1)*(M!)^2).
```

Nevertheless, for every `M>=6`,

```text
F_M := integral_0^1 (Pi(v_M)-nu*D(v_M)) > 1/10.
```

Here is an analytic lower bound, independent of the numerical solver. At
zero viscosity the scalar is `a^0=exp(-i*t*sin(y))` and the full
half-enstrophy at `t=1` is `5/8`, compared with its initial value `1/2`.
The difference from `a^0` satisfies an `H1` energy inequality with growth
coefficient at most `1/2` and forcing norm at most `10*nu` on `[0,1]`.
For example, the first three spatial derivatives of `a^0` have pointwise
magnitudes at most `1,2,5`; also `|U-1|<=nu`. Thus
`||a-a^0||_H1 <= 20*nu`, and the full net half-enstrophy gain is at least
`1/8-(31/2)*nu = 0.1095`.

Projection removes terminal half-enstrophy at most
`9*(1+(M+1)^2)/((M+1)!)^2`. Its unresolved-input work is exactly
`X_M=(U/2)*(1+M^2)*a_M*a_(M+1)`, with

```text
integral_0^1 |X_M| <= 9*(1+M^2)/(4*(M+1)*M!*(M+1)!).
F_M >= 1/8-(31/2)*nu
       -9*(1+(M+1)^2)/((M+1)!)^2
       -9*(1+M^2)/(4*(M+1)*M!*(M+1)!).
```

These bounds use `exp(2)<9` and the factorial tail estimate. At `M=6`
the lower bound is `2059957/18816000 > 1/10`, and the subtracted terms
decrease with `M`. The exact filtered balance retains `X_M`:
`Z_M(1)-Z_M(0)=F_M+integral X_M`.

Consequently no modulus tending to zero with `R_M`, independent of the
family, bounds `F_M`, even with this fixed datum, viscosity and interval.
More specifically, `F_M <= C*M^p*R_M^alpha` fails for every fixed finite
`C,p` and every `alpha>0`. Taking any fixed number of spatial derivatives
of the escaping source only introduces another polynomial factor, so it
does not repair such an estimate.
Integer Navier--Stokes scaling `u_L(t,x)=L*u(L^2*t,L*x)` places the whole
example above any prescribed lower frequency cutoff: all frequencies have
length at least `L`. Both displayed integrals scale by `L^4` on
`[0,1/L^2]`. The example therefore does not rely on lower-frequency feeding
into that high tail. It does **not** exclude an additive initial-data
allowance or prove that repeated growth is unbounded. It limits a uniform
deduction from qualitative support rigidity; the sufficient signed-history
budget remains open. Here the family grows while the energetically active
part of the flow stays essentially fixed. No claim is made about a bound
restricted to minimal active families or to annuli of fixed relative width.

The numerical checker uses one reference history for all family projections,
with `b_j=(-1)^j*2^j*j!*a_j` to avoid losing tiny boundary coefficients to an
absolute ODE tolerance. For reference order `R`, the iterated Duhamel series
bounds the `H1` error of the exact finite-section trajectory by
`2*sum_(n>=R+1) (1+n)/n! <= 6*(R+2)/(R+1)!` on `[0,1]`: the two series
agree until a path can leave the reference indices. This bound does not
include numerical integration error.

It also proves the claim about Galerkin trajectories: write `a^[M]` for
the scalar evolved with indices restricted to `|j|<=M` from the same initial
datum. Its distance in `H1` from the actual scalar is at most
`delta_M=6*(M+2)/(M+1)!`. Combining this with the Euler comparison gives
`||a^[M](1)||_H1 >= sqrt(3/2)-20*nu-delta_M`. Consequently its net
half-enstrophy growth is at least
`1/8-(31/2)*nu-(3/4)*delta_M`. For `M>=6` this is at least
`1433/14000 > 1/10`. The factorial bound on each coefficient, and hence the
displayed upper bound on the escaping source, also holds for this finite
section. Thus the fixed-family compactness bound has no family-independent
modulus. This argument distinguishes these Galerkin trajectories from
the projections `v_M` of the actual PDE history above.

Reference orders 32 and 40, halved maximum steps
and increased quadrature agree in `F_M` within `1.4e-17`; relative differences
in `R_M` are below `2e-11`. The complete filtered ledger has residual below
`2e-16`. A separate physical-space convection and vorticity-stretching check
at `M=6` agrees within `3e-17`, with relative escape error below `5e-13`.
For example, `F_6=0.12335688758`, `R_6=8.23e-12`, while
`F_20=0.12335688759`, `R_20=6.86e-52`. These are numerical diagnostics;
the analytic inequalities above, including their rational final comparison,
are not a Lean certificate or a numerical interval enclosure.

### Bent antiparallel vortex tubes

`bent_tube_history.py` supplies a second, explicitly defined concentration
geometry on the same periodic cube. For radius `a`, separation parameter
`d`, bend `b`, and positive integer `m`, set

```text
eta(y) = d - b cos(my),
F+ = exp([cos(x) + cos(z-eta(y)) - 2]/a^2),
F- = exp([cos(x) + cos(z+eta(y)) - 2]/a^2),
omega = Gamma (0, F+ - F-, eta'(y) (F+ + F-)).
```

The y and z derivatives cancel in `div omega`, and the mean vanishes.
The velocity is `curl(-Delta)^(-1) omega`; `Gamma` normalizes kinetic
energy after Fourier truncation. This analytic periodic family consists
of two bent tubes with opposite orientation. The tangent is used with
its displayed parameterization, without division by its speed, to retain
the divergence cancellation. It is not a reproduction of a named
Hou or Kerr dataset.

The defaults `a=.2, d=.5, b=.15, m=2` give kinetic energy `3π³`, initial
enstrophy about `1019.726117`, and peak vorticity about `36.8`. The
viscosity and kinetic energy match the Kida test above. The two reflection
planes preserved by these data reduce storage to `n × (n/2) × (n/2)`,
using Fourier coefficients in x and sine/cosine coefficients in y and z.
The equation, strict two-thirds truncation, RK-stage signed accounting,
and resolution warning are unchanged.

```sh
python3 -O labs/bent_tube_check.py
python3 -O labs/bent_tube_history.py --n 128 --check-only
python3 -O labs/bent_tube_history.py --n 96 --time .5 --report-every .025
python3 -O labs/bent_tube_history.py --n 128 --time .5 --report-every .025
```

The independent full-Fourier comparison includes evolved fields and
right-hand sides at `n=64, a=.35, t=.02` and at `n=96, a=.2, t=.002`.
Relative field and RHS differences were below `3e-15`; signed rate
differences were below `2e-13`. The independent filtered-RHS stretching
agrees with the strain-determinant formula within `1.2e-13`. Halving the
time step changes velocity relatively by less than `4.7e-10`. At n=128,
the initial reconstructed vorticity differs from the analytic profile by
`9e-15` relatively. These are consistency checks; interpreting later
history requires comparison across grids and time steps.

For the default tube data at `t=.1`, integrated self-stretching is below
half the accumulated dissipation at all three measured cutoffs. At cutoff 4:

| Full grid | Maximum step | Self-stretching | Half dissipation | Excess |
| --- | --- | --- | --- | --- |
| 96³ | .001 | 1.053966 | 2.388679 | -1.334713 |
| 96³ | .0005 | 1.053966 | 2.388679 | -1.334713 |
| 128³ | .001 | 1.054208 | 2.388687 | -1.334478 |
| 192³ | .001 | 1.054218 | 2.388687 | -1.334469 |

Time-step refinement changes the excess by `6.18e-8`. Spatial refinement
from 96 to 128 changes it by `2.35e-4`, and from 128 to 192 by `9.83e-6`.
On grid 192, the cutoff-8 and cutoff-12 excesses are `-.793243` and
`-.106208`, and the upper-band palinstrophy fraction is `5.70e-7`.
The additional checks are:

```sh
python3 -O labs/bent_tube_history.py --n 96 --time .1 --step .0005 --report-every .025
python3 -O labs/bent_tube_history.py --n 192 --time .5 --step .001 --report-every .025
```

The 96³, 128³ and 192³ longer runs stop at their resolution warnings at
`t=.175`, `t=.2` and `t=.25`, respectively. At `t=.225`, the last
below-warning report on grid 192, the cutoff-4 excess is positive
(`.716234`), with upper-band palinstrophy fraction `.003904`. Both coarser
grids have already stopped, so this later sign change lacks a matched
spatial refinement. The negative shared prefix must not be extrapolated
to that interval. Enstrophy remains close to its initial value in
the shared prefix, so this result does not establish control of a strong
growth episode. Neither this negative prefix nor the positive Kida prefix
settles the endpoint-independent finite-allowance budget.

### Simultaneous stretching and mean-circulation gain

Run `python3 -O labs/helical_mean_feedback.py`; this checker requires Sympy.
It compares the real helical streamfunction profiles

```text
f₀(r) = r² exp(-r²)
f₁(r) = r² exp(-r²) [1 + (r²-1)³].
```

They agree through two radial derivatives at radius one. Their initial
velocities and first spatial derivatives therefore agree on that cylinder.
The complete pressure response nonetheless makes the original mean peak's
acceleration negative for the first profile and positive for the second.
The latter also has strictly positive full signed enstrophy curvature.
The proof gives the exact lower bounds `105/(128 e³)` and `1053π/128` for
the respective quadratic coefficients.

The checker retains every pressure and vorticity component. It verifies
the stress identity, exact resolvent decompositions, heat primitive,
positive polynomial coefficients in the production integral, and the
horizontal energy normalization. The integral signs and the local
evolution are analytic arguments in Propositions 11–13 and Corollary 14
of the accompanying note; they are not Lean theorems.

Corollary 14 realizes simultaneous net enstrophy gain and mean-peak gain
on a uniform short normalized interval of unforced viscous whole-space
flows. The energy and critical defect history stay bounded across that
family. This excludes automatic drainage of the maximum mean circulation
as compensation for every stretching event. The peak increase remains
finite and of the same order as the defect-history allowance; it does not
establish recurrent growth within one datum or refute a bound depending
on the full initial datum.

### Persistent mean geometry suppresses one competing phase

Proposition 15 of the note extracts a conditional control result from the
same exact mixed-parent coefficient. Give the two fixed Gaussian parents
independent complex amplitudes `a,b`, with `|a|,|b| ≤ 1`, and use the
scaling with `δ=λ^(-2h)` and initial squared energy at most one.
Let `Mλ` measure the normalized axial
second derivative of the actual angular mean at the common short time,
over one fast axial period near the original peak. Then

```text
|a|² |b| ≤ C (1+Mλ) δ².
```

The proof uses exact symmetries of the nonlinear evolution: the fast mean
vanishes if either parent is absent and is even in the first amplitude.
Finite mixed amplitude derivatives therefore control its third time
derivative by `C |a|² |b|`. The nonzero second time derivative from
`mixed_helical_parent.py` persists on a common short interval. Averaging
along the actual spatial trace, including its slowly changing envelope,
then gives the displayed bound.

Deleting the smaller initial parent, without renormalizing the reference,
produces another actual unforced flow with

```text
∫ ||u-v_reference||∞² dt ≤ C (1+Mλ)^(2/3) λ^(-2h/3).
```

Thus bounded mean geometry makes this critical comparison history tend
to zero. This is an analytic restricted-family result, not a new Lean
theorem. The reference still has a slow envelope, and the error is not
the angular fluctuation `u-Pu`. No arbitrary-data decomposition, repeated
reference selection, or global budget for the retained parent follows.

### Delayed mean production limits that reduction

Proposition 16 uses angular indices `6,8`, both with axial phase index
one. A product with zero angular index and nonzero axial index needs
at least seven parent factors: `6a+8b=0` forces `a=4k,b=-3k`.
The Lean module `MettapediaNS.HelicalPhaseSelection` certifies this
integer statement, the sharp order-seven witness, and the general
lower bound `2k+1` for adjacent indices `2k,2(k+1)`. It asserts no
nonzero interaction coefficient or PDE estimate.

Finite amplitude derivatives of the actual unforced evolution then
bound its fast angular mean by `C ε⁷`. With `ε=√δ`, that is small
enough to preserve every prescribed mean derivative through order two.
Yet deleting either parent has critical comparison history bounded
above and below by positive constants, uniformly as the initial relative
angular defect tends to zero. The full angular fluctuation has the
same property. Thus the vanishing comparison conclusion of Proposition
15 depends on its particular low-order interaction; it cannot be
extended to arbitrary pairs of profiles using these mean bounds alone.

Run the exact Gaussian normalization check with:

```sh
python3 -O labs/helical_phase_delay.py
```

The script uses rational arithmetic from the Python standard library.
The PDE construction is analytic and restricted to a common short
normalized interval. It does not refute the conditional regularity
criterion, since the histories remain finite, and does not establish
repeated concentration from one fixed datum.

Corollary 17 strengthens this limitation to any fixed finite number `K`
of mean derivatives. Adjacent angular indices `2K+2,2K+4` delay the fast
mean to amplitude order `p=2K+3`. Taking `ε=δ^((K+1)/p)` makes that
mean small enough for every prescribed derivative through order `K`,
while the actual critical fluctuation history and both deletion-reference
histories are comparable to `λ^(2h/(2K+3))`, which diverges. The initial
squared energy stays at most one and the relative defect tends to zero.
Constants depend on `K`. This is an analytic family obstruction to a
uniform estimate from these inputs; the higher initial norms grow, so
it does not refute an allowance depending on the full initial datum.

### Testing the first permitted fast mean

`helical_mean_jet.py` computes the first permitted interaction for the
normalized Gaussian parents of angular indices `m,m+2`, with even `m`.
For `m=6`, four copies of the positive first parent and three copies of
the conjugate second parent have labels `(0,1)`. All 19 ancestral words
inside that parent count are retained, including every ordered binary
partition and every intermediate pressure projection.

The recursion computes the coefficient of `t^6` of parent amplitude
degree seven. Background interactions and viscosity would require an
additional time derivative, so they do not enter this coefficient.
It is a time coefficient, not the sixth derivative: no extra factorial
is included. With real parent amplitudes `ε`, its contribution and its
conjugate are `ε⁷ Re(U exp(2iz)) t⁶/64`.

```sh
python3 labs/helical_mean_jet.py --calibration
python3 labs/helical_mean_jet.py --n 256
python3 labs/helical_mean_jet.py --n 256 --form advection
python3 labs/helical_mean_jet.py --n 384 --box 20
```

The calibration recovers the known cubic circulation coefficient
`-16/(5 exp(3))` at radius one with relative error `4.7e-13`.
For the normalized `6,8` parents the coefficient is:

| Horizontal grid | Side length | Real mean circulation at radius one | Recipient velocity norm |
| --- | --- | --- | --- |
| 256 | 14 | -0.00853258187 | 2.1117880420 |
| 384 | 14 | -0.00853258374 | 2.1117880420 |
| 384 | 20 | -0.00853258246 | 2.1117873529 |
| 512 | 28 | -0.00853258187 | 2.1117873136 |

The norm is `sqrt(∫ |U|² dx_h/(2π))`. The independently evaluated
advective and vorticity forms at grid 256 agree in the radius-one
coefficient within `2.2e-13`. The circular observable uses the exact
Bessel integral of the retained Fourier polynomial, rather than angular
sampling. The output also reports other radii, the upper-frequency
velocity fraction and the divergence defect.

This is evidence that the first permitted coefficient does not cancel,
not a rigorous continuum nonvanishing certificate. The periodic square
only approximates the continuum angular symmetry, and neither grid nor
box comparison supplies an error enclosure. No positive-time lower
bound, sustained signed stretching or repeated cascade follows from
this coefficient alone.

### Full signed work during delayed mean production

Corollary 18 shows that the same family can raise its mean circulation
above the initial global maximum and increase its total enstrophy,
while retaining all the bounds in Corollary 17. The gains are at least
`c λ^(2h/(2K+3))` and `c λ^(1+4h+2h/(2K+3))`, respectively. Integrated
viscous enstrophy dissipation is at most `C ν λ^(1+4h)`.

The general Gaussian parent of angular index `m ≥ 6` has both a positive
initial circulation acceleration and positive total enstrophy curvature.
The calculation keeps the complete pressure term, which has a negative
part. An explicit rational bound pays that part using the remaining
signed production; a polynomial with positive coefficients proves the
margin for every integer `m ≥ 6`. Check the identities with:

```sh
python3 -O labs/helical_high_mode_feedback.py
```

The module `MettapediaNS.HelicalHighModeFeedback` separately kernel-checks
positivity of the circulation heat bracket and the strict inequality
for the rational negative-pressure allowance. It proves these algebraic
inequalities, not their PDE interpretation.

The Python checker requires Sympy. Its exact initial identities support the
analytic time argument: finite amplitude derivatives have a uniform
remainder, the quadratic coefficients have zero axial phase, and the
viscosity and slow-envelope errors are smaller than `ε²`. These estimates
give a common short interval of actual unforced whole-space solutions.
They do not construct a recurrent cascade. Initial higher norms grow
faster than the finite gains, so a full-datum history allowance remains
an open possibility.

### A parent velocity need not decorrelate

Proposition 19 gives an exact obstruction in the inviscid linearization
about the Gaussian swirl. For an angular mode `m≥3` and axial wave number
two, write its cylindrical coefficients as `(A,B,C)` and set `Q=2rB-mC`.
The full pressure cancels:

```text
Q_t + i m Ω Q = -2r ζ A,
Ω=2 exp(-r²),  ζ=4(1-r²) exp(-r²).
```

At radius one, `ζ=0`, so `|Q|` stays constant. For the normalized Gaussian
parent the real velocity supremum on that circle is therefore at least
`2(m-2)/(e sqrt(d_m) sqrt(4+m²))`, with `d_m=(m+1)!/2^(m+1)`.
Its squared velocity history grows at least linearly in time.

The viscous linearization about the actual heat-evolved swirl stays within
`C η (1+t)² exp(Ct)` of the inviscid parent in a fixed high Sobolev norm.
Its squared velocity history through time `a_m log(1/η)` is therefore
at least `b_m log(1/η)` for small positive viscosity `η`. Hence these
histories have no bound uniform in both time and viscosity.
This is a linear-variation statement on the periodic
cylinder; it neither controls a nonlinear remainder on a growing interval
nor constructs a whole-space cascade.

`MettapediaNS.HelicalParentMomentum` kernel-checks the pressure cancellation,
the scalar ODE's norm conservation and the Gram inequality. The cylindrical
PDE interpretation and the viscous convergence argument remain analytic.

### Persistence through a growing number of turnover times

Corollary 20 extends the parent lower bound to actual nonlinear whole-space
flows. Fix the number `K≥2` of controlled mean derivatives and choose
`0<σ<1/2`. With `p=2K+3`, `δ=λ^(-2h)` and
`ε=δ^((K+1+σ)/p)`, the normalized two-parent family remains smooth and
retains every prescribed mean derivative bound through normalized time
`a log(1/δ)`. Throughout that interval its angular fluctuation, and its
difference from either one-parent deletion reference, have velocity
supremum at least `c A ε`. Each squared velocity history is consequently
at least `c λ^(2h(1-2σ)/(2K+3)) log λ`.

The proof keeps the evolving nonlinear flow close to its stationary
extended reference for this logarithmic interval. Finite amplitude
derivatives grow at most exponentially, and the spare exponent `σ`
pays this growth in the delayed fast mean. The first derivative is
compared to the inviscid parent after applying the same Leray projection;
both sides of the energy comparison are then divergence-free. On the
nonzero parent axial phases, the existing projector estimate controls
the comparison by `δ` times one slow axial derivative. No such operator
estimate is assumed on the zero phase.

This is an analytic nonlinear persistence result, with fixed positive
physical viscosity and squared initial energy at most one. The time
window in physical units still shrinks across the family, higher initial
norms grow, and no infinite recurrence within one datum follows. The
conclusion concerns velocity history, not the sign of accumulated
stretching over the longer interval.

### A growing circulation peak can export energy

Proposition 21 changes the radial phase of the original Gaussian defect to
`P(q)=20q-15q²+4q³`:

```text
W = curl([(x²-y² + 2xy P(r²)) exp(-ρ)] e_z).
```

Its global nonlinear kinetic transfer into the Gaussian mean is
`T=-320(π/3)^(3/2)/27`, although its circulation torque and the torque's
radial derivative at the initial peak are `16/e²` and `-64/e²`.
The full Cartesian calculation and Gaussian integrals are checked by
`python3 -O labs/reynolds_stress.py`.

The analytic uniform local construction then gives actual unforced flows
on a short normalized interval during which the mean exports kinetic
energy to the fluctuation, its kinetic energy decreases, and its circulation
peak grows while moving inward. The fluctuation's kinetic energy increases
as well, after choosing concentration large enough to pay viscous loss.
Initial squared energy is at most one, relative angular defect can be
arbitrarily small, and the mean geometry bounds persist on that interval.

Initially the angularly averaged exchange density is negative at every
positive radius, since `P'(q)=12(q-5/4)²+5/4>0` and the mean shear is
negative. At the peak the unscaled local nonlinear work is `32/e³`: exchange
contributes `-16/e³` and the spatial flux divergence contributes `48/e³`.
The checker retains this flux identity. The pointwise sign is an initial
statement; persistence is proved for the global transfer.

In particular, the positive peak increment cannot be bounded solely by
a constant times `∫ max(T,0) dt`: that integral is zero on this interval.
Local concentration and global kinetic energy have different signs here.
This is an analytic finite-event result, not a Lean theorem, an estimate
of total enstrophy production, or a refutation of a full-datum allowance
for repeated concentration.

### A kinematic path satisfying the energy inequality

A separate time-dependent rescaling of `W_+` has zero mean and unit initial
squared velocity norm. For `0<h<1/4`, put `α=1/2-2h`,
`c²=160ν/(3α)`, `d²=8ν/α`, and
`A₀=((9/2)(π/2)^(3/2)c²d)^(-1/2)`. The prescribed path is

```text
u(x,-τ) = A₀ τ^(-1/2-h/2) W_+(x_h/(c√τ), z/(d τ^(1/2-h))).
```

Its energy and dissipation satisfy the exact formulas

```text
E=||u||₂²=τ^α,
(1/2)E' + ν||∇u||₂² = αE(τ^(2h)-3)/(8τ) < 0,
ν ∫[-1,0] ||∇u||₂² dt = (1-2h)/4.
```

Nevertheless its critical defect history diverges, and the normalized
stress on each fixed-ratio time interval stays positive. The script checks
these scaling identities. This path is **not a Navier–Stokes solution**:
its strict energy loss violates the equality for an unforced smooth flow,
and a force would be needed to cancel its nonzero mean Reynolds torque.
It shows only that energy inequality, finite dissipation and mean geometry
alone cannot pay the required stress history.

### Hidden forcing in a heat/HJB observation

`heat_observation.py` checks an explicit positive heat solution on an auxiliary
circle and the fluid equation satisfied by its observed derivative. It requires
SymPy and runs with:

```sh
python3 -O labs/heat_observation.py
```

For `nu > 0`, `t >= 0` and `|a|+|b| < 1`, set

```text
Phi(t,theta) = 1 + a exp(-nu t) sin(theta) + b exp(-4 nu t) sin(2 theta),
W = -2 nu log(Phi),
v(t) = -W_theta(t,0) = 2 nu (a exp(-nu t) + 2b exp(-4 nu t)).
```

The heat equation for `Phi` and viscous HJB equation for `W` hold exactly.
The mean-zero periodic velocity `u = v(t) sin(y) e_x` is incompressible, with
zero convection, but its Navier--Stokes residual is

```text
u_t + (u . grad)u - nu Delta u = f(t) sin(y) e_x,
f(t) = v'(t) + nu v(t) = -12 nu^2 b exp(-4 nu t).
```

The residual's curl has third component `-f(t) cos(y)`, so pressure cannot
remove a nonzero residual. Taking `a=epsilon`, `b=-epsilon/2`, with
`0 < epsilon < 2/3`, gives `u(0)=0` and `v'(0)=6 nu^2 epsilon > 0`.
This is a forced fluid path obtained from an unforced auxiliary heat equation;
it is not an unforced Navier--Stokes counterexample.

Retaining the second mode restores the exact history: `f'=-4 nu f`, or,
after eliminating it, `v''+5 nu v'+4 nu^2 v=0`. The sector `b=0` is invariant
and does give genuine unforced shear solutions. With
`c=a exp(-nu t)`, `d=b exp(-4 nu t)`, the full-state reserve satisfies

```text
Q = c^2+d^2 >= 0,
Q' = -2 nu c^2 - 8 nu d^2 <= 0,
20 nu^2 Q - v^2 = 4 nu^2 (2c-d)^2 >= 0.
```

This reserve includes hidden initial data. It is positive even when the
counterexample's entire physical initial velocity is zero. A physical
initial-data allowance therefore requires a compatible lift, not just a
bound on arbitrary auxiliary heat data.

There is also an analytic obstruction to any fixed finite time-jet summary
of unrestricted heat potentials. For every integer `m >= 0`, heat-evolve
`Phi(0,theta)=1+epsilon sin(theta)^(2m+3)`, with `0 < epsilon < 1`.
Oddness gives `Phi(t,0)=1`, and differentiation of the heat equation gives

```text
v^(r)(0) = 0                 for 0 <= r <= m,
v^(m+1)(0) = 2 epsilon nu^(m+2) (2m+3)! > 0.
```

These identities follow for all `m` from the order of vanishing of the odd
power. The program independently checks its finite Fourier expansion,
positivity margin and derivative moments for `m=0,...,12`. Thus the observed
finite jet can agree with the constant solution while its next derivative
differs. This excludes evolution laws based only on that jet for the full
unrestricted class; it does not exclude summaries retaining hidden modes or
an invariant compatible class of lifts.

Finally, a cubic perturbation of a potential leaves its first two derivatives
at the observation point unchanged but can change the observed HJB velocity
derivative. The script checks this with a nonconstant, noncommuting frame,
both at zero potential and at a nonzero seed. It also checks that a normalized
chart change `theta -> theta+epsilon theta^3` preserves the initial observation
of a chart-linear potential while changing its predicted acceleration.
These are exact finite-dimensional differential identities. An application
to an infinite-dimensional stochastic flow additionally needs generator
domains, convergence, and solution regularity; none is asserted by this lab.

### A transported-frame metric and its fluid-derived HJB equation

`transported_frame_metric.py` checks a different construction based on
actual vector transport. For `D = partial_t + u . grad - nu Delta`, let

```text
D v = B v + f,
D M = B M + M B^T,
Q = M^(-1),
q = v^T Q v,
r_j = partial_j v - (partial_j M) Q v.
```

For a symmetric positive definite tensor `M`, the exact identity is

```text
D q = 2 v^T Q f - 2 nu F,
F = sum_j r_j^T Q r_j >= 0.
```

For smooth unforced Navier--Stokes, use its actual vorticity `v=omega`,
its actual gradient `B=grad u`, and `f=0`. The tensor is the uncentered
second moment of transported frame vectors, rather than their centered
covariance. With a common spatially constant Brownian translation, the
quadratic-variation terms give precisely the Laplacian of this second
moment. These statements concern each smooth existence interval; they
do not construct an evolution beyond a candidate singular time.

`StochasticLagrangian.TransportedFrameMetric` kernel-checks the matrix
algebra and the nonpositive sign of the unforced production. Its rates
and gradients are explicit inputs. The construction of the random frame,
differentiation of its expectation, inverse-matrix differentiation and
parabolic comparison remain analytic here.

The identity also gives a concrete HJB observable. For a fixed `eta>0`,
put `Psi=-2 nu log(q+eta)`. Then

```text
D Psi + |grad Psi|^2/2 = 4 nu^2 F/(q+eta) >= 0.
```

The drift and geometric source are supplied by the same fluid and frame.
This is a PDE identity, not an assertion that arbitrary fluid data solve
an independently prescribed minimum-action bridge problem. A control in
the scalar HJB representation changes auxiliary sampling paths; it is not
automatically an admissible change of the physical fluid velocity.

The remaining comparison is essential. Define the directional factor
`kappa=|omega|^2/q` wherever `omega!=0`, and set it to zero at zeros.
For `M(0)=I`, comparison gives `q<=||omega(0)||_infinity^2`; hence a bound
on the time integral of `sup_x sqrt(kappa)` would bound the vorticity
integral. No arbitrary-data bound on this factor is proved here.
Controlling `q` alone does not control Euclidean vorticity: the matrices
`M=diag(lambda^2,lambda^(-2),1)` and vectors `v=lambda e_1` have
`det M=1` and `v^T M^(-1)v=1`, while `|v|^2=lambda^2`. This is a matrix
example, not a fluid trajectory.

The checker retains two exact physical tests:

* For the periodic unforced shear `u=A exp(-nu t) sin(y) e_x`, the frame
  starting at `I` is `[[1+c,b,0],[b,1,0],[0,0,1]]`, where
  `b=A t exp(-nu t) cos(y)` and

  ```text
  c=A^2(I0+I2 cos(2y)),
  I0=(1-(1+2 nu t)exp(-2 nu t))/(4 nu^2),
  I2=((2 nu t-1)exp(-2 nu t)+exp(-4 nu t))/(4 nu^2).
  ```

  Its determinant excess `c-b^2` has nonnegative heat source
  `2 nu |partial_y b|^2`. Also `I2>=0` and
  `I0+I2=(1-exp(-2 nu t))^2/(4 nu^2)`, giving the uniform trace bound
  `3+A^2/(4 nu^2)`. Actual vorticity lies in the unchanged third direction,
  so `kappa=1` wherever it is nonzero. A tensor initialized instead at
  `omega(0) omega(0)^T+delta I` has directional factor at most
  `delta+A^2`; its third component is the heat evolution of the initial
  squared vorticity plus `delta`.
* For the exact unforced Beltrami flow
  `u=A exp(-nu t)(sin(z)+cos(y), sin(x)+cos(z), sin(y)+cos(x))`, the
  checker verifies the pressure `p=-|u|^2/2`, the curl, and the initial
  frame production. At the origin, initial physical stretching is
  `omega . (grad u) omega=3A^3`. For the frame initialized at `I`,
  `partial_t kappa(0,0)=2A`, positive for `A>0`. Thus the directional
  factor need not decrease even on an actual globally regular flow.

The second test uses the tensor's initial derivative, not a computed
positive-time tensor solution. The general identity is also checked by
directly differentiating rational matrix expressions with arbitrary
specified first and second spatial jets, including a nonzero forcing.
The checker requires SymPy:

```sh
python3 -O labs/transported_frame_metric.py
```

### Directional conversion and the pressure history it must retain

`transported_frame_direction.py` checks the next comparison explicitly.
Write `s=|omega|^2`, `q=omega^T M^(-1) omega`, `G=|grad omega|^2`, and
`stretch=omega . (grad u) omega`. Where `q>0`, put `kappa=s/q`. Then

```text
(D - 2 nu grad(log q) . grad) kappa
  = (2 stretch - 2 nu G)/q + 2 nu s F/q^2.
```

Using `(s+eta)/(q+eta)` with one fixed `eta>0` makes the quotient positive
and smooth even at vorticity zeros. Replace `s` and `q` by `s+eta` and
`q+eta` in the identity; their parabolic rates are unchanged. If this
quotient is bounded by `K` and `q<=C`, then `s<=K(C+eta)`. Thus a bound
for one fixed regularizer suffices, without a zero-regularizer limit.
The Lean module proves this scalar comparison. The direct
rational-jet check retains arbitrary prescribed spatial Hessians of the
vector and tensor. The diffusion loss `F` increases this quotient; it
cannot simply be counted as damping. At the initial frame `M=I`, both
scalar fields and their gradients agree and `F=G`, giving the initial
directional rate `2 stretch/s` independently of viscosity.
For the regularized quotient it is `2 stretch/(s+eta)` instead.

There is an analytic control representation on each fixed smooth periodic
interval. Write `S=s+eta`, `Q=q+eta`, `k=S/Q`, and

```text
w = u - 2 nu grad(log Q),
V = (2 stretch - 2 nu G)/S + 2 nu F/Q.
```

Then `(partial_t+w.grad-nu Delta)k=Vk` and `k(0)=1`. For paths starting
at `Y_0=x` with drift `-w(t-r,Y_r)+beta_r` and diffusion `sqrt(2nu)`,

```text
log k(t,x) = sup_beta E integral_0^t [V(t-r,Y_r)-|beta_r|^2/(4nu)] dr.
```

Ito's formula and completion of the square prove the inequality and its
attainment at `beta=2nu grad(log k)(t-r,Y_r)`. All coefficients and this
feedback are smooth and bounded on the fixed compact interval. The Lean
module checks the Hamiltonian square, its upper bound and maximizing
control; the stochastic verification remains analytic. This is the usual
logarithmic control representation, with the coefficients here derived
from the actual fluid; see also
[Lehec, Section 2.4](https://arxiv.org/abs/1006.3028).

The optimal total sampling drift simplifies to
`-u+2nu grad(log S)`: the scalar frame normalization cancels. The sampling
drift is generally compressible and is not a freely chosen physical fluid
velocity. Neither the value representation nor smooth-prefix boundedness
gives a bound uniform up to a possible singular time. Such a bound still
requires the coupled geometric and pressure history.

The full-time aligned-shear test gives a nonconstant example of this value
formula with an explicit bound. For `u=A exp(-nu t) sin(y)e_x` and the
initial tensor `omega0 omega0^T+delta I`, put
`m=delta+(A^2/2)(1+exp(-4nu t)cos(2y))`. Then `q=s/m`, and
`k=(q*m+eta)/(q+eta)` is a convex combination of `m` and `1`. Consequently
`log k<=log(max(1,delta+A^2))` for all time. The checker verifies the full
parabolic quotient equation with its actual geometric cost. This is a
restricted positive case, not an arbitrary-data bound. Here `k(0)` need
not equal one, so its control representation retains the initial reward
`log k(0,Y_t)` in addition to the displayed running integral.

There is a precise limitation of one scalar HJB correction. For
`Lq=D-2 nu grad(log q).grad` and `R=Psi-log q`,

```text
Lq R - nu |grad R|^2
  = D Psi - nu |grad Psi|^2 + 2 nu F/q.
```

Hence the barrier requiring the left side to dominate
`(2 stretch-2 nu G)/s + 2 nu F/q` is exactly the ordinary log-vorticity
barrier for `Psi`. This change of scalar normalization alone supplies no
new bound. `StochasticLagrangian.TransportedFrameDirection` proves these
identities on supplied scalar rates and gradient pairings; constructing
the fields and applying PDE comparison are separate obligations.

The physical test uses the smooth `2pi`-periodic initial field

```text
u0 = (-a sin(x) cos(z) - b sin(y), b sin(x), a cos(x) sin(z)),
p0 = (a^2/4)(cos(2x)+cos(2z)) - b^2 cos(x) cos(y),
omega0 = (0, 2a sin(x) sin(z), b(cos(x)+cos(y))).
```

The checker verifies incompressibility, the exact initial pressure Poisson
equation, the solenoidal unforced velocity RHS, and its curl. These data
have a smooth local unforced evolution. The checker computes its actual
initial tangent; it does not provide a closed-form solution at later times.
At the origin, for `a,b>0`,

```text
u0=0,  grad omega0=0,  F0=0,
Dq(0,0)=0,  partial_t kappa(0,0)=2a>0,
partial_t |omega|^2(0,0)=8b^2(a-nu).
```

Both the initial trace and log-determinant rates of `M` vanish. Thus a
smooth local correction using only `q`, trace and determinant cannot
supply a negative parabolic rate there to pay for the positive ratio
production. This statement concerns that local payment without a separate
initial/time-dependent reserve, not every history certificate.

The example is not devoid of an internal stretching source. With
`w=(grad u)omega` and `P=Hess p`, the checker verifies

```text
D w = -P omega - 2 nu sum_j (partial_j grad u)(partial_j omega).
```

At the origin the cross-gradient term vanishes and `D w=(0,0,2a^2 b)`.
The pressure is generated by the same unforced velocity. The existing
`LocalMaterialStretching.hasDerivAt_stretchingAlong` proves the material
version of this evolution for actual solutions, including its viscous
terms. A geometric reserve must retain or bound the relevant directional
pressure history; incompressibility does not set it to zero.
The initial ordinary time derivative of directional strain is `-2nu a`
in this example. Positive stretching-vector production therefore does
not establish repeated regeneration or sustained growth of the strain.

Replacing `a` by `-a` preserves the entire initial `q` and `F` fields,
while reversing the directional growth at the origin. Their ordinary
scalar time derivatives agree at that stationary point. Away from it,
their velocity drifts differ, so agreement of ordinary time derivatives
is not asserted. The example refutes neither global regularity nor a
full-state, full-datum history allowance.

```sh
python3 -O labs/transported_frame_direction.py
```

### Separated pressure, exact swirl response and a joint history target

`pressure_boundary_response.py` checks a positive separated-pressure
estimate and an initial-data test of the information a boundary must
retain. The whole-space calculations below use `N(x)=1/(4 pi |x|)` and
energy `E=||u||_2^2`, without the factor one half. They concern actual
unforced initial data and the pressure they generate. They do not
establish recurrent amplification.

**The energy-paid separated contribution.** Away from zero, the fourth
derivative of `N` paired with an observation direction `e` twice and a
source velocity `v` twice has angular numerator

```text
K(n,e,v) = 105 (e.n)^2 (v.n)^2
  -15 (|e|^2 (v.n)^2 + (e.n)^2 |v|^2 +4(e.n)(e.v)(v.n))
  +3 (|e|^2 |v|^2 +2(e.v)^2),              |n|=1.
```

The derivative is `K/(4 pi r^5)`. Two exact sum-of-squares identities
give the sharp interval `-12 |e|^2|v|^2 <= K <= 24 |e|^2|v|^2`.
The Lean proof uses the components of `e` and `v` perpendicular to `n`
and their nonnegative Gram determinant. Thus the result does not select
a preferred axis. The checker independently differentiates `1/|x|`
in an adapted coordinate system and verifies attainment of both constants.

For a smooth finite-energy whole-space solution, define the far part
of the Hessian by integrating this fourth kernel against `u_i u_j`
over `|x-y|>=R`, with a fixed `R>0`. There is no singular integral in
this far part. The canonical pressure representation and the bound above
give, for every unit observation direction,

```text
|e . P_far(t,x) e| <= 6 ||u(t)||_2^2/(pi R^5).
```

The Hessian is symmetric, so the same bound holds for its operator norm.
The unforced energy inequality consequently gives

```text
||P_far(t,x)|| <= K_R := 6 ||u0||_2^2/(pi R^5),
integral_0^H ||P_far(t,X(t))|| dt <= H K_R.
```

This permits arbitrary observation positions and orientations; it assumes
no persistent packet shape. The Lean module `PressureBoundaryResponse`
proves the angular certificates, the explicit kernel integral bound, and
its physical-time integral under a common energy bound and the stated
measurability/integrability hypotheses. The integration measure may vary
with time, allowing restriction to the exterior of a moving observation
ball. Identification of that kernel integral with the actual pressure
Hessian, the operator-norm passage, and the physical energy application
are analytic here. `P_near=P-P_far` retains all singular/local terms.
No derivative of this decomposition is used. A shrinking `R(t)` would
instead require controlling its potentially divergent `R(t)^(-5)` cost;
the fixed-radius theorem does not supply that control.

**An exact boundary response of a compact swirl.** Let `chi` be a smooth
compactly supported radial profile, smooth as a function on space at
the origin, and let `n` be a unit vector. Set

```text
u(x)=chi(|x|) (n cross x),
I(r)=integral_0^r s^4 chi(s)^2 ds,
T(r)=integral_r^infinity s chi(s)^2 ds.
```

This field is divergence-free and has zero helicity density. For the
axis `n=e_z`, write `mu=z/r`. Its pressure is

```text
p(r,mu) = -(2/3) T(r) -(2/3) I(r) r^(-3) P_2(mu),
P_2(mu)=(3mu^2-1)/2.
```

Indeed `tr((grad u)^2)=-2chi^2-2chi chi' (x^2+y^2)/r`.
Splitting `Delta p=-tr((grad u)^2)` into its spherical degrees zero and
two gives the two radial ODEs checked by the script. The displayed
solution is regular at the origin and decays at infinity, identifying
the canonical pressure. Its energy is `E=(8pi/3) I(infinity)`.
Outside the support the pressure is therefore exactly

```text
p(x) = -E [3(n.x)^2-|x|^2]/(8pi |x|^5)
     = -(E/2) partial_nn N(x).
```

This is an exact quadrupole, without a small-packet approximation. Energy,
axis and centre suffice to describe this packet's instantaneous exterior
pressure. They are not asserted to be a closed dynamical state: the
subsequent coupled NS evolution need not preserve the radial packet.
Independent quadrature integrates the velocity stress against the fourth
Newtonian kernel at two resolutions; this is a numerical cross-check of
the analytic formula, not its proof.

**Same core and energy, opposite next directional growth.** Take a
central compact radial swirl whose profile is the constant `b>0` on a
ball around zero. There

```text
u0=b(-y,x,0),    omega0=2b e_z,    (grad u0)omega0=0,
p_core=constant+b^2(2x^2+2y^2+z^2)/5.
```

Place two further compact radial swirls at `+L e_z` and `-L e_z`, with
supports disjoint from each other and from the core. Give them total
energy `E`, half each, and axes `n` and `-n`. Disjoint supports make the
velocity stress, and hence the initial pressure, the sum of the three
contributions exactly. The remote pair's pressure is even about zero,
so its pressure gradient vanishes there. Counter-rotation also cancels
its total initial angular momentum. No persistent velocity parity is
assumed.

For these centres the exact remote axial Hessian is

```text
(P_remote)_zz(0) = 3E(1-3n_z^2)/(2pi L^5).
```

Choose `E=pi b^2 L^5`. Parallel axes `n=e_z` give total
`P_zz=-13b^2/5`; transverse axes `n=e_x` give `P_zz=19b^2/10`.
The two full initial data agree throughout the core ball. They have the
same total energy and every integer isotropic Sobolev norm: radial packet
rotation preserves each such derivative norm and the disjoint supports
remove the cross terms. Both have zero initial helicity, zero total
initial momentum, and the same initial angular momentum. These equalities
do not refute norm-dependent upper bounds; they show that these scalar
data do not determine the sign of the core response.

Each datum is smooth, compactly supported and divergence-free, so it
starts an actual local unforced whole-space NS evolution for every
`nu>0`. Consider the compatible frame with `M(0)=I`. In the initial
core ball, `omega_t=0` and `M_t=0`. At its centre, if `B0=grad u0`,

```text
B_t=-B0^2-P,    omega_tt=-P omega0,    M_tt=-2B0^2-2P,
q_t=q_tt=0,     q=omega^T M^(-1)omega.
```

The viscous derivatives vanish in these initial plateau jets. For the
fixed regularized directional ratio `k=(|omega|^2+eta)/(q+eta)`, `eta>0`,

```text
k(0,0)=1,    k_t(0,0)=0,
k_tt(0,0)=-8b^2 P_zz/(4b^2+eta).
```

It follows that the parallel-parent configuration initially increases
`k` at second order, while the transverse one decreases it. The checker
independently differentiates the matrix/vector Taylor expressions.
The actual local-solution and frame realization is analytic, not
Lean-certified by this script. The construction supplies neither
recurrent amplification nor an obstruction to a full-datum history bound.

**The joint quantity and the remaining geometric obligation.** Put
`D=partial_t+u.grad-nu Delta`, `B=grad u`, `zeta=B omega`, and
`C=sum_j (partial_j B)(partial_j omega)`. The full unforced laws are

```text
D omega=zeta,          D zeta=-P omega-2nu C.
```

For one fixed `tau>0`, set `J=|omega|^2+tau^2|zeta|^2`. The exact law is

```text
D J +2nu (|grad omega|^2+tau^2|grad zeta|^2)
  = 2omega.zeta -2tau^2 zeta.P omega -4nu tau^2 zeta.C.
```

The checker verifies both laws directly on a genuinely three-dimensional
periodic initial field, using its actual pressure and unforced tangent,
including nonzero spatial gradients. This check is separate from the
whole-space separated-kernel argument. With `P=P_far+P_near`, Young's
inequality and `||P_far||<=K_R` give

```text
D J +2nu (|grad omega|^2+tau^2|grad zeta|^2)
  <= (1/tau+tau K_R) J
       -2tau^2 zeta.P_near omega -4nu tau^2 zeta.C.
```

The Lean theorem `joint_production_le` checks this estimate on the
supplied values. The far contribution is paid uniformly over time and
orientation. The near-pressure work and viscous cross term are still
signed, uncontrolled terms; the cross term cannot be discarded as
damping. A finite-history estimate for their combined production,
retaining geometric coherence and actual regeneration, remains open.
Since `J>=|omega|^2`, a uniform spatial bound for `J` would supply the
vorticity continuation criterion. None of the results above proves that
bound for arbitrary data.

The checker requires SymPy and NumPy:

```sh
python3 -O labs/pressure_boundary_response.py
```

### Swirl pressure histories: rotation, dissipation and geometry defects

`swirl_pressure_history.py` continues the compact-swirl calculation above
from an instantaneous boundary response to its first physical time
derivative. The viscosity is positive and the energy convention remains
`E=||u||_2^2`. The initial data are smooth, compactly supported and
divergence-free, and therefore start actual local unforced whole-space
solutions. The physical calculation below is analytic. The Lean module
`StochasticLagrangian.SwirlPressureHistory` certifies the finite matrix
algebra and a conditional time-integrated reserve.

**The initial pressure response cone.** Put a counter-rotating pair at
`+L n` and `-L n`, with axes `n` and `-n` and equal packet energies. If
the pair's total energy is `E`, its exact Hessian at the origin is

```text
H_pair = c E (I-3 n n^T),                 c=3/(2pi L^5).
```

Use three orthogonal axes `n_i`, a common compact radial profile and
sufficiently small support radii to keep all packets disjoint. For a
trace-free symmetric target with eigenvalues `lambda_i`, choose
`a>=max_i lambda_i` and pair energies

```text
E_i=(a-lambda_i)/(3c) >= 0,               sum_i E_i=a/c.
```

The resulting Hessian is the target. At a prescribed total energy `S`,
this family realizes precisely the trace-free symmetric tensors with
`lambda_max<=c S`. This describes this packet family; it is not a claim
of energy optimality among all fluid fields. The Lean theorem
`pressure_cone_certificate` proves the nonnegative allocation and exact
diagonal response in the eigenvector frame. Orthogonal diagonalization
and realization by the actual velocity packets are analytic here.

**The first compatible history step.** Add a central radial swirl
`u_c(x)=chi_c(r)(e_z cross x)` with `chi_c(0)=b`. Its support is disjoint
from every remote packet. All remote packets use the same radial shape
and radius, with their amplitudes set by the chosen energies. Let
`p_full(t)` be the pressure of the actual solution from the combined
datum, and `p_core(t)` that of the separate solution from `u_c` alone.
Define

```text
H(t) = Hess p_full(t,0) - Hess p_core(t,0),
R x = e_z cross x,
gamma = 2nu (integral_0^infinity r^4 chi_r'(r)^2 dr)
             / (integral_0^infinity r^4 chi_r(r)^2 dr) > 0.
```

The remote profile `chi_r` may have any nonzero amplitude, which cancels
in `gamma`. At the initial time the exact pressure-excess law is

```text
H'(0) = -gamma H(0) + (2b/5)(H(0) R - R H(0)),
(d/dt)|H(t)|_F^2 at t=0 = -2gamma |H(0)|_F^2.
```

Thus the initial nonlinear feedback rotates this pressure tensor without
changing its squared Frobenius norm, while viscosity decreases that norm.
For a nonzero response it cannot be stationary to first order. The
definition uses the difference of two actual pressure histories. At
positive time it is not identified with the pressure of an independently
evolving tagged remote velocity.

Here is the analytic derivation, including the couplings retained in the
calculation. Write `B=grad u`. Since `-Delta p=tr(B^2)`, differentiating
along the unforced equation gives the pressure-source derivative
`2tr(B grad u_t)`. On an initial packet support,

```text
B = chi R_n + (chi'/r)(R_n x) x^T,
(u.grad)u = chi^2 R_n^2 x,                R_n x=n cross x.
```

Both `tr(B grad((u.grad)u))` and `tr(B Hess p_self)` vanish pointwise.
The second equality uses the axisymmetry of that packet's exact pressure.
Consequently its nonlinear source derivative is exactly
`-2(chi'/r) x^T (Hess p_other) R_n x`. Initial disjointness removes the
local cross-advection terms; the nonlocal pressures of all other packets
remain.

The total remote velocity is even under `x -> -x`, so its gradient is
odd. The complete initial pressure is even. The sum of the remote
nonlinear source derivatives is therefore odd, and its Hessian response
at zero vanishes. On the core support the external pressure `phi` is
harmonic. For a homogeneous harmonic component `phi_l`,

```text
tr(B_c Hess phi_l) = (chi_c'/r)(l-1) (R x).grad phi_l.
```

The radial operator and the rotation preserve spherical harmonic degree.
Only degree two contributes to the pressure Hessian at the centre. For
`phi_2=x^T H(0)x/2`, let `Lphi_2=(R x).grad phi_2`. Its response is
`f(r)Lphi_2`, where

```text
f''+(6/r)f'=2chi_c'/r,
f(r)=2r^(-5) integral_0^r s^4 chi_c(s) ds,
f(0)=2b/5,                              Hess Lphi_2=H(0)R-RH(0).
```

This solution is regular at zero and decays at infinity. The heat part
of each remote pressure response is its fixed quadrupole multiplied by
the initial energy derivative. The radial heat operator is
`nu(chi_r''+4chi_r'/r)`, and integration by parts gives
`E'=-2nu (8pi/3) integral r^4 chi_r'^2`. Thus it contributes `-gamma H(0)`.
The core heat contribution cancels against the isolated-core comparison.

**The geometry changes.** If the central profile is constant `b` near
zero, the isolated core's initial nonlinear velocity derivative there is

```text
(b^2/5)(x,y,-2z).
```

It immediately generates meridional motion. Thus radial swirl packets
are not an invariant family for the full NS equation. An external
Hessian `H(0)=(b^2/5)diag(1,1,-2)` can cancel the initial velocity-gradient
rate at the centre, but it commutes with `R` and still satisfies
`H'(0)=-gamma H(0)`. Cancellation at one instant does not supply a
stationary pressure driver.

**Unequal widths: disappearing cancellation.** The common remote decay
rate is essential. If the remote profiles have different radii, the
same derivation instead gives

```text
H'(0)=-sum_i gamma_i H_i + (2b/5)(H(0)R-RH(0)),
H(0)=sum_i H_i.
```

Each pair is still counter-rotating, so its nonlinear source derivative
has zero Hessian response at the centre by parity. The core term is still
the displayed commutator. For two orthogonal pairs, take

```text
H_1=diag(-2,1,1),       H_2=(1/4)diag(1,-2,1),
gamma_1=gamma,          gamma_2=100gamma.
```

These rates are physically realized with the same radial shape at radii
in ratio ten to one; amplitudes independently set the two pair energies
to `1/c` and `1/(4c)`. The widths may both be small enough to keep every
support disjoint. Exact calculation gives

```text
|H_1+H_2|_F^2=39/8,
2(H_1+H_2) : (-gamma H_1-100gamma H_2)=129gamma/2 > 0.
```

The rotation term contributes zero. Thus the actual initial norm of the
combined pressure excess increases, even though each parent's viscous
response decreases. This is a finite initial-time amplification, not a
recurrent-growth or singularity result. It requires a boundary history
to retain the parent-dependent decay and cancellation, or pay for their
loss through a defect. `unequal_decay_production` and
`unequal_decay_production_pos` certify the finite calculation in Lean;
the physical realization and pressure-rate identity are analytic.

The same test reaches the transported-frame observable directly. Rotate
the parents to `H_1=diag(1,1,-2)` and `H_2=diag(-2,1,1)/4`, so the
dangerous direction is the plateau core's vorticity axis. With `M(0)=I`,
`q=omega^T M^(-1)omega` and `k=(|omega|^2+eta)/(q+eta)`, `eta>0`, the
actual initial jets at the origin give

```text
q'(0)=q''(0)=q'''(0)=0,
(|omega|^2)'''(0)=184 b^2 gamma,
k'''(0)=184 b^2 gamma/(4b^2+eta)>0             if b!=0.
```

Here the core's own initial pressure-Hessian derivative vanishes, while
the remote excess has `P'_zz=-23gamma`. The initial plateau makes
`omega'=M'=0` throughout the core, and the external pressure is harmonic
there. The corresponding spatial Laplacians in these time jets vanish.
Differentiating the full vorticity and frame equations therefore gives
the displayed values. The script checks their matrix/vector jet algebra;
the physical and parabolic identifications remain analytic. The positive
third derivative is a contribution from changing parent cancellation;
by itself it does not determine the sign of the earlier time derivatives.
For `b=1` there is actual initial increase as well:
`k''(0)=54/(5(4+eta))>0`. These statements supply no assertion of later
or recurrent growth.

**An interval reserve with the missing cost explicit.** For any symmetric
matrix history satisfying, on an interval,

```text
H'=-gamma H + beta(t)(H B(t)-B(t)H) + D(t),       gamma>0,
```

the commutator has zero quadratic work. In the physical rotation case
`B(t)` is skew; the cancellation at a symmetric `H` holds even without
that restriction. Young's inequality gives

```text
(d/dt)|H|_F^2 + gamma |H|_F^2 <= |D|_F^2/gamma,
|H(b)|_F^2 + gamma integral_a^b |H|_F^2 dt
  <= |H(a)|_F^2 + (1/gamma) integral_a^b |D|_F^2 dt.
```

The Lean theorems `hasDerivAt_energy`, `interval_reserve` and
`interval_cost_le` prove this for componentwise differentiable histories
and the stated integrability hypotheses. Keeping the endpoint term
allows adjacent intervals to share the same reserve. The common-profile
first-time-step calculation has `D(0)=0`; it does not establish `D=0`
later. A full-datum bound on the actual defect history, including changes
in geometry and parent interactions, is still missing. This pressure
certificate also needs a comparison to the directional-vorticity
observable before it can supply the continuation target.
At fixed separation these packets are already covered by the preceding
far-pressure energy bound. The new tests concern the information needed
in a dynamical boundary summary; control of nearby parents at changing
scales remains open.

The checker verifies the radial ODE, exact source contractions, heat
integration-by-parts identity, cone reconstruction, commutator work, and
nonzero meridional tangent symbolically. Independently, it integrates
the actual nonlinear pressure-source derivative for a core and six
remote packets with axes rotated relative to the core, and repeats the
nonlinear check with unequal remote widths. Gauss resolutions
24 and 40 give relative errors about `2.64e-6` and `2.13e-9` against the
commutator formula. This quadrature is numerical supporting evidence,
not a proof or a time evolution. SymPy and NumPy are required.

```sh
python3 -O labs/swirl_pressure_history.py
```

## Changing-scale pressure feedback and a joint reserve

[`compressed_parent.py`](compressed_parent.py) checks an initial pressure
transfer calculation with a compact straining background and a candidate
reserve for its aligned feedback. `AlignedPressureReserve.lean` proves
the scalar certificate and its interval balance. `LocalDirectionalPressure.lean`
connects the strain slot to the constructed unforced periodic solution.
The whole-space compact construction and pressure calculation below are
analytic; their NS realization is not yet a Lean theorem.

**Compact physical construction.** In cylindrical coordinates let
`r=sqrt(rho^2+z^2)` and take a smooth decreasing radial cutoff `chi_B`,
equal to one for `r<=RB` and zero for `r>=2RB`. The vector potential
`A_theta=-a z rho chi_B(r)` gives the solenoidal meridional velocity

```text
v_r=a rho(chi_B+z^2 chi_B'/r),
v_z=-a z(2chi_B+rho^2 chi_B'/r).
```

It equals `a diag(1,1,-2)x` in the inner ball. Add two counter-rotating
radial swirls at `+/-L e_z`, of the same radial profile and support
radius `rho0<L`, entirely inside that ball. An aligned radial core
swirl with angular velocity `b>0` on a plateau may also be added,
disjoint from the remote swirls. These are smooth compact solenoidal
initial data. Axisymmetric meridional and azimuthal velocities have no
cross term in the pressure source `tr((grad u)^2)`.

For each remote radial profile set

```text
I=integral r^4 chi^2 dr,       K=integral r^6 chi^2 dr,
kappa=K/(I L^2),              gamma=2nu integral r^4 chi'^2 dr/I.
```

Here `0<kappa<rho0^2/L^2`. The pressure excess `H(t)` compares the full
actual unforced solution with the actual background-plus-core solution
without the remotes. Both pressures are evaluated at the origin; their
initial rates agree with material rates there because the initial
velocity vanishes there. Only the initial excess is a sum of packet
responses.

**Retaining the surrounding-fluid reaction.** A packet's exterior
pressure and its decaying Newtonian potential are

```text
p=-(2/3)I r^-3 P2,
q=(-Delta)^-1 p=-2I/(9r)+[-I/(9r)+K/(15r^3)]P2.
```

The monopole in `q` comes from the interior of `p`; replacing the entire
pressure by its exterior quadrupole loses that term. On the packet axis
at distance `L`, `Hzz=-8I/L^5`, `Hxx=4I/L^5`, and
`q_zzzz=Hzz(1-3kappa)`.

For the affine comparison write `A=-a rho partial_rho+2a z partial_z`
and `W=u_theta`. Its swirl rate is `W_t=AW-aW`, giving pressure-source
rate `A s_w-4a s_w` for `s_w=-(1/rho)partial_rho(W^2)`. The Newtonian
dilation commutator gives pressure rate `Ap-2ap+6a q_zz`. The induced
meridional velocity interacts with the existing background and supplies
another `6a q_zz`. Thus the carried axial coefficient is `a(8-18kappa)`
and the full coefficient is `a(14-36kappa)`.

The compact-background correction is exact:

```text
delta_B=(80/7)L^7 integral_RB^(2RB) (-chi_B') r^-7 dr,
0<delta_B<=(80/7)(L/RB)^7,
Hzz'(0)=[a(14-36kappa+delta_B)-gamma]Hzz(0),
Hxx'(0)=[a(20-36kappa+delta_B)-gamma]Hxx(0).
```

To obtain it, outside `RB` the source correction is
`-2 tr[(grad v_B-S) Hess p_remote]`, `S=a diag(1,1,-2)`. For exterior
harmonic degrees two and four its angular coefficients are respectively
`32(4d-e)/35` and `32(d-e)/7`, with `d=r chi_B'`, `e=r^2 chi_B''`.
Higher degrees vanish by spherical-harmonic orthogonality: the Hessian
of an exterior degree-`l` harmonic has spherical degree `l+2`, whereas
the background-gradient/kernel multiplier has angular degree at most
six. The degree-two radial integral is a total derivative with zero
boundary values. Integrating the degree-four term by parts yields the
displayed correction. The heat term follows from the radial energy
identity used in the previous swirl test.

The background itself has central pressure Hessian
`-a^2 diag(12/7,12/7,18/7)`, independent of the cutoff shape. Indeed its
degree-two pressure-source integral is
`(8/105)(18cd+3ce+2d^2-de)`, now with `c=chi_B`. Radial integration by
parts cancels all cutoff-derivative squared terms. Including the local
Newtonian-Hessian contribution `-2a^2` leaves the axial value `-18a^2/7`.

**The joint certificate.** At the plateau core initially put
`Omega=2b>0`, `sigma=-2a`, `h=-Hzz>0`, and `w=Omega^(1/7)`. The actual
initial rates are

```text
w'=sigma w/7,
sigma'=-(5/14)sigma^2-w^14/10+h,
h'=-7sigma h-gamma h+(18kappa-delta_B/2)sigma h.
```

The core pressure supplies `w^14/10`. Aligned core rotation commutes
with the remote tensor. No assertion is made that the compact radial
or affine geometry persists after this initial time.

For arbitrary differentiable scalar histories with rate defects
`f_w,f_sigma,f_h`, the leading equations have the exact reserve

```text
R=w^5(2090sigma^2+154w^14+665h),
R>=154w^19=154Omega^(19/7)                 when w,h>=0,

R'=-665gamma w^5h
   +(10450w^4sigma^2+2926w^18+3325w^4h)f_w
   +4180w^5sigma f_sigma+665w^5 f_h.
```

Lean proves this derivative and its integrated equality, retaining the
terminal reserve and the signed defect work. A finite bound on that
work gives a physical-vorticity bound. In the compact initial compression
test, the width/cutoff defect is favorable if `delta_B<=36kappa`.
The earlier mixed-axis, unequal-width example instead has `sigma=0`,
`h=7/4`, `h'=23gamma`, and zero initial vorticity rate. Its joint reserve
grows at rate `15295gamma w^5`. This is a finite burst requiring the
distinct parent histories, not a counterexample to a full-datum budget.

**Actual strain and the pressure-summary obligation.** Along the
constructed local unforced material flow, let

```text
sigma=<omega,S omega>/|omega|^2,
p_dir=<omega,(Hess p)omega>/|omega|^2,
G=|S omega-sigma omega|^2/|omega|^2.
```

`LocalDirectionalPressure.hasDerivAt_strain` proves, under the existing
common third Fourier-moment majorant and away from vorticity zeros,
`sigma'=-sigma^2-p_dir+G+V`, where

```text
V=[<nu Delta omega,S omega>
   +<omega,(nu Delta S)omega+S(nu Delta omega)>
   -2sigma<omega,nu Delta omega>]/|omega|^2.
```

This is the actual material derivative, not the parabolic operator.
The nonalignment square has nonpositive reserve work during compression.
For `w^14=|omega|^2`, define the instantaneous expression
`h_inst=-p_dir-(9/14)sigma^2+w^14/10`. The theorem
`hasDerivAt_strain_with_summary` permits any retained summary `h`, with
the precise defect `f_sigma=G+V+h_inst-h`. Thus an initial match between
`h_inst` and remote pressure does not remove their subsequent mismatch.

Even their first derivatives differ. In the compact test let `p_ref'`
be the initial axial pressure derivative of the actual reference flow.
Then

```text
h_inst'-h'=-p_ref'+(45/98)sigma^3+(23/70)sigma w^14-(9/7)sigma h.
```

The reference term is finite and independent of remote packet amplitude.
At fixed core and background, the reserve using `h_inst` has initial
derivative affine in the remote strength `h`, with coefficient

```text
665w^5[(18/7)a-gamma-36a kappa+a delta_B].
```

For sufficiently narrow packets and sufficiently strong compression this
coefficient is positive. Increasing their amplitude therefore gives
actual compact unforced data with positive initial reserve production,
even though the retained-excess version has nonpositive production under
the preceding cutoff condition. This rules out monotonicity of that
instantaneous replacement; it does not rule out a signed history bound.

**Spatial diffusion is also a cost.** For
`D=partial_t+u.grad-nu Delta`, `xi=omega/|omega|`,

```text
D w=sigma w/7+6nu|grad w|^2/w-(nu/7)w|grad xi|^2.
```

The Hessian chain rule for `R` adds the gradient work

```text
nu[(20900w^3sigma^2-35112w^17+6650w^3h)|grad w|^2
   -41800w^4sigma grad w.grad sigma
   -6650w^4 grad w.grad h-4180w^5|grad sigma|^2]
-(nu/7)w R_w |grad xi|^2.
```

The final term is favorable for `w,h>=0`. The other terms are not
automatically dissipative. At `w=h=1`, `sigma=0`, spatial jets
`w_x=1`, `sigma_x=0`, `h_x=-6251/665` give `R_x=0` but gradient work
`34048nu`. This is a scalar-jet check, not an asserted NS realization.
Actual planar flows correlate the variables: `sigma=p_dir=0`,
`h=w^14/10`, and `D h=-nu|grad Omega|^2/5`. Those correlations give
`R=(441/2)Omega^(19/7)` and total diffusion work
`-50274nu w^17|grad w|^2`, as required by convex-power vorticity decay.
The identities are checked where `Omega>0`; the planar composite power
is twice continuously differentiable across zero.

The remaining arbitrary-data task is to control the signed pressure,
summary-mismatch and spatial defects throughout compatible histories,
with a nonnegative reserve or a proved correction. The present results
do not provide that bound or an invariant geometric class.

The checker independently integrates the carried pressure-source rate,
the viscous rate and the finite-background response. At radial/angular
Gauss order 64, the first two relative errors are below `9e-13`, and the
cutoff responses at `RB/L=4,8,16` agree to relative error below `1.1e-11`.
The background pressure coefficient agrees to absolute error below
`1.2e-13`. These quadratures support the analytic identities; they are
neither NS time simulations nor error-certified PDE bounds.

```sh
python3 -O labs/compressed_parent.py
```

## Actual pressure history and a dissipation-paid source

`pressure_history_source.py` checks complete Fourier identities for smooth,
genuinely three-dimensional initial data on the torus of period `2*pi`.
It uses Gaussian rational coefficients, retains every generated mode,
and compares independently constructed pressure derivatives. The tests
are actual unforced initial tangents, not a closed finite-mode evolution.
The calculations below apply to smooth solutions on every regular time
interval, with the indicated pressure normalization and integrability.

Write `L=∂t+u·∇`, `D=L-νΔ`, `B=grad u`, `P=Hess p`, and
`G=(-Δ)^(-1)`. Pressure is the canonical Newtonian/Riesz pressure on
whole space or the zero-mean pressure on the torus. The exact source law is

```text
s = tr(B^2),       p = G s,
D B = -B^2-P,
D s = -2 tr(B^3) - 2 tr(BP) - 2ν Σk tr((∂k B)^2),
D p = G(D s) + [u·∇, G] s.
```

These follow by the matrix product rule and commutation of the constant
coefficient heat operator with `G`. The last gradient trace is not a sum
of positive squares: `B` is not symmetric. Taking its sign for granted
would discard part of the physical pressure history.

There is a second, useful form. Define the scalar stress operator
`Q(A)=G Σij ∂i∂j Aij` and the matrix operator `T(A)=Hess Q(A)`. Then
`p=Q(u⊗u)` and `P=T(u⊗u)`. The exact matrix equation is

```text
D P = [u·∇, T](u⊗u)
      - T(grad p⊗u + u⊗grad p)
      - 2ν T(Σk ∂k u⊗∂k u).
```

The three terms retain transport of the parents, their actual pressure
reaction, and the viscous product-rule source. The checker verifies the
equivalent scalar equation coefficient by coefficient and separately
checks transport of the Hessian. These are analytic PDE identities;
the finite checker is not a general PDE formalization.

### Directional cancellation and the full instantaneous defect

Let `Ω=|omega|>0`, `xi=omega/Ω`, `sigma=xi·B xi`, and `pi=xi·P xi`.
Differentiating both the direction and the Hessian gives

```text
L pi = -2 sigma pi + J + ν Vpi,
J = xi·Hess(D p) xi - Σk (∂k p) xi·Hess(u_k) xi,
Vpi = xi·ΔP xi + 2 (Δomega/Ω)·P xi
      - 2 pi (omega·Δomega)/Ω^2.
```

Indeed, `D P=Hess(Dp)-B^T P-PB-Σk (∂k p) Hess(u_k)`.
The first two matrix products cancel the corresponding directional
stretching when the unnormalized quadratic `omega·P omega` is
differentiated. Normalization leaves `-2 sigma pi`. The velocity-curvature
term in `J` remains; differentiating pressure as an independently supplied
scalar history would miss it.

For the instantaneous expression
`h=-pi-(9/14)sigma^2+Ω^2/10`, let `N=|B omega-sigma omega|^2/Ω^2` and let
`Vsigma` be the full material viscous strain rate from
`LocalDirectionalPressure`. Direct substitution gives

```text
L h = -(23/7) sigma h -(81/98) sigma^3 +(37/70) sigma Ω^2
      -(9/7) sigma (N+Vsigma) - J - ν Vpi
      +(ν/5) omega·Δomega.
```

Thus its defect relative to `L h=-7 sigma h-gamma h+fh` includes
`(26/7)sigma h+gamma h`, as well as the remaining displayed terms.
For `w=Ω^(1/7)`, the material amplitude defect is
`fw=(ν w/7)(omega·Δomega)/Ω^2`.
These laws specify physical inputs to the joint reserve. They prove
neither positivity of this instantaneous `h` nor an allowance for its
complete signed defect. A retained parent summary has its own history;
the previously proved strain-summary mismatch must still be included.

### One pressure-history channel has a finite initial resource

On `R^3`, separate the fourth Newtonian kernel at a radius `R>0` and
write `T_R` for its exterior convolution. For a unit direction `e`, let

```text
Fν,R(t,x,e) = -2ν Σk integral_{|x-y|>=R}
                   pressureKernel(e,x-y,∂k u(t,y)) dy.
```

This is the exterior part of the final source in the matrix equation.
The kernel bound from `PressureBoundaryResponse` gives

```text
|Fν,R(t,x,e)| <= [6/(pi R^5)] d(t),
d(t) = 2ν ||grad u(t)||_2^2,
E(t) + integral_0^t d(s) ds = E(0),       E(t)=||u(t)||_2^2.
```

The second identity follows from the actual unforced NS equation: the
transport and pressure work vanish, and viscosity dissipates. It is
proved in `WholeSpacePressureHistory.kinetic_balance`. Consequently,
for arbitrary moving receivers, unit directions and positive radii,

```text
integral_0^t R(s)^5 |Fν,R(s)(s,x(s),e(s))| ds
    + (6/pi) E(t) <= (6/pi) E(0).
```

`scaled_history_with_remaining` proves this with the actual derivative
fields of `NSEvolution`. No common lower bound on the sampled radius
and no bound on future velocity gradients enter the allowance.
The sampled integrand is required to be interval integrable. The
initial and terminal energies are retained, so compatible time segments
share the same remaining resource. For fixed radius, the unweighted
source integral is at most `6 E(0)/(pi R^5)`.

The relation to the candidate reserve is explicit. Write
`Rsv=w^5(2090 sigma^2+154 w^14+665 h)`, with `w,h>=0` and `w^14=Ω^2`.
Choose a positive resource scale `Λ` and a sampling radius satisfying
`R^5 Ω^2 >= Λ`. The coercivity `Rsv>=154 w^19` gives

```text
|665 w^5 Fν,R| <= c d(t) Rsv,       c=1995/(77 pi Λ).
```

This is the theorem `viscous_reserve_source_le`. Its sign is unrestricted.
In a material or parabolic reserve inequality
`D Rsv <= c d(t) Rsv + remainingWork`, multiplication by the explicit
time-only factor `exp(c E(t))` cancels this coefficient:

```text
D [exp(c E(t)) Rsv] <= exp(c E(t)) remainingWork.
```

The correction is finite initially and uses the actual remaining energy.
At `Ω>0` one can choose `R=(Λ/Ω^2)^(1/5)`; taking `Λ=E(0)>0` makes
the total exponential allowance `exp(1995/(77 pi))`. This is a payment
for one separated source only. It does not pay the near field or imply
global regularity, and positivity of a physical `Rsv` is still open.
The source estimates and scalar reserve comparison are Lean-certified;
the general pressure equation and this differential comparison are
analytic identifications.

### Boundaries that still retain costs

For a fixed radius, `T_R` is a translation-invariant exterior operator,
so its pressure-history law has the same transport commutator and
pressure-velocity reaction, with `T` replaced by `T_R`. Those terms
remain unpaid. For a spatially and temporally varying radius `R(t,x)`,
the composite field `P_R(t,x)` additionally has the chain-rule terms

```text
(∂R P_R) D R - ν (∂RR P_R) |grad R|^2
             - 2ν Σk (∂xk∂R P_R) ∂k R,
```

where derivatives of the operator family are taken before substituting
`R(t,x)`. These terms, moving directions, the interior kernel and all
other viscous reserve terms must remain in the signed defect. The
shrinking-radius estimate is not permission to omit them. In particular
this does not close a scale-independent local renewal budget.

For a solenoidal external force `f`, the pressure-Hessian equation also
contains `T(f⊗u+u⊗f)`, and the energy balance gains the actual work
`2 integral <u,f>`. The finite checker uses the diagnostic force
`f=curl u` on its datum: its instantaneous integrated kinetic work is
zero but its pressure-history contribution has 16 nonzero modes.
This shows why a bound on energy input alone does not identify an
effective force as realizable by unforced hidden parents. It is an
initial forcing diagnostic, not a forced singularity or an internal
realization theorem. The separated viscous estimate can also hold for
forced flows with finite work, so this channel alone does not distinguish
the unforced problem from forced constructions.

At `ν=2/7`, the same unforced datum has viscous source component
`Fν,zz(0)=-15376/24255` and `Fν,zz(pi,0,0)=15376/24255` for the full
periodic operator. Both signs are exact. The two source representations,
the directional law, the complete instantaneous `h` defect, kinetic
production and Galilean covariance all pass exact coefficient checks
at `ν=0` and `ν=2/7`. The data have eight velocity modes; the actual
pressure-time derivative has 32 and 48 modes respectively. These are
checks of the stated identities, not repeated-renewal dynamics. The
whole-space exterior kernel constants are not claimed for the torus.

```sh
python3 -O labs/pressure_history_source.py
```

## Transverse strain and compression-to-extension histories

`transverse_strain_history.py` extends the compact-core pressure calculation
to an arbitrary symmetric trace-free strain and an arbitrary vorticity
direction. It derives an exact transverse-resource law with the actual
pressure and viscosity retained. The comparison law bounds one stretching
episode, but compression can replenish its normalized resource in a smooth
unforced flow. This identifies a cost that an arbitrary-flow history
argument must retain. The physical construction and interval arguments
below are analytic; the checker certifies finite algebra and spherical
moments with SymPy, not the Lean kernel.

### A compact datum that realizes the complete pressure comparison

Fix a symmetric trace-free matrix `S`, a vector `omega`, and the
antisymmetric matrix `A x=(omega cross x)/2`. Choose smooth radial
cutoffs `chi,psi`, equal to one near the origin and compactly supported.
The entire support of `psi` is contained in a ball where `chi=1`. Set

```text
u_B = curl[-(chi(r)/3) x cross Sx]
    = (chi+r chi'/3) Sx - (chi'/(3r)) x (x·Sx),
u_C = psi(r) A x,                  u0 = u_B+u_C.
```

These are smooth compactly supported divergence-free fields. In a ball
about the origin, `u0=(S+A)x`; all local Laplacians of the strain and
vorticity therefore vanish there. Smooth local unforced NS evolution
exists for every positive viscosity. The pressure is canonical Newtonian
pressure, determined by the entire compact datum, not prescribed as an
independent forcing.

Its exact Hessian at the origin is

```text
P_core(S,omega) = -(2/7) S^2 -(5/21) tr(S^2) I
                 + (|omega|^2/5) I - omega omega^T/10
                 - (2/5)(SA-AS).
```

Here the three parts are the background, swirl, and cross pressure.
To compute them, write `q=tr((grad u)^2)`. The distributional Hessian
of the Newtonian kernel gives

```text
Hess p(0) = -q(0) I/3
            + integral_0^infinity average_S2[(3nn^T-I) q(rn)] dr/r.
```

The contact term is necessary. For the background, put `c=chi`,
`d=r chi'`, `e=r^2 chi''`. Its full gradient at `x=rn` is

```text
(c+d/3)S + ((4d+e)/3)(Sn)n^T
 - (d/3)(n·Sn)I - ((e-d)/3)(n·Sn)nn^T - (2d/3)n(Sn)^T.
```

The angular calculation uses
`average(n1^(2a) n2^(2b) n3^(2c)) =
 (2a-1)!!(2b-1)!!(2c-1)!!/(2a+2b+2c+1)!!`;
an odd exponent gives zero. After angular integration the radial moments
are only

```text
integral cd dr/r = -1/2,
integral ce dr/r = 1/2-J,
integral d^2 dr/r = J,
integral de dr/r = -J,               J=integral r (chi')^2 dr.
```

Integration by parts proves these identities, and every `J` term cancels.
For the swirl, `grad u_C=psi A+(r psi')(An)n^T`; the remaining moment is
`integral psi psi' dr=-1/2`. The cross source is
`2r psi' n·SA n`, with `integral psi' dr=-1`. This gives the displayed
pressure matrix, independently of the two cutoff profiles under the
nested-support hypotheses. The checker differentiates the background
vector potential and checks all matrix entries of these angular integrals.
Diagonalizing `S` is legitimate by orthogonal covariance; the rotation
axis remains arbitrary. The result is an initial pressure identity, not
an invariant class of NS solutions.

### Actual moving-direction law

For any smooth unforced flow, in either whole space or the periodic
setting, write `L=partial_t+u·grad`, `S=sym grad u`, `P=Hess p`, and
`Omega=|omega|>0`. Define `dev M=M-tr(M)I/3`. The actual material laws are
exactly

```text
L S = -(5/7) dev(S^2) -(3/20) dev(omega omega^T)
      +(2/5)(SA-AS)+E,
L omega = S omega+f,
E = P_core(S,omega)-P+nu Delta S,       f=nu Delta omega.
```

Thus `E` is a symmetric trace-free physical defect, not a free control.
The formula follows from `L S=-S^2-A^2-P+nu Delta S`.
Away from vorticity zeros, let

```text
xi=omega/Omega,         sigma=xi·Sxi,
z=Sxi-sigma xi,         G=|z|^2,
Q=I-xi xi^T,           U=QSQ+(sigma/2)Q,
delta^2=tr(U^2)/2,     K=delta^2+(19/4)G.
```

`U` is the trace-free transverse strain. Both terms in `K` are
nonnegative, with no alignment hypothesis. Equivalently,
`K=tr(S^2)/2-(3/4)sigma^2+(15/4)G`. In a frame with `xi=e3`,

```text
S = [ -sigma/2+d       e          z1 ]
    [     e       -sigma/2-d     z2 ]
    [     z1          z2        sigma ],
delta^2=d^2+e^2,             z·Uz=d(z1^2-z2^2)+2e z1 z2.
```

First set `E=f=0` to examine the comparison dynamics. Differentiating
the direction as well as the matrix gives

```text
L G       = -(26/7)sigma G +(4/7) z·Uz,
L delta^2 =  (10/7)sigma delta^2 -(19/7) z·Uz,
L K       =  (10/7)sigma K -(171/7)sigma G,
L sigma   = -(5/14)sigma^2 +(10/21)K -G/2 -Omega^2/10.
```

The transverse transfer cancels in `K`; the rotation commutator also
has zero work in these invariants. Holding the direction fixed would
give different equations.

For the actual flow, put `epsilon=xi·f/Omega` and `eta=Qf/Omega`.
The complete defects are

```text
F_sigma = xi·E xi + 2 eta·z,
F_K = tr(SE) -(3/2)sigma xi·E xi +(15/2)z·E xi
      +(15/2)eta·Sz -(21/2)sigma eta·z.

L Omega / Omega = sigma+epsilon,
L sigma = -(5/14)sigma^2 +(10/21)K -G/2 -Omega^2/10 + F_sigma,
L K = (10/7)sigma K -(171/7)sigma G + F_K.
```

In particular the normalized resource `kappa=K Omega^(-10/7)` obeys

```text
L kappa = Omega^(-10/7)
            [-(171/7)sigma G + F_K -(10/7)epsilon K].
```

These are material equations: both viscous Laplacians are retained in
`E,f`. Changing to a parabolic or stochastic equation also requires
the spatial chain-rule terms of these nonlinear observables. The
identities do not give those terms a favorable sign automatically.
The checker verifies the general frame algebra and separately evaluates
the full periodic NS RHS, including every generated Fourier mode, at
`nu=0` and `nu=2/7`. The latter tests do not impose `E=f=0`.

### A bound within one extension episode

In the comparison dynamics `E=f=0`, consider an interval starting at
`a` on which `Omega>0` and `sigma>=0`. Then `kappa` does not increase.
Retain its starting value `kappa_* = K(a) Omega(a)^(-10/7)` and put
`w=Omega^(1/7)`. The scalar

```text
F = 2090 w^5 sigma^2 +154 w^19 -(8360/9) kappa_* w^15
```

satisfies

```text
L F = (41800/21)sigma w^5 (K-kappa_* w^10)
      -2090 sigma w^5 G <= 0.
```

Although `F` contains a negative term, an explicit initial shift makes
it coercive. Let `B=8360/9`, `M=1+B kappa_*/77`, and
`A_*=B kappa_* M^4`. For `w>=0`, splitting at `w^4=M` gives
`B kappa_* w^15 <= 77 w^19+A_*`. Hence

```text
77 Omega(t)^(19/7) <= F(t)+A_* <= F(a)+A_*.
```

This bounds the complete extension episode from its incoming state,
including arbitrary transverse anisotropy and nonalignment, in the
comparison model. In the actual material equation, the exact additional
work is `4180 w^5 sigma F_sigma + (epsilon w/7) partial_w F`.
One must also establish the required upper bound on `kappa` from its
actual history law. These are explicit remaining physical costs, not
assumptions verified by the episode calculation.

### Compression can replenish the resource in an actual unforced flow

Use the compact construction with

```text
S = [ 1/2   0    1 ],       omega=(0,0,1),
    [  0   1/2   0 ]
    [  1    0   -1 ]

P(0) = [ -104/105      0        1/7    ]
       [     0     -74/105      1/5    ]
       [    1/7       1/5    -137/105  ].
```

At the origin initially, `E=f=0` for every viscosity. The actual NS
material tangent, computed from `L grad u=-(grad u)^2-P`, gives

```text
sigma=-1,  Omega=1,  G=1,  delta^2=0,  K=19/4,
L omega=(1,0,-1),       L Omega=-1,
L sigma=137/105,        L K=247/14,
L kappa=171/7 > 0.
```

The vorticity direction turns while the magnitude decreases. Smooth
local existence and continuity therefore give a genuine positive-time
increase of `kappa` along the material path. This does not assume the
pressure comparison persists: its agreement at the initial time is
sufficient to compute the derivative and its strict sign.

The example rules out monotonicity of `kappa` for all unforced flows,
and a pointwise renewal payment that vanishes whenever `E=f=0`.
It does not rule out a full-datum allowance, an estimate including the
intrinsic compression term, or global regularity. In particular it is
not a construction of repeated cycles or finite-time blowup.

The surviving history obligation includes the signed work
`Omega^(-10/7)[-(171/7)sigma G+F_K-(10/7)epsilon K]`.
Compression contributes positively through `(-sigma)G` even before
the pressure and viscous defects enter. Successive extension episodes
cannot be given independent fresh starting allowances: their incoming
`kappa` values belong to one actual evolving fluid. Its singular
normalization near `Omega=0` also prevents an immediate spatially
uniform bound; a threshold or regularized observable needs a proved
entry and reentry cost. Paying these costs from the full initial datum,
while preserving signed cancellations, remains open.

```sh
python3 -O labs/transverse_strain_history.py
```

## A sixth-order resource for complete strain cycles

`strain_cycle_reserve.py` and `StochasticLagrangian.StrainCycleReserve`
continue the transverse-history calculation. A nonnegative polynomial
is conserved by the full matrix comparison, with no eigenalignment
assumption. A quantitative geometric estimate then bounds the intrinsic
turning cost across an entire history in a stated spectral regime.
Actual pressure and viscosity produce explicit signed defects; bounding
those for arbitrary flows remains open.

### The polynomial and its physical moments

Use the preceding notation `S=sym grad u`, `omega=curl u`, and define

```text
Q=tr(S^2),      R=tr(S^3),      W=|omega|^2,
V=omega·S omega,                Z=omega·S^2 omega,
c=63/190.

J6 = Q^3-6R^2-2c Q^2 W+c^2 QW^2+6c QZ
     -6c RV+(c^2/2)V^2-2c^2 WZ.
```

In the compact-core comparison `E=f=0`, the exact moment equations are

```text
L Q = -(10/7)R-(3/10)V,
L R = -(5/14)Q^2-(9/20)Z+(3/20)WQ,
L W = 2V,
L V = (9/7)Z+(5/21)QW-W^2/10,
L Z = (16/21)QV+(4/21)RW-WV/5.
```

These follow from the actual matrix comparison and the trace-free
three-dimensional Cayley--Hamilton identity
`S^3=(Q/2)S+(R/3)I`. The rotation commutator cancels from all five
moment equations. Substitution gives `L J6=0`. The checker also verifies
the more general coefficients
`L S=-a dev(S^2)-b dev(omega omega^T)+k(SA-AS)`:
the same polynomial is conserved with `c=6b/(a+2)` when `a+2!=0`.
The Lean module certifies the fixed physical-comparison coefficients,
the derivative of the composed polynomial, and its signed defect law.

### Nonnegativity with the direction retained

Order the eigenvalues of `S` and let their successive gaps be `a,b>=0`.
They are `(2a+b)/3`, `(b-a)/3`, and `-(a+2b)/3`. In this frame put
`x=c omega_1^2`, `y=c omega_2^2`, `z=c omega_3^2`, and `h=a+b`.
The polynomial has the exact representation

```text
J6 = (h^2/2)(2ab-y)^2
     + h(bx+az)(2ab+y) + (bx-az)^2/2 >= 0.
```

`eigen_identity`, `eigenCertificate_nonneg` and `scale_identity` certify
this algebra. Its identification through the spectral theorem with the
physical matrix is analytic here. The certificate retains the actual
vorticity components relative to the strain directions.

Nonnegativity does not give vorticity coercivity. For example, every state
`S=diag(-sigma/2,-sigma/2,sigma)`, `omega=Omega e3` has `J6=0`, for arbitrary
`sigma,Omega`. `aligned_degeneracy` checks this exact limitation. The
resource is used to pay a turning cost alongside the previous amplitude
and strain quantities; it is not a replacement for their continuation
comparison.

### A quantitative payment for intrinsic compression and turning

Let `Omega>0`, `xi=omega/Omega`, `sigma=xi·Sxi`,
`G=|Sxi-sigma xi|^2`, and `Wbar=c Omega^2`. Suppose

```text
h^2 <= Wbar,                     h=maximum eigenvalue - minimum eigenvalue.
```

Then the following useful estimate holds:

```text
Wbar G^2 <= 16 J6.
```

Here is an elementary proof, including the constant. The case `h=0`
has `S=0`, so assume `h>0`. Normalize the preceding eigenframe masses by
`Wbar` and write them as `x,y,z`, now with `x+y+z=1`. Put

```text
r=a/h,  s=b/h,  t=h^2/Wbar,       r+s=1,  0<t<=1,
u=x+z,  ell=sx-rz,  m=sx+rz,     d=2trs,
H=(d-y)^2+ell^2+2m(d+y),
B=r^2 xy+s^2 yz+xz.
```

The eigenframe identities give `J6=(h^2 Wbar^2/2)H` and `G=h^2 B`.
Also `m-rsu=s^2 x+r^2 z>=0` and
`xz=rsu^2+(s-r)u ell-ell^2`. Split `B=B1+B2`, where
`B1=y(r^2x+s^2z)` and `B2=xz`.

For `n=r^2x+s^2z`, use `0<=n<=u<=1`, `y=(y-d)+d`, and
`r^2s^2 n^2 <= rs m`. The elementary squared-sum bound gives

```text
t B1^2 <= 2(y-d)^2+8trs m <= 2H.
```

For the second part,
`0<=xz<=rsu^2+u|ell|` and `r^2s^2u^2<=rs m` give

```text
t B2^2 <= 2ell^2+2trs m <= 2H.
```

Consequently `t B^2<=8H`, which is exactly the claimed inequality after
restoring the scales. This quantitative order argument is analytic;
the checker verifies its algebraic identities. It is not asserted to
have been kernel-checked by the eigenframe identity alone.

Since `|sigma|<=h`, `G<=h^2`, and `0<c<1`, the absolute turning numerator
`A=|sigma|G` satisfies both

```text
A <= Omega^3,                   A^2 <= 16 J6.
```

Set `w=Omega^(1/7)`. If `w<=1`, the first bound gives
`A/w^10<=w^11<=1`. If `w>=1`, the second gives
`A/w^10<=4 sqrt(J6)<=4(1+J6)`. Thus

```text
|(171/7)sigma G Omega^(-10/7)| <= (684/7)(1+J6).
```

`normalized_turning_numerator_le` and `normalized_turning_rate_le`
certify this scalar payment from the two displayed controls, without
fractional-power automation. For `kappa=K Omega^(-10/7)`, the conditional
comparison therefore obeys, throughout any one history that stays in
the spectral regime,

```text
|kappa(t)-kappa(a)| <= (684/7)(1+J6(a)) |t-a|.
```

More strongly, the integral of `|L kappa|` over that comparison history
has the same elapsed-time bound.

This pays intrinsic compression and turning through successive episodes
using one incoming state and the prescribed elapsed time. There is no
new allowance at each change of sign of `sigma`. The two-scale argument
also bounds this intrinsic cost as `Omega` approaches zero; its apparent
inverse-power singularity alone is not used as an obstruction. Physical
defects and transitions outside the regime still need their own bounds.

The spectral hypothesis is substantive. In the ordered-eigenframe
variables take `a=1`, `b=beta>0`, `x=y=2beta`, `z=0`. Then
`J6=8beta^3+10beta^4`, `sigma=(1+2beta)/6`, and `G=1/4`, while
`Wbar=4beta`. As `beta` tends to zero, `J6` vanishes but the turning
numerator tends to `1/24`. Neither the numerator-squared estimate nor
the normalized payment by a fixed multiple of `1+J6` extends to this
weak-vorticity family. This is a limitation of this auxiliary resource,
not a singularity or a failure of a full-datum regularity bound.
Reversing the whole velocity preserves `J6,G,Omega` and reverses `sigma`,
so the same limitation also applies to the positive compression cost.

### How actual pressure and viscosity change the resource

Retain the actual material defects from the preceding calculation:
`E=P_core-P+nu Delta S`, `f=nu Delta omega`. The five moment defects are

```text
eQ=2 tr(SE),          eR=3 tr(S^2 E),           eW=2 omega·f,
eV=omega·E omega+2f·S omega,
eZ=omega·(SE+ES)omega+2f·S^2 omega.

L J6 = (partial_Q J6)eQ+(partial_R J6)eR+(partial_W J6)eW
       +(partial_V J6)eV+(partial_Z J6)eZ.
```

The polynomial production identity and ordinary scalar derivative are
Lean-certified. Their identification with the physical matrix moments
is analytic, independently checked on full periodic NS tangents. At
`nu=1/100`, a datum and its velocity reversal have the same initial `J6`
and opposite signs of `L J6`. Hence the comparison conservation cannot
be applied unchanged even to unforced positive-viscosity flows.

For the parabolic operator `D=L-nu Delta`, the same statement can be
written using the polynomial as a function of `(S,omega)`:

```text
D J6 = partial_S J6 : (P_core-P)
       -nu sum_j Hess_(S,omega) J6[(partial_j S,partial_j omega),
                                  (partial_j S,partial_j omega)].
```

All spatial chain terms remain. Nonnegativity of `J6` does not imply
convexity or a favorable sign for this Hessian. An actual finite initial
allowance for these terms has not been supplied.

For a solenoidal external fluid force `F`, the material defects additionally
contain `sym grad F` and `curl F`. Those contributions are different from
an auxiliary stochastic control on sampled paths. Nor does a bounded
instantaneous kinetic work identify an effective subgrid force as realizable
by unforced parents; their coupled histories still have to satisfy the
full fluid equation.

The actual transverse law becomes a payment for its intrinsic part plus
the still-signed remainder
`Omega^(-10/7)[F_K-(10/7)epsilon K]`. Using the new resource for arbitrary
flows requires control of its physical production and that remainder,
as well as entries into the complementary strain-dominated region.
The previous separated viscous pressure-history bound remains available;
it does not already pay these new terms.

### An actual unforced compression-and-return cycle inside the regime

Use the smooth compact construction from `transverse_strain_history.py`
with fixed nested radial profiles and

```text
S_sigma = [ -sigma/2     0       1   ],      omega=(0,0,4).
          [     0    -sigma/2    0   ]
          [     1       0     sigma ]
```

All time derivatives here follow the material path starting at the origin.
Initially the pressure is exactly `P_core`, and all
local spatial derivatives of `S,omega` vanish. The vorticity RHS is
spatially constant in that initial ball, so the initial material
derivative of `nu Delta omega` also vanishes. Therefore the actual
second material vorticity derivative is `-P_core omega`. It follows that

```text
Omega(0)=4,           Omega'(0)=4 sigma,
Omega''(0)=4[(9/14)sigma^2+17/105].
```

At `sigma=0`, the strain eigenvalues are `1,0,-1`, so
`h^2=4 < c Omega^2=504/95`; `J6=2776/95`. The spectral hypothesis holds
strictly and the magnitude has positive second derivative `68/105`.

Now choose `sigma=-epsilon`, with `epsilon>0` small. For each fixed
`nu>0`, this compact parameter family has uniformly bounded initial
Sobolev norms of every required order. Smooth local NS estimates give
a common positive lifespan and uniform third time-derivative bounds
on a smaller interval. The resulting Taylor expansion, uniform in small
`epsilon`, is

```text
Omega_epsilon(t)-4 = -4epsilon t +(34/105)t^2
                    +O(epsilon^2 t^2+t^3).
```

At `t=(105/17)epsilon` the leading difference is negative; at
`t=(315/17)epsilon` it is positive. Continuity gives a return to the
initial magnitude, and the positive second derivative on this small
interval makes the compression-to-extension turn unique. Its return
time is `(210/17)epsilon+O(epsilon^2)`. Continuity of the extreme strain
eigenvalues and the strict initial margin keep the cycle inside the
spectral regime for sufficiently small `epsilon`.

This is an analytic short-cycle construction for actual unforced flows,
not a maintained pressure closure. It gives no repeated unbounded
renewal, no sign claim for the net physical `kappa` change over the cycle,
and no singularity. The exact checker certifies the initial time jets;
the uniform local-existence and return-time argument is not yet Lean
formalized.

```sh
python3 -O labs/strain_cycle_reserve.py
```

## Compatible diffusion and a quartic pressure correction

`strain_cycle_diffusion.py` tests the preceding resource on actual
incompressible spatial jets. It retains the complete Fourier pressure
and unforced NS tangent. Its coefficients belong to `QQ(i)[M,nu]`, so
the parameter identities below are symbolic, not fits to sampled runs.
`StochasticLagrangian.StrainCycleDiffusion` certifies the local polynomial
expansion and the resulting scalar rate comparisons. The identification
with the physical PDE remains analytic.

### An actual family at zero spatial resource gradient

On the torus of period `2pi`, set

```text
u_M = (-2 sin(y)+sin(z),
       2 sin(x)-2M(1-cos(y))cos(z),
       sin(x)+2M sin(y)sin(z)).
```

This is smooth, real, mean zero and divergence free for every real `M`.
Its normalized kinetic energy `average |u_M|^2` is `5+4M^2`. All
calculations are at the initial origin of its local unforced evolution.
There `u_M=0`, and the strain and vorticity are independent of `M`:

```text
S = [0 0 1; 0 0 0; 1 0 0],       omega=(0,0,4).
```

Thus the strict spectral margin `diam(S)^2=4<(63/190)|omega|^2=504/95`
holds. The actual pressure Hessian obtained from the full Poisson source is

```text
P = diag(3, 4+(4/5)M^2, -1-(4/5)M^2).
```

Write `L=partial_t+u.grad` and `D=L-nu Delta`. The exact resource rates are

```text
J6=2776/95,                    grad J6=0,
L J6=-(16656/95)nu,
D J6=(686256/1805)nu M^2.
```

The pressure contribution to `L J6` cancels at this receiver. The positive
parabolic source therefore survives after the actual pressure is included.
It is not an increase of material `J6` in this example: the displayed
material rate is negative. It rules out simply applying a heat subsolution
comparison to `J6`. At the same point any increasing scalar reparametrization
has `D Phi(J6)=Phi'(J6)D J6`; gradient-squared HJB terms vanish. This concerns
that local scalar repair, not a reserve retaining additional history.

The quadratic velocity jet responsible for the curvature is
`(-2y+z,2x-My^2,x+2Myz)`, whose divergence is identically zero. Its resource
has quadratic part

```text
-(24M^2/9025)(103757 y^2+45108 yz-32272 z^2).
```

Its quadratic trace is `-(686256/1805)M^2`.
`localJet_expansion` checks the full polynomial, including its higher
terms, and `quadraticTrace_eq` checks this trace. These are compatible
velocity derivatives, rather than freely prescribed independent strain
and vorticity derivatives.

### What the pressure-coupled weight changes

Let `Omega=|omega|`, `sigma=omega.Somega/Omega^2`, and
`pi=omega.Pomega/Omega^2`. For an exponent `p`, consider the instantaneous
physical-pressure expression

```text
R_p=Omega^p [(3325/2)sigma^2+(441/2)Omega^2-665pi].
```

The prior instantaneous pressure replacement has `p=5/7`. At the same
receiver, the bracket is `4193+532M^2`; its spatial gradient and that of
`Omega` both vanish. The full parameterized rate is

```text
D R_p / 4^p = nu M^2[(266-133p)M^2-21315-(4193/4)p].
```

For `p=5/7`, the quartic coefficient is `171`; the rate is positive at
`M=12` for every `nu>0`. For `p=2`, the quartic term cancels exactly:

```text
D R_2 / 16 = -(46823/2)nu M^2.
```

More generally, the displayed rate is nonpositive for `p>=2` and `nu>=0`.
The cancellation uses the actual directional-pressure rate
`D pi=(2/5)nu M^2(11-M^2)`, including its spatial chain terms.
The Lean module certifies this exponent comparison from those physical
slots; it does not assume that viscosity always has a favorable sign.

Rescale `R_2` to the fourth-degree expression

```text
F4 = 5(omega.Somega)^2/|omega|^2
     +(63/95)|omega|^4 -2 omega.Pomega.
```

For this family the resulting values and rates are

```text
F4 = (32/95)(599+76M^2),
D F4 = -(107024/95)nu M^2,
D(J6+F4) = -(269440/361)nu M^2.
```

This is a concrete pressure-coupled payment for the preceding diffusion
failure at the initial receiver. The different homogeneous degrees mean
the last sum is not asserted to be a universal scale-invariant reserve.
No positive-time persistence is assumed.

### The actual equation and the pressure defect that remains

The quartic expression has a useful physical meaning beyond that family.
For an arbitrary smooth unforced evolution, wherever `W=|omega|^2>0`, put

```text
V=omega.Somega,  N=omega.Pomega,  sigma=V/W,
G=|Somega|^2/W-sigma^2,
A=sum_j |partial_j omega|^2,
C=sum_j [4(partial_j omega).(partial_j S)omega
         +2(partial_j omega).S(partial_j omega)],
Gamma=sum_j [(partial_j omega).P(partial_j omega)
             +2(partial_j omega).(partial_j P)omega],
H_ij=sum_k (partial_i partial_j u_k)(partial_k p),
Xi=omega.[Hess(Dp)-H]omega.
```

The full physical parabolic identity is

```text
D F4 = 10 sigma(WG-N)+(252/95)WV-2Xi
       +nu[-10sigma C+10sigma^2 A-10W|grad sigma|^2
           -(252/95)WA-(126/95)|grad W|^2+4Gamma].
```

To derive it, use
`D W=2V-2nu A`, `D V=|Somega|^2-N-nu C`, and
`D N=Xi-2nu Gamma`. The gradient transport terms in `D N` cancel because
the same velocity transports both vorticity and the pressure Hessian.
Finally apply the exact perspective identity

```text
D(V^2/W)=2sigma DV-sigma^2 DW-2nu W|grad sigma|^2.
```

The checker compares this equation independently with the direct full
NS tangent and spatial derivatives, both in the parameterized families
and in the earlier genuinely three-dimensional Fourier fixture. No pressure
source is supplied as an independent control. The pressure-history term
`Dp` includes transport, nonlinear pressure reaction and the viscous source
identified previously; none is discarded by this change of weight.

The compact-core pressure gives a positive reference. With transverse
anisotropy `delta^2` as in the preceding section,

```text
F4 = W[(44/7)sigma^2+(20/21)delta^2+(32/21)G]
     +(44/95)W^2 -2 omega.[P-P_core]omega.
```

This identity is checked symbolically. It isolates a directional pressure
defect whose control would make the quartic quantity coercive in physical
vorticity. Such a control, and a finite initial allowance for the full
signed production above, remain unproved.

The separated viscous pressure source already has a concrete payment.
Whenever `F4 >= (44/95)W^2` and `Lambda <= R^5 W`, the existing whole-space
source estimate gives

```text
|2W Fnu,R| <= [1995/(77 pi Lambda)] (2nu ||grad u||_2^2) F4.
```

`WholeSpacePressureHistory.quartic_source_work_le` and
`quartic_viscous_source_le` certify this transfer to the new quantity.
`StrainCycleDiffusion.quartic_coercive_of_pressure_le` supplies its
coercivity when `omega.[P-P_core]omega <= 0`. Neither hypothesis is
claimed for arbitrary flows. The coefficient is the same as in the
earlier pressure-history reserve, so the kinetic-energy correction
`F4 exp(c E(t))`, `c=1995/(77 pi Lambda)`, still absorbs this one channel.
This does not pay the nonlinear pressure source, nearby contributions,
moving cutoffs, or the other signed gradient terms in the full equation.

Two adversarial checks prevent a premature positivity or monotonicity
claim. Swap the y and z axes of just the quadratic packet, leaving the
base velocity fixed. On this packet, which has no x dependence or component,
the swap equals the proper rotation `(x,y,z) -> (-x,z,y)`.
This remains an actual divergence-free periodic datum
with the same central `S,omega,J6`. Its corrected value is now
`(32/95)(599-76M^2)`, negative at `M=3`, although its parabolic rate remains
negative in this particular test. Separately, the general Fourier fixture
has `F4>0` and `D F4>0` at `nu=1/100`. Thus neither unconditional positivity
nor a universal subsolution inequality follows from the successful
cancellation. A history correction must retain the parents' pressure
contribution and geometry. These finite smooth data refute neither a
full-datum allowance nor arbitrary-data regularity.

```sh
python3 -O labs/strain_cycle_diffusion.py
```

## A coercive pressure/core envelope with a fixed-radius payment

`pressure_core_envelope.py` checks a positive replacement for the quartic
candidate above. Write `D=partial_t+u.grad-nu Delta`, `S=sym grad u`,
`P=Hess p`, and use the actual moments

```text
Q=tr(S^2),  W=|omega|^2,  V=omega.Somega,
Z=|Somega|^2,  N=omega.Pomega.
```

Fix `eta>0` and `delta>0`. These are fixed regularizers; no limit to zero
is needed for the continuation implication. Define

```text
T_eta = V^2/(W+eta),
P_eta = 5 T_eta+(63/95)W^2-2N,
C_eta = 5 T_eta+(4/7)Z+(10/21)QW+(44/95)W^2,
g = P_eta-C_eta = -2(N-corePressurePair),
h_delta(g) = (g+sqrt(g^2+delta^2))/2,
Y = 1+C_eta+h_delta(g).
```

Here `P_eta` is a scalar pressure branch, not the tensor `P`. The switch
gap is independent of `eta`. The reserve is smooth at `omega=0`, and

```text
Y >= 1+C_eta >= 1+(44/95)W^2.
```

There is no directional-pressure sign hypothesis. The inequalities
`V^2<=WZ`, `Z<=QW`, and `-N<=p W`, where `p` bounds the pressure Hessian
operator norm, also give

```text
Y <= 1+delta/2+(127/21)QW+(63/95)W^2+2p W.
```

Consequently its spatial initial supremum is finite for the admissible
smooth periodic or rapidly decaying data, using the canonical initial
pressure. This says nothing about the future values of these moments.
`PressureCoreEnvelope` certifies the scalar lower and upper bounds with
the moment hypotheses explicit, together with both switch derivatives.
The matrix inequalities and fluid identification are analytic here.

### Actual production, including the branch that restores positivity

Let `A,C,Gamma,Xi` have their actual spatial definitions from the preceding
section. Introduce

```text
K_S=sum_j ||partial_j S||_F^2,
Zcross=sum_j (Somega).(partial_j S)(partial_j omega),
Zgrad=sum_j |(partial_j S)omega+S(partial_j omega)|^2,
r=V/(W+eta).
```

The complete unforced identities, valid also at vorticity zeros, are

```text
DW = 2V-2nu A,
DV = Z-N-nu C,
DQ = -2 tr(S^3)-V/2-2 tr(SP)-2nu K_S,
DZ = -2(Somega).Pomega-4nu Zcross-2nu Zgrad,
DN = Xi-2nu Gamma,
D T_eta = 2r DV-r^2 DW-2nu/(W+eta)|grad V-r grad W|^2,
D(W^2) = 2W DW-2nu|grad W|^2,
D(QW) = Q DW+W DQ-2nu grad Q.grad W,
D P_eta = 5D T_eta+(63/95)D(W^2)-2DN,
D C_eta = 5D T_eta+(4/7)DZ+(10/21)D(QW)+(44/95)D(W^2).
```

For example `D(Somega)=-Pomega-2nu sum_j (partial_j S)(partial_j omega)`:
the stretching terms cancel, and the antisymmetric square annihilates
`omega`. Squaring this identity gives `DZ`. The trace of the strain law
gives `DQ`; the directional pressure-history cancellation gives `DN`.
None of these replaces the pressure Hessian by a free control.

The smooth envelope satisfies the exact chain rule

```text
theta=h_delta'(g)=(1+g/sqrt(g^2+delta^2))/2,  0<=theta<=1,
h_delta''(g)=delta^2/[2(g^2+delta^2)^(3/2)] >=0,
DY=theta D P_eta+(1-theta)D C_eta-nu h_delta''(g)|grad g|^2.
```

Thus switching adds a nonpositive diffusion term. The production of
`C_eta` remains part of the equation: positivity is not obtained by
dropping its physical cost. The checker independently differentiates
both branches using the full unforced Fourier tangent and the actual
pressure-time Poisson solution. It also checks the scalar chain rule
using arbitrary time, gradient and Laplacian jets.

### A complete payment for one physical channel

The positive offset gives the useful elementary bound
`2W<=(3/2)Y`. Hence the actual separated viscous pressure-Hessian source
`Fnu,R` from `WholeSpacePressureHistory` satisfies, for every fixed `R>0`,

```text
|theta 2W Fnu,R| <= c_R (2nu ||grad u||_2^2)Y,
c_R=9/(pi R^5).
```

The direction is `omega/|omega|` where `omega` is nonzero. At a zero the
weighted term vanishes, so any unit direction gives the same zero work.
There is no scale condition involving `W` and no moving-cutoff derivative
in this fixed-radius payment. The source and coercivity conversion are
Lean-certified in `coercive_viscous_source_le` and
`reserve_viscous_source_le`. This particular kernel payment is on the
whole space; it is not a periodic kernel estimate.

Retaining the actual terminal kinetic energy `E(t)=||u(t)||_2^2`, define
`X=exp(c_R E(t))Y`. The exact unforced identity
`E'=-2nu||grad u||_2^2` absorbs this source with one initial allowance,
not a new allowance after each renewal. More explicitly, put

```text
Remainder=theta[D P_eta+2W Fnu,R]+(1-theta)D C_eta
          -nu h_delta''(g)|grad g|^2.
```

Then `DY=Remainder-2theta W Fnu,R`, so `DX<=exp(c_R E)Remainder`.
The whole pressure tensor is still present in the branch equations.
Near pressure, pressure transport and reaction, and the signed
strain/vorticity gradient terms are not paid by the separated estimate.

For `L=log X`, this gives the physical scalar HJB inequality

```text
D L-nu|grad L|^2 <= Remainder/Y.
```

For `nu>0`, the quadratic term is precisely
`sup_b [b.grad L-|b|^2/(4nu)]`. In a reverse-time stochastic verification,
`b` is an auxiliary drift added to the sampling drift `-u`; it is not a
body force applied to the fluid. This identifies the scalar control
equation along a given smooth NS evolution. It does not prove that the
fluid itself solves an independent Schrödinger-bridge optimization.

The missing estimate is a bound on this signed potential over compatible
histories, uniformly over every smooth prefix up to a prescribed horizon,
using only the full initial datum, viscosity and that horizon. Defining
its value as a supremum over the unknown future is not such a bound.
If an initial-data bound `L<=B` were obtained on every such prefix, then
`|omega|<=(95/44)^(1/4)exp(B/4)` would supply the existing continuation
criterion. Coercivity and this one paid channel do not supply `B`.

### Adversarial and positive checks

In the parameterized packet from the preceding section, and in its
rotated version, `W=16` and `grad g=0`. Their exact branch rates are

```text
original: D P_eta=-16 M^2 nu(1939eta+107024)/[95(eta+16)],
rotated:  D P_eta=-16 M^2 nu(2547eta+116752)/[95(eta+16)],
both:     D C_eta=-256 M^2 nu(139eta+6974)/[95(eta+16)].
```

They are nonpositive for `nu>=0`, `eta>0`, and every real `M`.
The reserve stays positive in the rotated family that defeated `F4`.
For `u=(sin y,sin x,cos x-1)` at the origin, vorticity vanishes;
with `delta=1`, `Y=3/2` and `DY=-74nu/21`, for every `eta>0`.

The general three-dimensional Fourier fixture has strictly **positive**
`DY` at `eta=delta=1`, `nu=1/100`. Its certificate is rational:
both branch rates exceed the switching subtraction, bounded using
`sqrt(g^2+1)>=|g|`. Thus a universal heat-subsolution claim is false.
This finite smooth example does not refute a full-datum history bound.

There is also an all-time validation class. For the exact unforced shear
`u=(U(y,t),0,V(y,t))`, both profiles solve the one-dimensional heat
equation and the pressure is zero. Its moments satisfy `Q=W/2`,
`V_moment=Z=N=0`. The reserve is a function of `r=W^2`:

```text
Y(r)=1+(1399/1995)r+h_delta(-(4/105)r),
Y'(r)>=63/95,  Y''(r)>=0,
Dr=-4nu W sum_j |partial_j omega|^2-2nu|grad W|^2<=0.
```

Therefore `DY<=0` on the entire smooth shear history, including changing
vorticity direction and zeros. The heat maximum principle bounds it by
its initial supremum in the periodic class. This is a validation with
no vortex stretching; it does not settle arbitrary three-dimensional
histories. The full PDE statements in this subsection are analytic,
with exact coefficient checks, rather than Lean-certified evolutions.

```sh
python3 -O labs/pressure_core_envelope.py
```

## Signed pressure redistribution and the cost of following a region

`pressure_stress_transport.py` identifies two different pressure-history
mechanisms from the actual unforced equation. Cubic stress is transported
between regions, while pressure redistributes stress between directions.
Keeping the latter signed gives a full-history bound for a fixed global
direction. A localized or rotating observation retains additional costs.

Write `T=u tensor u`, `S=sym grad u`, `G_ij=sum_k partial_k u_i partial_k u_j`,
and let `p` be the canonical pressure. The exact tensor equation is

```text
partial_t T_ij + partial_k(u_k T_ij)
  + partial_i(p u_j)+partial_j(p u_i)
  = 2p S_ij + nu Delta T_ij -2nu G_ij.
```

Repeated `k` is summed. The pressure redistribution `2pS` has zero trace
because the fluid is incompressible; its directional entries need not
vanish. The complete Fourier checker verifies the tensor equation at
`nu=0` and `nu=2/7`, with all product modes retained. Its eight-mode
velocity generates 58 modes in `2pS`. Reversing the velocity preserves
pressure and energy while reversing that signed redistribution. This
parity check alone is not a dynamical obstruction or a history bound.

### A finite allowance for transported cubic stress

Set `E=||u||_2^2`, `D1=||grad u||_2^2`, and
`B=||u||_2 ||u||_4^2`. Cauchy--Schwarz, interpolation and the imported
Sobolev inequality `||u||_6^2<=3 S^2 D1` give

```text
integral |u|^3 <= B,
B^4 <= 27 S^6 E^3 D1^3.
```

For positive viscosity, the elementary fourth-power absorption yields

```text
B(t) <= 2nu D1(t)+a,       a=27 S^6 E0^3/(32 nu^3).
```

Here only `E(t)<=E0` has been used. The actual unforced kinetic balance
therefore gives, for every smooth prefix,

```text
integral_0^t B(s) ds + E(t) <= E0+a t.
```

The same allowance bounds the cubic velocity moment. In
`WholeSpaceCubicHistory`, the formal `transportSize` uses the existing
order-zero quartic-energy and kinetic-energy expressions for this
envelope. Its fourth-power estimate, absorption and the sampled-response
history estimate are Lean-certified. The time-integrability assumptions
are on each smooth prefix; no bound on their size is assumed. The final
constant is uniform over those prefixes and depends only on `E0,nu,t`.

This also has an analytic pressure-flux application. For the canonical
decaying pressure, the Fourier symbol of the map `u tensor u -> p` has
Frobenius norm one. Plancherel gives `||p||_2<=||u||_4^2`, hence
`integral |p||u|<=B`. This pressure-multiplier identification is not newly
Lean-certified here. A scalar pressure with an arbitrary additive constant
must first be put in this canonical gauge when using that norm estimate.

For a concrete contribution to the pressure Hessian, choose a smooth
radial cutoff `chi`, zero on `[0,1]`, one on `[2,infinity)`, with
`0<=chi<=1` and `|chi'|<=2`. Let

```text
K^R_e,ij(z)=chi(|z|/R) partial_ee partial_ij [1/(4pi|z|)],
Fadv,R(x,e)=- integral K^R_e,ij(x-y) partial_k(u_k u_i u_j)(y) dy.
```

The cutoff is smooth: replacing it by a hard indicator would add a
surface term to this integration by parts. For fixed `R>0` and unit `e`,
the full spatial integration by parts gives

```text
|Fadv,R(x,e)| <= [567/(pi R^6)] integral |u|^3.
```

The checker differentiates the fifth Newtonian derivative independently.
Writing `n=z/|z|`, its angular numerator for `partial_ee partial_vvv` is

```text
-945(e.n)^2(v.n)^3
+105[|e|^2(v.n)^3+6(e.n)(e.v)(v.n)^2+3(e.n)^2|v|^2(v.n)]
-15[6(e.v)|v|^2(e.n)+3|e|^2|v|^2(v.n)+6(e.v)^2(v.n)].
```

Cauchy--Schwarz bounds its absolute value by `2220|e|^2|v|^3`.
After the Newtonian factor this is `555/(pi R^6)`. The differentiated
cutoff contributes at most another `12/(pi R^6)` by the earlier fourth
kernel bound. These constants are conservative. The kernel identification
and this vector estimate are analytic; the scalar cubic allowance and
conditional integral-response conversion are Lean-certified.

The resulting **absolute** history allowance for this particular channel
is valid for arbitrary moving receivers and unit directions at fixed `R`:

```text
integral_0^t |Fadv,R| ds + [567/(pi R^6)] E(t)
  <= [567/(pi R^6)] (E0+a t).
```

It is the cubic source contribution, not the whole material pressure
commutator. Receiver transport, moving directions and pressure stress
redistribution have not been removed from that commutator. If the
coercive reserve is multiplied by this source with weight `2theta W`,
the previous `2theta W<=(3/2)Y` converts it to an integrable growth
coefficient. On a prescribed horizon `H`, the nonnegative resource
`E(t)+a(H-t)` pays it without restarting the allowance at a new episode.
Its coefficient diverges as `R` shrinks; there is no all-scale sum here.

### Global signed pressure transfer is already energy-paid

Fix a spatially constant unit direction `e`. Define

```text
a_e(t)=integral (u.e)^2,
d_e(t)=2nu integral_0^t integral |grad(u.e)|^2,
W_e(t)=integral_0^t integral 2p (e.S e).
```

Integrating the tensor equation gives the exact identity
`W_e=a_e(t)-a_e(0)+d_e(t)`. The fluxes have zero spatial integral.
On the whole space this follows by cutoff removal using their
integrability; on the torus it follows by periodic integration by parts.
Since `0<=a_e(t)<=E(t)` and `0<=d_e(t)<=E0-E(t)`,

```text
-a_e(0) <= W_e(t) <= E0-a_e(0),     |W_e(t)|<=E0.
```

This controls the **signed space-time integral**, not the time integral
of its absolute value and not the value on an individual trajectory.
It retains cancellation across any number of renewals. The actual-fluid
identity and passage to arbitrary unit directions are analytic here;
`fixed_direction_signed_abs` certifies the endpoint argument with all
component-energy and dissipation hypotheses explicit.

### The exact extra cost of a moving, localized observer

For a smooth symmetric matrix field `M(t,x)`, put `a_M=integral u.Mu`.
Testing the same stress identity gives

```text
integral 2p S:M = a_M'
  +2nu integral sum_k (partial_k u).M(partial_k u)
  -integral (u tensor u):(partial_t M+u.grad M+nu Delta M)
  -2 integral p u.div M.
```

For `0<=M<=I`, the component energy and dissipation are dominated by the
full kinetic quantities. Let `C_M` be the time integral of the last two
displayed integrands with their **positive** signs, before subtraction.
The exact signed endpoint allowance is then

```text
-a_M(0) <= W_M+C_M <= E0-a_M(0).
```

`signed_redistribution_bounds` certifies this algebraic implication.
It assumes the actual weighted-stress balance, not a bound on `C_M`.
The lab checks the physical identity for a positive spatial observer
`M=chi e(t)e(t)^T`, where
`chi=(3+cos(2z)+cos(2x+2z))/5` and `e(t)=(sin t,0,cos t)`.
Rotation, transport, diffusion and pressure boundary terms are retained;
the positive-viscosity test has nonzero diffusion and pressure boundary
work. Omitting either gives the wrong balance.

There is a useful fixed-window consequence. Suppose a time-independent
`M` has operator bounds `m0` on `M`, `m1` on its directional gradient,
`m2` on `Delta M`, and `md` on `div M`. Using the cubic and pressure-flux
envelope above yields analytically

```text
|W_M(t)| <= 2m0 E0+(m1+2md)(E0+a t)+nu m2 E0 t.
```

This holds without requiring `M` positive: the endpoint and dissipation
terms use its operator norm. Estimating the time derivative absolutely
would add `integral E(t)||partial_t M(t)||_infinity dt`. Keep that term
signed first: charging all rotation by its total variation can discard
cancellation. For a translated, rotating or shrinking window, the
derivative contains the actual translation, orientation and scale rates.
The fixed-window theorem does not pay these rates, and successive
episodes must share one allowance.

This is the remaining geometric question in a concrete form: control
the signed cost of following the dangerous region across scales and
renewals. The global cancellation and fixed-scale payments cannot be
substituted for that estimate. In particular, the pressure-Hessian
kernel has an indefinite tensor weight and becomes singular at zero
separation; neither fact is eliminated by the global directional bound.
The scalar HJB reserve still needs its full normalized signed remainder.

For a forced fluid the stress law gains `u tensor f+f tensor u`, and the
observer balance gains `2 integral (M u).f`. That term may be nonzero even
when the force's total kinetic work vanishes. The exact diagnostic
`f=curl u` on this fixture has zero total work and nonzero localized
directional work. It is not a forced singularity or an internal realization
of one. An unforced surrounding region enters through the compatible
boundary and observer terms, whose history must still be controlled.

```sh
python3 -O labs/pressure_stress_transport.py
```

## Shared stochastic displacement and the actual pressure observation

`synchronous_pressure_history.py` identifies the receiver and parent
terms in a two-point pressure history. Both points sample the same actual
unforced fluid and use the same Brownian motion. This cancels direct
diffusion of their separation kernel, but retains the mixed gradients
of their velocity, vorticity and observation weight. Integrating out the
parent gives the original pressure evolution, with no new source of
fluid forcing.

### A coupling with an exact physical marginal

Fix a smooth solution prefix and write `D=partial_t+u.grad-nu Delta`.
In backward time `s`, with physical time `tau=t-s`, consider

```text
dX_s=(-u(tau,X_s)+b_s)ds+sqrt(2nu)dB_s,
dY_s=(-u(tau,Y_s)+b_s)ds+sqrt(2nu)dB_s.
```

Here `b_s` is a bounded adapted auxiliary sampling drift, common to all
parent labels for the chosen receiver. It does not enter the fluid PDE.
For each Brownian/control history, the parent flow preserves volume:
subtracting the common translation gives an ordinary flow whose spatial
drift has zero divergence. Thus integrating over all parent labels still
reconstructs the fluid's pressure observation at the receiver. This
statement is on a given smooth prefix; it supplies no bound on how long
that prefix lasts.

The joint generator, acting on functions of physical time and both
positions, is

```text
L_b=-partial_t-u(x).grad_x-u(y).grad_y
    +nu sum_j (partial_xj+partial_yj)^2
    +b.(grad_x+grad_y).
```

For any fixed kernel `K(x-y)`, including a smooth separation cutoff,
`(grad_x+grad_y)K=0`. Its generator is exactly
`[u(y)-u(x)].grad K`. The Brownian motion and the common auxiliary drift
do not directly change the separation. Independent Brownian motions
would have a different joint generator and would lose this cancellation.

### The actual tensor and normalized-weight terms

Put `J=omega(x) tensor omega(x)`, `T=u(y) tensor u(y)`, and

```text
K_abij(z)=chi(z) partial_abij [1/(4pi|z|)],
F(t,x,y)=J_ab(t,x) K_abij(x-y) T_ij(t,y).
```

Repeated tensor indices are summed. For `b=0`, the exact joint identity is

```text
L_0 F=-(D J):K:T - J:K:(D T)
      +J:([u(y)-u(x)].grad K):T
      +2nu sum_j (partial_j J):K:(partial_j T).
```

There are no omitted kernel diffusion terms. The actual unforced field
equations supply, with `B=grad u`,

```text
D J=(B omega) tensor omega+omega tensor (B omega)
    -2nu sum_j partial_j omega tensor partial_j omega,
D T=-grad p tensor u-u tensor grad p
    -2nu sum_j partial_j u tensor partial_j u.
```

All receiver strain, parent pressure and mixed gradient terms remain.
The pressure/core reserve determines its own weight,
`c=2theta/Y`, with `theta=h_delta'(Peta-Ceta)`. It satisfies
`0<=c|omega|^2<=3/2`. This is a bound on the weight's value, not its rate.
The complete weighted equation is

```text
L_b(cF)=c L_0 F-(D c)F
        +2nu grad c.(grad_x+grad_y)F
        +b.(grad_x+grad_y)(cF).
```

The lab computes `c`, its time derivative, gradient and Laplacian from
the actual velocity, canonical pressure and pressure-time solution.
The generic product identity is checked independently. Its printed
decimal evaluations illustrate the weight costs; they are not used as
sign certificates. In particular, the pressure-time contribution in
`D c` is not replaced by an independently chosen control.

### Parent integration and a finite signed endpoint payment

Let `N_R=integral F(t,x,y)dy`, and `H_R=c N_R`, where the fixed smooth
cutoff has `|chi|<=1` and vanishes for `|z|<R`, `R>0`. Parent transport
integrates to zero by incompressibility; its divergence and cross
derivatives integrate to zero by decay or periodicity. Consequently

```text
integral L_b(cF)dy=(-D+b.grad)H_R,
|H_R(t,x)|<=[9/(pi R^5)] E(t),       E(t)=||u(t)||_2^2.
```

The second statement is Lean-certified in `WholeSpacePressureObserver`
for the actual whole-space smooth field, including the reserve-weight
instantiation and the uniform initial-energy application. The cutoff
bound is formulated for measurable cutoffs; smoothness and bounded
derivatives are additionally used in the analytic generator identity.
At vorticity zeros the weighted response vanishes, with no direction
singularity. No condition on the pressure's favorable sign is required.

For a smooth prefix on which Itô/Dynkin applies, the preceding physical
identity gives the analytic signed allowance

```text
|E_expectation integral_0^s (-D+b.grad)H_R(t-r,X_r)dr|
  <=[9/(pi R^5)] (E0+E(t)).
```

The same endpoint argument holds after localization at stopping times
with zero-mean stopped martingale. It controls the signed expected total
generator, not expected absolute variation or each separate source.
The stochastic construction and expectation theorem are not newly
Lean-certified here. Their constant is uniform over smooth prefixes
and bounded auxiliary controls, without restarting resources at a seam.

For the continuation candidate, the relevant separated contribution is
`-c D N_R`. The exact accounting is

```text
-c D N_R=(-D+b.grad)H_R
          +N_R D c-2nu grad c.grad N_R-b.grad H_R.
```

Thus the bounded primitive pays one complete signed combination. It
does not pay the weight terms on the right individually. A correction
to a Bellman value must retain them and the corresponding control and
quadratic-gradient terms. The remaining near field and a changing
cutoff scale are also not bounded by this fixed-R result.

There is a stronger comparison at the level of the observable. Keep all
moments fixed except the pressure pairing, and interpolate from `N` to
`N-N_R`. The exact derivative of the logarithmic reserve along this path
is `c_lambda N_R`. Each intermediate reserve has the same unconditional
coercivity, so the same primitive bound holds at every interpolation
parameter. The mean value theorem gives

```text
|log Y(N-N_R)-log Y(N)| <= [9/(pi R^5)] E(t).
```

This pressure-path derivative and comparison are also Lean-certified.
For an actual unforced evolution, `E(t)<=E0` makes the correction uniformly
finite. The interpolation changes an observation of the same fluid;
it does not prescribe a new pressure or a force. It permits a focus on
the nearby pressure in this observable, without any assumption on the
rate of the far pressure. The actual evolution of the nearby fluid still
contains the full pressure, and all derivatives of a corrected Bellman
quantity must be retained. The nearby singular kernel and the remaining
signed history estimate are not bounded by this comparison.

The spatial comparison uses field energy and can also apply to a forced
prefix with the same energy bound. It is not the mechanism that excludes
forced behavior. That distinction remains in the actual evolution and
compatible parent history, including the explicit body-force terms.

### Exact adversarial checks and scope

The periodic checker uses a finite observation kernel with modes
containing every nonzero initial pressure and pressure-time coefficient.
All velocity products and the actual NS tangent are retained; the mode
set truncates the observation, not the fluid evolution. Parent integration
then agrees coefficient by coefficient with the full initial pressure
pairing and its parabolic derivative. A fixed finite observation set is
not asserted to contain the full pressure at later times.

The two observation points are `x=0` and `y=(0,0,pi/2)`. Relative transport
and the mixed gradient are both active. At `nu=0` and `nu=2/7`, all exact
identities pass. An auxiliary common drift cancels from the kernel;
the physical diagnostic force `f=curl u` instead produces nonzero
receiver-vorticity and parent-velocity source terms. This diagnostic is
not the imported forced singularity and proves no internal realization.

Shared diffusion has no automatic favorable sign. For the actual
unforced pressure-free heat shears

```text
u=(U(y,t),0,V(y,t)),
U=exp(-nu t)(cos y+sin y),
V=exp(-nu t)(sin y +/- cos y),
```

the joint reverse generator of the local component
`omega_1(x)^2 u_1(y)^2` at zero has rates `-4nu` and `12nu`, respectively.
These are exact all-parameter evaluations in globally regular flows
with no vortex stretching. They refute only a universal favorable sign
for that component. In projected scalar notation, the mixed diffusion
has the exact decomposition

```text
2nu (v^2 a^2+w^2 b^2+4wvab)
  =3nu (va+wb)^2-nu (va-wb)^2,
```

where `w,v` are receiver/parent amplitudes and `a,b` their derivatives
in the common noise direction. Both squares must be retained before
using geometry. The full pressure kernel also has signed tensor weights.

```sh
python3 -O labs/synchronous_pressure_history.py
```

## Direct pressure reaction after changing the observation

`near_pressure_reaction.py` checks the complete pressure/core production
after a fixed pressure split. This isolates a further term with a finite
allowance: distant pressure still reacts on the local strain, even after
its pairing has been removed from the reserve's measurement.

Write `P=P_n+F`, with `F=K_R*(u tensor u)` the separated tensor from the
preceding section, and `P_n` the retained nearby tensor. For a spatial
cutoff that is one outside `2R`, its kernel is
`K_n=(1-chi_R) partial_abij[1/(4pi|z|)]`, as a distribution. The local
distributional terms at zero are included. No ordinary convergent
near-field integral is assumed.

### The complete nearby production

Put `N_n=omega.P_n omega`, `r=V/(W+eta)`,
`g_n=pressure_eta(N_n)-core_eta`, `theta=h_delta'(g_n)` and
`Y_n=1+core_eta+h_delta(g_n)`. Both regularizers stay strictly positive.
Use the actual unforced fields and `D=partial_t+u.grad-nu Delta`.
The gradient contractions are

```text
A=sum_j |partial_j omega|^2,
C=sum_j [4 partial_j omega.(partial_j S)omega
         +2 partial_j omega.S(partial_j omega)],
K_S=sum_j ||partial_j S||_F^2,
Z_cross=sum_j (S omega).(partial_j S)(partial_j omega),
Z_grad=sum_j |(partial_j S)omega+S(partial_j omega)|^2,
Gamma_n=sum_j [partial_j omega.P_n(partial_j omega)
              +2 partial_j omega.(partial_j P_n)omega].
```

The actual equations give `D W=2V-2nu A`. Define the parts of the other
moment rates left after isolating the direct `F` reaction:

```text
v_n=Z-N_n-nu C,
q_n=-2 tr(S^3)-V/2-2 tr(S P_n)-2nu K_S,
z_n=-2(S omega).P_n omega-4nu Z_cross-2nu Z_grad.
```

Thus `D V=v_n-omega.F omega`, `D Q=q_n-2tr(SF)` and
`D Z=z_n-2(S omega).F omega`. The pressure slot itself retains

```text
D N_n=2(S omega).P_n omega+omega.(D P_n)omega-2nu Gamma_n,
D P_n=K_n*[-grad p tensor u-u tensor grad p
            -2nu sum_j partial_j u tensor partial_j u]
      +[u.grad,K_n*](u tensor u).
```

The commutator means `u.grad(K_n*T)-K_n*(u.grad T)`. This distributional
definition keeps every local term. The pressure `p` at the parents is
the complete actual pressure, not a nearby substitute. Consequently the
split does not close the nearby fluid into an autonomous subsystem.

The full candidate has the exact identity

```text
D Y_n=R_n+R_F,
R_F=-10r (omega.F omega)
    -(1-theta)[(8/7)(S omega).F omega+(20/21)W tr(SF)],

R_n=10r v_n-5r^2 D W
    -10nu/(W+eta)|grad V-r grad W|^2
    +(1-theta)[(4/7)z_n+(10/21)(Q D W+W q_n-2nu grad Q.grad W)]
    +(44/95+theta/5)(2W D W-2nu|grad W|^2)
    -2theta D N_n-nu h_delta''(g_n)|grad g_n|^2.
```

These are parts of one actual evolution. In particular, `v_n,q_n,z_n`
are not asserted to be moment rates of a second fluid. All pressure,
switch and correlated-gradient costs remain in `R_n`.

### A uniform payment for the direct reaction

The scalar reserve has a bounded logarithmic sensitivity to strain:

```text
|R_F|/Y_n <= (9/4) ||F||_F.
```

This holds for every instantaneous geometry and nearby pressure value,
including vorticity zeros. It assumes no sign for `R_F`. To see the
uniform constant, put `s=||S||_F`, `w=|omega|`, `z=|S omega|`, `k=9/4`.
Matrix Cauchy--Schwarz bounds the three tensor contractions, while Young's
inequality bounds the remaining slope by

```text
10|V|w^2/(w^2+eta)+(8/7)zw+(20/21)w^2 s
 <= k[5V^2/(w^2+eta)+(4/7)z^2+(10/21)s^2w^2]
      +(508/189)w^2
 <= k Y_n.
```

The last step uses `w^2 <= (3/4)[1+(44/95)w^4]` and
`127/63<9/4`. `PressureCoreReaction` formally proves the strain-slot
derivative, these scalar bounds and the normalized conversion. Its
contraction hypotheses are explicit; the actual matrix/PDE identification
is analytic and independently checked on full NS Fourier tangents.

The symmetric separated tensor satisfies
`||F||_F <= sqrt(3)||F||_op <=12 E(t)/(pi R^5)` by the previous directional
kernel bound. On an actual unforced smooth prefix, `E(t)<=E0`. Therefore

```text
integral_0^tau |R_F/Y_n|(t,x(t))dt <= 27 E0 tau/(pi R^5)
                                   <= 27 E0 H/(pi R^5),   tau<=H,
L_n=log Y_n-[27 E0/(pi R^5)]t,
D L_n-nu|grad L_n|^2 <= R_n/Y_n.
```

The first assertion holds over any available smooth prefix and any
measurable receiver history; its constant uses the prescribed horizon.
No future strain bound or fresh allowance at an intermediate seam is
used. The tensor identification, finite-horizon application and HJB
conversion here are analytic; the scalar coefficient conversion is
Lean-certified. The coefficient is not uniform as `R` shrinks. This
payment alone does not distinguish unforced fluid from forced fluid with
the same separated-tensor bound. The unforced condition remains essential
in the full moment and parent equations above.

### Checks and the remaining obligation

The exact checker keeps all generated fluid and pressure-time modes.
It tests retaining all pressure, removing all pressure from the observed
slot, and a smooth Fourier multiplier split. These test the algebraic
identity; the multiplier split is not a spatial separation cutoff, and
the fixed-radius estimate is not inferred from those examples.

At viscosity `1/100`, the complete corrected production is strictly
positive in all three cases. Each sign has a rational lower certificate;
printed decimal rates only illustrate size. The omitted pressure remains
in the actual NS tangent, and its strain reaction agrees with the formula
above. These are initial-time tests on smooth data, not singularities or
refutations of a full-datum history allowance. The unresolved target is
a uniform signed history bound for `R_n/Y_n`, retaining the actual nearby
parent pressure, geometry and spatial gradients.

```sh
python3 -O labs/near_pressure_reaction.py
```
