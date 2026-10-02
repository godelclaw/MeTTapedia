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

## Viscous parent memory and the local heat defect

`viscous_parent_memory.py` tests whether the complete pressure/core
envelope automatically dissipates under viscosity. It finds an explicit
failure due to pressure at the parents and checks a physical memory
correction for precisely that source.

### A fixed-energy two-wave family

On the torus of period `2pi`, for an integer `n>=1`, take

```text
u_n=(sin(n(x+y)),
     2sin(nx)-sin(n(x+y)),
     sin(nx)-sin(n(x+y))).
```

The datum is divergence-free, and its mean squared speed is four,
independently of `n`. It depends on two coordinates and is not a
singularity candidate. Its canonical zero-mean pressure is

```text
p=(2/5)cos(n(2x+y))+2cos(ny).
```

At the origin its strain, vorticity and pressure Hessian are

```text
S=n [[1,1,0],[1,-1,-1/2],[0,-1/2,0]],   omega=(-n,0,0),
P=n^2 [[-8/5,-4/5,0],[-4/5,-12/5,0],[0,0,0]].
W=n^2, Q=(9/2)n^2, V=n^3, Z=2n^4, N=-(8/5)n^4.
```

All first spatial derivatives of these three fields vanish there.
Set the envelope regularizers to `eta=delta=1`. Its branch gap is
`g=(4/35)n^4>0`, so `theta=h_1'(g)>1/2`.

The *parabolic viscosity contribution* is the following differential
of the actual scalar observable, including the dependence of its
canonical pressure on the velocity:

```text
H_Y = derivative_of_Y[u](nu Delta u) - nu Delta_x Y[u].
```

This differs from its temporal derivative under the heat equation.
The strain/vorticity moment heat defects and the switch-gradient term
vanish at this receiver, but the complete pressure contributes

```text
P_t^heat-nu Delta P
  =nu n^4 [[-16/5,-8/5,0],[-8/5,16/5,0],[0,0,0]],
H_Y=(32/5)nu theta n^6.
```

Thus `H_Y>0` when `nu>0`, although all receiver first-gradient damping
terms vanish. Also `Y<=11n^4`, giving

```text
H_Y/Y >= (16/55)nu n^2,    n>=1.
```

`PressureViscousMemory` certifies the scalar family gap, weight, upper
bound, normalized lower bound, and its unboundedness over natural
frequencies. The Fourier realization and differential identification
are analytic and independently checked at `n=1,2,3` with the full
unforced NS tangent. The family formula follows from the displayed
pressure and the heat rates of its two parent modes.

This rules out automatic scalar heat dissipation, or a universal
energy-only instantaneous coefficient paid solely by receiver first
gradients. It is not a time-integral obstruction or a failure of a
full-datum allowance. Indeed both branch *temporal* heat derivatives
are negative in the three exact tests. At `n=1`, per unit viscosity,
they are `-3753/95` and `-81397/1995`. Positive `H_Y` cannot be read as
viscosity increasing the actual reserve value under heat evolution.

### An actual retained matrix history

Let `u,p` be an existing smooth unforced NS evolution on a compact
time prefix, with `nu>0`, and put

```text
D=partial_t+u.grad-nu Delta,
T=u tensor u,
G=sum_j partial_j u tensor partial_j u.
```

For the periodic case use normalized volume. For the whole-space case
assume the lane's smooth finite-energy class, with all spatial jets
in `L^2` continuously on the prefix. The corresponding bounded smooth
coefficients and integrable source give the componentwise linear problem

```text
D C=2nu G,    C(0)=0.
```

Its analytic identification with actual stochastic histories is explicit.
For each terminal `(t,x)`, use the backward characteristic

```text
dX_s=-u(t-s,X_s)ds+sqrt(2nu)dB_s,   X_0=x,   0<=s<=t.
C(t,x)=E integral_0^t 2nu G(t-s,X_s)ds.
```

Every integrand is positive semidefinite, so `C>=0`. Along that same
path, the sampled velocity has the Itô differential

```text
d[u(t-s,X_s)]
  =grad p(t-s,X_s)ds+sqrt(2nu)grad u(t-s,X_s)dB_s.
```

Consequently `C` is the expected accumulated matrix quadratic variation
of this sampled velocity. The pressure drift remains. In general `C`
is **not** the covariance of the terminal velocity. For the separate
pure heat equation with zero spatial drift it is the familiar covariance
`heat_t(u0 tensor u0)-heat_t(u0) tensor heat_t(u0)`.

Driving all initial labels by the same Brownian displacement produces
a volume-preserving map: its spatial Jacobian evolves with the
divergence-free drift, and the noise is a common translation. Tonelli's
theorem and the actual kinetic energy equality therefore give

```text
integral tr C(t) = 2nu integral_0^t integral |grad u|^2
                = E0-E(t),
A=T+C >=0,                 integral tr A(t)=E0,
D A=-(grad p tensor u+u tensor grad p).
```

These identities hold on every available smooth prefix. Their mass
bound is independent of its endpoint and uses no future regularity
bound. The signed pressure work has not disappeared; the trace equation
still contains its local divergence `-2 div(pu)`.

If `U_u(t,s)` is the actual scalar advection-diffusion propagator,
composition retains already accumulated memory:

```text
C(t)=U_u(t,s) C(s)+2nu integral_s^t U_u(t,r) G(r)dr.
```

The state passed across a history boundary includes `C(s)` and the
full fluid state. Resetting `C` to zero would erase physical information
and restart the same kinetic-loss allowance. No auxiliary stochastic
control is applied as a body force in this construction. Changing the
sampling drift would require retaining its additional generator terms.

### Pressure of the augmented stress

Let `K` denote the full translation-invariant pressure-Hessian operator:
`P=K*T`. On the torus it uses the canonical zero-mean pressure. On
whole space it is the fourth derivative of the Newtonian distribution,
including the local terms at zero. Define

```text
P_star=K*A=P+K*C.
D P_star
  =K*[-grad p tensor u-u tensor grad p]+[u.grad,K*]A.
```

The Laplacian commutes with `K`, so the explicit viscous source
`-2nu K*G` cancels. The actual pressure `p` at every parent and the
transport commutator both remain. Retaining this memory is a change
of observable, not a replacement of the NS pressure equation.

Replace `N` in the same coercive envelope by
`N_star=omega.P_star omega`, keeping the physical `S,omega`.
Initially `C=0`, so this candidate has exactly the previous finite
full-datum initial reserve and still controls `|omega|^4`.
At the two-wave receiver, `C_t=2nu G` and the tensor `K*C_t` cancels
the displayed pressure heat defect coefficient by coefficient. The
corrected initial viscosity contribution is zero.

At later times the actual strain still sees `P=P_star-K*C`.
The direct reaction of this difference has the bound from the preceding
section, `(9/4)||K*C||_F` after normalization. For any fixed whole-space
separation radius `R>0`, positivity and the trace mass extend the
separated kernel estimate from rank-one velocity tensors to `C`:

```text
||K_R*C||_F <=12 [E0-E(t)]/(pi R^5),
integral_0^tau |separated direct reaction|/Y_star
  <=27 E0 H/(pi R^5),    tau<=H.
```

This is an analytic consequence of the previously certified scalar
reaction bound and separated kernel estimate. It does **not** pay
the nearby singular action `K_near*C`. A finite total trace permits
concentration; it is not a bound on the pressure Hessian. Nearby memory
pressure, signed pressure work, the commutator, and the correlated
receiver gradients remain the physical history obligations. No general
heat-subsolution claim is made for the corrected envelope.

The earlier logarithmic observation bound gives a sharper organization
at a fixed whole-space radius. Since `A>=0` and its trace mass is `E0`,
the same pressure-slot sensitivity bounds the cost of removing `K_R*A`
from `Y_star` by `9E0/(pi R^5)`. Write `K_n=K-K_R` and set

```text
P_hat=K_n*A,    N_hat=omega.P_hat omega,
Y_hat=reserve(S,omega,N_hat),
P=P_hat+F,     F=K_R*T-K_n*C,
D P_hat=K_n*[-grad p tensor u-u tensor grad p]+[u.grad,K_n*]A.
```

This leaves the direct distant reaction of `K_R*T`, already paid by
`27E0 H/(pi R^5)`, and the direct reaction of `-K_n*C`, still unpaid.
The complete reserve production is the earlier `R_n+R_F` formula with
`P_n` replaced by `P_hat` and the displayed parent equation used for
`D N_hat`. Linearity splits `R_F` into those two direct reactions.
All its receiver-gradient and changing-weight terms remain. This exact
reorganization avoids treating the stored memory as an independent
force, or paying its same distant contribution twice.

For a forced fluid, `D A` additionally contains `f tensor u+u tensor f`,
and its total trace is `E0+2 integral_0^t integral u.f` in the squared-speed
convention used here. Finite force work is compatible with the imported
forced examples. Thus fixed trace mass alone cannot distinguish the
target unforced mechanism; the complete coupled parent equations must
supply that distinction.

### The remaining controlled-history estimate

The same organization gives a precise sufficient target. Put
`B_near=(R_hat+R_{-K_n*C})/Y_hat`, where `R_hat` is the preceding complete
nearby production with its corrected parent equation, and set
`kappa=27E0/(pi R^5)`. Then

```text
L=log Y_hat-kappa t,
D L-nu|grad L|^2 <= B_near.
```

For the auxiliary sampling process
`dX_s=[-u(t-s,X_s)+b_s]ds+sqrt(2nu)dB_s`, the sufficient missing bound is

```text
sup_b E integral_0^t [B_near(t-s,X_s)-|b_s|^2/(4nu)]ds
  <= A(u0,nu,H,R),    t<=H,
```

uniformly in receivers and all available smooth prefixes. The supremum
may be taken over bounded adapted controls on each prefix. Completing
the square in Itô's formula, with `b=2nu grad L`, would give
`sup_x log Y_hat(t,x)<=sup_x log Y_hat(0,x)+kappa H+A`.
Coercivity would then give a finite-horizon vorticity bound and the
existing continuation criterion. This is an analytic sufficient
inequality, not a bound established here. Defining `A` by the unknown
future supremum would not prove its finiteness from the datum. Every
sampled field, including the retained matrix, must remain the same
actual unforced solution; the control only changes the observation path.

### Certification boundary

The six scalar family statements are Lean-certified. The matrix-memory
construction, stochastic identification, composition and all-time mass
identity above are analytic. Besides the two-wave tests, the exact
checker differentiates a nonsymmetric three-dimensional NS datum twice
in time from `C(0)=0`. It retains every convolution mode, checks the
augmented stress equation and its time derivative, the actual corrected
pressure commutator, and zero first and second rates of total trace.
Its initial memory mass rate is `4087576/444675` at `nu=1/5`, exactly
the lost kinetic energy rate. These are time-jet checks, not numerical
evolutions or certification of an arbitrary-history continuation bound.

```sh
python3 -O labs/viscous_parent_memory.py
```

## A nonnegative reserve for memory geometry

`viscous_memory_entropy.py` develops a payment for actual spatial
variation and stochastic turning of the retained memory. It starts
from the preceding physical equation `D C=2nu G`, with `C(0)=0`,
`C>=0`, and `G=sum_j partial_j u tensor partial_j u`. Fix `eta>0` and
write

```text
H=eta I+C,
Phi_eta(C)=tr C-eta log det(I+C/eta),
r_eta=|u|^2+Phi_eta(C),
R_eta(t)=integral r_eta(t,x) dx.
```

For each eigenvalue `c>=0`,

```text
phi_eta(c)=c-eta log(1+c/eta),
0<=phi_eta(c)<=c,
phi_eta'(c)=c/(eta+c),   phi_eta''(c)=eta/(eta+c)^2.
```

Consequently `R_eta>=0` and its initial value is exactly `E0`. No
initial derivative bound is needed for this particular global resource.
The regularizer remains fixed; changing it in space or time would
introduce additional terms.

### The actual local and global balance

Matrix differentiation, valid through eigenvalue coincidences because
`H` is positive definite, gives

```text
D log det H = tr(H^(-1) D C)+nu F,
F=sum_j tr(H^(-1)(partial_j C) H^(-1)(partial_j C)) >=0,
J=2nu eta tr(H^(-1)G) >=0,
D r_eta=-2 div(pu)-J-nu eta F.
```

Here `F` is a sum of squared Frobenius norms of the symmetric matrices
`H^(-1/2)(partial_j C)H^(-1/2)`. Positivity of `G` makes `J`
nonnegative even when `G` and `C` do not commute. The actual full
pressure flux is retained in the local identity.

For every available smooth unforced prefix,

```text
R_eta(t)+integral_0^t integral [J+nu eta F] dx ds=E0.
```

On the torus this follows by integration with normalized volume.
On whole space use smooth cutoffs tending to one. Since
`0<=r_eta<=|u|^2+tr C`, its spatial integral is at most `E0` by the
previous mass identity. The transport and diffusion boundary errors
vanish using bounded velocity on each compact smooth prefix and this
`L^1` bound. The pressure boundary error vanishes using `pu in L^1`
on that prefix; the canonical pressure is in `L^2` and the velocity
is in `L^2`. Monotone convergence for the nonnegative costs then gives
both their integrability and the identity above. No future uniform
gradient bound is used in the resulting constant `E0`.

This is a nonnegative resource for the **displayed weighted source and
matrix-gradient costs**. It does not yet control vorticity or the
pointwise pressure Hessian. Compatible segments retain `C` and the
terminal `R_eta`; applying the same identity on the next segment gives
its remaining allowance, not a fresh copy of `E0`.

### What the matrix gradient cost pays

In an orthonormal eigenframe write `a_i=eta+c_i>0`. The invariant
expression for `F` has the pointwise decomposition

```text
F=sum_j [sum_i |partial_j c_i|^2/a_i^2
         +2 sum_(i<k) (a_i-a_k)^2/(a_i a_k)
                       |e_i.partial_j e_k|^2].
```

The frame formula applies where the required eigenvectors are smooth;
the matrix formula for `F` requires no spectral gap. Rotation within
an exactly repeated eigenspace has no observable cost. If
`a_i>=2a_k`, then

```text
2 (a_i-a_k)^2/(a_i a_k) >=1.
```

Thus changes of a separated memory direction consume the resource.
The coefficient grows with anisotropy; it is not an unweighted penalty
imposed on every choice of basis.

The positive source itself contributes to frame turning. In the same
basis its `i,k` angular rate is `2nu G_ik/(c_i-c_k)`. Put
`x=G_ii/a_i`, `y=G_kk/a_k`, `z=G_ik/sqrt(a_i a_k)`.
Positive semidefiniteness gives `z^2<=xy`, and for `a_i>=2a_k`,

```text
|2nu G_ik/(c_i-c_k)| <=2nu(x+y) <=J/eta.
```

This source rate alone is not the complete material or stochastic
frame derivative. The diffusion terms must also be retained.

### The complete stochastic principal-direction projector

Let `a_1>=a_2>=a_3` and restrict the observation to
`Omega={a_1>=2a_2}`. The principal projector `Pi=e_1 tensor e_1`
is smooth on the larger open set where the top eigenvalue is simple;
it is independent of the sign of `e_1`. Its actual parabolic law is

```text
D Pi=D_C Pi[2nu G]-nu sum_j D_C^2 Pi[partial_j C,partial_j C].
```

For a symmetric matrix increment `E`, let `d=c_1-c_2>=a_1/2`.
Elementary eigenvector differentiation gives

```text
||D_C Pi[E]||_F <=sqrt(2)||E||_op/d,
||D_C^2 Pi[E,E]||_F <=12||E||_op^2/d^2.
```

For the second bound, in an eigenbasis put
`v_b=E_b1/(c_1-c_b)`, `v_1=0`. The second normalized eigenvector
derivative satisfies
`w_1=-|v|^2` and
`w_b=2[(Ev)_b-E_11 v_b]/(c_1-c_b)` for `b!=1`.
Then `Pi''=w tensor e_1+e_1 tensor w+2v tensor v`;
`|v|<=||E||_op/d` and `|w_perp|<=4||E||_op^2/d^2` give the
displayed constant. This only uses the gap from the top eigenspace;
the two lower eigenvalues may coincide.

Since `G>=0`, `||G||_op<=tr G` and
`tr(H^(-1)G)>=tr G/a_1`. For the gradient increments,
`||partial_j C||_op<=a_1||H^(-1/2)(partial_j C)H^(-1/2)||_F`.
The preceding estimates therefore imply, on `Omega`,

```text
||D Pi||_F <=3 J/eta+48nu F,
sum_j ||partial_j Pi||_F^2 <=2F.
```

The second inequality also follows directly from the frame decomposition.
The entropy identity pays the complete geometric drift and noise:

```text
eta integral_0^t integral_Omega ||D Pi||_F <=48E0,
eta integral_0^t integral_Omega 2nu sum_j ||partial_j Pi||_F^2 <=4E0.
```

Along the actual backward characteristic, Itô's formula has drift
`-D Pi` and noise coefficient `sqrt(2nu)grad Pi`, up to an exit from
the simple-eigenvalue region. The last two estimates therefore control
its stochastic drift and quadratic variation **after integration over
receiver positions**. The common-noise flow preserves volume. These
are not bounds for a worst receiver or a controlled sampling density,
and no free endpoint bound is asserted across arbitrary spectral-gap
exits and re-entries.

### Scope, checks and the next physical estimate

`ViscousMemoryEntropy` certifies eight scalar statements: the initial
entropy, its bounds and first two derivatives, the eigenvalue-sum bounds,
the exact source balance, and the two orientation coefficients. The
matrix calculus, complete projector estimates and actual NS
space-time identities above are analytic. In particular, the formal
module does not yet construct the stochastic matrix process.

The exact checker uses the complete unforced shear histories starting
from `u0=(3(sin y+alpha cos y),0,cos(2y))`, `alpha=0,1`. Here
`q=exp(-nu t)`, the velocity evolves by the heat equation, and
`C=heat_t(u0 tensor u0)-u(t) tensor u(t)` exactly. Fluid and memory
pressure are zero throughout this class. The checks keep every Fourier
mode and differentiate the determinant polynomial independently of
the inverse-matrix formula. At `q=1/2,3/4`, `nu=1/5`, `eta=1`,
they verify the local reserve balance, total energy-plus-memory mass,
matrix positivity, spatial and source turning payments, and the full
projector drift/noise bounds. At `alpha=0` the memory gradient cost at
the receiver is entirely due to orientation. For `alpha=1` the
source-induced turning is also nonzero. The initial case `q=1` checks
the entropy identity through the completely repeated memory eigenvalue;
no principal direction is assigned there. The independent symbolic
three-dimensional projector derivatives satisfy the differentiated
commutation, idempotency and trace identities through second order.

The memory's principal direction is not identified with the vorticity
direction. Turning of this memory is only one part of the geometry
that must enter the signed nearby-pressure estimate. Spatially
integrated cost can concentrate, so the above budget does not provide
the controlled-history bound for `B_near` in the preceding section.
Both the pressure/vorticity comparison and receiver concentration
remain obligations; they may need to be controlled jointly.

For forced fluid the same calculation adds `2u.f` to the local balance
and cumulative force work to the global allowance. Finite-work forced
examples can therefore obey this geometric budget. It is not, by
itself, an obstruction to their realization or an unforced regularity
argument. Any continuation application must use the rest of the
actual unforced parent equations, including the signed pressure terms.

```sh
python3 -O labs/viscous_memory_entropy.py
```

## Memory pressure, spatial rearrangement and the receiver cost

`viscous_memory_pressure.py` connects the paid matrix metric to an actual
pressure pairing. It also checks an unforced history where pressure is
generated without turning the memory eigenframe. Both results concern
the nearby-memory term in the preceding pressure/core reserve.

### A weighted pressure estimate on actual memory histories

Retain `H=eta I+C`, fixed `eta>0`, and the paid metric
`F=sum_j tr(H^(-1) C_j H^(-1) C_j)`. Put `m=tr H` and `h=div C`.
At a point, diagonalize `H` in an orthonormal basis frozen there, with
eigenvalues `a_i>0`. The entries `d_jik` are full tensor derivatives;
they include orientation changes, not just eigenvalue derivatives.
Weighted Cauchy--Schwarz gives

```text
h.H^(-1)h <= m F,
|h.v|^2 <= F [m v.H v].
```

For example, apply it to `h_i=sum_j d_jij` with weights `a_j`, divide
by `a_i`, and sum over `i`. The resulting sum uses only a subset of
the nonnegative terms in `F`. A second weighted Cauchy--Schwarz gives
the receiver bound. `ViscousMemoryPressure` proves these finite-tensor
inequalities and their Young-inequality form, with no commutation or
alignment assumption on `C_j`.

For a smooth test tensor `M`, let `q_M` solve
`-Delta q_M=div div M`, with the canonical periodic or whole-space
normalization. Write `P_C=Hess q_C`. Spatial integration by parts gives

```text
integral M:P_C = -integral h.grad q_M.
```

The sign is consistent with
`integral C:P_C=integral |grad q_C|^2>=0`. On any available smooth
unforced prefix, define the receiver cost

```text
T(M)=integral_0^t integral m (grad q_M).H(grad q_M).
```

For smooth periodic tests, or suitable decaying whole-space tests with
the displayed integrals finite, the preceding entropy identity yields

```text
|integral_0^t integral M:P_C| <= sqrt[E0 T(M)/(nu eta)],
|integral_0^t integral M:P_C|
  <= alpha E0 + T(M)/(4 alpha nu eta),   alpha>0.
```

The first factor is paid from the initial datum. **No uniform bound on
`T(M)` is asserted.** The pressure integration and space-time application
are analytic; the finite-tensor and scalar inequalities are Lean-certified.

The named consumer is the direct memory-pressure contribution in
`B_near`: after smoothing the receiver, take
`M=rho (partial_S Y_hat)/Y_hat`, holding the observed pressure slot fixed
in this strain derivative. The full pressure operator is used in the
pairing identity. Replacing it by `K_near` adds the already controlled
fixed-radius far-memory correction. This does not remove the other
parent-pressure, commutator or receiver-gradient terms from `B_near`.
Controlling this particular `T(M)`, together with the cancellations of
the complete source, remains a physical estimate, not a new definition
of a supposedly finite reserve.

### Coherent rank-one stress and the missing transversality

Locally write a rank-one stress as `C=b^2 a tensor a`, with `b>0` and
`|a|=1`. Let `c=b^2` and `delta=div(b a)`. Direct differentiation gives

```text
div C = c[(a.grad)a-(div a)a] + 2b delta a,
F = |grad c|^2/(eta+c)^2
    +2c^2 |grad a|^2/[eta(eta+c)].
```

Denote the second term by `F_angle`. Since `a` is unit, curvature is
orthogonal to `a`, and
`|(a.grad)a|^2+(div a)^2<=2|grad a|^2`. Consequently

```text
delta=0  implies  nu |div C|^2/(eta+c) <= nu eta F_angle,
nu |div C|^2/(eta+c) <= 2nu eta F_angle+8nu delta^2.
```

Thus genuine solenoidality of the rank-one factor makes geometry pay
for its stress divergence. A fixed direction with transverse amplitude
has zero stress divergence and zero pressure. The extra `delta` is an
explicit defect when that transversality fails. The two local algebraic
bounds are Lean-certified; no rank-one assumption is made for arbitrary
NS memory, and no averaging over hidden parents is claimed to preserve
this sharper cost.

Each source vector `partial_j u` is solenoidal at birth. Componentwise
passive transport need not preserve this property, even though the
fluid itself remains incompressible. For a vector carried by the common
Brownian translation, its Stratonovich divergence equation contains

```text
d delta+u.grad delta dt+sqrt(2nu) grad delta . circ dB
  =-sum_(i,j) (partial_i u_j)(partial_j v_i) dt.
```

This is a defect of the transported vector, not compressibility of
the fluid. At the retained tensor level, the exact deterministic law is

```text
D h_i=2nu (div G)_i
       -sum_(j,k) (partial_j u_k)(partial_k C_ij).
```

Any use of transported transverse parents must account for this term.
The entropy controls `h` in the weighted sense above, but neither this
equation nor incompressibility alone bounds the receiver cost.

### Actual unforced histories with a fixed memory eigenframe

On the period-`2pi` torus take, for `n>=1`,

```text
u(t)=q(t) (sin(nx)cos(ny), -cos(nx)sin(ny), beta sin(nx)sin(ny)),
q(t)=exp(-2nu n^2 t),
p(t)=q(t)^2 [cos(2nx)+cos(2ny)]/4.
```

These are complete smooth unforced NS solutions. The third component
is a multiple of the horizontal streamfunction; its advection is zero.
Their mean squared speed initially is `1/2+beta^2/4`. Use actual memory
`D C=2nu G`, `C(0)=0`. Direct calculation gives `div G=0` for this
entire family. Nevertheless,

```text
q_C(0)=partial_t q_C(0)=0,
partial_t^2 q_C(0)
  =(2nu n^3/5)[cos(3nx)cos(ny)-cos(nx)cos(3ny)].
```

The source and Laplacian terms have zero pressure. The displayed term
is precisely the pressure of `-2nu u.grad G`, so it records internal
transport of the memory source.

For `beta=0`, every source matrix has the form
`[[g,d,0],[d,g,0],[0,0,0]]`. Uniqueness of the componentwise linear
parabolic problems preserves that form for `C` at every time. Hence
one constant orthonormal frame diagonalizes every memory matrix; its
orientation part of `F` vanishes. Pressure is still generated. This
is not a failure of the full entropy budget, which includes amplitude
variation and the source cost `J`.

The generated pressure also enters the existing reserve with a positive
sign at a concrete receiver. Set `n=1`, `nu=1/5`, `beta=0`, and choose
`x=y` with `cos x=3/5`, `sin x=4/5`. With the envelope regularizers equal
to one, and using the full canonical pressure observation `Y_star`
(no separated cutoff in this periodic test), its initial switch gap
and the second time derivative of the
direct memory reaction are

```text
g_0=4575232/13671875,
partial_t^2 R_memory(0)=(1-theta_0) 138018816/341796875 > 0,
theta_0=(1+g_0/sqrt(g_0^2+1))/2.
```

Here `R_memory=(partial_S Y_star):P_C`; `P_C` and its first time
derivative vanish initially, so no changing-weight terms are missing
from this second derivative. The same conclusion holds for the
normalized reaction after division by the positive initial reserve.
Smoothness gives a positive short-time interval for each fixed datum;
no uniform Taylor window over frequencies is claimed.

This refutes paying this entire direct memory contribution solely by
turning of the memory eigenframe, with no additional allowance. It
does not refute a full-datum budget, the full entropy cost, or regularity.
For `beta=1` there is also a nonzero direct vorticity-pressure pairing;
the checker does not claim a constant full memory eigenframe in that case.
These remain regular periodic examples, not finite-energy whole-space
flows or singularity candidates.

### The unsmoothed point-receiver limit still fails

The weighted weak estimate cannot be inserted directly into the Bellman
target. This is visible even with `C=0`. On whole space let
`rho_s=(4pi nu s)^(-3/2) exp(-|x|^2/(4nu s))` and `M=rho_s I`.
Then `q_M=-rho_s`, `H=eta I`, and

```text
integral |grad rho_s|^2 = [3/(4nu s)](8pi nu s)^(-3/2),
T(M)=3eta^2 integral_0^t integral |grad rho_s|^2 = infinity.
```

The endpoint divergence is `s^(-5/2)`, although actual memory pressure
work in this zero-memory example is zero. This is a limitation of the
unsubtracted dual norm, not divergent fluid dynamics. For any nonzero
constant symmetric coefficient `A`, replacing `M` by `rho_s A` multiplies
the gradient norm by `[(tr A)^2+2tr(A^2)]/15>0`, so the same endpoint
problem remains. These are tests of the dual norm, not an identification
of an arbitrary coefficient with the actual reserve receiver. Smooth receivers
with positive initial width give finite costs. Passing to a point
requires additional pressure cancellations or a stronger joint estimate;
finite total entropy alone does not justify that limit.

The exact checker verifies the full symbolic-in-time NS equations,
memory time derivatives at `n=1,2`, `beta=0,1`, and `nu=1/5`, the
pressure pairing sign, weighted matrix inequalities, rank-one
sum-of-squares decompositions, the passive-parent divergence defect,
and the Gaussian endpoint integral. The six formal statements concern
finite-dimensional inequalities. None claims the missing arbitrary-data
controlled-history bound.

```sh
python3 -O labs/viscous_memory_pressure.py
```

## Geometric-mean normalization and a conditional continuation bound

The point-receiver obstruction motivates using the memory equation
locally before estimating a spatial pressure pairing. The candidate
in `viscous_memory_normalization.py` keeps the complete envelope and
divides it by a scalar constructed from actual retained memory.

Fix the memory regularizer `eta>0`, independently of the envelope's
positive regularizers. On every available smooth unforced prefix set

```text
H=eta I+C,
h=det(I+C/eta)^(1/3),    psi=log h,
A_j=H^(-1/2)(partial_j C)H^(-1/2),
F_shape=sum_j [||A_j||_F^2-(tr A_j)^2/3].
```

Arithmetic--geometric mean and `C>=0` give
`1<=h<=1+tr C/(3eta)`. The shape cost is nonnegative: each summand
is `||A_j-(tr A_j)I/3||_F^2`. It retains all orientation changes and
changes in relative eigenvalues, while subtracting isotropic expansion.
There is no spectral-gap assumption, and repeated eigenvalues are
harmless. The earlier Taylor--Green example has a fixed eigenframe;
its relative eigenvalues can still vary.

### The actual geometric payment and sampling law

Using `D C=2nu G` in the full determinant chain rule gives

```text
Q_geom=(2nu/3) tr(H^(-1)G)+(nu/3)F_shape >=0,
D h = h Q_geom,
D psi-nu|grad psi|^2=Q_geom.
```

In particular, define the nonnegative local and global reserves

```text
r_vol=|u|^2+tr C-3eta(h-1) >=0,
R_vol(t)=integral r_vol(t,x) dx.
```

Their actual unforced balances are

```text
D r_vol=-2 div(pu)-3eta h Q_geom,
R_vol(t)+3eta integral_0^t integral h Q_geom=E0.
```

The whole-space cutoff argument is justified by
`0<=r_vol<=|u|^2+tr C` and `0<=h-1<=tr C/(3eta)`, as in the preceding
entropy identity. Nonnegative costs are integrated by monotone
convergence. No uniform future norm is used in the resulting allowance.
This is a genuine resource for the displayed costs; it does not itself
control their distribution along a concentrated receiver.

The corresponding stochastic law is also explicit. Along the actual
backward viscous characteristic
`dX_s=-u(t-s,X_s)ds+sqrt(2nu)dB_s`, the density

```text
Z_s = h(t-s,X_s)/h(t,x)
      * exp(integral_0^s Q_geom(t-r,X_r)dr)
```

has stochastic differential
`dZ_s=Z_s sqrt(2nu) grad psi(t-s,X_s).dB_s`. On each compact smooth
prefix its bounded coefficients justify the martingale and change of
measure. The reweighted path has drift `-u+2nu grad psi`. It is an
auxiliary sampling process; all physical fields remain the same actual
unforced solution. The density ratios telescope at intermediate times
and its integral costs add, provided the actual memory at the seam is
retained. This identifies a concrete Doob transform, not an independently
chosen endpoint-constrained Schrödinger-bridge optimizer.

### The normalized Bellman target

Retain the earlier nearby observation `Y_hat`, its complete signed
source `B_near`, and its paid distant coefficient
`kappa=27E0/(pi R^5)` for fixed whole-space separation `R>0`. In the
periodic full-pressure formulation use its complete source and no
separated term. Put

```text
Z=Y_hat/h,      L=log Z-kappa t,
D_tilde=partial_t+(u-2nu grad psi).grad-nu Delta.
```

The change of observable and drift gives exactly

```text
D_tilde L-nu|grad L|^2 <= B_near-Q_geom.
```

Thus the missing sufficient bound can be sought on these particular
compatible histories:

```text
sup_b E integral_0^t
  [B_near(t-s,X_s)-Q_geom(t-s,X_s)-|b_s|^2/(4nu)]ds
  <= A(u0,nu,H,R,eta),     t<=H,
dX_s=[-u+2nu grad psi+b_s](t-s,X_s)ds+sqrt(2nu)dB_s.
```

The bound must be uniform in receivers and all available smooth
prefixes. The control `b` changes sampling only. Since `h(0)=1`, Itô's
formula and square completion would give

```text
sup_x Z(t,x) <= exp[sup_x log Y_hat(0,x)+kappa H+A].
```

This reward bound is **not proved here**. It retains the full nearby
pressure, parent commutator, memory reaction and receiver-gradient
terms in `B_near`. The explicit nonnegative subtraction changes the
candidate estimate; the finite global payment alone does not bound
its expectation under arbitrary controlled sampling.

### Why the normalization still suffices for continuation

Here is an analytic implication in both settings, for `nu>0`. Suppose
`Z<=B` uniformly on all prefixes up to a prescribed horizon, with `B`
fixed from the datum and parameters. Coercivity of the envelope gives
`Y_hat>=(44/95)|omega|^4`. Set `M=(95/44)B` and `c=tr C`. Then

```text
|omega|^4 <= M[1+c/(3eta)].
```

On whole space the constant on the right cannot be integrated. Instead,
split at `|omega|^4=2M`. The low part is paid by enstrophy, and the high
part by memory:

```text
|omega|^4 <= sqrt(2M)|omega|^2+(2M/(3eta))c.
```

Write `W(t)=integral |omega|^2`, `F4(t)=integral |omega|^4`. The actual
energy equality and memory mass give

```text
integral_0^t W <= E0/(2nu),    integral c(t)<=E0,
integral_0^t F4 <= K4,
K4=sqrt(2M)E0/(2nu)+2M E0 H/(3eta),    t<=H.
```

The same argument works with normalized periodic volume. All these
constants are independent of the endpoint of the available prefix.
`ViscousMemoryNormalization.integrable_quartic_of_memory` formally proves
the spatial splitting and integral bound on an arbitrary measure space.
It does not assume integrability of the fourth power in its hypotheses.

There is a shorter continuation argument that is now formalized in
`WholeSpaceMemoryEnvelope`. For a velocity-gradient matrix `A`,

```text
2 omega.A omega <= |A|_F^2+|omega|^4,
```

because the difference is `sum_ij (A_ij-omega_i omega_j)^2`.
Betchov's identity identifies the integral of this stretching with the
literal order-one NS production. Consequently, on an actual unforced
whole-space evolution,

```text
W' <= W+F4 <= (1+sqrt(2M))W+(2M/(3eta))E0.
```

This linear differential inequality gives a horizon bound directly.
`hasNSEvolution_of_mass_envelope` and
`wholeSpaceStatementA_of_mass_envelope` certify the actual continuation
implication. The hypothesis requires common constants from the datum
and horizon for every available smooth prefix. Neither the physical
construction of C nor a bound on the normalized envelope is assumed to
have been proved. The determinant and stochastic identifications above
remain analytic; the corresponding periodic application is analytic.
The following section gives a weaker, spatially integrated target.

### Checks and scope

Six formal statements certify normalized scalar coercivity, the
low/high-amplitude split, its measure-theoretic integrability consequence,
the matrix shape identity and positivity, and the exact change of drift.
The determinant calculus, nonnegative physical reserve, Doob density and
NS continuation application remain analytic. Generic noncommuting
matrix jets check the full determinant formula independently. Six exact
positive-time and initial shear samples check its physical realization,
including repeated eigenvalues; their complete normalized envelope is
a parabolic subsolution for the derived auxiliary drift. These shears
have no vortex stretching and do not establish the general reward bound.
A full nonsymmetric three-dimensional NS initial tangent, with `C(0)=0`
and viscosity `1/1000`, has strictly positive normalized parabolic
production even after the memory correction and geometric subtraction.
A rational lower certificate is included. This refutes automatic
subsolution behavior, not temporal growth, regularity, or a full-datum
history allowance. The remaining signed estimate is still necessary.

All continuation claims above concern unforced NS. A body force adds
terms to the physical energy, vorticity and envelope equations. No claim
that an imported forced candidate violates this particular normalized
bound is made without checking those hypotheses and terms.

```sh
python3 -O labs/viscous_memory_normalization.py
```

## Space-time excess, actual continuation and the forced comparison

`WholeSpaceMemoryEnvelope` and `WholeSpaceMemoryExcess` connect the
geometric observable to actual smooth NS evolutions on whole space.
They also test both sufficient criteria on the imported forced solution.
The open input is now allowed to be a space-time excess bound, rather
than a uniform pointwise bound on the normalized observable.

### The formal physical estimate

For the literal curl of a smooth solenoidal velocity, define the spatial
property `MassEnvelope u M B` by

```text
there exists c>=0, integrable on R3, with integral c<=B,
|omega|^4 <= M(1+c).
```

The majorant may encode the entire retained history. Its existence with
common constants is an estimate to prove, not a definition that assumes
regularity. For `M>=0`, the low/high-amplitude split gives

```text
integral |omega|^4 <= sqrt(2M) W+2MB,
W=integral |omega|^2=integral |grad u|^2.
```

The proof derives fourth-power integrability; it does not assume it.
The actual unforced production obeys `W'<=W+integral |omega|^4`, by the
sum-of-squares and Betchov argument above. If `B=B(t)>=0` is a continuous
capacity path, the kernel-checked bound is

```text
1+W(t) <= (1+W(0)) exp[(1+sqrt(2M))t+2M integral_0^t B(s)ds].
```

Thus the capacity may have large peaks. Its time integral alone must
have a bound fixed from the full datum, viscosity and prescribed horizon,
uniformly over all available smooth prefixes. The theorems
`hasNSEvolution_of_memory_capacity` and
`wholeSpaceStatementA_of_memory_capacity` prove the actual whole-space
continuation and official-statement implications with those quantifiers.
They do not establish the capacity bound.

### A weaker target for the geometric reserve

Fix a horizon `H>0`, memory regularizer `eta>0`, and whole-space separation
`R>0`. Retain the earlier complete nearby source `B_near` and set

```text
k=44/95, kappa=27E0/(pi R^5), k_H=k exp(-kappa H)>0,
X=exp(-kappa t) Y_hat,    h=det(I+C/eta)^(1/3),
e_b=(X-b h)_+,           E_b(t)=integral e_b(t,x) dx.
```

Production remains signed; the positive part specifies the excess
observable, not the absolute value of the nonlinear residual.

Choose one fixed `b` strictly above both `sup_x Y_hat(0,x)` and the
far-field offset `1+delta/2`. The datum gives this finite threshold;
it is not readjusted after a burst. Initially `C=0`, `h=1`, and `e_b=0`.
The exponential pays the already controlled distant strain reaction.
For full periodic pressure use `kappa=0` and the complete periodic source.

Suppose the following uniform bound were proved:

```text
integral_0^tau E_b(t)dt <= A(u0,nu,H,R,eta,b),  tau<=H.
```

Coercivity and the determinant mass bound give

```text
|omega|^4 <= (b/k_H)[1+trC/(3eta)] + e_b/k_H.
```

The formal lemma `massEnvelope_of_excess` absorbs the last term into
`c=trC/(3eta)+e_b/b`. The capacity path can therefore be

```text
M=b/k_H,
B(t)=E0/(3eta)+E_b(t)/b,
integral_0^tau B <= E0 H/(3eta)+A/b.
```

It follows that

```text
1+W(t) <= (1+W(0)) exp[
  (1+sqrt(2M)+2M E0/(3eta))H+2A/k_H].
```

This is finite if the proposed full-datum allowance A is finite. The
new sufficient target permits unbounded pointwise `Y_hat/h` and requires
no worst-receiver stochastic estimate. Its connection to the actual
normalized memory field is analytic; the spatial absorption, actual
whole-space energy estimate and continuation implications are formal.
The same analytic energy argument works on the torus. No periodic formal
criterion is added in these two modules.

### The remaining signed pressure/parent estimate

There is a direct physical equation for this excess. The complete
unforced equations give

```text
D X <= X B_near,        D h=h Q_geom,
D=partial_t+u.grad-nu Delta.
```

Convex approximation of the positive part yields the distributional
inequality

```text
D e_b <= 1_{X>b h} [X B_near-b h Q_geom].
```

The nonpositive diffusion contribution at the level boundary is retained
in the derivation and may be dropped for this upper bound. On a compact
smooth prefix, the positive part has bounded spatial support: X tends
to its smaller far-field offset while `h>=1`. Smooth convex approximants
vanishing for negative arguments avoid an infinite-volume offset.
The existing all-jet regularity justifies integration and continuity
of the spatial excess. Incompressibility removes the transport integral.
Define the signed quantity

```text
P_b(t)=integral_{X>b h} [X B_near-b h Q_geom] dx.
```

Then `E_b'<=P_b` in distributions. Since `E_b(0)=0`, integration with
the fixed horizon weight gives

```text
integral_0^tau E_b(t)dt+(H-tau)E_b(tau)
  <= integral_0^tau (H-t) P_b(t)dt,    tau<=H.
```

A uniform upper bound on the signed right-hand side is therefore a
precise remaining sufficient physical estimate. The threshold region,
near pressure, parent commutator, memory reaction and receiver gradients
are all part of this same actual evolution. The global geometric
identity bounds the subtracted payment by `b H E0/(3eta)`; it does not
bound the positive pressure/parent contribution. This is an open history
estimate, not a closed reserve obtained from its definition. The weak
pressure-pairing estimate may now be investigated on these spatial
receivers without substituting a singular point heat kernel, but its
receiver norm is still not automatically controlled.

### An actual forced obstruction to both criteria

`CandidateProperties` in the imported whole-space construction requires
positive viscosity, smooth velocity and pressure before time one with
common compact spatial support, bounded kinetic energy, globally smooth
compact spacetime forcing, and unbounded speed near time one. In
particular the force's first and second derivative L2 norms remain
bounded across that time. The formal forced-path estimate retains the
first derivative force bound F:

```text
1+W(t) <= (1+W(0)) exp[(1+sqrt(2M)+F)t+2M integral_0^t B].
```

A uniform capacity would thus bound gradient energy. The existing
`no_uniform_gradient_energy` theorem excludes this for the actual
candidate, using its bounded second-order force norm and the H2
embedding. `no_uniform_mass_envelope` and
`no_uniform_memory_capacity` prove both obstructions, and their
`openAI_solution_...` versions apply them to `NavierStokesR3.theorem_1_1`
for every positive viscosity. No velocity surrogate is substituted.

For the actual memory interpretation, fix a starting time `a=1/2` and
construct C consistently from `C(a)=0` on all later slabs. Let Ebar bound
`||u(t)||2^2`, let F0 bound `||f(t)||2`, and put `H0=1/2`. The forced
energy equation gives the analytic bounds

```text
integral trC(t) <= D_C=||u(a)||2^2+2H0 sqrt(Ebar) F0,
R_vol(t)+3eta integral_a^t integral h Q_geom
  =||u(a)||2^2+2 integral_a^t integral u.f <= D_C.
```

All constants are finite. Earlier retained memory may instead be carried
through a; its finite mass is then included once in D_C. Thus the
geometric resource remains finite in this forced test. Nevertheless,
for every fixed admissible b and finite kappa the space-time excess of
the same coercive envelope cannot have a uniform finite bound. Otherwise
`massEnvelope_of_excess` would supply the capacity just excluded.
The memory construction and this last excess interpretation are analytic;
the physical forced-path obstruction itself is kernel-checked.

This distinguishes a finite geometric payment from the missing unforced
comparison. It does not determine which separated term of the new
scalar reserve carries the forced divergence. In particular, after
Helmholtz projection write the force as g and the canonical advective
pressure as p_u. The augmented-stress equation becomes

```text
D(u tensor u+C)=-sym(u tensor grad p_u)+sym(u tensor g).
```

The full reserve production also contains the strain and vorticity
terms from `sym grad g` and `curl g`, and the observed parent-pressure
term `K_near*sym(u tensor g)`. A uniform bound on all their logarithmic
reserve pairings is not established here. Their history
must be checked before attributing divergence solely to B_near. For the
unforced target these explicit force terms vanish; the interacting
parents and pressure still evolve and remain the open comparison.

## Differentiable excess and a complete unforced mixing history

`memory_soft_excess.py` tests the receiver needed by the preceding spatial
pressure estimate. A differentiable perspective avoids a singularity of
the sharp region selector while preserving the continuation implication.
An actual unforced mixing class both exposes that singularity and admits
an explicit full-history payment. The latter uses a decaying parent and
does not close arbitrary mutually interacting NS histories.

### A perspective with a paid weight derivative

Retain the same positive X, memory h, and fixed datum threshold b>0. Set

```text
z=X/h,
F_b(X,h)=(X-b h)_+^2/X=h phi_b(z),
phi_b(z)=(z-b)_+^2/z.
```

For X>0, this is C1 and locally C1,1, including at the threshold. It is
not asserted to be C2 there. Its value and first derivatives vanish on
the inactive side. Pointwise,

```text
0<=F_b<=(X-b h)_+,
X<=2b h+F_b,
(X-2b h)_+<=F_b.
```

Thus replacing the linear excess changes the datum-fixed threshold by at
most a factor of two. In particular a uniform integral of F_b supplies
`MassEnvelope` with

```text
M=2b/k_H,
B(t)=E0/(3eta)+(integral F_b(t,x)dx)/(2b).
```

`ViscousMemorySoftExcess.massEnvelope_of_soft_excess` proves the spatial
implication for the literal vorticity. The previous actual whole-space
capacity theorem then applies. The imported forced obstruction also
persists: a finite soft-excess allowance would imply the excluded capacity.

On z>b, put

```text
a_b=1-b^2/z^2,       c_b=2b(1-b/z),
phi_b''=2b^2/z^3.
```

Set a_b=c_b=0 on z<=b. Both coefficients are continuous and locally
Lipschitz. The active perspective Hessian is the nonnegative square

```text
Hess F_b[(dX,dh),(dX,dh)]
  =(2b^2/X^3)(h dX-X dh)^2.
```

The exact weak chain rule, with the earlier actual equations for X,h, gives

```text
D F_b <= a_b X B_near-c_b h Q_geom-J_b,
J_b=nu h phi_b'' |grad z|^2 on z>b, and zero on z<=b.
```

The chain rule follows by convex approximation or the C1,1 chain rule.
There is no jump of the first derivative to create a level-surface measure.
In particular the derivative of the pressure weight is paid:

```text
(nu b h/2)|grad a_b|^2 <= J_b,
```

because `a_b'=phi_b''<=2/b` on the active side. This controls precisely
the derivative introduced by selecting the excess region. For the actual
strain-slot tensor `T=exp(-kappa t) partial_S Y_hat`, the previous sensitivity
bound is `||T||_F<=K X`, K=9/4. The scalar inequality also yields

```text
(nu/(2K^2 b h)) ||T||_F^2 |grad a_b|^2 <= J_b.
```

The direct memory-pressure receiver is now `M=a_b T`, with no value jump.
Its derivative still includes `a_b grad T`. Moreover the weak pressure
norm uses `tr(eta I+C)` and the matrix `eta I+C`, not simply the scalar
weight `1/h` displayed here. Neither the remaining derivative nor the
nonlocal weighted norm is paid by this calculation. The unforced signed
production bound remains the task; the cutoff defect is one identified
part of its receiver cost.

If `E_soft(t)=integral F_b`, the new sufficient signed target is an upper
bound, uniform on available prefixes, for

```text
integral_0^tau (H-t) integral
  [a_b X B_near-c_b h Q_geom-J_b] dx dt.
```

It controls `integral_0^tau E_soft+(H-tau)E_soft(tau)`, since E_soft(0)=0.
The subtracted geometric part is at most `2b H E0/(3eta)`. The sign,
complete parents, pressure and diffusion must be retained in the comparison.

### Actual NS with a bounded stochastic parent history

On the period-2pi torus, with normalized volume, fix A,B>=0 and nu>0.
Consider the actual unforced velocity and canonical pressure

```text
u=(A exp(-nu t) sin y, 0, v(x,y,t)),    p=0,
v_t+A exp(-nu t) sin(y) v_x=nu(v_xx+v_yy),
v(0,x,y)=B sin x.
```

The horizontal component solves heat flow independently. The third
component solves a linear, smooth parabolic equation globally; it does
not feed back because every field is independent of z. These are actual
global NS solutions, not velocities with a residual force omitted.

Set q=exp(-nu t) and write `v=B q Im(exp(ix) phi(t,y))`. Then

```text
phi_t=nu phi_yy-i A exp(-nu t) sin(y) phi,    phi(0,y)=1.
```

The physical stochastic-characteristic formula reduces exactly to

```text
phi(t,y)=E exp[-i A integral_0^t
  exp(-nu(t-s)) sin(y+sqrt(2nu) B_s) ds],
```

where B_s here denotes a one-dimensional Brownian motion, not the initial
vertical amplitude B. The independent x Brownian motion supplies the
factor q. This identifies the stochastic representation of this NS
subsystem; it is not an additional force or an independently chosen
Schroedinger-bridge optimizer.

The phase has modulus one. Differentiation in y is justified by the
deterministic bound on its derivative. Therefore

```text
|phi|<=1,
|phi_y|<=A integral_0^t exp(-nu(t-s))ds=A(1-q)/nu,
|v_x|<=Bq,       |v_y|<=AB q(1-q)/nu.
```

This bounds the complete parent history using only the datum and viscosity.
It permits real stretching: with `a=partial_y u_1`, `d=v_x`, `e=v_y`,

```text
omega=(e,-d,-a),
W=a^2+d^2+e^2,    Q=W/2,
V=-a d e,        Z=a^2 d^2.
```

V is generally nonzero. The memory is also the actual evolving C. Its
second row and column vanish, and C_11 depends only on y,t. The equation
DC=2nu G preserves these properties from C(0)=0. Thus `div div C=0` and
the canonical memory pressure is zero for the entire history. In this
periodic full-pressure observation, `P_hat=0` exactly.

For any positive envelope regularizer and switch regularizer delta, its
gap and upper bound simplify to

```text
gap=-(4/7)Z-(4/105)W^2<=0,
Y_hat<=1+delta/2+(39/7)Z+(1399/1995)W^2.
```

Here `V^2/(W+eta_envelope)<=Z`. Put

```text
L^2=A^2+B^2+(AB/nu)^2,
K=(39/7)A^2 B^2+(1399/1995)L^4.
```

The stochastic derivative bounds imply W<=L^2 q^2 and Z<=A^2 B^2 q^4.
Since h>=1, for every fixed b>1+delta/2,

```text
F_b(Y_hat,h) <= (Y_hat-b h)_+ <= K exp(-4nu t),
integral_0^infinity integral F_b <= K/(4nu).
```

Choosing b also above the initial envelope gives the same zero-initial-excess
setting as the general target. This is an analytic complete-history
bound, not merely an initial-time test. It is uniform in the final horizon
for this class. The payment uses the integrable decay of an autonomous
parent. Arbitrary NS parents mutually stretch and need not obey this
decay estimate; extending that step is the unproved physical bridge.
These z-independent periodic fields are not finite-energy whole-space data.

### Why the sharp receiver fails on this same physical class

The raw weak norm of the previous section requires a square-integrable
gradient of q_M, where `-Delta q_M=div div M`. For the sharp receiver

```text
M=1_{X>b h} exp(-kappa t) partial_S Y_hat,
```

a regular interface with nonzero normal-normal tensor jump produces a
delta-prime term in `div div M`. The potential q_M has a nonzero jump;
it cannot belong to H1. Since `eta I+C>=eta I`, its weighted receiver
norm is infinite. This is failure of that derivative-based estimate,
not divergent physical pressure work.

Such an interface occurs in the actual unforced family above with
A=B=1 and sufficiently small positive nu. To locate it rigorously, use
the fixed-time inviscid comparison

```text
u_E=(sin y,0,sin(x-t sin y)).
```

At t=1,y=0 let r=cos(x)^2. With envelope regularizers both one,

```text
W=1+2r, V=r, Z=r, Q=W/2,
core=5r^2/(2+2r)+(4/7)r+(1399/1995)(1+2r)^2.
```

Choose the fixed threshold

```text
b=sqrt(13)/6+20051/3192,
sup_x Y_hat(0,x)<=19457/3990 < b.
```

At x=pi/6,y=0,t=1 the limiting Y equals b. The interface is regular;
the derivative with respect to r is at least 15483/1862>0. Its normal
is parallel to n=(-1,1,0). The exact strain-slot tensor T_E satisfies

```text
n.T_E n=-(25/21)(1+2/sqrt(13)) !=0.
```

Its trace-free part also has a nonzero normal-normal contraction. These
are exact algebraic certificates, not floating-point sign tests.

For completeness, this is a positive-viscosity argument, not a substitution
of Euler for NS. On any fixed finite interval the horizontal heat parent
differs from sin y by O(nu) in every fixed spatial derivative norm. The
difference w=v_nu-v_E obeys the linear equation

```text
w_t+a_nu w_x-nu Delta w
  =nu Delta v_E+(sin y-a_nu) partial_x v_E,    w(0)=0.
```

The source is O(nu). Differentiated energy estimates and Gronwall give
w=O(nu) in every fixed C^m norm on that interval, with constants bounded
as nu tends to zero. The same estimates for DC=2nu G give C=O(nu).
The implicit-function theorem therefore preserves the regular level and
its nonzero tensor contraction for all sufficiently small positive nu,
and over an open time interval around one. The threshold stays the same
and remains strictly above the full initial envelope. Hence the sharp
receiver's time-integrated norm really is infinite on these regular
unforced histories, although their actual memory-pressure work is zero.

Keeping only the sharp-limit level diffusion does not pay that norm with
a fixed coefficient. For a cubic transition `sigma(s)=3s^2-2s^3` of width
epsilon, `integral sigma'=1` whereas the squared derivative cost is
`6/(5 epsilon)`. The differentiable perspective weight a_b removes this
interface divergence. It does not by itself bound the remaining physical
receiver norm uniformly over arbitrary solution prefixes.

### Certification boundary

Twelve Lean statements certify the excess comparisons, active derivatives,
perspective Hessian identity, receiver-weight payments and actual-vorticity
mass-envelope implication. The weak PDE chain rule, stochastic formula,
full-history comparison and positive-viscosity interface persistence are
analytic. The exact checker verifies the algebra, complete NS reduction,
memory structure and interface certificates. It does not numerically evolve
an arbitrary flow or certify the missing universal signed production bound.

```sh
python3 -O labs/memory_soft_excess.py
```

## Full strain-receiver diffusion: obstruction and a joint completion

`pressure_diffusion_completion.py` addresses the remaining derivative of
the strain-sensitivity tensor. The preceding perspective pays its selection
weight derivative. Paying the tensor derivative additionally requires the
complete coupled strain, vorticity and pressure diffusion, rather than only
the positive Hessian in a strain slot with other variables fixed.

### An actual unforced diffusion obstruction

On the period-2pi torus, set

```text
u1 = 3 sin(x+z) + 3 alpha (cos z-1),
u2 = 4 sin x + 4 sin(y+z) - 2 sin z - 3 alpha (cos z-1),
u3 = -3 sin(x+z) - 4 sin(y+z) + 6 sin x + 5 sin y.
```

This is a smooth divergence-free, genuinely three-dimensional datum.
At the origin its velocity is zero, and its gradient and canonical
pressure Hessian, independently of alpha, are

```text
B = [ 3  0  3 ]          P = [ -112/5     4     -56/5 ]
    [ 4  4  2 ]              [    4    -118/5   -76/5 ]
    [ 3  1 -7 ]              [ -56/5   -76/5     -50  ].
```

The perturbation changes a spatial gradient of B in the solenoidal
rank-one direction `E=(3,-3,0) tensor (0,0,1)`. With the preceding envelope
regularizers equal to one, its core curvature in that direction is
`-1124556302/53865`. The complete calculation additionally differentiates
the canonical pressure and uses the actual unforced NS tangent. At C=0,
it includes `C_t=2nu sum_j partial_j u tensor partial_j u` in the observed
pressure. The coefficient of `nu alpha^2` in `D Y_hat` is strictly larger
than 20000, with an exact rational-plus-radical certificate in the checker.
The geometric-mean normalization leaves this coefficient unchanged.

An independent differentiation of the complete coupled spatial Hessian
recovers the same coefficient. Thus automatic nonnegative diffusion of
this envelope fails on actual data. The test does not assert that its
datum-fixed excess is initially active: b is above the initial supremum.
It also does not refute an integrated signed history allowance, temporal
regularity, or a payment using other retained resources.

### A completion retaining both pressure and core branches

Write `S=sym B`, `omega=curl B`, `W=|omega|^2`, `Q_s=tr(S^2)`,
`V=omega.S omega`, and `Z=|S omega|^2`. For fixed eta>0 use the original
two branches

```text
p0 = 5 V^2/(W+eta) + (63/95)W^2 - 2 omega.P_hat omega,
c0 = 5 V^2/(W+eta) + (4/7)Z + (10/21)Q_s W + (44/95)W^2.
```

P_hat is the retained-pressure observer from the actual stress
`u tensor u+C`. For a fixed sigma>0, define

```text
r = ||B||_F^2,       q = sqrt(sigma^2+||P_hat||_F^2),
Q = r+q,            R = Q^2,
A = p0+48R,         B0 = c0+48R,
Psi = 1+sqrt(A^2+B0^2).
```

Here Q differs from the strain invariant Q_s. This is a candidate
completion of the joint observable, not a claim that the new production
is already payable. The positive additions retain actual pressure and
geometry while making their entire diffusion convex.

The identities `r=||S||_F^2+W/2`, `V^2/(W+eta)<=||S||_F^2 W`, and
`Z<=||S||_F^2 W` give

```text
0<=c0<=5r^2,          -Q^2<=p0<=6Q^2,
47Q^2<=A<=54Q^2,      48Q^2<=B0<=53Q^2,
Psi>=1+48Q^2>=1+12|omega|^4.
```

Both completed branches are strictly positive. The radial combination
is smooth, including at vorticity zeros and strain eigenvalue collisions.
Coercivity supplies the same existing soft-excess continuation interface
with `k=12` when X=Psi. With `X=exp(-kappa t)Psi`, use the fixed
`k=12exp(-kappa H)` on the prescribed horizon. Integrability and a uniform
full-datum allowance for the excess remain physical obligations.

### Uniform full Hessian estimates

Let E and L vary B and the symmetric P_hat simultaneously. Put
`H=sym E`, `v=curl E`, `e=||E||_F^2`, `g=||L||_F^2`, `d=B:E`, and
`ell=(P_hat:L)/q`. Matrix Cauchy--Schwarz gives `d^2<=r e` and `ell^2<=g`.
Direct differentiation yields

```text
D2 R = 8d^2+4Q e+8d ell+2g+(2r/q)(g-ell^2),
D2 R - 2Q e - (2/5)g
  = (2/5)(5d+2ell)^2 + 2(r e-d^2) + 2q e
    + (8/5)(g-ell^2) + (2r/q)(g-ell^2) >=0.
```

This calculation allows noncommuting pressure variations. For the
perspective T=V^2/(W+eta), its exact second derivative is

```text
D2 T = 2/(W+eta) (D V - (V/(W+eta))D W)^2
       + 2(V/(W+eta))D2 V - (V/(W+eta))^2 D2 W,
D2 V = 2v.S v+4v.H omega,       D2 W=2|v|^2.
```

Consequently `D2 T>=-6||S||^2|v|^2-8||S||||omega||||H||||v||`.
The remaining core cross terms are retained: `D2 Z` has possible
negative part `-4||S||||omega||||H||||v||`, and `D2(Q_s W)` has possible
negative part `-8||S||||omega||||H||||v||`.
The equalities for r and e give
`||S||||omega||||H||||v||<=r e/2` and `||S||^2|v|^2<=2r e`.
These imply the universal analytic lower bounds

```text
D2 c0 >= -(1744/21)r e,
D2 p0 >= -(88r+8q)e-8g.
```

The second retains `-4v.P_hat v-8v.L omega`. In obtaining its bound,
`4||P_hat|||v|^2<=8q e` and
`8||v||||L||||omega||<=16sqrt(r e g)<=8r e+8g`.
Combining with the completion gives, for either branch,

```text
D2 A, D2 B0 >= 8Q e+(56/5)g.
```

For `rho=sqrt(A^2+B0^2)`, its full Hessian is

```text
D2 rho = (A D2 A+B0 D2 B0)/rho
          +(B0 D A-A D B0)^2/rho^3.
```

The second term is nonnegative and `(A+B0)/rho>=1`. Thus

```text
D2 Psi[(E,L),(E,L)] >= 8Q||E||_F^2+(56/5)||L||_F^2.
```

This is a uniform analytic matrix estimate. Nine Lean statements certify
the scalar decomposition and combination steps, with the matrix norm and
derivative bounds supplied as explicit hypotheses. The uniform matrix
identification itself is not yet a Lean theorem.

### Diffusion pays the full strain-receiver gradient

For a pure strain increment H, with omega and P_hat fixed, the original
branch Hessians are at most `20r||H||^2` and `(508/21)r||H||^2`.
The completion contributes at most `576Q||H||^2`. Their strain gradients
have norms at most `212Q^(3/2)` and `217Q^(3/2)`. Since rho>=48Q^2,
the radial Hessian formula gives

```text
D2_SS Psi[H,H] <=3200Q||H||_F^2,
||partial_S Psi||_F^2<=93000Q^3.
```

For `T=partial_S Psi`, positive-Hessian Cauchy--Schwarz therefore gives

```text
||d T[(E,L)]||_F^2<=3200Q D2 Psi[(E,L),(E,L)].
```

This controls the derivative with pressure and vorticity varying together.
It is not restricted to an aligned model or a frozen direction.
Define the actual local diffusion loss

```text
D_Psi=nu sum_j D2 Psi[(partial_j B,partial_j P_hat),(...)]>=0.
```

For the existing differentiable excess, z=Psi/h, put
`a=(1-b^2/z^2)_+`, `M=a T`, and
`J=nu h (2b^2/z^3)|grad z|^2` on z>b, zero otherwise.
The squared product rule and `z phi_b''(z)<=2` yield

```text
(nu/Q)||T||^2|grad a|^2 <=3875 J,
(nu/Q)a^2||grad T||^2 <=3200 a D_Psi,
(nu/(8000Q))||grad M||_F^2 <= J+a D_Psi.
```

At the threshold the first derivative of the excess is continuous, so
there is no interface value jump. For kappa>=0 the same constants work
with T multiplied by exp(-kappa t) and D_Psi by exp(-kappa t).
`PressureDiffusionCompletion.full_receiver_gradient_paid` certifies the
last scalar combination, retaining the explicit hypotheses. The spatial
matrix and weak-PDE application are analytic.

The actual pressure observation satisfies
`D P_hat=K[-u tensor grad p-grad p tensor u]+[u.grad,K](u tensor u+C)` for the
fixed convolution observer K. Its explicit heat source cancels with
the retained C equation. Thus the chain-rule diffusion above is the
complete explicit local viscosity loss of Psi. Reaction and transport
commutators are still part of its physical production.

### What this pays, and the remaining history question

This local norm has weight 1/Q. The earlier nonlocal memory-pressure norm
uses `tr(H) grad(q_M).H grad(q_M)`, with `H=eta_mem I+C` and
`-Delta q_M=div div M`. No comparison of that anisotropic pressure norm
with the new local payment has been proved. Finite trace mass of C does
not by itself supply such a comparison.

The positive completion also adds pure-gradient and observed-pressure
reaction. These may be expensive: observed pressure includes memory
pressure, whose derivatives are not bounded by trace mass alone. They
must remain in the full signed production; the completion does not pay
them or prove equivalence with the earlier history target. That target
remains available independently.

For the completed variant, let P_X be the actual chain-rule production
of X=exp(-kappa t)Psi before subtracting its positive local diffusion
D_X=exp(-kappa t)D_Psi. The named sufficient OPEN estimate is a
datum-fixed bound on

```text
integral_0^tau (H-t) integral
  [a P_X-c_b h Q_geom-a D_X-J] <= A(u0,nu,H,...),  tau<=H.
```

It would bound the integrated excess and its terminal remainder. The
new lemma supplies a concrete local payment inside this expression.
It does not establish its uniform signed bound over actual smooth
prefixes or prevent indefinite regeneration by mutually amplifying parents.

The previously controlled stochastic mixing history remains a consumer.
Its actual fluid and memory pressure vanish, `r=|omega|^2`, and
`r<=L^2exp(-2nu t)` with `L^2=A^2+B^2+(AB/nu)^2`. The far-field
offset is `Psi_inf=1+48sqrt(2)sigma^2`. The norm's Lipschitz inequality
and the branch bounds give

```text
Psi-Psi_inf<=192sigma r+107r^2,
integral_0^infinity integral F_b
  <=96sigma L^2/nu+107L^4/(4nu),
```

for b fixed above the initial envelope and offset, on normalized periodic
volume. This is an analytic full-history consequence of the already
identified stochastic parent bound A/nu. Its triangular autonomy still
does not model mutual parent amplification.

The forced filter also persists: coercivity and a finite completed excess
would supply the actual capacity criterion that the imported forced
singularity violates. This does not identify which individual new
production term diverges on that construction.

The checker retains every Fourier output and independently checks the
initial PDE tangent, memory correction, coupled Hessian, completion
derivative, scalar coefficients and preserved mixing allowance. It does
not evolve arbitrary flows or certify a recurrent-history bound.

```sh
python3 -O labs/pressure_diffusion_completion.py
```

## Actual pressure diffusion and the joint memory receiver

The convex completion introduced two distinct obligations: spatial costs
of its retained pressure, and signed nonlinear production. The following
comparison pays one of the spatial costs. It keeps the nonlinear history
obligation separate.

Write `B=grad u`, `r=||B||_F^2`, and let `P=Hess p` be the actual canonical
fluid pressure, so `-Delta p=tr(B^2)`. For arbitrary smooth solenoidal
whole-space velocity with all derivatives in L2,

```text
integral ||P||_F^2 = integral tr(B^2)^2 <= integral r^2,
integral ||partial_k P||_F^2
  = integral partial_k(tr(B^2))^2
  <= 4 integral r ||partial_k B||_F^2.
```

These identities require the actual Poisson source and gradient character
of the pressure. They do not treat pressure as a free symmetric matrix.
They are spatial identities at every smooth prefix, without a uniform
future bound. In `WholeSpacePressureDiffusion`, the pressure is the
upstream Helmholtz construction, not an independently supplied potential.

The elementary integrated identity underlying the calculation is

```text
integral sum_ij partial_j v_i partial_i v_j
  = integral (div v)^2.
```

Two integrations by parts exchange the crossed derivatives. If v is a
gradient, its gradient matrix is symmetric, so the left side is its
squared Frobenius norm. This applies even if the scalar potential itself
is not in L2. For v=grad p, solenoidality gives the pressure source. For
v=partial_k grad p, it gives the differentiated source. Finally
`partial_k tr(B^2)=2 sum_ij B_ji partial_k B_ij` and matrix
Cauchy--Schwarz supplies the constant four. Products of upstream smooth
L2 fields certify integrability throughout.

### A strict payment for the derivative of memory pressure

For the actual retained stress memory, write `P_hat=P+P_C` and
`P_C=Hess q_C`, with `-Delta q_C=div div C`. The completed observable's
analytic lower bound gives

```text
D_Psi >= nu sum_k [8Q ||partial_k B||_F^2
                    +(56/5)||partial_k P_hat||_F^2],  Q>=r.
```

The weighted square

```text
(33/5)a^2+(33/28)b^2-(a-b)^2 = (28a+5b)^2/140
```

retains the coefficients needed to combine this with actual pressure:

```text
integral ||partial_k P_C||_F^2
  <= (33/5) integral ||partial_k P_hat||_F^2
     +(33/28) integral ||partial_k P||_F^2
  <= (33/5) integral ||partial_k P_hat||_F^2
     +(33/7) integral r ||partial_k B||_F^2,

nu integral ||grad P_C||_F^2 <= (33/56) integral D_Psi.
```

The pressure identities, bounds and final conditional diffusion adapter
are Lean-certified. The adapter accepts a smooth observed gradient and
the displayed physical Hessian lower bound. It does not construct the
evolving memory or identify that Hessian with a matrix derivative; those
applications remain analytic. Its coefficient is strictly below one.

### Fixed low frequencies plus full diffusion

Positive memory has finite mass `M(t)=integral tr C(t)<=E0`. For the
whole-space Fourier convention
`C_hat(k)=integral exp(-i k.x) C(x) dx`, positivity gives

```text
||P_C_hat(k)||_F = |k^T C_hat(k) k| <= |k|^2 M(t).
```

For positive viscosity and any cutoff Lambda>0, fixed before all solution prefixes,

```text
integral ||P_C||_F^2
  <= Lambda^7 E0^2/(14 pi^2)
     +Lambda^(-2) integral ||grad P_C||_F^2,

integral_0^tau integral ||P_C||_F^2
  <= H Lambda^7 E0^2/(14 pi^2)
     +(33/(56 nu Lambda^2)) integral_0^tau integral D_Psi, tau<=H.
```

Plancherel splits the disjoint low and high frequencies. The low constant
is `(2pi)^(-3) integral_{|k|<=Lambda}|k|^4 dk=Lambda^7/(14pi^2)`.
The high part uses `1<=|k|^2/Lambda^2`. Thus any fixed coefficient times
this pressure square can be paid by an arbitrarily small multiple of
the **full** diffusion plus an explicit finite datum/viscosity/horizon
allowance. On normalized 2pi-periodic volume the analogous low cost is
`E0^2 sum_{0<|k|<=Lambda}|k|^4`; the same high-frequency payment holds.
This charges the stronger completed diffusion; it does not restore an
energy-only allowance for the earlier, different renewal functional.

This frequency split and its time integration are analytic, not new
whole-space Fourier declarations. The exact checker verifies the
periodic version on the actual generated initial memory source
`G=C_t/(2nu)=BB^T`, including a separated parent with a different phase.
It does not assert that C=G at a finite time or evolve a closed cascade.

The distinction between full and selected diffusion is essential.
The soft excess pays `a_b D_Psi`, where a_b vanishes in the inactive
region. The preceding estimate cannot be transferred by inserting a_b
into an unweighted pressure identity. Even for a smooth scalar weight a,
integration by parts for a gradient vector v gives the extra terms

```text
integral a ||grad v||_F^2
 = integral a (div v)^2
   + integral [(grad a.v) div v
               -sum_ij (partial_j a) v_i partial_i v_j].
```

Taking `v=partial_k grad p` identifies the specific localization defect.
Symmetry of the third pressure derivatives combines the three directions:

```text
integral a ||grad P||_F^2
 = integral a ||grad Delta p||^2
   + integral grad a.[P grad Delta p-(1/2)grad ||P||_F^2].
```

Thus the pressure-source bound with weight a has a signed pressure-flux
correction. It is not obtained by simply weighting the unweighted identity.
The checker verifies the pointwise divergence formula and a nonzero
integrated correction on actual fluid pressure with a smooth strictly
positive trigonometric test weight. That test weight is not the actual
excess selector, so it refutes only the uncorrected weighted identity.
The continuous excess weight already has a paid derivative, but the
remaining v and grad v factors have not been absorbed. The next section
supplies a weighted comparison retaining this flux and an analytic weak-limit
application to the actual continuous excess selector. The nonlinear
production budget remains open. A full spatial entropy could supply full
diffusion, at the
price of retaining its added nonlinear reactions; it is not an equivalent
replacement for the weaker excess target.

### Retain both receivers and the transport commutator

Let `K T=Hess(-Delta)^(-1) div div T`. For
`D=partial_t+u.grad-nu Delta`, the actual unforced stress history obeys

```text
D(u tensor u+C)=-u tensor grad p-grad p tensor u,
D P_hat=K[-u tensor grad p-grad p tensor u]
         +[u.grad,K](u tensor u+C).
```

For the complete soft-excess receiver define two symmetric tensors,
`M=a_b partial_S Psi` and `N=a_b partial_P Psi`. Splitting
`p=p_hat-q_C` gives the joint memory contribution

```text
I_C = integral M:P_C
      + integral N:K[u tensor grad q_C+grad q_C tensor u]
    = integral [-div M+2(KN)u].grad q_C
    = integral C:Hess q_eff
    = -integral div C.grad q_eff,

q_eff=(-Delta)^(-1)[div div M-2div((KN)u)].
```

The pressure-slot receiver changes the effective test. Controlling the
old strain receiver alone would omit it. The tensor products above are
explicit sums, avoiding a convention-dependent factor in `sym`.

The isolated I_C is also sensitive to a constant-velocity shift U:

```text
I_C(u+U)-I_C(u)=2U.integral (KN) grad q_C.
```

The full physical production remains invariant. Solenoidality gives
`K[U tensor u+u tensor U]=0`; the actual pressure equation gives

```text
[u.grad,K](U tensor u+u tensor U)
  =K[U tensor grad p+grad p tensor U].
```

This exactly compensates the changed pressure-source term. A test of the
isolated memory contribution must therefore retain the coupled pressure
reaction and commutator. On the torus the conserved mean velocity permits
a mean-free moving frame. A uniform boost of a nonzero whole-space field
is not finite-energy data, so the periodic test is not transferred to the
whole-space datum class as a counterexample.

The exact checker uses a genuinely 3D finite Fourier velocity and its
generated initial memory source. For the leading cubic strain and
quadratic pressure receivers of the completed observable, the isolated
pairing is zero in the original frame, while its boost coefficients are
`(-256/33,256/33,0)`. Every output mode verifies exact compensation in
the full pressure production. These unselected leading coefficients
are not the initially inactive datum-fixed soft excess, and the result
does not refute a finite history allowance.

```sh
python3 -O labs/pressure_memory_diffusion.py
```

The remaining physical target is the signed joint production over
compatible, retained-memory NS histories. The strict unweighted derivative
payment and fixed-cutoff pressure-square estimate discharge specific
spatial costs; they do not yet prevent repeated parent amplification or
establish arbitrary-data continuation.

## Signed weighted pressure payment and cellular parent histories

`MettapediaNS.WholeSpacePressureLocalization` extends the actual-pressure
spatial calculation to a varying weight. The pressure gradient is constructed
from the full smooth solenoidal whole-space velocity; its scalar potential
need not belong to L². Put `P=Hess p`, `B=grad u`, and `r=||B||_F²`.
For a smooth scalar weight `a` with all jets in L², two integrations by parts
give, for every genuine gradient field A,

```text
integral a ||grad A||_F²
  =integral a (div A)²
   +integral grad a.[(div A)A-(grad A)A].
```

Applying this to each coordinate derivative of `grad p` and summing yields
the literal pressure flux

```text
Flux_p=P grad(Delta p)-(1/2)grad||P||_F²,
integral a ||grad P||_F²
  =integral a ||grad Delta p||²+integral grad a.Flux_p.
```

These weighted identities and the flux formula are Lean-certified. For
`a>=0`, the actual Poisson source derivative satisfies
`|partial_j tr(B²)|²<=4r||partial_j B||_F²` pointwise. Consequently, with
`P_C=P_hat-P` and the same explicit completed diffusion lower bound as
in the preceding section,

```text
nu integral a ||grad P_C||_F²
 <=(33/56) integral a D_Psi
   +(33/28)nu integral grad a.Flux_p.
```

The memory-pressure consumer keeps the physical lower bound as a hypothesis.
The new strict comparison does not discard the signed flux. An additional
payment for that flux, together with the joint receivers and transport
commutator, remains necessary over arbitrary histories. The unweighted
coefficient cannot simply be inserted into an excess-selected estimate.

### Applying the identity to the actual continuous selector

There is an analytic approximation argument on a fixed smooth whole-space
prefix. Assume the velocity and constructed memory have the stated smooth,
decaying jets, `C>=0`, and a fixed threshold `b>Psi_inf`. Then `h>=1`,
`z=X/h>0`, and `a_b=(1-b²/z²)_+` is compactly supported and Lipschitz.
Indeed the jets decay at infinity, `h->1`, and `X` approaches at most
`Psi_inf`; the threshold is strictly above that offset. The derivative
`2b²/z³` is bounded by `2/b` on the active branch. The weight is continuous
at the threshold, so its weak derivative has no jump measure.

Convolve `a_b` with a positive compactly supported mollifier. The smooth
nonnegative weights converge uniformly, their derivatives converge almost
everywhere and remain bounded by the Lipschitz constant of this fixed
prefix, and their supports lie in one compact enlargement. The pressure
flux is integrable, being a sum of products of smooth L² pressure jets.
Dominated convergence passes both weighted identities and the conditional
payment to `a_b`. The required physical lower-bound integrand is likewise
integrable on the fixed prefix. Per-prefix regularity is used only for this
identity, not as a uniform future estimate. The weak-limit application is
analytic, not a new Lean theorem. On the torus the corresponding integration
by parts and approximation are periodic; the whole-space L² theorem is not
applied to a periodic lift.

### A pressure-bearing family with a finite stochastic parent reserve

Work on the normalized `2*pi` torus. Let

```text
psi(x,y)=sum_j a_j cos(k_j.(x,y)+theta_j),
|k_j|²=lambda>0,       A1=sum_j |a_j|,
u_h(t)=exp(-nu lambda t) J grad psi,       nu>0,
u(t,x,y,z)=(u_h(t,x,y),v(t,x,y)).
```

The same arguments allow a real combination of sine and cosine modes,
with `A1` taken from an amplitude representation. The vertical datum `v0`
is arbitrary smooth periodic data independent of z. The horizontal
vorticity is proportional to psi, so its self-advection vanishes. Literal
NS substitution gives

```text
p(t)=-exp(-2nu lambda t)(|grad psi|²+lambda psi²)/2,
v_t+u_h.grad v=nu Delta v.
```

The pressure formula is up to an irrelevant spatial constant. The vertical
component has no feedback into the horizontal equation because every field
is independent of z; its genuine stretching is retained. The full vorticity
is `(v_y,-v_x,-lambda exp(-nu lambda t)psi)` and may change direction.
This defines an actual unforced periodic NS class, with nonzero pressure
and recirculating horizontal parents, rather than prescribed free pressure.

The horizontal gradient has operator norm at most
`lambda A1 exp(-nu lambda t)`. Define the nonnegative remaining parent reserve

```text
R_parent(t)=A1 exp(-nu lambda t)/nu,
-R_parent'(t)=lambda A1 exp(-nu lambda t),
integral_s^t ||grad u_h||_op,infty
 <=R_parent(s)-R_parent(t).
```

Compatible segments use the same decaying parent amplitudes; composition
does not grant a new initial reserve. All parameters are fixed by the full
initial horizontal datum and viscosity, before any solution prefix.

The stochastic representation of the vertical component uses backward
horizontal characteristics
`dY_s=-u_h(t-s,Y_s)ds+sqrt(2nu)dW_s`. The spatial Jacobian obeys
`J_s'=-grad u_h(t-s,Y_s)J_s`. Its norm is bounded pathwise by the exponential
of the paid parent history. Differentiating the representation gives

```text
||grad v(t)||_infty
 <=B exp(A1(1-exp(-nu lambda t))/nu),   B=||grad v0||_infty.
```

This is an identification with the literal passive-component PDE through
Itô's formula. The Brownian motion represents viscosity; it does not apply
a force to the fluid. No Schrödinger-bridge optimizer identification is
used. The smooth known drift and smooth initial datum give a global smooth
linear evolution, so the estimate assumes no arbitrary NS continuation.

### Paying the observed memory pressure from the same parents

The complete memory still obeys
`(partial_t+u.grad-nu Delta)C=2nu B B^T`, `C(0)=0`. Its stochastic formula
preserves positivity. Since all fields are z independent, its pressure
observer depends only on the horizontal block `C_hh`. That block is driven
entirely by the known horizontal parents. The other components remain in
the full memory determinant `h`; they cannot be discarded at history seams.

Let `M>=1` bound the absolute components of every horizontal input frequency.
For derivatives of total order m, the parents obey
`||partial^alpha u_l||_infty<=M^(m+1) A1 exp(-nu lambda t)`.
Let `N4(t)` be the maximum absolute component norm of all derivatives of
`C_hh` through order four. Differentiating its literal parabolic equation
and applying comparison to this finite derivative system yields

```text
N4'(t) <=K4 exp(-nu lambda t) N4(t)
          +S4 exp(-2nu lambda t),
K4=2M A1 ((1+M)^4-1),
S4=4nu M^4 (2M)^4 A1²,
N4(0)=0.
```

The upper derivative can be interpreted in the Dini sense. In the transport
commutator, the sum of binomial coefficients with the frequency weights is
`(1+M)^m-1`; all differentiated memory terms have order at most m. In the
quadratic source it is `2^m`, with two horizontal derivative directions.
No memory norm of an unknown future solution occurs on the right. Thus

```text
N4(t)<=K_C,
K_C=(2/lambda) M^4 (2M)^4 A1² exp(K4/(nu lambda)).
```

For each horizontal tensor component,
`||(1-Delta)^2 C_ij||_2<=9K_C`; the four-component Frobenius norm is at most
`18K_C`. The memory-pressure symbol has norm at most
`|k|²||C_hh_hat(k)||_F`. Fourier Cauchy--Schwarz and

```text
sum_(k in Z²) (1+|k|²)^(-2)
 <=1+8 sum_(n>=1) n^(-3)<=13<16
```

therefore give `||P_C||_infty<=72K_C`. This bound has two derivatives of
memory and is not inferred from trace mass alone.

The full velocity gradient is bounded by
`r<=r_star=(lambda A1)^2+B² exp(2A1/nu)`. Let `P_star` be any fixed Fourier
majorant of the initial horizontal pressure Hessian. The completed observable
from the preceding section then obeys

```text
||P_hat||_infty<=P_star+72K_C,
Psi<=K_Psi=1+76[r_star+sqrt(sigma²+(P_star+72K_C)^2)]²,
Psi/h<=K_Psi,                 h>=1.
```

The coefficient 76 follows from the earlier branch bounds
`A<=54Q²`, `B0<=53Q²`, and `sqrt(54²+53²)<76`.
The constants are conservative and may be large, but are finite from the
full datum and viscosity. The soft excess satisfies `F_b<=Psi<=K_Psi`,
so its time-integrated mass on every horizon H is at most `H K_Psi`.
If f(t) is its spatial mass, the complete signed PDE production satisfies

```text
integral_0^tau(H-t) f'(t)dt
  =(H-tau)f(tau)-H f(0)+integral_0^tau f(t)dt
  <=H K_Psi,                       tau<=H.
```

Both receivers, the transport commutator and memory evolution are retained
in f'. This is an analytic allowance for the complete compatible histories
of this class. Equivalently `K_Psi-f(t)` is a physically justified nonnegative
reserve for the signed excess change; it cancels at compatible seams.
The local pressure flux need not vanish for this conclusion.

The autonomous eigenshell parents are the crucial restriction. General 3D
parents can produce new modes and amplify one another. No replacement for
their finite decaying reserve, no arbitrary-history flux absorption, and
no arbitrary-data global regularity bound has been proved here. The periodic
class is not a finite-energy whole-space field.

### Exact checks and resolved-prefix diagnostics

`cellular_parent_history.py` checks the exact Euler/NS parent, canonical
pressure, literal passive-component reduction, parent reserve and memory
coefficients. Its two-mode parent has zero total pressure localization
defect pointwise. Its three-mode parent has a nonzero defect, verified in
Gaussian rational Fourier arithmetic with every output retained.

The optional solver evolves the vertical component and all six symmetric
memory components. It evaluates the full coupled Hessian, the actual
continuous excess selector, pressure flux, signed production, memory
positivity and kinetic-plus-memory balance. These are Fourier approximations,
not kernel-certified histories. Their explicit threshold uses the exact
initial pressure-Hessian majorant `578/125` and the analytic initial
gradient bound, rather than a later grid maximum.

```sh
python3 -O labs/cellular_parent_history.py
python3 -O labs/cellular_parent_history.py --run-prefix --n 128 --final-time 2 --dt .005 --diagnostic-n 512
python3 -O labs/cellular_parent_history.py --run-prefix --n 128 --final-time 2 --dt .005 --diagnostic-n 1024
python3 -O labs/cellular_parent_history.py --run-prefix --n 128 --final-time 2 --dt .0025 --diagnostic-n 512
python3 -O labs/cellular_parent_history.py --run-prefix --n 256 --final-time 2 --dt .005 --diagnostic-n 512
```

For `nu=.01`, the three-parent fixture and `v0=2sin x`, the threshold is
about `19507.852`; the initial excess is zero. At t=2 its excess mass is
about `2901.694`. On a common 512 quadrature grid, the 128 and 256 histories'
pressure corrections differ by less than `8e-10` at the same time step.
Halving the step at resolution 128 changes that correction by less than
`1e-11`. A 1024 quadrature evaluation gives a positive
pressure correction about `.0150534`. The derivative-based flux pairing
agrees to about `.00004`; its kink-sensitive quadrature is reported separately
from evolution resolution. Sampled memory eigenvalues stay positive after
the initial zero tensor on these resolved prefixes; the energy-memory
balance error is below `6e-13`. A coarser 64 evolution loses memory positivity
later and is not used as physical evidence.

The selected memory-pressure derivative cost divided by the displayed
diffusion lower bound is about `5.45e-5`, well below `33/56`; against the
full completed diffusion it is about `5.90e-7`. This supports this tested
payment and illustrates a real excess burst. It does not verify an estimate
uniform over arbitrary mutually amplifying parent histories. The stochastic
representation, parabolic comparison, pressure observer bound, weak selector
limit and resulting full-history allowance remain analytic results.

## Canonical pressure square and selected diffusion

`pressure_square_augmentation.py` examines a stronger sufficient observable
that pays the varying-selector memory-gradient cost pointwise. Let
`P=Hess p`, `P_hat=P+P_C`, and let `Psi` be the completed joint observable.
The proposed addition is the **actual canonical pressure**, not a free
pressure slot:

```text
Phi=Psi+|P|^2,
D_Phi=D_Psi+2nu sum_j |partial_j P|^2.
```

For arbitrary matrices `L` and `PP`, the exact square is

```text
(33/5)|L|^2+(33/28)|PP|^2-|L-PP|^2
  =|28L+5PP|^2/140 >=0.
```

The completed observer diffusion supplies `(56/5)nu|grad P_hat|^2`.
The extra square supplies `2nu|grad P|^2`. Thus

```text
nu a|grad P_C|^2 <= (33/56)a D_Phi
```

pointwise for every nonnegative weight `a`. No positive lower bound on `a`
and no spatial derivative of it is used. In particular this accepts
`a=max(1-b^2/z^2,0)` on `z=Phi/h>0`. The corresponding integrated theorem
accepts bounded measurable weights. The scalar square diffusion, actual
initial-cost bound, selector identification and conditional continuation
adapter are Lean-certified in `WholeSpacePressureAugmentation`. The full
matrix lower bound and construction of the physical memory remain analytic
application obligations.

The addition preserves coercivity and has finite initial cost:

```text
integral |P0|^2 <= integral |grad u0|^4.
```

It creates extra signed production, which must be retained. With the exact
pressure-Hessian observer `K` and the physical material-diffusion operator
`D=partial_t+u.grad-nu Delta`, the unforced equation gives

```text
D P=-K(u tensor grad p+grad p tensor u)
     +[u.grad,K](u tensor u)-2nu K(grad u (grad u)^T),
extra production=2P:D P.
```

The default checker differentiates the actual canonical pressure using
every coefficient of the full NS right-hand side and compares the entire
field with this formula. It also checks the literal pressure-square
Laplacian, the absorption square and the initial quartic estimate. Checks
use exact Gaussian-rational algebra and remain enabled under `python3 -O`.
For the reciprocal-parent datum at `epsilon=1/5`, `nu=1/100`, the two phases
have the same pressure-square mass `8549/6250` but added production
`-phase*2728269/24062500`. The transport commutator is included; its work is
`phase*63/15625`. The viscous-source work happens to vanish at this initial
slice, and is retained at later slices. These are instantaneous identities,
not a sign obstruction to a compatible time-integrated reserve.

From the package directory:

```sh
python3 -O labs/pressure_square_augmentation.py
python3 labs/reciprocal_parent_history.py --prefix --n 96 --final-time 1.5 --dt .005 --sample-interval 1.5 --save-state state.npz
python3 labs/pressure_square_augmentation.py --state state.npz --diagnostic-n 192
```

The diagnostic reads the saved velocity and all six memory entries without
reintegration. Its threshold is the previous full-datum majorant plus the
square of the initial pressure majorant; it is fixed before evolution.
It checks the pointwise absorption and reports the pressure-production
components separately. Its signed excess expression is the full physical
PDE evaluated on a padded Galerkin slice. Galerkin residuals are not included,
so it is not the derivative of the truncated solution. Positive sampled
memory and quadrature/refinement checks do not constitute a continuum
enclosure. This stronger candidate leaves payment of arbitrary signed
production histories open; it does not assert equivalence with the weaker
unaugmented excess criterion.

### Full canonical receiver derivative and nonlocal projection

The same diagnostic now retains both terms of the added canonical receiver
`N=2aP`, with `a=(1-b^2/z^2)_+`, `z=Phi/h`, and `c=2b^2/z^3` on the active
branch and zero otherwise:

```text
partial_j N=2a partial_j P+2P c partial_j z,
nu |partial_j N|^2 <=8nu a|partial_j P|^2+16J_j,
J_j=nu h c|partial_j z|^2.
```

This pointwise payment uses `|P|²<=Phi=hz` and `zc<=2`. It makes no division
by `a`. The diagnostic checks every sampled point and forms the literal
receiver divergence from this whole jet. It then applies the full discrete
orthogonal gradient projection without a Galerkin mask; Parseval supplies
the projection norm. The Helmholtz pressure component has the negative
sign corresponding to `-Delta q_N=div div N`. Its norm satisfies

```text
nu ||grad q_N||_2^2 <=nu ||div N||_2^2
                  <=24nu integral a|grad P|^2+48 integral J.
```

`WholeSpacePressureReceiver` certifies the actual whole-space product rule
almost everywhere, local Lipschitz regularity of the receiver, its `L²`
membership, derivative integrability and this **unweighted** projection
payment. The ratio's Lipschitz modulus establishes differentiability and
does not occur in the cost. The selector is Lipschitz, not generally `C¹`;
the minimum at zero handles the cutoff level without a null-level-set
assumption. The weak Poisson interpretation additionally uses integration
by parts for the Lipschitz receiver, an analytic identification here. This
does not pay the anisotropic memory-weighted norm or signed histories.

On the saved `96^3` state at `t=1.5`, independent quadrature gives:

| Quantity | `192^3` | `208^3` |
| --- | ---: | ---: |
| Literal receiver derivative cost | 0.20090249 | 0.20030063 |
| Native diffusion majorant | 6654.71160 | 6676.18654 |
| Receiver divergence cost | 0.13021713 | 0.12954801 |
| Projected pressure-gradient cost | 0.08997961 | 0.08982153 |
| Normalized weak-test residual | 0.00920544 | 0.00165355 |

The weak test chooses a nonzero low Fourier moment of the actual receiver,
among frequencies with components at most four, and aligns its phase. Both
grids choose `(3,-1,2)`. At `208^3`, the two entry-`00` moments are
`-0.01712019` and `+0.01729181`; the discrepancy is quadrature error across
the cutoff. A first arbitrary test vanished by symmetry and was replaced.
This meaningful test supports the derivative implementation; it is neither
a rigorous weak-PDE verification nor a continuum enclosure. No new
evolution or time-integrated history estimate is supplied by this diagnostic.

For the saved `96^3` prefix at `t=1.5`, the `192^3` and `208^3` diagnostic
grids give:

| Quantity | `192^3` | `208^3` |
| --- | ---: | ---: |
| Augmented excess mass | 97.85460061 | 97.85205124 |
| Selected memory-gradient cost | .00271088672 | .00271034600 |
| Selected augmented diffusion | 141.07097081 | 141.15267432 |
| Added signed pressure production | .03815585728 | .03816474308 |
| Selected transport-commutator production | .09547050445 | .09546497523 |
| Weight-gradient diffusion | 415.91755863 | 417.25974173 |

Both grids retain positive sampled memory and satisfy the pointwise square
payment. The extra selected pressure production is positive: its positive
transport commutator exceeds negative pressure-work and viscous-source
contributions. These refined spatial diagnostics concern the same numerical
history, not independent evolution resolutions or a future resource bound.

## Reciprocal cellular-parent renewal

`reciprocal_parent_history.py` adds genuine three-dimensional feedback to
the pressure-bearing cellular datum above. Its torus has period `2*pi` and
normalized volume. Keep the three cellular parents and `v0=2sin x`, and add
two real cosine modes with Fourier amplitudes

```text
k=(1,1,1),    u_k=u_-k=(epsilon/2)(1,-1,0),
l=(0,-1,1),   u_l=u_-l=(sigma epsilon/2)(1,1,1),  sigma=±1.
```

They are transverse and vertically dependent. Together with the other
parents, the datum is genuinely three-dimensional. Their difference is the
receiving cellular frequency `q=(1,2,0)`, whose initial coefficient is
`i(-1/5,1/10,0)`. Only the ordered pairs `(k,-l)` and `(-l,k)` reach this
receiver. The complete, canonical-pressure-corrected nonlinear source is

```text
N_q=i sigma epsilon^2(-4/5,2/5,1/4),
Re(conj(u_q).N_q)=sigma epsilon^2/5,
E_{q,-q}'=(4/5)sigma epsilon^2-nu.
```

The exact checker retains all outputs, including forty newly generated
modes for `epsilon=1/5`. The full nonlinear kinetic work is zero. At
`epsilon=1/5`, the cellular parents receive nonlinear energy at rate
`4/125` for the positive phase, and the remaining modes lose energy at
exactly that rate. Reversing the phase reverses this transfer. Both data
have energy `469/200` and the same initial pressure-Hessian Fourier
majorant `1831996/144375`. No body force or independent hidden controller
is introduced.

`MettapediaNS.CellularParentRenewal` kernel-checks the real, transverse datum,
the two actual sources, equal initial energy, complete kinetic balance,
physical receiving-pair rates, and their derivative consumer. It identifies
the apparent force on the observed plane wave with the existing all-input
subgrid force, including the Leray pressure correction. The finite support
describes the initial datum; it is never assumed invariant under evolution.
Lean's torus has period one: viscosity `1/(200*pi)` and the receiving rates
`11*pi/250` and `-21*pi/250` correspond to viscosity `1/100` and rates
`11/500` and `-21/500` here. The derivative consumer requires the actual
coefficient derivative at the stated datum; it supplies no new existence
or time-interval theorem.

The heat-style parent reserve from the restricted class is, on this initial
cellular set `P`, while its coefficients are nonzero,

```text
R_P=(1/nu) sum_{q in P}|u_q|/|q|,
S_P=sum_{q in P}|q| |u_q|,
R_P'=-S_P+(1/nu)sum_{q in P} Re(conj(u_q).N_q)/(|q| |u_q|).
```

It starts at `54` for `nu=.01`. Its initial rate is `1/2` for the positive
phase and `-59/10` for the reversed phase. Thus autonomous monotonicity of
this projected reserve fails outside the restricted class. Smooth local
NS existence and continuity turn the positive initial rate into a short
increasing interval analytically; that interval claim is not newly
Lean-certified. A corrected full-datum reserve and recurrent-history
payment remain possible.

For a fixed parent band, elementary kinetic control already gives
`R_P <= sqrt(6 E0/5)/nu` and `S_P <= sqrt(30 E0)`, because these six modes
have squared frequency five. This finite-band bound is consistent with
the observed increase. The open problem is a payment that controls the
dangerous observable across all evolving scales and geometries.

The default checker also compares every velocity and memory coefficient of
the numerical initial operator with the exact complete Fourier operator.
Six rational amplitude/phase checks pass; the maximum floating operator
error is below `7e-17`.

```sh
python3 labs/reciprocal_parent_history.py
python3 labs/reciprocal_parent_history.py --prefix --n 32 --final-time .1 --dt .005
python3 labs/reciprocal_parent_history.py --prefix --n 48 --final-time .1 --dt .005
python3 labs/reciprocal_parent_history.py --prefix --n 48 --final-time .1 --dt .0025
python3 labs/reciprocal_parent_history.py --prefix --n 48 --final-time .1 --dt .005 --phase -1
```

Prefixes evolve all velocities and all six symmetric memory entries with
no prescribed parent path. The threshold `b=75713.1665463` is fixed from an
analytic initial gradient bound and the exact initial pressure majorant;
it is not fitted to a future maximum. Pressure and its full nonlinear
history are evaluated on an enlarged grid. Diagnostics retain canonical
pressure, the full pressure commutator, memory positivity, high-frequency
fractions, the soft selector, completed diffusion and the signed parent
reserve and energy ledgers.

The joint-excess production diagnostic evaluates the full PDE expression
on the current approximate field. It is not asserted equal to the excess
derivative of the truncated evolution: that comparison also requires
the Galerkin residual. The parent ledgers, in contrast, use the actual
coefficient RHS integrated by the numerical solver.

At `t=.1`, the positive-phase reserve is `54.0092382831345`; spatial
refinement changes it by less than `4e-14`, and halving the time step by
less than `1.2e-11`. Its renewal integral is about `.279295323817`, exceeding
the shear integral `.270057040682`. The reversed-phase reserve is about
`53.3735035945694`. Sampled memory eigenvalues are positive at that endpoint
and both signed ledgers close to about `1.4e-13` or better. The soft excess
is still zero there, so this does not test its active pressure payment.

Longer coarse prefixes lose memory positivity and are excluded from
physical payment evidence, even when their integrated kinetic balance
looks accurate. Numerical prefixes are Fourier-Galerkin approximations,
not continuum enclosures; unretained evolution, positivity and threshold
quadrature require separate refinement. No bound for arbitrary repeated
parent renewal is inferred from these finite checks.

## Old stochastic memory and a recent-parent pressure remainder

`memory_age_pressure.py` and `MettapediaNS.MemoryAgePressure` price the age of
retained memory. The physical input is the same positive tensor, not a new
fluid force or a different equation:

```text
D=partial_t+u.grad-nu Delta,   D C=2nu B B^T,   C(0)=0,   B=grad u.
```

Let `U(s,t)` propagate scalar incompressible advection and diffusion, acting
entrywise on tensors in a fixed frame. It preserves positivity and composes.
For a prescribed `delta>0`, set

```text
C_old(t)=U(t-delta,t)C(t-delta)                         t>=delta,
C_old(t)=0                                             t<delta,
C_recent(t)=2nu integral_max(0,t-delta)^t U(s,t) B B^T(s) ds.
```

Their sum is the actual `C`. All past parents and every tensor component are
retained. The age cut does not grant another initial allowance.

### Smoothing independent of the unknown future drift

The scalar propagator is positivity preserving and contracts `L1`. For
`y=||f||_2^2`, incompressibility gives `y'=-2nu||grad f||_2^2`. On whole
space, with the Fourier transform `integral exp(-ik.x)f(x)dx`, splitting
frequencies at `R` gives

```text
y<=R^3||f||_1^2/(6pi^2)+R^-2||grad f||_2^2,
y^(5/3)<=C_N||f||_1^(4/3)||grad f||_2^2,
C_N=2^(5/3)/(6pi^2)^(2/3).
```

The second inequality follows by balancing the two terms; its constant is
not optimal. Integrating the resulting differential inequality bounds the
`L1->L2` norm by `(3C_N/(4nu(t-s)))^(3/4)`. The adjoint propagates the reversed
divergence-free drift and has the same estimate. Composition at the temporal
midpoint therefore gives

```text
||U(s,t)||_(L1->Linfinity)<=(sqrt(3)/pi^2)[nu(t-s)]^(-3/2).
```

On the normalized period-2pi torus, at most `27R^3` modes lie below `R>=1`.
For `y>54||f||_1^2` use `R=(y/(54||f||_1^2))^(1/3)`; otherwise use that
threshold directly. The same energy, adjoint and composition argument gives

```text
||U(s,t)||_(L1->Linfinity)<=54 max(1,[3/(nu(t-s))]^(3/2)).
```

These analytic estimates apply to any smooth incompressible drift on an
available prefix, including a forced one. The unforced input is the original
source payment `integral tr C(t)<=E0=||u0||_2^2`. Positivity and smoothing
bound `C_old<=L_delta I`, where `L_delta` is `E0` times the respective kernel
bound at `delta`. No future strain modulus appears. Construction of `U`,
the adjoint and the Nash differential inequality are not yet Lean-certified.

### Geometry retained in the pressure cost

Fix `eta>0`, put `H=eta I+C`, `K=eta+L_delta`, `c=tr C_recent`, and let `v`
be the pressure gradient of an actual receiver tensor. Positivity gives
`v.C_recent v<=c|v|^2`, without a common eigenframe. More precisely,

```text
tr(H)v.Hv <=(3K+c)(K|v|^2+v.C_recent v)
          =3K^2|v|^2+R_geom,
R_geom=K c|v|^2+(3K+c)v.C_recent v.
```

This retains directional geometry and the isotropic trace term. The simpler
consequence, using `2(K-c)^2>=0`, is
`tr(H)v.Hv<=5K^2|v|^2+3c^2|v|^2`. Both tensor comparisons are Lean-certified.
Their old-bound and positivity hypotheses are explicit. The integral consumer
constructs weighted-cost integrability from the recent remainder, and applies
the spatial result to the actual canonical pressure receiver from
`WholeSpacePressureReceiver`.

That constructed receiver `N=2aP` has native payment

```text
nu integral|grad q_N|^2<=48Q_native,
Q_native=sum_j [2nu integral a|partial_j P|^2+integral J_j].
```

The full augmented selected diffusion plus `J` dominates this native cost.
The module proves the literal projection consumer, with the same ratio
regularity and instantaneous integrability hypotheses as its predecessor.
It does not identify this component with the whole joint effective receiver.

For any receiver with the same integrated native payment, the analytic
entropy pairing yields `|I|<=alpha E0+T/(4alpha nu eta)`, where
`T=integral tr(H)v.Hv` and `I=integral receiver:P_C`. With all integrals over
one entire available prefix and `alpha=36K^2/(epsilon nu^2 eta)`, the new
scalar certificate gives

```text
|I|<=36K^2 E0/(epsilon nu^2 eta)+epsilon Q
       +(epsilon nu/(144K^2)) integral R_geom,    epsilon>0.
```

The trace version instead gives the allowance `60K^2 E0/(epsilon nu^2 eta)`
and remainder `(epsilon nu/(80K^2)) integral c^2|v|^2`. Neither remainder is
asserted bounded. The space-time entropy/weak-pressure identification remains
analytic. The original allowance is used once, not again at each seam.
As `delta` tends to zero, the whole-space allowance grows like
`E0^3/(epsilon eta nu^5 delta^3)`. Taking a vanishing age cannot remove the
recent cost. This is a component estimate with explicit recent parents;
full pressure work, the signed commutator and repeated renewal remain open.

### Spectral compression can destroy the required positivity

The exact checker also constructs the globally smooth unforced shear

```text
u(t,y)=(sum_(k=1)^3 exp(-nu k^2 t) sin(ky)/k,0,0).
```

At time zero its actual positive memory source, divided by `2nu`, is
`(cos y+cos 2y+cos 3y)^2`. Projection onto `|k_y|<=3` gives
`3/2+2cos y+(3/2)cos 2y+cos 3y`. At `cos y=1/10`, the actual source is
`21609/15625`, while the projected source is `-33/500`. The projected
memory starts from zero and has a negative initial derivative there for
every `nu>0`. Its positivity guarantee fails. The genuine unforced velocity
and its unprojected memory do not fail. The Fourier coefficients are checked
exactly; the rational scalar certificates and negative viscous rate are Lean.

A bounded extension of the existing 96-cube reciprocal-parent prefix to
`t=1.6`, with memory older than `delta=.1` transported without new sources,
also loses recent-memory positivity under its spectral cutoff. On the
evolution grid the recent minimum eigenvalue is about `-9.74e-5`, although
old and total memory remain sampled positive. This run is excluded from
physical pressure-payment evidence; no weighted bound is inferred from it.
The diagnostic guard rejects the approximation before estimating that cost.
A positivity-preserving memory discretization, with its own convergence
checks, is required to use further numerical history evidence here.

```sh
python3 -O labs/memory_age_pressure.py
```

Default checks retain exact noncommuting tensor fixtures, both payment
constants, the actual heat shear memory equation and the filtering defect.
The arbitrary-flow fresh-parent reserve remains the principal physical target.

## Complete canonical pressure-square production

`pressure_source_production.py` compares the full NS tangent with the local
Poisson-source evolution on the normalized `2*pi` torus. Gaussian rational
arithmetic retains every convolution output. For `B=grad u`, `s=tr(B²)`,
canonical `P=Hess p`, and `D=partial_t+u.grad-nu Delta`, it verifies

```text
D s=-2tr(B³)-2tr(BP)-2nu sum_j tr((partial_j B)²),
D(s²)=2s Ds-2nu|grad s|².
```

The actual pressure-square mass, its tangent, complete signed production
and square diffusion agree after integration with those of the source.
The whole-space pointwise source/time laws and crossed viscous absorption
are kernel-certified in `MettapediaNS.WholeSpacePressureProduction`.
The integrated time identification for the pressure square is analytic.
No finite-history production bound is inferred from these identities.

The resonant datum adds a transverse `(0,0,+/-2)` mode to the general
three-dimensional fixture. Reversing its sign changes the crossed viscous
production from `+48/175` to `-48/175` at `nu=1/10`. Both signs are required
by the checker. Thus this production term is not automatically dissipative.
Nevertheless, at every point of every smooth velocity, for `nu>=0`,

```text
|4nu s sum_j tr((partial_j B)²)|
  <=4nu|B|² sum_j|partial_j B|².
```

The right side is half the local strain-gradient density in the completed
diffusion lower bound. The checker verifies the actual crossed-trace
sum-of-squares and integrated comparison; Lean proves the pointwise,
selected and whole-space spatial comparisons. The full candidate Hessian
identification and remaining nonlinear history payment are separate.

For the added pressure square, the complete cotangent `4Hess(s)u` differs
from the local cotangent `-4Bᵀ grad s` by `4grad(u.grad s)`. They perform
the same work on the actual solenoidal velocity tangent. This identity
is exactly checked, including a constant drift; it does not discard the
canonical pressure from the observable or the other coupled equations.

The localization flux is `J=(P-Delta(p)I)grad p`, with
`div J=|P|²-s²`. For a fixed smooth weight `a`,

```text
integral a partial_t(|P|²-s²)=-integral grad a.partial_t J.
```

The checker retains every output of `J` and its complete time derivative
and verifies a nonzero flux correction against a smooth positive weight.
This is not the actual soft selector. Differentiating an entire weighted
mass with an evolving selector also differentiates that selector. The
chain-rule component `a partial_t|P|²` itself does not add that derivative.
The selector's weak-limit identification still needs proof.
The local source square cannot replace the selected pressure square in
the memory reserve without these corrections.

The forced tangent uses the solenoidal force `f=u` at the tested state.
Its additional source is `2tr(B grad f)` and its square production is
`4s tr(B grad f)`. This is a nonzero initial-state forcing comparison,
not the imported forced blowup construction. The unforced interacting
parent pair retains its opposite nonlinear signs.

```sh
python3 -O labs/pressure_source_production.py
```

## Complete selected pressure cotangent and its native payment

[`pressure_selected_cotangent.py`](pressure_selected_cotangent.py) tests
the complete canonical pressure-square first variation with a spatially
varying selector on the normalized `2*pi` torus. All outputs have exact
Gaussian rational coefficients. Both signs of the resonant 3D datum and
both phases of the interacting-parent datum are retained. The tangents
include every nonlinear output and viscosity; no Galerkin closure is used.

Let `B=grad u`, `s=tr(B²)`, `-Delta p=s` and `P=Hess p`. At the current
state, for a fixed selector coefficient `a`, define

```text
chi=(-Delta)^-1 divdiv(aP),
N=2aP, V=-Pi_gradient div N=2grad chi,
ell=-2B^T V.
```

The checker verifies the literal negative Helmholtz projection at every
Fourier output and the full selected pressure first variation along the
actual solenoidal NS tangent. The stress cotangent and its local
representative obey

```text
4Hess(chi)u-ell=4grad(u.grad chi),
integral 2aP:partial_t P=integral ell.partial_t u.
```

The discarded term is a genuine gradient whose work on the compatible
tangent vanishes. The nonlocal selector response remains in `chi`.
Replacing `chi` by `a*s` gives erroneous work, including `-6253/34650`
and `-1163/3850` in the two resonant fixtures. This refutes that shortcut,
not a finite allowance or the regularity goal.

The continuous positive test selectors range from `1/4` to `3/4`; they
are not identified with the candidate reserve's actual ratio. A constant
drift changes the fixed Eulerian selected derivative by `-75203/23100`
or `-36997/23100` in the resonant fixtures. The advective work changes
by the opposite amount. The checker additionally keeps the selector's
own derivative as a separate leg of a full weighted-mass chain rule, for
an auxiliary advected-diffused selector. That auxiliary law is not claimed
for the physical reserve selector.

The exact pointwise sum-of-squares witness is

```text
4|B|²|V|²-|ell|²
  =4sum_j sum_(i<k)(B_ij V_k-B_kj V_i)².
```

The kernel module `MettapediaNS.SelectedPressureCotangent` proves the
resulting normalized cost bound, its genuine whole-space integrability,
and its literal canonical-receiver consumer:

```text
nu integral |ell|²/(1+|B|²)<=192 Q_native,
Q_native=sum_k(2nu integral a|partial_k P|²+integral J_k).
```

It also constructs the canonical pressure-gradient variation, proves its
exact finite increment, and uses the solenoidal Lie bracket to identify the
divergence-form work. Pressure-gradient and Hessian-entry time derivatives
and that work identity hold on the actual complete smooth NS evolution.
The weak integration-by-parts interpretation of the Lipschitz selector
as selected Hessian work is analytic. The complete material transport,
joint strain/pressure/memory production and recurrent-parent allowance
remain obligations; a paid receiver norm does not pay its time work.

```sh
python3 -O labs/pressure_selected_cotangent.py
```

## Complete joint receiver payments and an actual-parent obstruction

[`joint_receiver_diffusion.py`](joint_receiver_diffusion.py) retains the
full geometric gradient and pressure slots. Its default checks use exact
rational Fourier fields and independently differentiated matrix fixtures.
The estimates and the asymptotic argument below are analytic; the kernel
module `MettapediaNS.JointReceiverDiffusion` certifies the scalar radial
and product-rule coefficients and an actual-NS signed work identity.

### The full gradient and pressure blocks

Use the completed `Psi` defined above, with any fixed positive envelope
regularizers. Put `r=|B|²`, `q=sqrt(sigma²+|P_hat|²)` and `Q=r+q`.
Let `E` vary the FULL `B`, `H=sym E`, `v=curl E`, and `e=|E|²`.
The identities `r=|S|²+|omega|²/2` and `e=|H|²+|v|²/2` imply

```text
|S||omega||H||v|<=r e/2,
|S|²|v|²<=2r e,        |omega|²|H|²<=2r e.
```

The complete first and absolute second directional derivative bounds are

| Term | First derivative divided by `r^(3/2)sqrt(e)` | Second derivative divided by `r e` |
| --- | ---: | ---: |
| `V²/(W+eta)` | 16 | 152 |
| `W²` | 16 | 48 |
| `Z=|S omega|²` | 8 | 18 |
| `Q_s W` | 8 | 12 |

For the perspective, divide its positive Hessian square by `W+eta` before
bounding. The resulting upper bound is
`70|S|²|v|²+4W|H|²+8|S||omega||H||v|<=152r e`.
This avoids any inverse-vorticity singularity and is uniform in `eta>0`.
The pressure term has first `B` derivative at most `8q sqrt(r e)`
and pure `B` curvature at most `8q e` in magnitude. The completion adds
first derivative at most `192Q^(3/2)sqrt(e)` and second at most `576Q e`.
Thus both completed branches have full `B` sensitivities at most
`300Q^(3/2)` and pure `B` upper blocks at most `1400Q`.

Their pressure gradients have norms at most `100Q` and `96Q`. Their pure
pressure blocks are at most `96Q/q`: the original pressure branch is
linear in this slot, and `D²_PP(Q²)<=2Q/q`.
The radial Hessian and `rho>=48Q²` therefore give

```text
Hess_BB Psi<=6600Q I,       |Psi_B|²<=180000Q³,
Hess_PP Psi<=600(Q/q) I,    |Psi_Phat|²<=20000Q².
```

Indeed the upper radial coefficients are `2800+180000/48=6550<6600`
and `192+19216/48=1777/3<600`. The previously derived FULL Hessian is
positive, so its Cauchy--Schwarz inequality controls mixed slot changes:

```text
|d(Psi_B)[E,L]|²<=6600Q Hess Psi[(E,L),(E,L)],
|d(Psi_Phat)[E,L]|²<=600(Q/q) Hess Psi[(E,L),(E,L)].
```

No vorticity derivative, axis change or pressure increment is frozen.
These uniform matrix identifications remain analytic, with exact fixture
and coefficient checks; their scalar radial combinations are Lean-certified.

### Payments for both actual local slots

Let `Phi=Psi+|P|²`, `z=Phi/h`, `h>0`, and fix `b>0`. Set

```text
a=(1-b²/z²)_+,       J=nu h phi_b''(z)|grad z|²,
M=a Psi_B,          N=a Psi_Phat+2aP,
D_Phi=nu sum_j Hess Psi[(B_j,P_hat_j),(...)]+2nu|grad P|².
```

On the active set, `Phi=hz`, `z phi_b''(z)<=2` and `Phi>=48Q²`.
The squared product rule gives

```text
nu |Psi_B|²|grad a|²/Q<=7500J,
nu (q/Q)|Psi_Phat|²|grad a|²<=(2500/3)J.
```

With `a²<=a`, the mixed derivative estimates yield

```text
nu |grad M|²/Q<=15000(J+a D_Phi),
nu (q/Q)|grad(a Psi_Phat)|²<=1700(J+a D_Phi).
```

The existing canonical component has
`nu|grad(2aP)|²<=16J+8nu a|grad P|²`.
Since `0<q/Q<=1`, addition pays the complete pressure receiver:

```text
nu (q/Q)|grad N|²<=3500(J+a D_Phi).
```

The identities hold almost everywhere across the threshold for the
continuous Lipschitz selector. Its weak product identification remains an
application obligation. The pressure receiver's weight is essential;
weighted Helmholtz contraction is not asserted.

For `V=-Pi_gradient div N`, the full divergence-form velocity cotangent is

```text
Lambda_u=-div M-2B^T V,
Lambda_C=K(a Psi_Phat)-beta hH^-1/3.
```

Lean proves the signed velocity work on compatible solenoidal directions
and on the actual NS tangent, with ordinary `L²` receiver divergences.
The entire pressure projection is retained. It also proves

```text
|Lambda_u|²/Q<=2|div M|²/Q+8|V|².
```

The last term is UNWEIGHTED. The local `q/Q` payment does not supply it,
and the complete norm comparison below actually fails. Identifying the
weak receivers with `Psi` and paying their physical time work remain open.

### An explicit actual NS family

On the normalized `2pi` torus, let `n` be a positive integer and take

```text
u_n=(n sin y,n^-2 sin(n x),0),     C_0=0,
p_n=2 cos y cos(n x)/(n²+1),      eta=sigma=b=1.
```

Both velocity parents are kept. The data are smooth and divergence-free,
and `p_n` is their actual canonical pressure. The complete initial NS
tangent, including viscosity, is used. The exact checker additionally
retains both signs of the small parent. Initial squared energy is
`(n²+n^-4)/2`; this family does not have uniformly bounded full data.
The physical memory source is `C_t=2nu BB^T>=0`. Its pressure observation
is zero AT THIS STATE: its two nonzero diagonal entries vary transversely
to their tensor indices. No zero-memory-pressure history is inferred.

The fixed test threshold `b=1` is below the initial envelope. It tests a
uniform spatial consumer, not the route's above-initial-supremum
initialization. That latter choice would make the initial excess inactive.
Neither a finite initialized reserve nor its repeated-renewal allowance
is refuted by this calculation.

### Analytic norm obstruction, retaining the entire cotangent

Write `phi=nx`, `c=cos y`, and

```text
alpha=48+63/95,       beta0=48+1399/1995,
gamma=sqrt(alpha²+beta0²),       kappa=(alpha+beta0)/gamma,
q_inf=sqrt(1+4c²cos²(phi)).
```

Outside the measure-zero set `c=0`, `Q/n²` tends to `c²` and
`Psi/n^4` tends to `gamma c^4`. The pressure receiver's leading `xx` entry is

```text
N_xx/n² -> -192 kappa c³cos(phi)/q_inf.
```

Its `zz` entry has no divergence, and its other divergence entries are
lower order. In the phase variables the physical gradient projection
has symbol `(n k_phi,k_y,0)`. For nonzero `k_phi` it converges to the `x`
projection. The scaled divergence has zero phase mean and converges in
`L²` to `192 kappa c³sin(phi)/q_inf³` in the `x` direction. Consequently

```text
V/n³ -> -192 kappa c³sin(phi)/q_inf³ e_x.
```

These are strong `L²` limits: the pressure and its phase derivatives are
uniformly bounded, the local pressure-gradient sensitivity is `O(Q)`,
and its mixed `B` sensitivity is `O(sqrt(Q))`. Thus phase derivatives of
`N/n²` are uniformly bounded, its `y` divergence divided by `n³` vanishes,
and dominated Fourier convergence applies to the bounded projection.
The mixed sensitivity follows by differentiating
`Psi_Phat=96(A+B0)Q P_hat/(rho q)-2A omega tensor omega/rho`,
using the branch gradients above. No weighted projection estimate is used.

The operator `B^T/sqrt(Q)` is uniformly bounded and converges almost
everywhere to `sign(c)` times the map from `x` to `y`. The full `div M`
term has cost `O(n^4)` by its local payment, so it vanishes after the
`n^6` normalization. Therefore the COMPLETE normalized velocity cost has
strictly positive finite limit

```text
(nu/n^6) integral |Lambda_u|²/Q
  -> nu (384 kappa)² integral c^6 sin²(phi)/q_inf^6 = L>0.
```

Direct differentiation of the restricted observable gives

```text
(1/n^4) integral (J+a D_Phi)
  -> nu integral [12 gamma c²(1-c²)
                   +384 kappa c^4 sin²(phi)/q_inf³] = D>0.
```

The block upper bounds dominate the scaled diffusion uniformly, so this
limit also follows by dominated convergence. The selector-gradient cost
and the added canonical pressure diffusion are lower order. Thus the
ratio of full normalized receiver cost to native payment grows as
`(L/D)n²`. No universal constant pays that norm from this diffusion on
all actual states. The asymptotic proof is analytic, not Lean-certified.

### The actual signed work cancels

In contrast, the full nonlinear WORK has zero mean at the initial state.
The observable and soft selector are even under `phi -> -phi`. Its
complete `B` gradient has only the `xy/yx` entries, and their actual
nonlinear tangents are odd. Diagonal pressure entries are even and their
nonlinear tangents odd; the `xy/yx` pressure entries are odd and their
tangents even. Their pairings are all odd. This includes both parents and
both pressure slots. The memory-pressure source vanishes as checked above;
the remaining capacity source is favorable. Incompressible transport has
zero integrated divergence. Hence the complete initial excess mass obeys

```text
d/dt integral F |_0
  = -integral(J+a D_Phi)-(2nu/3)integral beta |B|² <=0.
```

This is an analytic actual-state statement, not persistence of the parity
or of favorable production at later times. It demonstrates why a large
receiver norm is not itself evidence for dangerous recurrent stretching.
A signed reserve must use the actual compatible parent evolution.

### Reproducible checks and precise remaining scope

```sh
python3 -O labs/joint_receiver_diffusion.py
python3 -O labs/joint_receiver_diffusion.py --quadrature
```

The optional companion [phase quadrature](joint_receiver_quadrature.py)
retains physical derivatives and the Helmholtz symbol on independent
128 and 256 phase grids. At `nu=1/10`, the analytic-limit quadrature gives
`L=1769.68263`, `D=16.002274`, and `L/D=110.58945`. For `n=64` the measured
complete cost/payment ratio is about `453503`; its local `q/Q` pressure
payment ratio is about `37.7`. The complete velocity/memory chain rule and
signed parabolic balance are checked at the physical work scale, rather
than at the much larger unpaid norm scale.

These quadratures are spatial continuum-PDE diagnostics. They are neither
Galerkin trajectories nor continuum enclosures. The exact checker retains
all polynomial Fourier outputs; the analytic limits supply the uniform
obstruction. The full matrix identification, weak receiver calculus,
nonlinear reaction and finite full-datum compatible-history allowance
remain open. The initialized threshold and growing initial resources must
remain explicit when this test is used in a continuation argument.

## Signed viscous pressure flux and a reserve financed by the full datum

The failed uniform receiver-norm comparison does not require discarding
pressure. Its explicit viscous channel has a signed spatial payment that
retains the selector's boundary flux. An additional unselected resource
is finite from the original full datum. The remaining nonlinear history
estimate is still open.

### The actual pressure generated by derivative parents

Use row convention `B_ij=partial_j u_i`. Write

```text
G=BB^T,       s=tr(B^2),       -Delta p=s,       P=Hess p,
E_k=partial_k B,             -Delta q_G=div div G.
```

For solenoidal `u`, all derivative parents `v_k=partial_k u` are
solenoidal. Differentiating both factors of `G` gives

```text
div G = sum_k (v_k.grad)v_k,
div div G = sum_k tr(E_k^2),
grad q_G = sum_k grad p[v_k] = -Pi_gradient(div G).
```

These are the actual source parents, with no frequency truncation or
alignment hypothesis. Cauchy--Schwarz and the UNWEIGHTED orthogonal
projection give the sharper constant one:

```text
|div G|^2 <= r sum_k |E_k|^2,             r=|B|^2,
||grad q_G||_2^2 <= integral r sum_k |E_k|^2.
```

`SignedViscousPressure` constructs the smooth tensor rows, their actual
divergence and the derivative-parent pressure. It certifies its canonical
Poisson source, this norm bound and genuine spatial integrability. Given
the completed observable's analytic diffusion lower bound,

```text
D_Phi >=8nu r sum_k |E_k|^2,
nu ||grad q_G||_2^2 <= (1/8) integral D_Phi.
```

This source is `C_t/(2nu)` at initial memory zero. At later times it is
the source in `D C=2nu G`, not the full memory or its pressure. No
weighted projection contraction or unproved memory realization is used.

### The selector flux, with its exact sign

The pointwise bilinear Hessian identity is

```text
P:Hess q_G - s sum_k tr(E_k^2)
  = div[(P+sI) grad q_G].
```

It follows from `tr P=-s` and commuting scalar derivatives. Integration
against the actual continuous soft weight `a` yields

```text
-4nu integral a P:Hess q_G
  = -4nu integral a s sum_k tr(E_k^2)
    +4nu integral grad a.(P+sI)grad q_G.
```

The boundary term is retained. A selected canonical pressure square
cannot be replaced by a selected local source square without this term.
Its weak whole-space integration by parts remains an analytic application
obligation; the exact checker also verifies a NONZERO flux on a positive
smooth trigonometric test weight.

The literal pressure trace gives

```text
|P+sI|_F^2=|P|_F^2+s^2 <= |P|_F^2+r^2 <= Phi.
```

The matrix-square identity and its actual canonical-pressure adapter are
kernel-certified. The last coercivity follows from the completed `Phi`.
The perspective selector has `nu Phi |grad a|^2<=2J`. Consequently the
squared boundary density is at most `32J nu|grad q_G|^2`. The square

```text
(J/2+16G0)^2-32J G0=(J/2-16G0)^2
```

pays its absolute value by `J/2+16nu|grad q_G|^2`. Set
`S=integral a D_Phi`, `J0=integral J`, and `D0=integral D_Phi`. The
previous local crossed-viscosity estimate and the source payment give

```text
|V_selected| <= S/2+J0/2+2D0,
|V_unselected| <= D0/2,
V_selected=-4nu integral a P:Hess q_G,
V_unselected=-4nu integral P:Hess q_G.
```

These do not grant the unselected diffusion for free. It is supplied by
the correction below, together with all of that correction's production.

### One initial resource, retaining complete signed production

Retain the actual memory and joint observable from the previous section:

```text
D C=2nu G, C_0=0,   h=det(I+C)^(1/3),
P_hat=K(u tensor u+C),   Phi=Psi(B,P_hat)+|P|^2,
Phi_infinity=1+48sqrt(2)sigma^2.
```

Here `K(T)=Hess(-Delta)^-1 div div T`. The stress satisfies
`D(u tensor u+C)=-u tensor grad p-grad p tensor u`. Thus define

```text
A_hat=[u.grad,K](u tensor u+C)-K(u tensor grad p+grad p tensor u),
A_p  =[u.grad,K](u tensor u)  -K(u tensor grad p+grad p tensor u),
R_NL =Psi_B:(-B^2-P)+Psi_Phat:A_hat+2P:A_p.
```

All pressure transport, phases, parents and orientations remain in these
expressions. The exact unforced equations give
`D P_hat=A_hat` and `D P=A_p-2nu Hess q_G`. In particular, memory cancels
the explicit viscous source in the observed pressure, while the added
canonical pressure square retains its source.

Use the fixed correction

```text
R_b=integral [F_b+8(Phi-Phi_infinity)],
D_total=S+J0+8D0,
N_total=integral (a+8)R_NL,
C_capacity=integral beta D h >=0.
```

The complete analytic integrated chain rule is

```text
R_b' = N_total+V_selected+8V_unselected-C_capacity-D_total.
```

The viscous estimates imply

```text
|V_selected+8V_unselected| <= (3/4)D_total,
R_b'+D_total/4 <= N_total-C_capacity.
```

The coefficient combinations are kernel-certified. Full matrix
identification, the positive transported-memory application, weak selector
calculus and this time chain rule remain analytic. The correction is a
candidate repair of the reserve; it does NOT bound `N_total`.

The initial deposit is finite without a future norm. The completed branch
values satisfy, uniformly in the vorticity regularization,

```text
0<=Phi-Phi_infinity
  <=256[r^2+sigma r+|P_hat|^2+|P|^2].
```

For the upper bound, use `|p0|<=13r^2+4r q`, `0<=c0<=14r^2`,
`q=sqrt(sigma^2+|P_hat|^2)`, the Euclidean triangle inequality for the
two branch values, and `r q<=sigma r+(r^2+|P_hat|^2)/2`. Both completed
branches are at least `48sigma^2`, giving the lower bound. At `C_0=0`,
`P_hat=P`, and the actual pressure-square theorem gives
`integral |P|^2<=integral r^2`. Choose `b` once above the initial
supremum, and above the far-field offset in the whole-space setting.
Then `F_b(0)=0` and

```text
R_b(0) <=6144 integral r_0^2+2048sigma integral r_0.
```

This deposits finite full-initial-data resources. It is not an energy-only
allowance, nor a bound on the future corrected reserve. It is never
re-deposited at a history seam. Nonnegativity and domination of the soft
excess are kernel-certified, as is the adapter from a corrected-reserve
bound to the existing actual whole-space continuation envelope.

### Remaining physical estimate and adversarial checks

A sufficient next target, for example, is

```text
integral_0^tau N_total dt
  <=(1/8)integral_0^tau D_total dt+A(u_0,nu,H),   tau<=H,
```

with `A` finite from the full original datum, viscosity and prescribed
horizon for every compatible unforced prefix. No such estimate is proved
here. This is the signed history crux with its explicit viscous channel
paid, not a claimed reduction of the entire regularity difficulty.

For a solenoidal force `f`, the same spatial payments hold, but the production also
contains

```text
integral (a+8)[Psi_B:grad f+(Psi_Phat+2P):K(u tensor f+f tensor u)].
```

The exact checker retains this extra leg for solenoidal `f=curl u` that
does zero instantaneous kinetic work on its fixtures. This is a finite
forcing diagnostic, not the imported blowup construction or a realization
by hidden unforced parents. Dropping this leg would erase the required
forced/unforced distinction.

```sh
python3 -O labs/signed_viscous_pressure.py
python3 -O labs/signed_viscous_pressure.py --quadrature
```

The default checks retain all Fourier outputs, tensor rows, derivative
parents, canonical pressure, nonzero localization flux and actual memory
source. A resonant extra parent breaks the base fixture's sign symmetry.
Optional independent spatial quadratures test the actual soft selector,
full initial NS/memory generator and surviving diffusion, retaining
opposite signs of the nonlinear work. Their fixed test threshold is below
the initial envelope; these are spatial consumer tests, not initialized
history estimates, Galerkin evolutions or continuum enclosures.

On the resonant fixtures, independent 96 and 128 grids agree within
`5.06e-8` on the reported comparisons; the largest scaled complete-generator
or flux residual is `2.96e-9`. At amplitude one, the nonlinear work is
approximately `+1492697.57` and `-1492697.57` for the two velocity signs.
For the positive sign of production, the corrected reserve's full initial
derivative is approximately `+212910.63`. Thus even this corrected reserve
need not decrease at an active state. The initial resources are finite,
and the test uses a threshold BELOW the initial envelope. Neither an
initialized full-datum allowance nor arbitrary-data regularity is refuted.

## Pressure-compensated history: a paid channel and its geometric consumer

The previous correction pays the explicit viscous pressure channel while
retaining the full nonlinear reaction. A second positive component now pays
one genuine pressure history on the actual fluid drift. This payment comes
from incompressible transport and viscosity, with the original initial label
retained at every seam. It does not yet control the weighted geometric
receiver or the arbitrary-data continuation criterion.

### Literal passive transport and its signed pressure reserve

On an existing smooth unforced NS prefix, put

```text
D=partial_t+u.grad-nu Delta,
Du=-grad p,      div u=0,
DH=0,           H(0)=u_0,
I=H-u,          DI=grad p,           I(0)=0.
```

The passive vector `H` need not be solenoidal. Only the actual fluid drift
must be incompressible. The auxiliary linear parabolic equation can be
constructed on each existing smooth prefix; the bound below requires no
constant depending on its unknown future derivatives. That construction
and its stochastic representation are analytic here, not Lean existence
theorems.

`MettapediaNS.PressureImpulseHistory.PassiveHistory` contains the literal
passive PDE, continuity of all spatial L2 jets, and its original initial
value. There is no energy estimate or desired conclusion in its fields.
Lean derives both complete energy balances from those equations:

```text
||H(t)||_2^2+2nu integral_0^t ||grad H||_2^2=E_0,
||u(t)||_2^2+2nu integral_0^t ||grad u||_2^2=E_0,
E_0=||u_0||_2^2.
```

The squared triangle inequality, applied to the terminal fields and their
actual accumulated gradients, gives the kernel-certified history payment
for `nu>=0`:

```text
spent(t)=||I(t)||_2^2+2nu integral_0^t ||grad I||_2^2 <=4E_0,
spent(t)=2 integral_0^t <I,grad p>,
0<=spent(t)<=4E_0,
reserve(t)=4E_0-spent(t)>=0.
```

For positive viscosity this includes
`integral_0^t ||grad I||_2^2<=2E_0/nu`. The actual segment law is

```text
spent(s)+2 integral_s^t <I,grad p>=spent(t),
2 integral_s^t <I,grad p> <=reserve(s).
```

It retains `H(s)`, `I(s)` and the original datum. Restarting `H` from `u(s)`
would change the history and would not prove this same statement. The
signed cumulative payment can decrease; this result does not bound the
sum of positive bursts or the absolute pressure work. It neither bounds
the pressure Hessian nor supplies the critical geometric reserve.

### The actual backward stochastic identification

Starting from `(t,x)`, use the backward diffusion

```text
dX_s=-u(t-s,X_s)ds+sqrt(2nu)dW_s,
Y_s=u(t-s,X_s),
J_s=integral_0^s grad p(t-r,X_r)dr,
M_s=Y_s-J_s.
```

The actual NS equation makes `M_s` a martingale, with stochastic derivative
`sqrt(2nu) B(t-s,X_s)dW_s`. Thus the existing memory satisfying
`DC=2nu BB^T`, `C(0)=0`, is analytically identified as

```text
C(t,x)=Cov(M_t)=E integral_0^t 2nu BB^T(t-s,X_s)ds.
```

This is covariance of the pressure-compensated terminal velocity. It is
generally different from covariance of `u_0(X_t)` alone. The compensation
is an auxiliary path observable; it is not an additional force applied to
the fluid and does not choose a stochastic-control optimizer.

The joint terminal moments make the necessary boundary information explicit:

```text
U_0=u_0(X_t),       H=E U_0,           I=E J_t,
L=E[U_0 tensor U_0],
K_cross=E[U_0 tensor J_t],
Q_imp=E[J_t tensor J_t],
u tensor u+C=L-K_cross-K_cross^T+Q_imp.
```

Their equations retain the common fluid drift and pressure:

```text
DL=0,
DK_cross=H tensor grad p,
DQ_imp=I tensor grad p+grad p tensor I,
D(Q_imp-I tensor I)=2nu (grad I)(grad I)^T,
integral tr(Q_imp)=spent(t)<=4E_0.
```

The impulse variance is positive diffusive memory. Dropping the cross moment
changes the augmented stress seen by the pressure observer. These joint
moments identify a concrete compatibility obligation for a boundary summary;
no nonlinear boundary-reconstruction theorem is asserted here.

For forced flow, `Du=-grad p+f`. The martingale compensation and impulse
equation therefore contain `grad p-f`, and the kinetic balance contains
force work. Even vanishing instantaneous kinetic work does not remove the
force impulse. The finite diagnostic uses a fixed Eulerian solenoidal
`f=curl u_0`, with zero kinetic work only at the tested initial state.
It is not the imported blowup construction or its internal unforced
realization.

### The receiver response still needed by the geometric reserve

The paid impulse gradient has a named consumer. Put `A=grad I`, retaining
row convention `B_ij=partial_j u_i`. Differentiating its actual equation gives

```text
DA=P-AB,       P=Hess p.
```

For a smooth time-dependent tensor receiver `N` with the required spatial
integrability and vanishing boundary terms, integration by parts gives

```text
integral_0^t integral N:P
 = [integral N:A]_0^t
   +integral_0^t integral A:
       [N B^T-(partial_t+u.grad+nu Delta)N].
```

The complete adjoint response includes receiver diffusion with the displayed
sign, transport, its time derivative, and parent deformation. Endpoints
must also be paid. This identity is analytic here; the exact checker
verifies the differentiated impulse equation on the full actual initial
time jets.

For the evolving geometric receiver, these response terms include pressure,
memory, selector changes and interacting parents. A finite bound for them
from the original full datum is OPEN. The paid unweighted impulse cannot
replace that theorem. The still-sufficient target remains

```text
integral_0^tau (N_total-C_capacity)
 <= integral_0^tau D_total/8+A(u_0,nu,H),       tau<=H,
```

with the full reactions defined in the preceding section and a finite
allowance fixed before the unknown future history. No Schrodinger-bridge
optimizer identification or arbitrary-data regularity theorem is proved.

### Exact jets and initialization-sensitive diagnostics

```sh
python3 -O labs/pressure_impulse_history.py
python3 -O labs/pressure_impulse_history.py --initialized-quadrature
```

The exact checker uses rational Fourier coefficients on genuinely
interacting 3D data, both velocity signs and two amplitudes. It retains all
outputs, the first two actual NS/passive time derivatives, pressure's own
time derivative, and the nonzero joint cross moment. It checks the passive
and unforced energy derivatives, augmented stress through second order,
and the positive impulse-variance source through third order. Replacing
the compensated covariance by raw terminal-velocity covariance gives a
nonzero exact discrepancy. These are finite initial jets, not constructed
continuum trajectories or kernel-certified stochastic identities.

The optional independent 96 and 128 spatial grids use a datum-fixed analytic
Fourier bound ABOVE the complete initial envelope, with `C(0)=0` and initial
soft excess zero. For amplitude one the bound is `b=23625733`, independent
of the grid and unknown future. The sampled initial envelope maxima are
about `1.215e6`, well below that bound. The augmented reserve nevertheless
has full initial derivative approximately `+189384.56` for one velocity
sign, with complete nonlinear work approximately `+1326842.27`.
The opposite sign gives a negative initial derivative. The selected
diffusion and initial capacity payment vanish because the selector is
inactive; the unselected correction and its full PDE production remain.

The largest scaled generator residual is `2.96e-9`, and the independent
reported comparisons agree within `4.37e-10`. These are numerical spatial
diagnostics, not continuum enclosures. They warn against assuming immediate
monotonicity even with the intended initialization. An initial burst is
compatible with a finite full-datum allowance; neither that allowance nor
arbitrary-data regularity is refuted. The changing-receiver and recurrent
parent estimates remain the decisive obligations.

## Retained-parent completion with the actual vorticity geometry

The impulse payment does not justify cancelling or bounding the entire
pressure contribution independently of the receiver. On the preceding
interacting 3D fixture, the original direct strain-pressure leg is favorable
for the sign with positive complete initial production. Removing that leg
by its impulse endpoint transfer therefore increases the initial production.
The dominant positive component is parent deformation. The following
completion retains that deformation and the actual vorticity geometry.

### An actual split, with the original geometry preserved

Let `H` be the original-datum passive vector and `I=H-u` as in the previous
section. Write

```text
B_H=grad H,      A=grad I,      B=B_H-A=grad u,
D B_H=-B_H B,   D A=P-AB,      D B=-B^2-P.
```

Here `D=partial_t+u.grad-nu Delta`. The two retained parents share the
actual NS drift and original history; they are not independently selectable
controls. Physical vorticity, strain and the branch invariants are computed
from B. In particular the passive vector's curl does not replace the fluid
vorticity.

Keep the previously defined `p0(B,P_hat)` and `c0(B)`. Change their radial
completion to the joint size

```text
R=|B_H|^2+|A|^2,        q=sqrt(sigma^2+|P_hat|^2),        Q=R+q,
U=p0(B,P_hat)+192Q^2,   V=c0(B)+192Q^2,
Psi_joint=1+sqrt(U^2+V^2),
Phi_joint=Psi_joint+|P|^2.
```

The positive regularizers remain fixed. Since `|B|^2<=2R` and
`|omega|^2<=2|B|^2`, while `c0>=0`,

```text
Psi_joint>=1+192Q^2,
Phi_joint>=1+48|B|^4+|P|^2>=1+12|omega|^4+|P|^2.
```

The pressure branch obeys `U>=190Q^2>0`. Both branches are at least
`192sigma^2`, so the background
`Phi_joint,infinity=1+192sqrt(2)sigma^2` can be subtracted nonnegatively.
The same actual-vorticity continuation interface therefore applies once
its integrability, capacity and uniform physical-time allowance are supplied.
That allowance is not established here.

### Why the constant 192 preserves the physical source payment

For simultaneous increments `E_H,E_I,L` put

```text
E_B=E_H-E_I,       e=|E_H|^2+|E_I|^2,       g=|L|^2,
d=B_H:E_H+A:E_I,   ell=(P_hat:L)/q.
```

The radial curvature formula applies to the joint space:

```text
D2(Q^2)=8d^2+4Qe+8d ell+2g+(2R/q)(g-ell^2)
        >=2Qe+(2/5)g.
```

All increments vary together. The retained geometry obeys
`r_B=|B|^2<=2R`, `|E_B|^2<=2e`, hence `r_B|E_B|^2<=4Re`.
The original negative-part bounds for the actual B branches give

```text
D2 c0>=-(6976/21)Re,
D2 p0>=-(352R+16q)e-8g.
```

Adding `192D2(Q^2)` leaves, for either branch,

```text
D2 U,D2 V>=32Qe+(56/5)g,
D2 Psi_joint>=32Qe+(56/5)g>=8|B|^2|E_B|^2.
```

The radial norm's remaining curvature is its nonnegative square. This is
an analytic uniform mixed matrix estimate; Lean certifies the coefficient
combinations with their physical negative-part inputs explicit. Independent
exact matrix differentiation checks both retained increments and a
noncommuting pressure increment. It also checks the numerical value and
two derivatives against those independently differentiated expressions
when the impulse is nonzero. These tests do not assert that arbitrary
matrix pairs are attained by a fluid history.

`MettapediaNS.RetainedParentCompletion` additionally constructs the actual
impulse-gradient entries and joint parent sizes from whole-space smooth L2
fields. It proves the original velocity's parent-cost comparison and applies
the already certified pressure projection to its literal derivative-parent
source:

```text
nu ||grad q_G||_2^2<=integral D_Phi,joint/8,
G=(grad u)(grad u)^T.
```

The physical mixed-curvature lower bound and integrability of its constructed
diffusion remain explicit inputs to this kernel source consumer. No
weighted projection contraction is used. The flux matrix square is still
`|P+sI|^2=|P|^2+s^2<=Phi_joint`, with `s=tr(B^2)`.
Consequently the prior signed selected/unselected viscous absorption applies
to this joint completion with the same surviving quarter of total diffusion,
under the same weak chain-rule and integrability obligations.

At the original datum `B_H=B`, `A=0`, `C=0`, `P_hat=P`. The conservative
analytic bound

```text
0<=Phi_joint-Phi_joint,infinity
 <=1024(R^2+sigma R+|P_hat|^2+|P|^2)
```

gives a finite initial deposit for the same soft-excess correction:

```text
R_joint=integral[F_b(Phi_joint,h)+8(Phi_joint-Phi_joint,infinity)],
R_joint(0)<=24576 integral |grad u_0|^4
             +8192sigma integral |grad u_0|^2,
```

when b is fixed above the initial supremum and `h(0)=1`. This uses the
actual initial canonical Hessian comparison `integral|P|^2<=integral|B|^4`.
The physical initial bound is analytic, not kernel-certified assembly.

### Complete reaction and the remaining history estimate

Denote the derivatives of `Psi_joint` in its three independent slots by
`Psi_H`, `Psi_A`, `Psi_hat`. Retain the previous actual pressure reactions
`A_hat` and `A_p`, including transport commutators and all memory parents.
The full unforced nonlinear reaction is

```text
R_NL,joint=Psi_H:(-B_H B)+Psi_A:(P-AB)
           +Psi_hat:A_hat+2P:A_p.
```

The canonical explicit viscous pressure source remains unchanged. The
analytic assembled production inequality is therefore

```text
R_joint'+D_total,joint/4
 <= integral(a+8)R_NL,joint-C_capacity,joint.
```

At `A=0`, the radial part of `Psi_A` vanishes, so its direct pressure
injection is transferred. The derivative of the actual vorticity geometry
with respect to A is still present: differentiating B=B_H-A retains its
pressure leg. At later times the radial impulse-pressure term also returns.
The parent deformation is not cancelled, and the paid unweighted impulse
does not bound these weighted work terms automatically.

The sufficient missing estimate remains a finite original-datum payment
for every compatible unforced prefix:

```text
integral_0^tau [integral(a+8)R_NL,joint-C_capacity,joint]
 <= integral_0^tau D_total,joint/8+A(u_0,nu,H).
```

It is OPEN. Receiver responses and endpoints must keep the two coupled
parents, actual vorticity, pressure, memory and original label. No
Schrodinger-bridge optimizer or independently tunable fluid force is
identified with this completion.

For forced flow, `D A=P-grad f-AB`, while `D B_H=-B_H B`. The pressure
reactions also retain their force contributions. The finite force test
keeps these extra legs for fixed Eulerian `f=curl u_0`, with zero kinetic
work only initially. It is not the imported blowup construction or an
unforced internal realization.

### Reproducible tests

```sh
python3 -O labs/retained_parent_completion.py
python3 -O labs/retained_parent_completion.py --quadrature
```

The exact default checks retain all Fourier outputs, both velocity signs,
the actual passive/impulse gradient equations and the force impulse.
The quartic gradient reaction has parent contribution
`+162790222016/75150075` and pressure contribution
`-314203808/20495475` for one sign, with both signs reversed for the other.
These are reaction components, not the full viscous derivative or a
counterexample to a finite full-datum history allowance.

Optional independent spatial quadratures retain the complete initial
NS/pressure/memory generator, all joint slots and actual mixed diffusion.
Their threshold comes from the analytic Fourier bound above the initial
joint envelope, independently of the grid and unknown future. They test
the signed balance, actual derivative-parent payment and previous viscous
absorption. They do not construct a continuum trajectory or provide a
continuum enclosure. Finite bursts and changing geometry remain allowed.

At `nu=0.1`, the independent `96^3` and `128^3` checks use the same
datum-fixed threshold `b=94502831`; the sampled initial joint envelope
maximum is below `4.81e6`. For one sign the complete initial derivative
is approximately `+792957.81`, with nonlinear work `+5300633.63` and
total diffusion `4507675.81`. The opposite sign gives a negative initial
derivative. The initial soft selector is inactive, so the selected costs
vanish while the unselected correction retains the complete generator.

The largest scaled generator residual is `2.80e-9`, and the reported
independent comparisons agree within `2.09e-9`. Transferring the radial
pressure injection changes the derivative by `+45091.51` for the positive
production sign. Thus pressure transfer does not remove the initial parent
burst on this fixture. These are spatial numerical diagnostics, not a
continuum sign certificate or a counterexample to a finite full-datum
history allowance. The latter remains the open estimate.

## Covector-parent history and pressure-generated frame diffusion

The retained parents share the actual unforced NS drift:

```text
D=partial_t+u.grad-nu Delta,  B=grad u,
B_H=grad H, A=grad I, I=H-u,
D B_H=-B_H B, D A=P-AB, P=Hess p.
```

Their rows, viewed as columns, transport with deformation `-B^T`.
They are covectors. The forward frame used for vorticity is therefore not
automatically their correct metric. The existing `TransportedFrameMetric`
algebra can be reused with this covector deformation.

### The inverse-flow coframe and the paid original parent

On an existing compact smooth prefix, use the common translation-noise
stochastic flow with the actual drift. If J is its forward Jacobian,
evaluated at the corresponding inverse label, the two uncentered moments are

```text
M=E[J J^T],         D M=B M+M B^T,       M(0)=I,
N=E[J^-T J^-1],     D N=-B^T N-NB,      N(0)=I,
Q=N^-1,            N_j=partial_j N.
```

These moments belong to the same physical flow. They are not independently
selectable controls, and neither is the pressure-compensated velocity
covariance C of the earlier reserve. Their stochastic construction,
positivity and PDE identification remain analytic. Smooth-prefix bounds
justify the local operations; a future stretching modulus cannot serve as
an original-datum continuation bound.

For a literal parent gradient V with `DV=-VB+S`, the inverse identity is

```text
D tr(V Q V^T)=2tr(V Q S^T)-2nu F_V,
F_V=sum_j tr[(partial_j V-V Q N_j) Q
             (partial_j V-V Q N_j)^T]>=0.
```

All metric derivatives remain in the square. Consequently

```text
q_H=tr(B_H Q B_H^T),    D q_H=-2nu F_H,
q_I=tr(A Q A^T),        D q_I=2tr(A Q P^T)-2nu F_I.
```

Parabolic comparison on the smooth prefix gives
`q_H(t,x)<=sup_x |grad u_0(x)|^2`. Under the usual spatial integrability,
incompressibility gives the complete signed payment

```text
integral q_H(t)+2nu integral_0^t integral F_H
  =integral |grad u_0|^2.
```

The right side retains the ORIGINAL datum. A stochastic matrix
Cauchy--Schwarz gives the same directional comparison by retaining the
joint inverse label and gradient of the original velocity. The tensor and
PDE/time constructions and comparison are analytic, not kernel-certified
assembly. This normalized passive-parent payment also holds for a forced
drift; it does not by itself separate forced from unforced renewal.

`MettapediaNS.CovectorParentHistory` certifies the literal gradient of the
passive RHS, the original impulse's canonical-pressure rate, and the
inverse-metric production on those actual rows and their actual spatial
derivatives. Its sign theorem exposes the metric rate and compatibility
inputs. The ordinary-vorticity consumer keeps a conversion bound explicit;
that bound is not a conclusion of the metric identity.

The full joint production still contains `2tr(A Q P^T)`. The preceding
unweighted impulse payment `spent<=4E0` does not pay this changing
Hessian receiver automatically. The frame can also lose ordinary coercivity.
Neither weighted pressure history nor that physical conversion has a
uniform arbitrary-data bound here. Their coupled payment remains the
regularity obligation. An auxiliary stochastic optimizer is not identified
with a freely adjustable force on the fluid.

### Transfer of the Hessian receiver to the paid derivative square

Let `C_j=partial_j A-A Q N_j`. Differentiating the actual inverse metric
gives the exact spatial relation

```text
partial_j(AQ)=C_j Q,
R=div(AQ)=sum_j C_j Q e_j,
W=integral tr(A Q P^T)=-integral R.grad p.
```

The integration by parts uses the full canonical pressure force and the
same smooth-prefix integrability as the impulse equation. Every metric
derivative remains in R. Positivity of Q and completion of all squares give

```text
nu F_I+nu^-1 tr(Q)|g|^2-2 R.g
 =nu^-1 sum_j tr[(nu C_j-g e_j^T) Q (nu C_j-g e_j^T)^T]>=0.
```

Applying this to `g=-grad p` pays the changing receiver from diffusion:

```text
2W<=nu integral F_I+nu^-1 integral tr(Q)|grad p|^2,
(integral q_I)' +nu integral F_I
  <=nu^-1 integral tr(Q)|grad p|^2.
```

This is an analytic physical receiver-transfer estimate, with exact
matrix-derivative and evolving Fourier checks. It is not a kernel-certified
weak/PDE assembly. The remaining pressure-force cost is lower in spatial
derivative order than the Hessian receiver, but its finite history payment
from the original full datum is OPEN. The previously paid signed impulse
work does not bound it automatically. It cannot be supplied as an unknown
future-solution input to an arbitrary-data continuation proof.

### Why inversion cannot be performed after averaging

If one instead pairs the parent with the forward moment M, the exact
production is

```text
D tr(B_H M B_H^T)
 =-2nu sum_j tr(E_j M E_j^T)-4nu sum_j tr(B_H M_j E_j^T),
E_j=partial_j B_H, M_j=partial_j M.
```

Deformation cancels, but the second term has no fixed sign. For the
compatible actual moments the reciprocal gap is

```text
G=M-Q,
D G=B G+G B^T+2nu sum_j Q N_j Q N_j Q,   G(0)=0.
```

The source is nonnegative. A matrix comparison, or the shared-flow
second-moment construction, gives `G>=0`. Diffusion can make it nonzero:
M is not generally `N^-1`. Averaging and inversion cannot be interchanged
merely because every sample preserves volume. The analytic gap equation
retains this evolving covariance defect; it does not bound its size from
the original datum or supply the missing coercivity.

### An actual unforced pressure-generated short history

Choose a smooth compact radial swirl with a rigid core around zero,
`u_0=b(e_z cross x)` there, and a distant disjoint smooth compact radial
swirl centered at `L e_z`, with axis e_z and `E=integral |u_remote|^2>0`. Take b>0,
nu>0 and L large enough to separate the supports. Both fields are
solenoidal, finite-energy whole-space data. Their canonical pressures add
at time zero because their velocity supports are disjoint.

The central pressure is locally `b^2(2x^2+2y^2+z^2)/5`, up to a constant.
The remote pressure is the exact harmonic exterior quadrupole
`-E(3(z-L)^2-|x-L e_z|^2)/(8pi|x-L e_z|^5)`, as in the earlier pressure
boundary calculation. With `P_j=partial_j Hess p_0(0)` and
`c=15E/(2pi L^6)`, its complete third tensor is

```text
P_x=[[0,0,c],[0,0,0],[c,0,0]],
P_y=[[0,0,0],[0,0,c],[0,c,0]],
P_z=diag(c,c,-2c).
```

Start the actual local unforced NS solution, the original passive history
and both frames. Their initial data are flat in the core, and the complete
actual velocity tangent is `u_1=nu Delta u_0-B_0 u_0-grad p_0`.
Differentiating the passive equation retains this pressure-induced drift:

```text
partial_t grad H(0)=-B_0^2,
partial_tt grad H(0)=2B_0^3+B_0 Hess p_0,
E_j(t,0)=t^2 B_0 P_j/2+O(t^3),
M_j(t,0)=-t^2 P_j+O(t^3),
N_j(t,0)=+t^2 P_j+O(t^3).
```

Here `B_0=b spin_z` and `sum_j|B_0 P_j|^2=4b^2c^2`. The full production
formulas therefore give

```text
D tr(B_H M B_H^T)(t,0)=+6nu b^2c^2 t^4+O(t^5),
D q_H(t,0)           =-2nu b^2c^2 t^4+O(t^5),
tr[B_H(M-Q)B_H^T](t,0)=(8/5)nu b^2c^2 t^5+O(t^6).
```

Thus the proposed pointwise nonpositive forward-frame generator fails on
an ACTUAL unforced short history. The correct inverse covector square has
the proper sign. Smooth local realization and the Taylor remainder imply
some positive short interval; no numerical endpoint is certified. This is
an analytic counterexample with exact jet checks, not a Lean-certified
counterexample. It refutes only that forward-frame generator assertion,
not a finite full-datum history allowance, regularity, or the repaired
stochastic route. It shows a finite internal pressure effect; it does not
show that surrounding fluid can sustain a forced blowup indefinitely.

### Reproducible checks and the next history obligation

```sh
python3 -O labs/covector_parent_history.py
```

Independent rational differentiation of complete quadratic forms verifies
both metric generators, their spatial cross terms and the weighted impulse
source. The central/remote test independently differentiates the canonical
pressure and the full first NS and second passive/frame jets. A separate
rational 3D Fourier fixture retains every convolution output, the actual
second NS tangent and the third frame jets. The reciprocal gap has a
nonzero mean trace third jet `412168192/5780775`. No finite closed-mode
evolution, continuum numerical enclosure or arbitrary-history bound is
asserted by these checks.

The receiver transfer independently differentiates `A(x)N(x)^-1`, retains
all three Young squares, and checks integration by parts through two actual
unforced time jets. Both evolving canonical pressure and coframe derivatives
are retained. These verify the transfer on the tested jets; a full original
history payment for its remaining pressure-force cost is not asserted.

Next: retain the inverse-flow coframe, impulse, original gradient labels
and physical vorticity together when paying the weighted pressure response
and conversion. A decreasing normalized gradient or a nonnegative gap
does not supply that coupled finite-horizon payment. The original signed
renewal/continuation target remains open.

## Joint coframe pressure and the retained cross moment

The actual gradient is `B=B_H-A`, where `B_H=grad H` is the original
passive parent, `I=H-u` is the original pressure impulse and `A=grad I`.
Use the same inverse coframe as above, `Q=N^-1`, throughout the history.
Combining the parents before estimating their pressure work gives

```text
q_B=tr(B Q B^T)=q_H+q_I-2tr(B_H Q A^T),
Dq_B=-2tr(B Q P^T)-2nu F_B,
F_B=sum_l tr[(partial_l B-B Q N_l)Q
             (partial_l B-B Q N_l)^T]>=0.
```

The cross term retains the same canonical pressure and joint covariant
diffusion. This avoids introducing the separate impulse parent's
weighted force-square cost as a new payment at this stage. It does not
establish a history bound for the combined observable.

`MettapediaNS.JointCoframePressure` certifies actual gradient-square and
pressure-work reconstruction, the literal canonical NS gradient rate,
its supplied-metric production and actual-vorticity comparison with a
conversion input. The metric rate and derivatives are those of
`TransportedFrameMetric`; construction of N and the physical-time chain
rule remain analytic obligations. Neither N nor Q is a freely selectable
control. The exact local derivative test independently differentiates
`tr(B N^-1 B^T)`, retaining all first and second spatial derivatives of
B and N. The diffusion cost is `40697/512`, pressure work is `-25/4`,
and full generator is `-8697/2560` in that rational fixture. These
matrices test the algebra, not a constructed fluid trajectory.

### The actual pressure cancels for every constant metric

Let `g=grad p`, with the canonical pressure of the full smooth solenoidal
velocity. Its Hessian `P` is symmetric. With `B_ik=partial_k u_i`, put

```text
Z_i=sum_kj B_ik Q_kj g_j,
C=sum_ikj B_ik (partial_i Q_kj) g_j.
```

Solenoidality gives `sum_i partial_i B_ik=0`. Consequently

```text
div Z=tr(B Q P^T)+C,
W_B=integral tr(B Q P^T)=-integral C.
```

Every anisotropic constant matrix cancels: `partial_i Q=0` implies
`W_B=0` without positivity, isotropy or a smallness assumption. The
certified whole-space class is `Q=Q0+w`, where Q0 is constant and every
entry of w is a smooth scalar field with all L² jets. Integrability
follows from smooth field products. Integration by parts uses the
pressure gradient, so the scalar potential need not belong to L².
Applying this class to the evolving stochastic coframe requires its
field regularity identification. The torus checker independently
verifies the full flux divergence.

Under a compatible smooth time realization and the requisite spatial
integrability, the integrated balance is therefore

```text
integral q_B(t)+2nu integral_0^t integral F_B
  =integral |grad u0|^2+2 integral_0^t integral C.
```

This time balance is analytic; the spatial cancellation and algebraic
generator are kernel-certified. A finite signed allowance for C must
come from the original full datum, viscosity and horizon. The initial
label, both parents and the metric cannot be reset at a later seam.
A bounded q_B also needs quantitative conversion in physical gradient
or vorticity directions to control an ordinary continuation criterion.
Both coupled obligations remain open.

A forced gradient equation additionally contains `grad f`; its metric
production contains `2tr(B Q (grad f)^T)`. Zero instantaneous kinetic
work does not remove this term. An internal region must retain its
surrounding fluid and compatibility, rather than treating an effective
force as an independent prescribed control. This cancellation neither
embeds the imported forced singularity into an unforced flow nor proves
that its organization cannot recur internally.

### Complete unforced jets reject a universal pressure sign

```sh
python3 -O labs/joint_coframe_pressure.py
```

The Gaussian-rational Fourier test uses the existing genuinely 3D
`interacting_datum()` on the `2*pi` torus, with `nu=1/10`. Every
convolution output is retained. Reported spatial integrals in this test
are normalized torus means. Both unforced NS tangents are solenoidal;
the canonical pressure is retained through second order. Initial
`N(0)=Q(0)=I`; both coframe jets use the full same actual drift:

```text
Q_t(0)=B+B^T=S, N_t(0)=-S,
N_tt(0)=nu Delta N_t-u.grad N_t-B_t^T-B_t
        -B^T N_t-N_t B,
Q_tt(0)=-N_tt+2N_t^2.
```

The integrated pressure jets are

```text
W_B(0)=0,
W_B'(0)=-156013232/10405395 <0,
W_B''(0)=416637952/52026975.
```

Independent commutator contractions agree with both time derivatives.
B_t, B_tt, P_t and P_tt remain in the pointwise work. Constant metric
cancellation removes their relevant integrated contributions. A spatial
test metric `I+S/100` has coefficient-certified lower eigenvalue
`181523/250250` and pressure work `-39003308/260134875`; that metric
is not asserted to occur at a finite time in the actual history.

The actual time test retains the complete pointwise generator and its
first derivative, including drift_t, viscosity and every metric
derivative. Initial integrated total production is
`-103042048/5780775`, with covariant diffusion `103042048/1156155`.
Its second derivative is `13618068064/260134875`; this does not certify
a positive-production time window. Both parent squares and their cross
moment reconstruct the actual square at all three tested time orders.

On a smooth local NS/coframe realization the strict negative pressure
derivative implies W_B<0 on some short interval despite positive
viscosity. This rejects only `W_B>=0` for every actual history. Smooth
coframe construction and the Taylor argument are analytic here; no
numerical endpoint or closed finite-mode evolution is certified. The
test does not refute a finite signed full-datum payment, complete metric-
production monotonicity or unforced regularity.

Next: pay the evolving signed commutator and physical conversion
together from original resources. A one-signed pressure rule and a
separately estimated impulse force square do not supply that theorem.

### Nonnegative pressure-endpoint completion

The signed commutator receiver is
`T_j=sum_i partial_i(BQ)_ij=sum_ik B_ik partial_i Q_kj`.
Since `D I=grad p`, the actual compatible history satisfies, under its
spatial/time regularity and integrability,

```text
integral_0^t integral C
  =integral T(t).I(t)-integral T(0).I(0)
   -integral_0^t integral I.(partial_t+u.grad+nu Delta)T.
```

The PLUS sign on adjoint diffusion and both endpoints are essential.
This analytic transfer gives a receiver, not a finite payment. With
`J=integral T.I`, spatial integration by parts gives
`J=-integral tr(B Q A)`. The transpose in this contraction differs
from the original parent cross moment. For positive symmetric Q,

```text
Z=B+A^T=B_H+A^T-A,
integral tr(ZQZ^T)=integral q_B-2J+integral tr(A^T Q A)>=0.
```

The added transposed-gradient square is not the already paid original
parent channel, or the impulse's unweighted energy. Its payment cannot
be assumed. This concrete nonnegative correction cancels the explicit
Hessian because P is symmetric, but leaves a complete source:

```text
D Z=-B^2-B^T A^T=-Z B+S,
S=A^T B-B^T A^T,
Dtr(ZQZ^T)=2tr(ZQ S^T)-2nu F_Z,
2(B-B^T)=(B_H-B_H^T)+(Z-Z^T).
```

`MettapediaNS.JointCoframeCompletion` certifies the literal retained-
parent rate, nonnegative square and diffusion, the full supplied-metric
production, and reconstruction of the actual antisymmetric gradient.
Construction of the coframe and physical-time comparison remain
analytic. Ordinary antisymmetric reconstruction does not provide
coercivity of an anisotropic metric; that physical conversion still
needs a bound.

```sh
python3 -O labs/joint_coframe_completion.py
```

The complete unforced time test retains both original parents, pressure,
the same coframe, all convolution outputs and full diffusion. Its first
two completed-gradient rate jets cancel the canonical Hessian exactly.
The full metric generator and its first time derivative, nonnegative
completion and actual antisymmetric reconstruction agree pointwise.
Independent endpoint/adjoint contractions retain the plus diffusion.
Spatial means are normalized on the `2*pi` torus.

Initially the source is zero, but the same genuine 3D datum at nu=1/10
has source derivative `S_t=P B-B^T P`, which is antisymmetric, and

```text
(mean tr(ZQ S^T))'(0)=296646304/10405395 >0,
(mean tr(ZQZ^T))'(0)=-103042048/5780775 <0,
(mean tr(ZQZ^T))''(0)=144403648/1819125.
```

Under analytic smooth short-prefix realization, the strict positive
first source-work jet rejects a universal nonpositive source-work rule.
The complete initial production remains dissipative; no positive total-
production interval, recurrent growth, arbitrary-history bound or
regularity refutation is asserted. Cancelling pressure moves its effect
into the original impulse's changing deformation. That retained source
and physical metric conversion are the next coupled history obligations.

For forcing, `D I=grad p-f` gives the additional source
`grad f-(grad f)^T` in the completed gradient. It is exactly the
rotational force gradient; a pressure-gradient force cancels here.
The checker retains a fixed solenoidal force
`f=-Delta u0-alpha u0`, with `alpha=mean|grad u0|^2/mean|u0|^2`.
Its initial kinetic work is zero while its completed rotational work
is strictly positive. The full initial velocity/impulse generator
retains that term. This is a local forced filter, not the imported
singular construction or a zero-work assertion for later times.

### Actual covector reconstruction and the retained curl

The velocity covector formulation is the
[Constantin--Iyer stochastic representation](https://arxiv.org/abs/math/0511067),
Theorem 2.2 and equation (4.5). It is an identification on a smooth solution
interval, not an arbitrary-data global existence theorem. For
`D=partial_t+u.grad-nu Delta`, `B=grad u`, and the actual Helmholtz
projection P, retain the original canonical covector:

```text
D m=-B^T m,       m(0)=u_0,       u=P m.
```

If gamma=m-u is a smooth gradient, its full Lie transport satisfies
`(u.grad)gamma+B^T gamma=grad(u.gamma)`. Also
`B^T u=grad(|u|^2/2)`. Projecting the COMPLETE covector equation
therefore gives exactly the unforced Navier--Stokes equation. Curl m is
the actual fluid vorticity. `MettapediaNS.CovectorFluidBridge` certifies
both statements on literal whole-space smooth L² fields, with the actual
projection rather than an abstract observation map. The stochastic
construction and identification of its smooth time paths remain analytic.

For the SAME translation-noise flow X, inverse label A=X^-1, F=grad A,
the analytic representation has `m=E[F^T u_0(A)]` and `N=E[F^T F]`.
Incompressibility preserves volume for each noise realization. With
`Q=N^-1`, `N(0)=I`, and `K_j=(partial_j N)Q`, the complete generator is

```text
D(m^T Q m)=-2nu F_m,
F_m=sum_j r_j^T Q r_j >=0,     r_j=partial_j m-K_j m.
```

This uses the full inverse differentiation, including every spatial
metric derivative. Under the smooth stochastic/time realization, spatial
comparison yields
`integral m(t)^T Q(t)m(t)+2nu integral_0^t integral F_m <= ||u_0||_2^2`.
Weighted Cauchy--Schwarz also gives
`m^T Q m <= E[|u_0(A)|^2]` pointwise. These are analytic payments for
the normalized covector, not bounds on the ordinary curl. Lean certifies
the literal material covector rate, full supplied-metric production,
nonnegative square/cost and initial identity. It does not construct Q or
prove the physical-time comparison.

The curl conversion retains the connection:

```text
omega_i=r_(i+1),(i+2)-r_(i+2),(i+1)+C_i,
C_i=(K_(i+1)m)_(i+2)-(K_(i+2)m)_(i+1).
```

Indices are cyclic. Lean certifies this actual-vorticity decomposition and,
if `b>=0` and `b |r_j|^2<=r_j^T Q r_j` for every j, the pointwise bound
`b |omega|^2<=4 F_m+2b |C|^2`. Useful physical coercivity requires b>0.
Neither that lower bound nor a payment for C is provided by the normalized
energy inequality. Even finite spacetime L² vorticity alone would not
give the required continuation criterion. Bounds must have the necessary
spatial strength and remain finite on every prescribed finite horizon
from the full original datum.

```sh
python3 -O labs/covector_fluid_bridge.py
```

The exact checker retains all Fourier convolution outputs on the `2*pi`
torus, canonical pressure, original m(0)=u_0, the same coframe and complete
unforced first/second time derivatives. Projection and actual curl agree
at all three tested orders; the full metric generator and its first
time derivative retain drift_t and every diffusion/connection term.
These are initial derivatives of the full PDE, not a closed Galerkin
evolution or a uniform Taylor window.

For the three-dimensional datum at nu=1/10,

```text
(mean m^T Q m)'(0)=-31905344/5780775 <0,
(mean m^T Q m)''(0)=171344128/28903875,
C(0)=0,       C'(0)=-(u_0.grad)omega_0,
mean |C'(0)|^2=183108608/3468465 >0,
W(0)=W'(0)=0,       W''(0)=64/33 >0,
W(t)=mean omega(t).C(t).
```

The first connection curl is transport and has zero integrated signed
vorticity work. Its next COMPLETE derivative has positive work. Under
analytic smooth short-prefix realization this excludes a universally
zero or nonpositive W. It does not assert positive total covector
production, indefinitely renewed stretching, failure of a finite
full-datum history payment, or unforced singularity.

A nonzero retained gradient difference preserves the projected RHS and
curl but changes the covector energy. Thus projection equality cannot
authorize a reset of the canonical original-data reserve. An auxiliary
gradient source projects to zero. A physical solenoidal force survives
in the reconstructed equation and its curl. The checker tests these
filters with an explicit initial source; it does not realize or exclude
an imported singular trajectory inside unforced fluid. A freely chosen
auxiliary control is not a physical fluid force, and no Schrodinger
optimizer or Bellman certificate for the unbounded curl history is
identified here.

The next physical obligation is joint original-datum control of the
changing-frame curl and its conversion to a sufficient continuation
norm, retaining compatible parents, phases, pressure, geometry and
viscosity. The pressure/strain/vorticity completion above remains a
parallel route to that same history bound.

### Joint original-parent variance and the geometric source

The same stochastic flow used in the
[Constantin--Iyer representation](https://arxiv.org/abs/math/0511067)
retains more information than its separate averaged moments. Write
`F=grad A`, `J=F^-1`, `v=u_0(A)`, and use one joint realization:

```text
m=E[F^T v],   N=E[F^T F],   Q=N^-1,   a=Qm,
g=E[Jv],      M=E[J J^T],   h=E|v|^2.
```

Here a is an auxiliary normalized vector; it is not the incompressible
fluid velocity. The original forward parent g obeys Lie transport by the
actual fluid drift, with viscosity:

```text
D g=B g,      g(0)=u_0,      div g=0,
D=partial_t+u.grad-nu Delta, B=grad u.
```

`MettapediaNS.CovectorJointParent` certifies the literal whole-space
smooth-field RHS `nu Delta g-(u.grad)g+(g.grad)u` and its membership in
the solenoidal space when u and g are solenoidal. Constructing g's smooth
stochastic time path and proving its time-dependent identification remain
analytic. The finite joint sample structure below does not assert that
arbitrary supplied frames arise from a fluid flow.

Retaining each inverse frame with its own original parent gives

```text
V=h-m^T Qm=E|v-Fa|^2,       0<=V<=h,
g-a=E[J(v-Fa)],
|z.(g-a)|^2 <= V (z^T M z),
 2 z.(g-a) <= V+z^T M z,
-2 z.(g-a) <= V+z^T M z.
```

Lean certifies the exact finite normalized-law statements for every
receiver z, with `Na=m` for the energy-deficit identification. The
full signed completion is `E|v-Fa-t J^T z|^2>=0` for every real t.
This preserves joint frame/parent choices rather than matching independent
summaries. Under the smooth continuous stochastic realization,
`D h=0`, `D V=2nu F_m`, and spatial volume preservation gives
`integral V=||u_0||_2^2-integral m^T Qm<=||u_0||_2^2`.
Thus the integrated variance on a prescribed horizon H is at most
`H ||u_0||_2^2`. These time and spatial passages are analytic here;
the forward receiver cost is not paid by this inequality.

The complete normalized-parent and connection equations retain diffusion:

```text
K_j=(partial_j N)Q,        r_j=partial_j m-K_j m,
D a=B a+2nu sum_k K_k^T partial_k a,
D(a-g)=B(a-g)+2nu sum_k K_k^T partial_k a,
D K_j=[K_j,B^T]-partial_j B^T-N(partial_j B)Q
       -sum_k B_kj K_k+2nu sum_k (partial_k K_j)K_k,
D r_j=-B^T r_j-sum_k B_kj r_k+N(partial_j B)a
       +2nu sum_k (partial_k K_j)r_k.
```

The source `N(partial_j B)a` has a concrete joint receiver when tested
in the inverse-frame metric. With
`z=sum_j (partial_j B)^T r_j`, Lean proves

```text
2 sum_j r_j.(partial_j B)a
 <= 2 sum_j r_j.(partial_j B)g+V+z^T M z.
```

One variance payment transfers the entire combined source. The retained
parent work and the receiver cost remain. For clarity, the full analytic
covariant-gradient production is

```text
D F_m = -2 sum_jk B_kj r_j^T Q r_k
        +2 sum_j r_j.(partial_j B)a
        +4nu sum_jk r_j^T Q (partial_k K_j)r_k
        -2nu sum_jk |partial_k r_j-K_k r_j|_Q^2.
```

The source transfer alone does not bound the other terms, physical metric
coercivity, changing-frame curl, or a continuation norm. A joint allowance
for these actual evolving geometric quantities is still required.

```sh
python3 -O labs/covector_joint_parent.py
```

The exact checker uses three separate tests. The full Fourier test retains
all convolution outputs, canonical pressure, original initial velocity,
and first/second unforced PDE derivatives on the `2*pi` torus. At nu=1/10,

```text
a'(0)=g'(0)=nu Delta u_0,
div g'(0)=div g''(0)=0,
mean|div a''(0)|^2=5019506670815216/11139119866875 >0,
a''(0)-g''(0)=2nu sum_k K_k'(0)^T partial_k u_0,
mean|a''(0)-g''(0)|^2=1274001115178936/33417359600625.
```

These complete initial derivatives refute the claim that moment
normalization always yields an incompressible parent, conditional on
smooth short-prefix realization. They do not refute physical
incompressibility, a full-datum history allowance, or regularity.
No uniform Taylor window is asserted.

A second test exercises nonzero mixed diffusion with noncommuting rational
matrix jets. It checks every term of the displayed K, a and r equations,
including the combined source receiver. These supplied local jets are
algebra fixtures, not a stochastic fluid realization. A third test uses a
normalized finite law with determinant-one frames and joint original
terminal vectors. Its variance equals the energy deficit, every tested
completion is nonnegative, and the geometric-source transfer holds.
Permuting only the terminal parents changes the covector; shared choices
are necessary for reconstruction. Lean proves the finite-law inequalities
universally, while the script checks these particular fixtures.

For a physical force f the complete covector equation adds f, the
normalized-parent equation adds Qf, and the original h deficit has
`D(h-m^T Qm)=2nu F_m-2m^T Qf`. That deficit is no longer the nonnegative
original-parent variance unless the changed stochastic source is retained.
The forced representation includes the accumulated pulled-back force
(Constantin--Iyer, Remark 2.4). The checker retains a fixed solenoidal
initial source with zero initial kinetic work; this is neither the
imported singular trajectory nor a zero-work assertion at later times.
No auxiliary stochastic control is treated as a free physical force.

### Actual receiver cancellation and signed area memory

The receiver of the complete covariant-gradient source is
`z=sum_j (partial_j B)^T r_j`, with `B=grad u` and
`r_j=partial_j m-K_j m`. Split it using the current actual velocity:

```text
E_j=r_j-partial_j u,
z=grad(|B|^2/2)+sum_j (partial_j B)^T E_j,
P_sol z=P_sol sum_j (partial_j B)^T E_j,
integral z.g=integral [sum_j (partial_j B)^T E_j].g   (div g=0).
```

`MettapediaNS.CovectorReceiverGeometry` proves the literal whole-space
smooth-field receiver identity, decomposition, gradient membership,
Helmholtz projection equality and integrated parent-work equality.
These statements hold for every current smooth velocity and retained
gradient columns, not just at the original time. Constructing their
stochastic paths and paying the evolving defect are separate obligations.
In particular the auxiliary a=N^-1m need not be solenoidal, so this
parent-work cancellation does not authorize dropping the gradient part
from the full variance transfer or from its M-weighted receiver cost.

The original passive parent supplies a compatible pressure completion.
Let R have columns r_j, `B_H=grad H`, `D H=0`, and `H(0)=u_0`.
Then, with every connection term retained,

```text
D R=-B^T R-RB+S,
S_j=N(partial_j B)a+2nu sum_k (partial_k K_j)r_k,
D B=-B^2-P,                    P=Hess p,
D E=-B^T E-EB+P-B^T B+S,        E=R-B,
A=grad(H-u),                   D A=P-AB,
Y=E-A=R-B_H,                   Y(0)=0,
D Y=-B^T Y-YB-B^T B_H+S.
```

The explicit pressure Hessian cancels in Y without selecting a new
pressure or restarting H. Lean proves the actual-field reconstruction
`E=grad(H-u)+Y` and the supplied full matrix-rate identity. The continuum
R equation, parabolic comparison and original-data payment of the
remaining terms are analytic/open. The original B_H channel has the
earlier inverse-coframe gradient payment; its coupling with Y and S
still requires an estimate. Cancellation alone is not a continuation
bound, and a future-solution norm is not an initial allowance.

The forward receiver metric must also retain its joint area covariance.
For the same determinant-one inverse-flow samples `F=grad A`, `J=F^-1`,

```text
G=F^T F,       J J^T=adj(G),
N=E[G],        M=E[adj(G)],
Gamma=M-adj(N),                 Gamma(0)=0,
D N=-B^T N-NB,                  D M=BM+MB^T,
D adj(N)=B adj(N)+adj(N) B^T-2nu sum_k adj(partial_k N),
D Gamma=B Gamma+Gamma B^T+2nu sum_k adj(partial_k N).
```

Here adj is the three-dimensional adjugate. Lean proves the finite
determinant-one sample identity for the existing joint law and the
algebraic strain/area-defect rates. The parabolic chain rule, stochastic
identification and history payment are analytic here. Even with
incompressibility, adjugation cannot be commuted through expectation.
The signed source is a genuine term, not a positive scalar variance or
an automatically dissipative correction.

```sh
python3 -O labs/covector_receiver_geometry.py
```

The checker uses full Gaussian-rational convolution without truncation
on the `2*pi` torus. It computes physical u through its second canonical
time derivative, m through second order and N/M through third order,
including pressure, time-dependent drift and all mixed connection
diffusion. It independently checks the complete first derivative of
both E and Y equations above. At nu=1/10,

```text
mean z(0).g(0)=0,
(mean z.g)'(0)=183108608/3468465 >0,
mean|P_sol z'(0)|^2=1075568653965170009072/408005910307870875 >0,
Gamma(0)=Gamma'(0)=Gamma''(0)=0,
Gamma'''(0)=4nu sum_k adj(partial_k N'(0)),
Gamma'''_00(0,0)=6494816/9316125 >0.
```

The mean trace of the last tensor is negative
`-206084096/5780775`, while its displayed direction is positive. An
averaged trace does not control every receiver direction. The nonzero
projected receiver derivative excludes the persistent-zero shortcut,
conditional on smooth short-prefix realization. It does not refute a
finite original-data allowance. A separate noncommuting local matrix
fixture checks the full parabolic adjugate rule with nonzero spatial
diffusion; those supplied jets are not asserted to be a fluid flow.

There is also an analytic whole-space obstruction to the cofactor
comparison in the actual full receiver direction. Take the local core

```text
u_q=(xz,yz,(x^2+y^2)/2-z^2),
u_l=(-y,x,0),                    u_core=u_q+u_l,
A_core=-x cross u_q/4-x cross u_l/3,
u_0=curl(chi A_core),            chi=1 on |x|<=2, chi=0 on |x|>=3.
```

The homogeneous vector-potential identity `curl A_core=u_core` is
checked exactly. A smooth cutoff makes u_0 compactly supported,
divergence-free and finite-energy, with all derivatives in L²; the
existing local existence theory supplies an actual unforced prefix.
The cutoff and this time passage are analytic, not constructed by the
checker. At the interior point x_*=(0,0,-1), nu=1/10,

```text
omega_0=(0,0,2),      omega_0.B_0 omega_0=8,
z_0=grad(|B_0|^2/2)=(0,0,-6),
Gamma'''(0,x_*)=(8/5)diag(-3,-3,1),
z_0^T Gamma'''(0,x_*) z_0=288/5,
z(t,x_*)^T Gamma(t,x_*) z(t,x_*)=(48/5)t^3+O(t^4)>0
```

for some short positive interval. The same positive direction is the
nonzero initial vorticity direction. The leading coefficient depends
only on the local original strain derivatives: the changing canonical
pressure/drift cancels from Gamma's first three time jets. Thus the
localized datum, not an infinite-energy affine flow, rejects
`M<=adj(N)`, including the full receiver-cost comparison
`z^T M z<=z^T adj(N)z`. This is the unprojected receiver used by the
joint variance transfer; no failure in a projected receiver direction
is inferred. No explicit uniform Taylor endpoint is claimed.
This excludes a particular pointwise comparison, not a signed history
payment, indefinite renewal or global regularity.

The checker finally retains an initial physical solenoidal force f
with zero initial kinetic work. Its first gradients cancel in
`E=R-B` but survive as `grad f` in `Y=R-grad H`, because H retains
the original passive datum. This is an initial source filter, not the
imported forced singular trajectory, its internal realization, or a
claim of zero force work at later times. No stochastic control is
treated as a free physical force.

The next estimate must jointly pay the original parent work,
receiver-gradient defect, signed area covariance and remaining complete
gradient production, with metric/curl conversion in a norm sufficient
for continuation. Every allowed constant must come from the full
initial datum, viscosity and prescribed horizon.

### Joint two-index metric and original-gradient payment

The two indices of the completed receiver Y must retain their common
stochastic path. A more direct packet also transports the original
velocity gradient. The starting representation is the
[Constantin--Iyer stochastic Weber formula](https://www.math.cmu.edu/~gautam/research/papers/200511-detsns.pdf),
Theorem 2.2; its forced extension is Remark 2.4. The tensor and metric
calculations below are consequences on a smooth prefix, not a global
existence conclusion from the representation theorem.

Write `D=partial_t+u.grad-nu Delta`, `B=grad u`, `alpha=X^-1`, and
`F=grad alpha`. Each inverse-flow path starts at the same original datum.
Let `G=F^T F`, `N=E G`, `J=F^-1`, and `M=E[J J^T]`. Vectorize 3-by-3
matrices by their row indices. The joint two-index frame and moment are

```text
Phi=F tensor F,                 C=E[Phi^T Phi]=E[G tensor G],
L=-B^T tensor I-I tensor B^T,   D C=L C+C L^T,
W=C^-1,                        K2_k=(partial_k C)W,
partial_k W=-W K2_k,
D W=-W L-L^T W-2nu sum_k K2_k^T W K2_k.
```

`MettapediaNS.JointReceiverTensor` proves the finite same-sample joint
Gram identity, positive definiteness from the normalized law and its
invertible frames, and the exact tensor strain/production algebra.
Positive definiteness gives an inverse at that state; it gives no
uniform lower eigenvalue over unknown future histories.

For the original-gradient packet, retain all label information:

```text
A=E[F^T (grad u_0)(alpha) F],        A(0)=grad u_0,
D A=-B^T A-AB,
q_A=vec(A)^T W vec(A),
F_A=sum_k |vec(partial_k A)-K2_k vec(A)|_W^2,
D q_A=-2nu F_A.
```

The finite original-label variance proves

```text
a=W vec(A),
E|vec(grad u_0(alpha))-Phi a|^2
    = E|grad u_0(alpha)|_F^2-q_A >=0.
```

The normalized finite law, actual joint inverse, variance expansion and
bound are kernel-certified. Under the continuous construction, volume
preservation and the scalar transport equation give

```text
h_grad=E|grad u_0(alpha)|_F^2,       D h_grad=0,
0<=q_A<=h_grad,
integral q_A(t)+2nu integral_0^t integral F_A
    <= ||grad u_0||_2^2.
```

The last statement uses the full continuum construction and spatial/time
comparison on a smooth prefix; it remains analytic. Its resource is the
original gradient energy, not an energy-only allowance or the current
state's freshly assigned gradient energy. Every continuation retains
the original paths. No Schrödinger-bridge optimizer is identified here.

This packet has a direct physical curl. Differentiating the actual
covector `m=E[F^T u_0(alpha)]` gives

```text
grad m=A+E[sum_a u_0,a(alpha) Hess(alpha_a)].
```

The second tensor is symmetric. With `u=P_sol m`, its antisymmetric
part therefore reconstructs actual vorticity exactly:

```text
omega_i=A_(i+2,i+1)-A_(i+1,i+2),
|omega|^2<=2|A|_F^2.
```

Lean proves that reconstruction for literal whole-space smooth fields,
with the gradient projection difference and curvature symmetry stated
explicitly. It also certifies a pointwise conversion whenever
`b|A|_F^2<=q_A`, with `b>=0`. Deriving the continuum curvature identity
and controlling the changing geometry over arbitrary histories are
separate obligations. In this representation there is no separate curl
of a moment connection; the earlier regression representation still has
its correctly retained connection curl.

A sufficient next physical theorem is a bound
`|omega|^2<=K(u_0,nu,H) q_A` on all smooth prefixes of a fixed horizon,
or a weaker spatial estimate giving the same bounded enstrophy. It need
only control the actual packet's curl channel; bounding every direction
of the nine-dimensional metric would be stronger. With the analytic
original-gradient payment, this would feed the established whole-space
enstrophy continuation theorem. No such full-datum geometric bound is
proved. The periodic continuation application and stochastic passage
also retain their separate formalization obligations.

The generated receiver Y is a different tensor. With the original
passive H and the complete Hessian/connection source S,

```text
Y=R-grad H,                 Y(0)=0,
T_Y=S-B^T grad H,
D Y=-B^T Y-YB+T_Y,
q_Y=vec(Y)^T W vec(Y),
D q_Y=2 vec(Y)^T W vec(T_Y)-2nu F_Y.
```

The same lift certifies this complete supplied-rate identity. An
unforced fluid generally has `T_Y!=0`; transporting original A does not
erase Y's internal source. Coupled physical pressure/receiver estimates
may still need its signed history payment.

The common path is essential. For any skew matrix `[v]_cross`,

```text
vec([v]_cross)^T C vec([v]_cross)=2v^T Mv.
```

This finite area-channel identity is kernel-certified. Replacing C by
`N tensor N` loses the signed area covariance. More directly, with
`Q=N^-1` and `K_k=(partial_k N)Q`, the complete parabolic rate of the
independent product `Q tensor Q` contains the extra term

```text
2nu sum_k (QK_k tensor QK_k).
```

Its contribution to tensor production has no universal sign. Rational
supplied matrices give `841/1280>0` and `-447/5120<0`. For the actual
compactly localizable core
`u=(xz-y,x+yz,(x^2+y^2)/2-z^2)` at `(0,0,-1)` and `nu=1/10`, the
completed receiver has `Y'(0)=diag(-3,-3,-2)`. Its extra independent
metric production is `(232/5)t^4+O(t^5)`, and its independent-minus-joint
normalized square is `(232/15)t^5+O(t^6)`. Localization and the smooth
positive-time/Taylor passage are analytic. This rejects dropping the
signed cross diffusion; it refutes neither joint production nor a full
original-datum history bound.

```sh
python3 -O labs/joint_receiver_tensor.py
```

The checker retains all Gaussian-rational Fourier outputs on the
`2*pi` torus, canonical pressure and the changing NS drift. It checks
original A, m, curvature symmetry and actual curl through second order;
the complete original normalized diffusion law through its first time
variation; generated Y's complete source and production; and all 81
entries of the joint-moment gap through third order. In particular,

```text
C-N tensor N has zero first and second jets,
(C-N tensor N)'''(0)=4nu sum_k N'(0)_k tensor N'(0)_k,
mean q_A(0)=31905344/1156155,
(mean q_A)'(0)=-103042048/5780775,
mean F_A(0)=103042048/1156155,              nu=1/10.
```

The nine tensor coordinates are all retained in the diffusion residual.
A finite noncommuting determinant-one sample law independently checks
original-label variance, the joint inverse, full spatial connections
and both index-strain cancellations.

Finally, a fixed solenoidal forcing filter has zero initial kinetic
work but positive curl/gradient square. It contributes `grad f` to
Y's source and `curl f` to physical vorticity, absent from original A.
The forced stochastic representation needs the accumulated pulled-back
force and its extra gradient packet. Thus the original-label payment
cannot be applied to the forced solution's full curl without that cost.
This filter is an initial-time test, not the imported singular trajectory
and not a claim of zero forcing work at later times.

### Physical curl and a paid triangular parent history

The common original-gradient packet above retains actual curl. Its
physical conversion can use just the area cost in that direction. Write
`omega=curl A`, `q_A=vec(A)^T C^-1 vec(A)` and `M=E[J J^T]`.
For each direction z, pairing curl against z is precisely pairing A
against the skew matrix `[z]_cross`. Cauchy in the retained joint metric,
together with `vec([z]_cross)^T C vec([z]_cross)=2z^T Mz`, gives

```text
(z.omega)^2<=2q_A z^T Mz,
|omega|^4<=2q_A omega^T M omega.
```

`MettapediaNS.JointCurlGeometry` certifies these finite-law estimates,
including a literal whole-space smooth-field curl consumer with the
projection difference and curvature symmetry explicit. If the same
retained law has `omega^T Momega<=kappa |omega|^2`, kappa>=0, Lean
proves `|omega|^2<=2kappa q_A`. At zero curl the inequality holds
without division. The argument does not require a lower eigenvalue
bound in every direction of the nine-dimensional joint tensor.

For a velocity tangent to a fixed plane and independent of its normal
coordinate, every frame preserves a common planar normal n.
If curl is parallel to n, then `J^T omega=omega` on every path and
the normal cost is exactly `|omega|^2`. The certified invariant-direction
conversion gives `|omega|^2<=2q_A`. This allows arbitrary deformation
inside the plane. This physical illustration applies to the periodic
planar class or a genuinely two-dimensional problem: nonzero
z-independent fields are not finite-energy velocities on R3.

The class in [the stochastic parent-history calculation](#actual-ns-with-a-bounded-stochastic-parent-history)
provides a three-component positive consumer with actual stretching.
For period 2pi and normalized periodic volume, a,b>=0 and nu>0, let

```text
u=(a exp(-nu t)sin y,0,v(x,y,t)),      p=0,
v_t+a exp(-nu t)sin(y)v_x=nu(v_xx+v_yy),    v(0)=b sin x.
```

This is the literal unforced NS equation. The horizontal heat parent
decays autonomously; the vertical component is globally supplied by
the smooth linear parabolic subsystem. The already identified
stochastic phase formula gives, with q=exp(-nu t),

```text
|partial_y u_1|<=a q,
|v_x|<=b q,
|v_y|<=ab q(1-q)/nu.
```

Common translation noise has no spatial Jacobian. Along each original
stochastic path the forward frame satisfies `J'=B J`, `J(0)=I`, with
`B=grad u`. Its complete solution has the form

```text
J=[[1,beta,0],[0,1,0],[gamma,delta,1]],
beta'=partial_y u_1,
gamma'=v_x,
delta'=v_x beta+v_y.
```

The derivative bounds hold uniformly over space and thus along every
original path. Integration gives

```text
|beta(t)|<=a(1-q)/nu,
|gamma(t)|<=b(1-q)/nu,
|delta(t)|<=ab(1-q)^2/nu^2.
```

Both terms in delta' are counted. Its comparison envelope has derivative
`2ab q(1-q)/nu`, the sum of their full envelopes; none is discarded
as transport. With r=a/nu, s=b/nu, this yields

```text
tr(JJ^T)<=kappa=3+r^2+s^2+r^2s^2,
z^T Mz=E|J^T z|^2<=kappa |z|^2,
|omega|^2<=2kappa q_A,
sup_t integral |omega(t)|^2<=2kappa ||grad u_0||_2^2.
```

Here the initial normalized gradient energy is `(a^2+b^2)/2`.
The certified finite frame-square/triangular algebra supplies the
conversion. Stochastic construction, comparison, continuous original
payment and the spatial/time argument remain analytic. This is an
all-time full-datum allowance for this actual class, not an arbitrary
3D continuation theorem. Genuine stretching is present:
`omega^T S omega=-(partial_y u_1)v_x v_y`, where S is symmetric strain.
The important restriction is the absence of vertical feedback into
the horizontal parent. Original labels and paths are never reset
when the interval is partitioned.

The directional geometry cannot be dropped. A single coherent law with

```text
F=diag(lambda^-1,lambda,1),      J=diag(lambda,lambda^-1,1),
V=[e_1]_cross,                  A=F^T V F,
q_A=2,                         |curl A|^2=4lambda^2
```

has determinant one and constant original tensor norm, yet unbounded
ordinary curl as lambda grows. Its directional Cauchy estimate is an
equality: the growing area cost pays exactly the difference. This
refutes a geometry-free universal conversion from incompressibility
and coherence alone. It assigns no finite-energy or periodic NS
trajectory to those frames and does not refute a full-datum physical
history budget.

For the actual history target, retain the complete parabolic rate.
On a smooth unforced prefix, `D omega=Bomega` and `D M=BM+MB^T`.
Let `W=|omega|^2`, `Omega=omega^T Momega`, `V=omega^T S omega`.
The full product rule gives

```text
D Omega=4omega^T M S omega
  -2nu sum_k [(partial_k omega)^T M(partial_k omega)
             +2(partial_k omega)^T(partial_k M)omega],
D W=2V-2nu sum_k |partial_k omega|^2.
```

For rho=Omega/W on W>0,

```text
(D-2nu grad log W.grad)rho
  =(4omega^T M S omega-2rho V)/W
   -(2nu/W)sum_k [(partial_k omega)^T(M-rho I)(partial_k omega)
                  +2(partial_k omega)^T(partial_k M)omega].
```

The mixed diffusion has no automatic favorable sign. At M(0)=I and
zero initial spatial moment derivatives, rho(0)=1 and its initial
material rate is `2V/W`. The complete canonical unforced periodic
datum tested below has positive rate `2134367150/1383763869` at the
origin, even at nu=1/10. This is consistent with the earlier inverse-
metric quotient calculation: viscosity is not an instantaneous
nonincrease theorem for the changing measurement. It refutes that
monotonicity shortcut, not finite full-datum payment for its growth.
The initial tangent is exact; stochastic realization and a positive-
time passage are analytic. No uniform Taylor window is asserted.
Pressure also remains physical: `D B=-B^2-Hess p` is checked using
the actual canonical Poisson pressure in every Fourier output.

```sh
python3 -O labs/joint_curl_geometry.py
```

The checker keeps all nine tensor coordinates, a single normalized
three-sample original law, and both copies of every determinant-one
frame. It checks the original-label variance and payment, directional
curl conversion, the invariant planar normal, complete triangular
comparison envelopes, the coherent kinematic obstruction, and the
full signed cost-rate algebra with nonzero spatial derivatives. Its
actual three-dimensional periodic initial-data test uses the full
canonical unforced RHS, not a closed mode evolution.

The next physical estimate is finite directional geometry payment for
parents that reciprocally amplify, with constants fixed from the full
original datum, viscosity and horizon. A pointwise rho bound is one
sufficient candidate; a weaker spatial estimate controlling physical
enstrophy also suffices. The derivative terms, rotating orientation,
pressure and parent feedback must remain in that estimate. The
triangular class establishes a working mechanism, not that extension.

A small reciprocal-parent test extends its initial datum to

```text
u_0=(a sin y,epsilon sin z,b sin x),
```

with a,b>0, epsilon>=0. At epsilon=0 this is the established mixing
datum. For epsilon>0 all three components interact in a loop. The
exact initial field and its full unforced viscous tangent remain
solenoidal. Canonical periodic pressure has

```text
p(0)=0,
partial_t p(0)=-2ab epsilon cos x cos y cos z,
V(0)=3ab epsilon cos x cos y cos z,
partial_t rho(0,0)=6ab epsilon/(a^2+b^2+epsilon^2).
```

The pressure derivative is verified by the complete differentiated
Poisson equation, including viscosity; its mean is zero. At a=2,
b=3, epsilon=1/4 the initial directional rate is 144/209. These
are actual periodic initial NS jets, not an external strain or force.
They expose both reciprocal amplification and generated pressure for
the next prefix estimate. They establish neither its payment over
time nor indefinitely renewed stretching.

### Cyclic pressure renewal and the original frame history

`cyclic_pressure_history.py` tests a full coupled history with

```text
u_0=a(sin y,sin z,sin x),       a>0, nu>0,
D=partial_t+u.grad-nu Delta,
D B=-B^2-Hess p,              D M=BM+MB^T,   M(0)=I.
```

M is the original forward-frame moment, not the additive viscous memory
C evolved in the cellular-parent lab. Its initial identity is assigned
once, at the original datum; there is no restart at a later seam. This
is the actual directional conversion from the preceding tensor/curl
estimate. The nine-dimensional joint metric and q_A are not evolved by
this lab, so it makes no numerical claim about their payment identity.

The initial velocity is odd under complete spatial reflection and
equivariant under cyclic permutation of the coordinates. These
symmetries are preserved on a smooth unforced lifespan by uniqueness.
They make the origin a stationary material point and give

```text
B(t,0)=[[0,alpha,beta],[beta,0,alpha],[alpha,beta,0]],
ell=alpha+beta,                w=beta-alpha,
omega(t,0)=w(1,1,1),           Pi=partial_x partial_y p(t,0),
mu(t,x)=(1,1,1)^T M(t,x)(1,1,1)/3.
```

At the origin, cyclic symmetry of the symmetric M implies that (1,1,1)
is its eigenvector with eigenvalue mu. Consequently the physical
directional cost rho is mu whenever w is nonzero. Unlike the quotient
rho, mu remains defined at w=0. Spatial derivatives below are those of
the full fields, not derivatives of a closed centre ODE. The complete
equations at the material symmetry centre are

```text
ell'=nu Delta ell-(alpha^2+beta^2)-2Pi,
w'=nu Delta w+ell w,
mu'=nu Delta mu+2ell mu,
(log mu)'=2ell+nu Delta mu/mu.
```

The quadratic loss is `(ell^2+w^2)/2`. The pressure comes from the
entire evolving fluid, not from an independent control or a free
boundary source. In particular, its offdiagonal component need not
stop renewal. The canonical zero-mean pressure has the exact jets

```text
p(0)=0,
p_t(0)=-2a^3 cos x cos y cos z,
p_tt(0)=-(2/3)a^4 [sin(2x) cos y sin z
                  +sin x sin(2y) cos z
                  +cos x sin y sin(2z)]-6nu p_t(0),
Pi(0)=Pi_t(0)=0,             Pi_tt(0)=-4a^4/3.
```

Both differentiated Poisson equations retain every velocity component,
the previous pressure, viscosity and newly generated modes. Their
solutions have zero spatial mean. On an actual smooth local solution,
Taylor continuity therefore gives

```text
Pi(t)=-(2/3)a^4 t^2+o(t^2),
integral_0^tau -2Pi(t) dt=(4/9)a^4 tau^3+o(tau^3)>0
```

for sufficiently small positive tau. The initial stretch derivative
is nevertheless `ell'(0)=-a^2-nu*a<0`. The claim is positive pressure
renewal, not growth of ell at every time. The exact checker establishes
the jet identities; identifying them with the smooth solution and the
positive interval is analytic. No viscosity-uniform or amplitude-uniform
Taylor window is proved. This refutes the universal sign `-2Pi<=0`,
not a datum-fixed cumulative payment or global regularity.

The feedback calculation also connects directly to the positive triangular
class. For `u_0=(a sin y,c sin z,b sin x)`, arbitrary positive a,b,c,
the checker proves the complete pressure jets with
`p_t=-2abc cos x cos y cos z` and

```text
p_tt=-(2/3)abc [b sin(2x) cos y sin z
               +a sin x sin(2y) cos z
               +c cos x sin y sin(2z)]-6nu p_t,
(P_xy)tt(0)=-4a^2bc/3,
(P_xz)tt(0)=-4ab^2c/3,
(P_yz)tt(0)=-4abc^2/3.
```

These pressure renewals vanish with c, the parent that closes the
feedback loop. At c=0 the earlier triangular class has a proved analytic
all-time payment. These jet identities do not give an all-time history
allowance or quantify a stable perturbation neighborhood. The original
parents' subsequent renewal still has to be controlled.

The complete rational Fourier recurrence checks the first four canonical
pressure jets, including their additional output modes, for
`(a,nu)=(1,1/2),(1,1/10),(2,1/2)`. It also checks every coefficient of
the numerical velocity/moment operator against independent exact Fourier
products, both at the initial identity and at a nonidentity moment, and
checks all full-product pressure Hessian components at that second
snapshot. These checks survive Python optimization.

```sh
python3 -O labs/cyclic_pressure_history.py
python3 -O labs/cyclic_pressure_history.py --prefix --n 32 --nu .1 --final-time 4 --dt .01
python3 -O labs/cyclic_pressure_history.py --prefix --n 48 --nu .1 --final-time 4 --dt .01
python3 -O labs/cyclic_pressure_history.py --prefix --n 64 --nu .1 --final-time 4 --dt .01
python3 -O labs/cyclic_pressure_history.py --prefix --n 32 --nu .1 --final-time 4 --dt .005
```

The optional prefixes reuse the dealiased grid operations and Lawson RK4
from the existing reciprocal-parent solver. They evolve all three
velocities and all six symmetric entries of M, rather than an initial
mode family or a centre ODE. The signed physical ledgers are

```text
ell(t)-a+integral quadratic_loss
        -integral pressure_renewal-integral viscous_stretch = 0,
log mu(t)-integral 2ell-integral nu Delta mu/mu = 0.
```

For a Galerkin prefix, the corresponding retained projection-residue
integrals are subtracted as well. All ledger costs are integrated at the
same RK stages as the coupled state. Pressure is reconstructed with
every quadratic product output on a grid enlarged by a factor 3/2;
it is not restricted to the modes evolved by the Galerkin dynamics.
The explicit signed residues measure that distinction. Reports also
include the kinetic energy/dissipation balance, moment positivity,
cyclic symmetry, reality, incompressibility, high palinstrophy and
high moment-gradient fractions. The solver stops if the reported
moment positivity or frequency-resolution diagnostic fails. These
checks are convergence diagnostics, not continuum error bounds.

For a=1 and nu=.1, all four prefixes reach T=4. Selected values from the
64-cubed run are:

| Time | ell | mu | Pressure renewal -2Pi | Accumulated pressure renewal |
| --- | --- | --- | --- | --- |
| 0.5 | 0.509463 | 2.067017 | 0.236687 | 0.043710 |
| 1.25 | 0.046836 | 2.860116 | 0.668438 | 0.406541 |
| 2.5 | -0.153503 | 2.214426 | 0.679187 | 1.299616 |
| 4 | -0.119179 | 2.045015 | 0.447118 | 2.152211 |

At T=4, the cumulative quadratic loss is 3.008171 and the signed viscous
stretch contribution is -0.263218. These compensate the positive pressure
renewal. The log-frame ledger contains cumulative strain 0.469420 and
diffusion 0.245985. Its late instantaneous diffusion contribution is
positive, about 0.471548, while 2ell is negative, about -0.238358:
deformation from surrounding histories can increase the local frame
moment even during compression. This is a numerical observation on
these resolved prefixes, not an analytic arbitrary-history estimate.

The largest reported frame-diffusion discrepancy between 32 and 48
points per coordinate is 0.00203784, at t=2. On refinement from 48 to
64 it falls to 0.00000298817. Across the reported times, the latter
comparison changes ell and pressure renewal by at most 3.1e-9 and
mu by at most 1.3e-7. Halving the 32-grid time step changes the selected
centre channels by at most 7.0e-9. At 64 points, the largest signed
history-balance error is 2.2e-10; the reported moment eigenvalues remain
positive, with minimum above 0.0501. The accumulated stretch/frame
projection residues at T=4 are approximately -2.2e-11 and -1.7e-10.
The coarse derivative discrepancy is retained as a resolution warning,
despite its already closely matching velocity. None of these diagnostics
is a certified continuum error bound or a test of a singular solution.

For comparison, holding this initial velocity stationary requires the
manufactured force `f=(u.grad)u-nu Delta u`, with p=0. Its value at the
origin is zero, yet `partial_y f_1+partial_z f_1=a^2+nu*a` there. This
force gradient exactly supplies the missing stretch reaction. Its
normalized kinetic work is `nu integral |grad u|^2=3nu*a^2/2>0`.
It is a regular sustaining-force filter, not the imported forced
blowup construction. A zero observed force value does not remove its
effect on deformation. Applying the original-data tensor to a forced
solution would require the separately accumulated pulled-back force.

The target remains finite original-datum payment for the coupled
spatial geometry over every compatible continuation. The pressure
jet shows that unforced surrounding fluid can provide renewal. The
full frame equation also keeps diffusion from surrounding histories:
local compression alone need not decrease mu. Neither effect grants
a fresh resource at a seam, and neither establishes indefinitely
renewed dangerous stretching.

A concrete spatial target can avoid division by curl altogether. With
`Omega=omega^T Momega>=0`, spatial Cauchy and the original-gradient
payment give the analytic implication

```text
integral |omega|^2<=sqrt(2 integral q_A integral Omega),
||omega||_2^4<=2 ||grad u_0||_2^2 integral Omega.
```

It applies on R3 as well as the torus, without a volume factor. Thus a
finite original-datum bound on integral Omega over every continuation
would control the existing enstrophy criterion. The complete production
of Omega, including its mixed vorticity/moment derivatives, was stated
above; those signed terms have no proved arbitrary-history payment.
The spatial stochastic passage and this integral implication remain
analytic. This lab's centre ledgers do not supply that spatial bound.

## Same-frame tensor channels and the physical compatibility source

`joint_tensor_symmetry.py` checks the original-gradient packet rather than
a new independently supplied tensor or a reset history. Its finite law has
three noncommuting determinant-one frames with weights `1/3,1/6,1/2`.
Each original label gradient and both copies of its coframe stay together.
Write `T vec(A)=vec(A^T)`, `A_s=(A+A^T)/2`, `A_k=(A-A^T)/2`,
`C=E[(F^T F) tensor (F^T F)]`, `W=C^-1` and `M=E[J J^T]`.
The exact identities, certified in `MettapediaNS.JointTensorSymmetry`, are

```text
CT=TC, WT=TW,
C vec(skew(z))=vec(skew(Mz)),
W vec(skew(z))=vec(skew(M^-1 z)),
vec(A_s)^T W vec(A_k)=0,
q_A=q_sym+(1/2) omega^T M^-1 omega.
```

Here `skew(z)` is the cross-product matrix and
`omega=(A_21-A_12,A_02-A_20,A_10-A_01)`. The actual-curl consumer retains
the projection and symmetric flow-curvature hypotheses; it is not an
arbitrary declaration identifying a supplied tensor with physical curl.
The finite forward moment is proved positive definite, so its inverse is
genuine. The factor `1/2` accounts for the two skew matrix entries per
vorticity coordinate.

The split also retains complete spatial diffusion. For determinant-preserving
frame tangents, `K_k=C_k W` preserves transpose, and

```text
r_k=partial_k vec(A)-K_k vec(A),
r_k=r_sym,k+r_skew,k,
F_A=sum_k r_k^T W r_k=F_sym+F_skew,
F_skew=(1/2) sum_k (partial_k omega-M_k M^-1 omega)^T
                         M^-1 (partial_k omega-M_k M^-1 omega).
```

Lean certifies the split into symmetric/skew diffusion and supplied
source-free production with explicit transpose and metric-connection
hypotheses. The last three-dimensional connection formula is checked
exactly in the finite lab. Three spatial directions, all nine coordinates,
all metric derivatives and the inverse-metric diffusion correction remain.
The independent full-production calculation gives `Dq_A=-2nu F_A`.
Continuous stochastic construction, passage under expectations and
space-time integration remain analytic. The absence of a quadratic cross
term does not remove the nonlinear coupling of the two channels through
the actual velocity or pressure.

The physical coupling can be represented by `E=A-B`, `B=grad u`.
It starts at zero and is symmetric after the actual curl identification.
Its complete parabolic source differs from the source-free original packet:

```text
D=partial_t+u.grad-nu Delta,  P=Hess p,
D E=-B^T E-E B+S_E,   S_E=P-B^T B,
Dq_E=2 vec(E)^T W vec(S_E)-2nu F_E.
```

The finite equation, symmetric source, complete production and literal
canonical NS gradient rate are kernel-certified. The physical construction
of A over time is analytic. The signed source work must be paid over every
compatible continuation; the identity supplies no finite arbitrary-data
allowance and q_E alone is not asserted to be a regularity criterion.

The actual test keeps every generated Fourier mode and the complete
canonical pressure on the normalized period-2*pi torus. For
`u_0=(a sin y,c sin z,b sin x)`, the initial pressure is zero and
`p_t(0)=-2abc cos x cos y cos z`. At `x*=(pi/2,pi/2,0)` and
`z=(1,-1,0)`, the full equations give

```text
E(0)=0, E_t(0)=-B_0^T B_0<=0,
z^T E_t(0,x*)z=0,
z^T E_tt(0,x*)z=4abc-2nu(a^2+b^2).
```

Pressure supplies `4abc` in this direction; viscosity supplies
`-2nu(a^2+b^2)`. Transport and the remaining reaction terms are included
and vanish in this particular contraction at the selected point. Thus
`2abc>nu(a^2+b^2)` makes the second derivative positive. For
`a=b=c=1,nu=1/10` its value is exactly `18/5`, and
`z^T E(t,x*)z=(9/5)t^2+o(t^2)>0` on a sufficiently short actual smooth
interval. Analytic stochastic identification, local existence and Taylor
continuity justify that passage. It is not a Lean-certified or uniform
positive-time window.

This refutes the comparison `A-grad u<=0` for all unforced evolutions.
It does not refute a bound on the trace, a signed integral correction,
a full-datum allowance, or global regularity. The data are periodic;
their nonzero periodic lifts are not finite-energy whole-space data.
No indefinite renewal or singularity is inferred from this finite burst.

Independent Gaussian-rational Fourier checks verify the complete defect
rate and symmetry through second time order, actual curl identification,
and the normalized channel split through the same order. They also verify
the first nonzero full defect production, retaining the changing joint
metric, actual pressure and every spatial derivative. At `a=1,nu=1/10`,
the normalized spatial means are

```text
source_work_E'(0)=9/8,
q_E''(0)=9/4,
q_E'''(0)=-9/4.
```

Run the exact tests, whose checks remain active under optimization:

```sh
python3 -O labs/joint_tensor_symmetry.py
```

The useful remaining theorem is finite payment for the coupled physical
geometry and compatibility from the full original datum, viscosity and
horizon. The symmetric original-gradient packet still retains parent
information, but its norm has no free cross-channel transfer. A successful
correction must use actual pressure/velocity coupling and complete
histories, with no reset of spent resources at a composition boundary.

## Joint pressure cotangent and a complete paid history

`joint_pressure_cotangent.py` checks a concrete pressure payment for the
original tensor, with a full-pressure analytic consumer and an adversarial
sign test. Use normalized spatial mean on the period-2*pi torus. Keep the
original stochastic inverse frame `F`, `J=F^-1`,
`C=E[(F^T F) tensor (F^T F)]`, `W=C^-1`,
`A=E[F^T(grad u_0)(alpha)F]`, `B=grad u`, `P=Hess p` and `E=A-B`.
Both copies of each frame and its original label gradient stay on the same
sample. No independent tensor average or new initial history is used.

### Diffusion pays the receiver; the induced pressure cost remains

Write `e=vec(E)`, `K_j=C_j W`, `r_j=partial_j e-K_j e` and
`F_E=sum_j r_j^T W r_j`. Since `W_j=-W K_j`, the complete product rule gives

```text
Z=unflatten(W e),
partial_j vec(Z)=W r_j,
(div Z)_i=sum_j (W r_j)_(i,j),
R(W)_il=sum_j W_(i,j),(l,j).
```

For `slot_j(v)=vec(v tensor e_j)`,

```text
v.div Z=sum_j r_j^T W slot_j(v),
v^T R(W)v=sum_j slot_j(v)^T W slot_j(v),
sum_j |nu r_j-slot_j(v)|_W^2
 =nu^2 F_E-2nu v.div Z+v^T R(W)v >=0.
```

For `nu>0`, this proves
`2v.div Z<=nu F_E+nu^-1 v^T R(W)v`.
`MettapediaNS.JointPressureCotangent` certifies these identities, positivity
of the induced metric, and agreement with the existing full tensor diffusion.
It also proves that a supplied bound `W<=kappa I` implies
`v^T R(W)v<=3kappa |v|^2`. Deriving that supplied bound for an evolving
fluid is a separate physical obligation.

Weak integration by parts, with `v=-grad p`, yields

```text
2 mean(vec(E)^T W vec(P))=-2 mean(div Z.grad p)
 <=nu mean(F_E)+nu^-1 Gamma,
Gamma=mean(grad p^T R(W)grad p),
d_t mean(q_E)+nu mean(F_E)
 <=nu^-1 Gamma-2 mean(vec(E)^T W vec(B^T B)).
```

This keeps the changing metric derivative and every spatial direction.
The weak integration and actual stochastic construction are analytic here;
the finite absorption is kernel-certified. Gamma is an induced pressure
cost, not an unweighted projection contraction or an established finite
history allowance. The quadratic source remains signed.

For a coherent single frame, `H=(F^T F)^-1` gives
`W=H tensor H` and `R(W)=tr(H)H`. At
`F=diag(lambda,lambda^-1,1)`, the extra factor is
`lambda^2+1+lambda^-2`, unbounded as lambda grows. The exact lab retains
three noncommuting rational samples and three determinant-preserving frame
tangents; it also checks this single-frame identity. The latter is only a
kinematic obstruction to a uniform one-index metric comparison, not an
actual NS history counterexample or a refutation of full-datum payment.

### An original-history reserve for Taylor--Green

The exact unforced periodic flow, for `a>=0,nu>0`, is

```text
u=a exp(-2nu t)(sin x cos y,-cos x sin y,0),
p=(a^2/4)exp(-4nu t)(cos 2x+cos 2y).
```

The checker verifies incompressibility, mean-zero canonical pressure,
`(u.grad)u+grad p=0`, `Delta u=-2u` and the full all-time NS equation.
Pressure and all parents are included. With
`d=a exp(-2nu t)cos x cos y` and
`h=a exp(-2nu t)sin x sin y`,
`B=[[d,-h,0],[h,-d,0],[0,0,0]]`. Its singular values are `|d+h|,|d-h|,0`,
bounded by `a exp(-2nu t)` because `d+/-h=a exp(-2nu t)cos(x-/+y)`.
The normalized physical quantities are exactly

```text
mean(|u|^2)=(a^2/2)exp(-4nu t),
mean(|grad u|^2)=a^2 exp(-4nu t),
mean(|grad p|^2)=(a^4/4)exp(-8nu t).
```

Analytic stochastic transport now has a finite resource fixed by the
original datum, rather than a bound assumed on an unknown future flow:

```text
D=integral_0^infinity a exp(-2nu s)ds=a/(2nu),
||F||_op,||J||_op<=exp(D),
exp(-4D)I<=C,W<=exp(4D)I,
R(W)<=3exp(4D)I.
```

These bounds apply pathwise to the original smooth stochastic flow; averaging
the same-frame quadratic forms and inversion preserve the stated comparison.
The uniform all-time derivative bound is available from the explicit flow.
It is not a proved arbitrary-flow estimate. The pressure leg is therefore paid:

```text
nu^-1 integral_0^infinity Gamma <=3exp(4D)a^4/(32nu^2).
```

The complete other source is paid too. The original label gradient has
Frobenius norm at most `sqrt(2)a`, so

```text
|A|<=sqrt(2)a exp(2D),
|E|<=sqrt(2)a[exp(2D)+exp(-2nu t)],
|B^T B|<=sqrt(2)a^2 exp(-4nu t),
|2 mean(vec(E)^T W vec(B^T B))|
 <=4a^3 exp(4D)[exp(2D)+exp(-2nu t)]exp(-4nu t).
```

Thus, from `E(0)=0`, full production and spatial integration give

```text
mean(q_E(T))+nu integral_0^T mean(F_E) <=K,
K=exp(4D)[3a^4/(32nu^2)+(a^3/nu)(exp(2D)+2/3)].
```

More precisely, the remaining reserve is

```text
R_TG(t)=exp(4D)[3a^4 exp(-8nu t)/(32nu^2)
          +(a^3/nu)exp(2D)exp(-4nu t)
          +(2a^3/(3nu))exp(-6nu t)].
```

It is nonnegative, starts at K, tends to zero, and its negative derivative
equals the complete upper source payment. Every original compatible
interval therefore satisfies

```text
mean(q_E(t))-mean(q_E(s))+nu integral_s^t mean(F_E)
 <=R_TG(s)-R_TG(t),  s<=t.
```

The original labels, D and original amplitude are retained through seams.
Summing compatible intervals cancels intermediate reserves and grants no
new allowance. The scalar derivative and all-time integrals are checked
exactly. Stochastic identification, metric differentiation and spatial
integration are analytic, not certified by this scalar checker.

There is an actual physical consumer. The original source-free payment
gives `mean(q_A)<=mean(|grad u_0|^2)=a^2`; metric comparison and `B=A-E`
give `mean(|grad u|^2)<=2exp(4D)(a^2+K)`.
This recovers a finite enstrophy bound by the proposed history mechanism,
although the explicit flow already has the sharper exact bound above.
Unlike the earlier triangular shear example, the full pressure is nonzero.
It has no reciprocally amplifying parent: advection is an exact gradient
and the remaining velocity is caloric. Extending this source/geometry
payment to arbitrary mutually amplifying parents is open. Assuming their
unknown future strain integral to be finite would supply the missing
regularity control rather than prove it.

### Weighted pressure does not have a universal favorable sign

Ordinary incompressibility gives `mean(B:P)=0` at every time. For the
original metric, however,

```text
J_p(t)=mean(vec(B)^T W vec(P)),
W(0)=I, W_t(0)=(B+B^T) tensor I+I tensor(B+B^T),
J_p(0)=0, J_p'(0)=4mean(S^2:P),  S=(B+B^T)/2.
```

The complete canonical Fourier tangent retains the evolving B and P:
their two unweighted legs integrate to zero; the metric leg remains.
The genuinely 3D interacting datum gives `-391507472/10405395`, at each
of the two checked positive viscosities. Every generated mode is retained.
The full weak receiver identity is independently checked. This is weighted
physical-gradient pressure work, distinct from the defect source pairing.

For the opposite sign, put a planar annular swirl `u_0=V(r)e_theta`,
independent of z, strictly inside radius pi of the periodic cell.
Its pressure satisfies `p_r=V^2/r`, `Delta_h p=2V'V/r`, and
`S^2=(V'-V/r)^2 I_h/4`. Therefore

```text
J_p'(0)=(1/pi) I,
I=integral (V'-V/r)^2 V'V dr.
```

The piecewise linear tent on `[1,1+delta,3]`, rising from zero to one and
falling back to zero, has

```text
I=delta^-4[log(1+delta)-delta/(1+delta)]
  +9(2-delta)^-4[log(3/(1+delta))-3/(1+delta)+1].
```

The exact primitive for `V=alpha r+beta` is
`alpha beta^2(alpha log r-beta/r)`. At delta=1/10, elementary rational
log bounds give `I>=2996550/75449>39`; at delta=1 they give `I<=-1/2`.
The checker verifies the physical polar source, quartic invariant,
primitive, both ramp integrals and rational bounds.

Smooth radial mollification, supported away from zero and inside radius pi,
converges in `W^(1,4)` and preserves the strict sign. The quartic functional
is continuous there; equivalently, the canonical pressure Hessian is an
L2 bounded transform of the quadratic source. Smooth local unforced
existence and original-metric differentiability then give the corresponding
strict short-time weighted-work signs. This passage is analytic; no explicit
mollifier width, uniform interval, continuum enclosure or Lean time theorem
is claimed. It refutes a universal zero or nonpositive weighted pressure
work, not a signed full-datum allowance, indefinite renewal or regularity.
These are periodic data; their nonzero lifts are not R3 finite-energy data.

Run all exact checks, which remain active under optimization:

```sh
python3 -O labs/joint_pressure_cotangent.py
```

The named remaining estimate is a finite original-datum payment for Gamma
and the complete signed parent source, together with the physical geometric
comparison, or a weaker coupled correction controlling the established
curl/enstrophy criterion. Payment of q_E alone is not that criterion. It must retain
original histories, pressure, changing geometry and every parent. The paid
class demonstrates a mechanism; it does not extend its datum-fixed frame
bound to arbitrary continuations.

## Causal joint-source history and reciprocal pressure generation

`joint_source_history.py` checks the complete compatibility defect
`E=A-grad u` in its original nine-coordinate moment `C` and inverse `W`.
Pressure and parent history share that original metric. The exact lab retains
every generated Fourier output, changing drift, matrix connection and spatial
diffusion. Its independent symbolic calculation uses exact torus moments of
trigonometric polynomials rather than numerical quadrature.

### A physical-time comparison with a named source

The established supplied rate is

```text
D q_E=2 vec(E)^T W vec(S_E)-2nu F_E,
S_E=Hess p-B^T B,  D=partial_t+u.grad-nu Delta.
```

`JointSourceHistory.lean` certifies the finite metric Cauchy--Schwarz estimate
and its tensor-production consumer, retaining the complete diffusion. It also
certifies the scalar time comparison

```text
q,b,d>=0, q(0)=0, q'+d<=2sqrt(q)b
 => q(T)+integral_0^T d<=(integral_0^T b)^2.
```

For a smoothly constructed original tensor history, weak spatial integration
gives `q=integral E:W E`, `d=2nu integral F_E`, and
`b=sqrt(integral S_E:W S_E)`. Spatial Cauchy--Schwarz, the original continuous
stochastic construction and its physical-time identification remain analytic
obligations. The scalar theorem handles zero energies by regularizing the
square root; no nonzero initial energy is assumed.

The combined source keeps
`q(S_E)=q(Hess p)+q(B^T B)-2(Hess p):W(B^T B)`.
It does not replace the two legs by independently averaged frames or remove
their cross term. The norm bound can nevertheless overpay cancellation between
different times. It is a comparison benchmark and sufficient cap target,
not a proof that this stronger norm cap is the only possible signed mechanism.

With an arbitrary seam energy, the time theorem retains
`sqrt(q(s))+B_source(t)-B_source(s)`. For a zero initial defect and the same
original source primitive, every compatible interval satisfies

```text
q(t)-q(s)+integral_s^t d
 <= B_source(t)^2-B_source(s)^2,
B_source(t)=integral_0^t b.
```

If an original-datum cap `B_source(t)<=L` is proved on the whole window,
`R(t)=L^2-B_source(t)^2` is nonnegative and pays these costs at every seam.
The required cap is not assumed in the construction of the history. Replacing
an interval by the fresh increment's square loses
`2 B_source(s)(B_source(t)-B_source(s))`; Lean proves that strict underpayment
for positive old and new amplitudes. Compatibility preserves the original
source primitive and diffusion cost. It supplies no new allowance.

### Actual reciprocal parents create positive defect-pressure work

On the normalized period-2pi torus, take
`u0=(a sin y,b sin z,c sin x)` and positive viscosity. Initial pressure is zero.
Full canonical NS jets give

```text
p1=-2abc cos x cos y cos z,
p2=-(2/3)abc[c sin(2x)cos y sin z+a sin x sin(2y)cos z
                      +b cos x sin y sin(2z)]-6nu p1.
```

Here subscripts denote time derivatives at zero. The independent original
packet and moment equations give `E1=-B0^T B0` and the complete `E2,E3,W1,W2`.
Every defect jet remains symmetric and every original packet jet keeps the
literal physical curl. Define

```text
P_E(t)=2mean(E:W Hess p),  T_E(t)=2mean(E:W B^T B),
q(t)=mean(E:W E),  F(t)=mean(F_E),
S4=a^4+b^4+c^4,  R=a^2 b^2 c^2.
```

The generic exact identities are:

| Quantity | Time derivative at zero |
| --- | --- |
| `P_E''` | `0` |
| `P_E'''` | `27R` |
| `q''` | `3S4/4` |
| `q'''` | `-15nu S4/2` |
| `q''''` | `27R+69nu^2 S4` |
| `T_E'''` | `-33nu^2 S4` |
| `F''` | `S4` |
| `F'''` | `-18nu S4` |

The pointwise fourth-order balance, before spatial integration, keeps
`q4+u0.grad q3+3u1.grad q2-nu Delta q3=P_E3-T_E3-2nu F3`.
After averaging it gives exactly the displayed energy derivative. A negative
diffusion derivative in this table describes its initial change; the
diffusion density itself is nonnegative.

All three legs of `P_E'''` are checked:

```text
mean(E2:P1)=(9/2)R,
mean(E1:P2)=0,
mean(vec(E1)^T W1 vec(P1))=0,
P_E'''=6[mean(E2:P1)+mean(E1:P2)+2mean(vec(E1)^T W1 vec(P1))].
```

Consequently `P_E(t)=(9/2)R t^3+o(t^3)>0` for nonzero parents and a
sufficiently short actual smooth solution interval, using analytic local
existence and original stochastic identification. This rejects a universal
nonpositive defect-pressure work, not a full-datum allowance or regularity.
The third-parent-zero limit removes this feedback. Sign flips leave `R`
unchanged. Five positive-viscosity rational cases and one zero-viscosity
algebraic diagnostic are checked; zero viscosity is not the viscous theorem's
setting. These are periodic data, not whole-space finite-energy lifts.

The source histories `DY_P=-B^T Y_P-Y_P B+Hess p` and
`DY_G=-B^T Y_G-Y_G B+B^T B`, both initially zero, reconstruct
`E=Y_P-Y_G`. The full fourth norm identity retains their cross pairing.
Its spatial mean vanishes to this order for this family; it is not discarded
as a general history rule. `mean(Y_P:W Y_P)=(9/8)R t^4+o(t^4)`.
The causal pressure-input square has the same leading coefficient, since
`mean(P1:P1)=(9/2)R`. In contrast,
`nu^-1 integral_0^t Gamma=(3/(2nu))R t^3+o(t^3)` for the cotangent estimate.
The latter remains valid but overpays this initial feedback. The causal input
uses a weighted pressure Hessian rather than a weighted pressure gradient;
its later cost has not been paid from original data.

No uniform Taylor remainder, certified turnover window, renewed-parent cap,
indefinite recurrence or singularity is claimed. Physical `q_E` payment alone
is also not the established continuation criterion: original `q_A` payment
must still be combined with sufficient curl-direction geometry. For a forced
velocity, the compatibility source also retains `-grad f`; the causal comparison
works for a supplied source and does not itself distinguish forced from
unforced dynamics. The unforced structure must enter the source-history and
geometry estimates. No arbitrary-fluid stochastic optimizer is identified.

Run the exact checks, including the independent symbolic formulas:

```sh
python3 -O labs/joint_source_history.py
```

## Directional cubic renewal and original labels

`cubic_parent_renewal.py` retains the actual vorticity observation in the
original stochastic-gradient history. The normalized torus has period
`2*pi`. Write `D=partial_t+u.grad-nu Delta`, `B=grad u`, `P=Hess p`,
`DA=-B^T A-A B`, `D omega=B omega`, and `E=A-B`. The product
`H=omega^T A omega` has the complete local rate

```text
D H=-2nu J_A,
J_A=sum_k[(partial_k omega)^T A(partial_k omega)
   +(partial_k omega)^T(partial_k A)omega
   +omega^T(partial_k A)(partial_k omega)].
```

Let `h` be the passive scalar with original label
`h0=omega0^T B0 omega0`, and set `chi=h-H`. Then

```text
D chi=2nu J_A,
omega^T B omega=h-chi-omega^T E omega,
D(chi+omega^T E omega)=omega^T(P-B^T B)omega+2nu J_B.
```

The last identity cancels the original-packet derivatives between the
two histories. The actual pressure and every physical mixed derivative
remain. `J_A` and `J_B` are signed; neither is asserted to be a positive
diffusion square. Same-path matrices satisfy
`(J w0)^T(F^T V0 F)(J w0)=w0^T V0 w0`, for `FJ=I`. Averaging that same
path preserves the passive label, while multiplying the three separate
means gives H and introduces chi. Continuous stochastic identification,
construction of h and its conserved spatial mass are analytic here.
Passive advection--diffusion also has its original unsigned L1 allowance;
this does not by itself pay chi or E.

`MettapediaNS.JointCubicRenewal` certifies the finite complete production,
same-path cancellation, the retained physical-gradient rate and a
conditional continuation consumer. For actual smooth solenoidal whole-space
evolutions it proves the literal order-one energy balance. With
`g0=integral omega0^T B0 omega0` and prescribed horizon T, a sufficient
missing estimate is

```text
-2 integral_0^tau integral(chi+omega^T E omega)
  <= (2-delta)nu integral_0^tau integral |grad omega|^2 + K(u0,nu,T),
0<delta<=2,  tau<=T.
```

It gives
`||omega(tau)||_2^2+delta nu integral_0^tau ||grad omega||_2^2`
`<=||omega0||_2^2+2T|g0|+K`. The kernel version uses the actual
`orderEnergy 1/2` and the literal physical stretching-mass difference.
The equivalent curl interpretation and realization by h, chi, E are
analytic. With delta=1, the theorem quantifies one K before every solution
prefix from the same datum and invokes existing whole-space continuation.
No bound on K is supplied. This is an explicit history form of the open
crux, not a reduction of its difficulty or a proved reserve. It does not
require independently bounding every weighted Hessian or every frame
direction. At seams the original h and both histories remain; resetting
them changes the physical reconstruction.

The complete canonical Fourier jets independently evolve A and h, retain
actual curl, and check the pointwise product law and pressure-parent
Riccati observation. No outputs are truncated. For
`u0=(a sin y,b sin z,c sin x)`, put `S22=a^2 b^2+a^2 c^2+b^2 c^2`.
Independent generic trigonometric-polynomial integration gives

```text
mean(h0)=mean(H)'(0)=mean(chi)'(0)=0,
mean(H)''(0)=-nu S22/2,  mean(chi)''(0)=nu S22/2,
mean(omega^T E omega)'(0)=-S22/4,
mean(omega^T E omega)''(0)=3nu S22/2,
mean(omega^T B omega)'(0)=S22/4,
mean(omega^T B omega)''(0)=-2nu S22.
```

Thus covariance and compatibility have different orders and signs already
at birth. Positive-viscosity fixtures include equal and unequal signed
parents, a two-parent triangular boundary and a single-parent boundary.
The signed spatial mean of the original label is zero in these fixtures,
but its unsigned mass and the signed physical histories are not generally
zero. The two-parent triangular and single-parent fixtures have their
complete initial cubic label identically zero; this is checked pointwise.

A mixed-scale test isolates the covariance sign. For the actual real
solenoidal polynomial v in `signed_viscous_pressure.interacting_datum`,
`mean(omega_v^T grad(v) omega_v)=-384/65` and `mean(J_grad(v))=-384/13`.
For `u_n=v(x)-v(nx)/n`, the checked scales n=5,7,11 have

```text
mean(h0)=0,
mean(J_B0)=384(n^2-1)/13,
mean(chi)'(0)=768nu(n^2-1)/13.
```

Replacing u_n by -u_n reverses that derivative while leaving the zero
signed initial mass unchanged. The full canonical unforced initial
tangent is checked at n=5,nu=1/10, including its pressure and physical
compatibility. Its negative covariance derivative is `-9216/65`.
This excludes a universal favorable covariance sign and a zero payment
from the initial signed cubic mass alone. Unsigned initial labels and
the full original datum remain available. The fixed-datum short-time
passage is analytic; no uniform window, indefinite renewal, failure of
a full-datum allowance or singularity is claimed. These periodic fields
are not whole-space finite-energy lifts.

An explicit diagnostic force `f=curl u` has zero instantaneous kinetic
work on v but a nonzero extra cubic source
`(curl f)^T A omega+omega^T A(curl f)`. Its exact mean is `-128/195`.
This retains the physical curl-source leg. It is not the imported forced
blowup construction and proves no internal realization by hidden fluid.

There are two paid analytic calibrations for the joined physical budget.
For the previously established stochastic triangular class
`u=(a exp(-nu t) sin y,0,v)`, `v0=b sin x`, the original derivative
bounds give

```text
|v_x|<=b exp(-nu t),
|v_y|<=ab exp(-nu t)(1-exp(-nu t))/nu,
|mean(omega^T B omega)|<=a^2 b^2 exp(-3nu t)(1-exp(-nu t))/nu.
```

Here `g0=0`. Every joined history interval is paid by the same decreasing
nonnegative reserve

```text
K_mix=a^2 b^2/(6nu^2),
R_mix(t)=K_mix[4exp(-3nu t)-3exp(-4nu t)],
2 integral_s^t mean(omega^T B omega)<=R_mix(s)-R_mix(t).
```

Consequently `mean|omega(t)|^2+2nu integral_0^t mean|grad omega|^2`
`<=mean|omega0|^2+K_mix`. The checker verifies the exact scalar reserve
identities; the stochastic derivative bounds and complete spatial/time
payment are analytic. This payment uses actual stretching and the coupled
history identity, without independently estimating chi, E or every frame
direction. The vertical field does not feed its horizontal parent.

The same triangular class refutes payment from the complete original
cubic label alone, including its unsigned mass. Set a=b=A and hold
`nu>0` and a prescribed positive horizon fixed. Every datum
`u0=(A sin y,0,A sin x)` has `h0=0` pointwise. In turnover variables
`sigma=A t`, `kappa=nu/A`, its vertical component is `A w_kappa`, where

```text
partial_sigma w_kappa+exp(-kappa sigma)sin y partial_x w_kappa
  =kappa Delta w_kappa,  w_kappa(0)=sin x.
w_0=sin(x-sigma sin y).
```

The limiting field has normalized enstrophy `1+sigma^2/4` and complete
vorticity-gradient mass `1+3sigma^2/4+3sigma^4/16`. The lab checks those
exact integrals and the full viscous difference equation. Actual
positive-viscosity convergence is analytic: for `z=w_kappa-w_0`,

```text
partial_sigma z+exp(-kappa sigma)sin y partial_x z-kappa Delta z
  =(1-exp(-kappa sigma))sin y partial_x w_0+kappa Delta w_0,  z(0)=0.
```

On any fixed interval `[0,S]`, its forcing has H2 norm at most
`kappa C(S)`, with
`C(S)=sup_[0,S](sigma ||sin y partial_x w_0||_H2+||Delta w_0||_H2)`.
This finite constant uses only the explicit limiting profile. The
commutators of the six derivatives `1,x,y,xx,xy,yy` give
`Y'<=4Y+kappa^2 C(S)^2` for their squared L2 norm sum Y. Hence
`||z||_H2<=kappa C(S)sqrt(exp(4S)-1)/2`. The horizontal shear also
converges at rate kappa. Consequently, at the actual time t=S/A,

```text
mean|omega(t)|^2=A^2[1+S^2/4+O_S(nu/A)].
```

At S=1 and sufficiently large A this gives an enstrophy increase of at
least `A^2/8`, within any prescribed positive horizon. Because g0=0,
the exact enstrophy balance makes the half-dissipation renewal excess

```text
-2 integral_0^t mean(chi+omega^T E omega)
  -nu integral_0^t mean|grad omega|^2
 =mean|omega(t)|^2-mean|omega0|^2
   +nu integral_0^t mean|grad omega|^2 >= A^2/8.
```

Thus a finite K depending only on the common label h0=0, viscosity and
horizon fails on actual unforced, globally regular flows. A reserve must
retain more of the original datum than its cubic label. Initial enstrophy
is A^2 here, and `K_mix=A^4/(6nu^2)` pays the entire class. No
full-datum bound, indefinite renewal or singularity is refuted. This is
a periodic triangular analytic argument, not a whole-space lift or a
Lean-certified convergence theorem; the checker certifies its exact
residual and limiting identities. It uses a linear parabolic difference
estimate, not an unproved uniform NS Taylor window.

For a smooth mean-zero periodic divergence-free Beltrami eigenfield
`curl V=kappa V`, the full unforced evolution is `u=exp(-nu kappa^2 t)V` and
`p=-|u|^2/2`, up to a time-only gauge. Actual vorticity is `omega=kappa u`.
Its pointwise stretching is the divergence of
`kappa^2 u |u|^2/2`, so its spatial mean, g0 and joined renewal vanish
at every time. Thus this entire class has `K=0` for the joined budget,
even with nonzero pressure and genuinely three-dimensional pointwise
stretching. The checker verifies the full ABC example
`V=(a sin z+c cos y,b sin x+a cos z,c sin y+b cos x)` and its original
packet/passive-label jets. At a=1,b=2,c=3,nu=1/10 the complete jets give
`mean(chi)''(0)=49/5` and `mean(omega^T E omega)''(0)=-49/5`, while
the joined renewal vanishes. The individual legs are not discarded.
The all-time equations and divergence identity
are exact; the continuous stochastic identification and periodic spatial
integration are analytic. Monochromatic parents decay by heat. The
arbitrary mutually amplifying-parent estimate remains open.

Run the complete exact and independent symbolic checks:

```sh
python3 -O labs/cubic_parent_renewal.py
```

## Returned parent work and a paid reciprocal neighborhood

`parent_return_history.py` keeps the original sine parents, the modes
generated from them, and their later return interactions. The domain is
the normalized torus of period `2*pi`; all energies below are squared
L2 norms, without a factor of one half. Parent kinetic work is distinct
from vorticity stretching. The purpose is to test whether every internal
return must damp its original parent, and to retain the actual resource
paying a return when that stronger assertion fails.

Let P be the fixed L2 orthogonal projection onto the three divergence-free
vectors `(sin y,0,0)`, `(0,sin z,0)`, `(0,0,sin x)`, and Q=I-P. These
vectors have Laplacian eigenvalue -1. For the complete unforced NS source
`N(u)=-Leray[(u.grad)u]`, write

```text
W_P=<Pu,PN(u)>, E_P=||Pu||_2^2,
E_H=||Qu||_2^2, D_H=||grad Qu||_2^2.
E_P'+2nu E_P=2W_P,
E_H'+2nu D_H=-2W_P.
```

These are actual smooth-solution kinetic balances: P commutes with the
Laplacian, and total nonlinear kinetic work vanishes. If the unobserved
modes start empty, `E_H(0)=0`. Thus on every compatible interval

```text
2 integral_s^t W_P=E_H(s)-E_H(t)-2nu integral_s^t D_H<=E_H(s).
```

Later positive return may spend storage created by earlier negative
parent work. Resetting the hidden energy or phases at a seam discards
that history. The identity bounds net return; it does not by itself
bound repeated positive transfers or pay the derivative-level
continuation criterion. It is not a new energy-conservation mechanism
distinguishing NS from every energy-conserving averaged equation.
The earlier [crossing-box test](#generated-modes-can-return-positive-work-to-their-parents)
already has a positive individual return channel in an initial jet.
Here the positive-viscosity interval concerns the net work of the original
parent projection, with its complete prior history and an all-time payment.

### An actual positive-viscosity return interval

Use the globally regular triangular class already described above,
`u=(a exp(-nu t)sin y,0,v)`, `v0=b sin x`, with a,b>=0. Its vertical
scalar obeys `v_t+a exp(-nu t)sin y v_x=nu Delta v`. Set a=b=A>0,
`sigma=A t`, `kappa=nu/A`, and v=A w_kappa. Then

```text
w_sigma+exp(-kappa sigma)sin y w_x=kappa Delta w, w(0)=sin x,
p_kappa=2mean(w_kappa sin x),
r_kappa=partial_sigma p_kappa+kappa p_kappa
       =2exp(-kappa sigma)mean(w_kappa sin y cos x),
W_P=A^3 p_kappa r_kappa/2.
```

At kappa=0 the explicit reference is `w_0=sin(x-sigma sin y)`.
Define the phase integrals
`J0(sigma)=mean_y cos(sigma sin y)` and
`J1(sigma)=mean_y sin y sin(sigma sin y)=-J0'(sigma)`.
The original mode has p_0=J0 and r_0=-J1. Integrating the absolutely
convergent cosine and sine series, with
`mean sin(y)^(2m)=(2m)!/[4^m(m!)^2]`, gives

```text
J0(3)=sum_m>=0 (-1)^m(9/4)^m/(m!)^2,
J1(3)=(3/2)sum_m>=0 (-1)^m(9/4)^m/[m!(m+1)!].
```

After m=1 the absolute terms decrease. Odd/even partial sums through
m=5/4 therefore certify `J0(3)<-1/4` and `J1(3)>1/3`.
Differentiating the phase integrals gives `|J0'|<=1` and `|J1'|<=1/2`.
These exact rational margins are checked by the program.

The passage to actual positive viscosity uses a scalar L2 contraction,
not a generic NS Taylor window. For z=w_kappa-w_0 the complete equation is

```text
z_sigma+exp(-kappa sigma)sin y z_x-kappa Delta z
  =(1-exp(-kappa sigma))sin y (w_0)_x+kappa Delta w_0, z(0)=0.
```

The drift is divergence-free and the diffusion is dissipative. The
explicit reference satisfies
`||sin y (w_0)_x||_2=1/2` and
`||Delta w_0||_2^2=1/2+3sigma^2/4+3sigma^4/16`.
For sigma>=0 its latter norm is at most `1+sigma+sigma^2/2`.
Using `1-exp(-kappa sigma)<=kappa sigma`, on [0,S] contraction gives

```text
||z(sigma)||_2<=kappa B(S), B(S)=S+3S^2/4+S^3/6,
|p_kappa-J0|<=(3/2)kappa B(S),
|r_kappa+J1|<=kappa[B(S)+S].
```

The observation bounds follow by Cauchy--Schwarz, using
`||sin x||_2=1/sqrt(2)`, `||sin y cos x||_2=1/2`,
`||w_0||_2=1/sqrt(2)` and `sqrt(2)<3/2`.
For S=49/16 and `0<kappa<=1/1000`, both errors are less than 1/16.
The phase derivative bounds then give throughout I=[47/16,49/16]

```text
p_kappa<=-1/8, r_kappa<=-1/6,
W_P>=A^3/96, integral_(I/A) W_P>=A^2/768.
```

The original mode changes sign before receiving positive work. Generated
modes are initially empty. This disproves universal instantaneous damping
of returned parent work on actual unforced positive-viscosity flows.
It does not disprove a full-datum history payment or regularity. At fixed
nu>0 the interval fits any prescribed positive horizon by choosing
`A>=1000nu` and `A>=49/(16T)`.

The full return is paid. Since the vertical scalar always retains its
nonzero x harmonic, diffusion gives
`||v||_2,||v_x||_2<=b exp(-nu t)/sqrt(2)`.
The parent projection and Cauchy--Schwarz consequently give

```text
|W_P(t)|<=a b^2 exp(-3nu t)/2,
integral_0^infinity |W_P|<=a b^2/(6nu),
R_kin(t)=a b^2 exp(-3nu t)/(3nu),
2 integral_s^t |W_P|<=R_kin(s)-R_kin(t).
```

This nonnegative original reserve crosses every seam. The previously
proved analytic actual-cubic allowance `a^2 b^2/(6nu^2)` is a different
payment; the kinetic allowance is not substituted for it.

### Reciprocal parents retain generated pressure

For `u0=(a sin y,b sin z,c sin x)`, all initially unobserved modes vanish
and canonical pressure starts at zero. Complete Fourier velocity jets
through order four retain every output and pressure through order three.
An independent symbolic calculation retains p1 and p2 explicitly:

```text
p1=-2abc cos x cos y cos z,
p2=-(2/3)abc[c sin(2x)cos y sin z+a sin x sin(2y)cos z
             +b cos x sin y sin(2z)]-6nu p1.
```

Only in the independent final parent projection is grad p3 omitted:
it is orthogonal to the divergence-free original sine vectors. The full
Fourier calculation does retain p3 and all other output components.
Write `S22=a^2 b^2+a^2 c^2+b^2 c^2`,
`S42=a^2 b^4+b^2 c^4+c^2 a^4` and `R=a^2 b^2 c^2`. The generic result is

```text
W_P(0)=0, W_P'(0)=-S22/4, W_P''(0)=2nu S22,
W_P'''(0)=(9/16)S42+(3/2)R-12nu^2 S22.
```

The first transfer depletes the original parents and fills hidden modes.
The positive three-parent correction `(3/2)R` disappears from the sum
of the three two-parent limits. At a=1,b=2,c=3,nu=1/10, the four work
jets are `0,-49/4,49/5,97773/400`, and the cycle correction is 54.
The exact kinetic ledger is checked at every available derivative order.
The initial mean cubic stretching g0 is zero, also checked independently.
These are jets of actual smooth unforced NS at its initial data; they do
not supply a uniform time window or establish indefinite renewal.

### A paid class with a nonzero third parent

A positive all-time analytic calibration allows reciprocal feedback,
within an original-datum small neighborhood of the triangular reference.
Use the inhomogeneous multi-index Sobolev norm
`||u||_Hm^2=sum_(|alpha|<=m)||partial^alpha u||_2^2` on this torus.
The reference's scalar equation commutes with x differentiation, and every
vertical derivative retains x harmonic one. After j y differentiations,
its source is the complete sum
`-sum_(r=1..j) binom(j,r) partial_y^r U partial_x partial_y^(j-r) v`.
Here `||partial_y^r U||_infinity<=a exp(-nu t)` for a>=0.
Scalar contraction and induction therefore give

```text
||partial_x^ell partial_y^j v||_2<=b exp(-nu t) P_j(L(t))/sqrt(2),
L(t)=a(1-exp(-nu t))/nu,
P_0=1, P_j(0)=0, P_j'=sum_(r=1..j) binom(j,r)P_(j-r),
P_1=L, P_2=L+L^2, P_3=L+3L^2+L^3,
P_4=L+7L^2+6L^3+L^4.
```

The scalar L2 differential inequality follows by pairing with the
differentiated field; the x harmonic contributes at least nu times its
norm. Vanishing norms are handled by a regularized norm and passage to
the limit. No unknown future bound on the reference is assumed.
Counting every multi-index, with no z derivatives, proves

```text
||u_ref(t)||_H4<=Q4 exp(-nu t),
Q4^2=5a^2/2+(b^2/2)sum_(j=0..4)(5-j)P_j(a/nu)^2.
```

Let d=u-u_ref be an actual smooth mean-zero solenoidal perturbation and
Y=||d||_H3^2. Pair every differentiated difference equation with the
corresponding derivative of d. Pressure gradients remain orthogonal.
The reference transport commutators and `d.grad u_ref` are bounded using
its H4 norm; the complete self-transport commutators use H3 embedding.
Thus there is a fixed torus/norm constant C3>0 such that

```text
Y'+2nu D4<=C3 ||u_ref||_H4 Y+C3 Y^(3/2),
D4=sum_(|alpha|<=3)||grad partial^alpha d||_2^2>=Y.
```

The last inequality is Poincare for the mean-zero fields. Put
`M=C3 Q4/nu` and choose the original perturbation so that
`sqrt(Y0)exp(M/2)<=nu/(2C3)`. Bootstrap within
`sqrt(Y)<nu/C3`: its self term is absorbed by nu D4, and comparison gives

```text
Y(t)<=Y0 exp[M(1-exp(-nu t))-nu t]<=Y0 exp(M)exp(-nu t).
```

This stays strictly inside the bootstrap region, supplies the H3
continuation bound and hence an all-time smooth unforced solution for
smooth initial data in this neighborhood. It is a standard perturbative
comparison around an explicitly controlled reference. The constants are
fixed by the original reference, initial perturbation, viscosity and torus;
they are not read off an unknown future NS flow. For the genuinely
three-dimensional third parent `d0=(0,epsilon sin z,0)`, `Y0=2epsilon^2`.
Its canonical pressure has `p1=-2a epsilon b cos x cos y cos z`, so the
reciprocal pressure interaction is present when a,b,epsilon are nonzero.
The threshold can be extremely small. It does not certify the larger
epsilon used in the numerical prefixes below.

This class pays the actual continuation bill. Write
`N=Q4+sqrt(Y0)exp(M/2)`; then `||u(t)||_H3<=N exp(-nu t/2)`.
For a fixed torus Sobolev constant C_emb,
`|mean omega^T grad(u) omega|<=C_emb ||u||_H3^3`, using
`||omega||_2=||grad u||_2` for solenoidal u. Consequently

```text
R_3D(t)=4 C_emb N^3 exp(-3nu t/2)/(3nu),
2 integral_s^t |mean omega^T grad(u) omega|<=R_3D(s)-R_3D(t).
```

R_3D is finite, nonnegative, decreasing and determined by the full original
datum. For the cyclic sine perturbation g0=0, it pays the joined
covariance/compatibility renewal of the preceding section directly.
For a general perturbation with nonzero g0, the sufficient finite-horizon
joined allowance can be `R_3D(0)+2|g0|T`. This is an actual cubic reserve,
not the kinetic hidden-energy ledger. The derivative recurrence, bootstrap,
continuous stability and spatial continuation are analytic arguments;
the program checks the polynomials and scalar comparison/reserve rates.
No new Lean certification of these continuous estimates is claimed.

Combining strict return on the triangular compact interval with continuous
dependence gives positive returned parent work for a sufficiently small
nonzero third parent as well. The margin can be fixed from the original
data. Let C_N be a fixed constant for
`||N(v,w)||_2<=C_N ||v||_H3 ||w||_H3`.
For `||d||_H3<=Q4`, expansion of the parent work gives
`|W_P(u_ref+d)-W_P(u_ref)|<=7C_N Q4^2 ||d||_H3`.
When a=b=A, in addition to the all-time threshold choose

```text
sqrt(Y0)exp(M/2)<=min(Q4,A^3/(1344 C_N Q4^2)).
```

Then the actual full three-parent flow has `W_P>=A^3/192` throughout
I/A and integrated work at least `A^2/1536`, while its original reserve
pays actual cubic stretching for all time. A nonzero epsilon satisfying
both original-data thresholds exists. This produces genuinely reciprocal,
globally paid actual flows with positive parent return. It proves no
all-time claim for an arbitrary third parent, nor the general mutually
amplifying-parent estimate.

### Three-dimensional numerical prefixes

Optional prefixes evolve the full three-velocity field from
`u0=(sin y,(1/20)sin z,sin x)`, nu=1/1000, with the integrating-factor
RK4 solver used in `reciprocal_parent_history.py`. Nonlinear products use
strict componentwise 2/3 dealiasing. Canonical pressure diagnostics use a
doubled grid retaining every quadratic pressure output of that Galerkin
state. A nontrivial polynomial probe checks the complete pressure L2 and
Hessian moments against the independent exact canonical calculation.
These observations do not remove pressure from the actual velocity
equation. Its Leray projection remains at every stage.

At the matched phase interval [47/16,49/16], all original parents together
receive positive nonlinear work. The hidden energy drops from about
0.46947 to 0.45829 while paying this return and viscosity.

| Velocity grid | Time step | Twice integrated parent work in the interval |
| --- | --- | --- |
| 32 cubed | 0.005 | 0.0105072475486 |
| 48 cubed | 0.005 | 0.0105073075457 |
| 48 cubed | 0.0025 | 0.0105073075455 |
| 64 cubed | 0.005 | 0.0105073086842 |

The 32-to-48 grid difference is about 6e-8 for that integrated work.
Halving the time step at 48 cubed changes sampled parent work by less
than 1e-12. The refined maximum kinetic-ledger error is below 1.6e-13.
The pressure-Hessian moment changes by about 2e-5 under the first spatial
refinement; it is more sensitive than the parent observation. Refining
48 to 64 cubed changes the integrated work by about 1.2e-9, sampled
parent work by less than 6.6e-9, and the pressure-Hessian moment by about
1.3e-6. These are
dealiased finite Galerkin prefixes and numerical convergence checks, not
continuum enclosures. In particular epsilon=1/20 is not certified to meet
the conservative all-time perturbation threshold.

Run exact checks and optional prefixes:

```sh
python3 -O labs/parent_return_history.py
python3 labs/parent_return_history.py --prefix --n 48 --dt 0.0025
```

This step retains a funded return with actual changing phases and pressure,
rather than assuming universal parent damping. It supplies a paid
perturbative reciprocal class but does not supply the arbitrary-data
reserve. The remaining obligation is to control derivative-level signed
renewal when mutually affecting parents leave every controlled reference
neighborhood, keeping original storage and spent resources across all
seams. No internal realization or impossibility theorem for the imported
forced blowup candidate follows from these periodic examples.

## Complete pair stretching and viscous reciprocal loops

[`paired_stretching_history.py`](paired_stretching_history.py) compares
complete unforced histories beginning with three cyclic parents. For
an observable O, define its mixed difference by inclusion-exclusion:

```text
Delta O = O(U123) - O(U12) - O(U23) - O(U31)
                  + O(U1) + O(U2) + O(U3).
```

Each Uij is the actual nonlinear evolution with its two original parents,
including the generated modes. Each single evolution is a heat-decaying
shear. The single terms vanish for cubic stretching but must remain for
enstrophy and dissipation. This is a difference of physical functionals,
including their interference, not the self-stretching of the pair-subtracted
velocity remainder. The latter already has independent sign obstructions.

Use normalized volume on the torus of period 2pi, and let

```text
Z = mean |grad u|^2 = mean |omega|^2,
D = mean |Delta u|^2 = mean |grad omega|^2,
G = mean omega^T grad(u) omega = <grad u,grad N(u)>,
Z' + 2nu D = 2G,          E' + 2nu Z = 0.
```

Here N is the complete Leray-corrected nonlinear source. Every exact
coefficient check retains all outputs. An independent actual-curl cubic
calculation checks G, alongside both physical balances. The complete
generated pressure is retained before taking observations. Neither a
pressure-free evolution nor an independently controlled parent is used.

### First mixed jet across scales and profiles

For `u0=(a sin(r0 y),b sin(r1 z),c sin(r2 x))` with positive integer
radii, complete canonical time jets give

```text
Delta G(0) = Delta G'(0) = Delta G''(0) = 0,
Delta G'''(0) = -(3/2)(a b c r0 r1 r2)^2.
```

The generic radius coefficient is checked separately with symbolic
rational functions. All earlier Leray projections remain. Only the final
pressure gradient can be discarded from that independent scalar
calculation, because its initial receiver is divergence-free. A separate
Gaussian-rational check retains that final pressure too.

Translation by half a period changes any one original sine parent's sign
without changing a mean observer. The observer is therefore even in each
amplitude. A mixed term using all three parents needs at least six
amplitude factors. Three time derivatives of cubic stretching have degree
at most six; viscosity lowers that degree. Thus only the displayed
sixth-degree term survives in the mixed third jet, at every viscosity.

The same phase balance extends the coefficient to mean-zero separated
profiles `u0=(f(y),g(z),h(x))`:

```text
Delta G'''(0) = -12 ||f'||_2^2 ||g'||_2^2 ||h'||_2^2.
```

At degree six there are exactly two Fourier inputs on each axis; spatial
mean forces their frequencies to be opposite. The generic radius symbol
therefore sums by Parseval into the three derivative norms. Finite Fourier
profiles suffice first; rapid Fourier decay extends the identity to smooth
profiles. This reasoning is analytic, not a Lean smooth-profile theorem.
The independent test uses

```text
f(y)=sin y+(1/2)cos(2y),
g(z)=2sin z-(1/3)cos(3z),
h(x)=(3/2)cos x-2sin(2x).
```

Their derivative norm squares are `1,5/2,73/8`; the mixed third derivative
is `-1095/4` at both `nu=0` and `nu=1/5`. The fourth velocity jet retains
over a thousand output modes and its canonical pressure source has 856
modes. A favorable initial jet does not establish a uniform time window.

### Complete viscous coefficient history

Now set `u0=alpha*(sin y,sin z,sin x)`, `nu>0`, and `tau=nu*t`.
Write `u=nu*sum_m (alpha/nu)^m U_m(tau)`. The finite amplitude derivatives
are determined by the full Duhamel recurrence

```text
U1(tau)=exp(tau Delta) U1(0),
Um(tau)=integral_0^tau exp[(tau-r)Delta]
                         sum_(i+j=m) -P div(Ui tensor Uj)(r) dr.
```

The checker integrates this recurrence exactly as exponential polynomials,
including resonant heat rates. It retains 264 velocity outputs and 212
pressure outputs at degree seven. There is no time discretization or
frequency truncation in these coefficients. Identifying them with
continuous solution-map derivatives is analytic; they are not an exact
finite-amplitude evolution or a bound on its remainder.

The first mixed stretching coefficient has degree six:

```text
Delta G(t;alpha) = alpha^6/nu^3 gamma6(nu*t) + O_(nu,t)(alpha^8),
gamma6(tau)=(3/32)exp(-4tau) H(tau),
H(tau)=1-2tau+(2tau^2-1)exp(-2tau).
```

Since `exp(2tau)>=1+2tau`, its derivative obeys

```text
H'=-2+2exp(-2tau)(1+2tau-2tau^2) <= -4tau^2 exp(-2tau) <= 0.
```

Together with `H(0)=0`, this proves `gamma6<=0` throughout the entire
nonnegative viscous clock. Its primitive from the original time is

```text
I6(tau)=-5/2304
       +(3tau/64-3/256)exp(-4tau)
       +(1/72-tau/96-tau^2/32)exp(-6tau),
I6(0)=0,        I6'=gamma6,
2 integral_0^infinity gamma6 = -5/1152.
```

`MettapediaNS.PairCycleHistory` kernel-checks these explicit scalar
derivatives, the sign for every nonnegative time, and payment on every
interval `0<=s<=t` using `I6(t)-I6(s)`. It does not certify the continuous
Fourier identification or the full NS remainder. The improper integral
value above is an analytic consequence of the checked primitive and
exponential decay; the exact checker also evaluates it rationally.

### The complete signed diffusion comparison

The sixth-degree mixed enstrophy and dissipation coefficients are

```text
Z6=(9/256)exp(-2tau)+(3tau/16-3tau^2/8)exp(-4tau)
   +(-9/256-21tau/64-9tau^2/32)exp(-6tau),
D6=(9/256)exp(-2tau)+(9tau/16-3tau^2/4)exp(-4tau)
   +(-9/256-45tau/64-21tau^2/32)exp(-6tau),
Z6' + 2D6 = 2gamma6.
```

Lean certifies this exact balance, `Z6(0)=0`, and `Z6(2)>0`. The last
inequality can be checked using `exp(4)>=40`:

```text
Z6(2)=exp(-4)[9/256-(9/8)exp(-4)-(465/256)exp(-8)] > 0.
```

D6 is a difference of complete dissipations. Its sign cannot be borrowed
from the nonnegativity of each flow's dissipation. Negative stretching
alone therefore does not order the full enstrophy histories.

This also supplies an analytic counterexample to the stronger assertion
`Z(U123)<=sum_pairs Z(Uij)-sum_singles Z(Ui)` for actual small unforced
data. At fixed `nu>0` and time `2/nu`, the mixed difference is
`alpha^6/nu^4 Z6(2)+O_nu(alpha^8)>0` for sufficiently small nonzero alpha.
To justify the passage without a future solution bound, use the mild NS
equation on `C([0,2/nu],H^s)`, `s>5/2`. The heat-gradient estimate and
the Sobolev product bound give a bilinear norm at most
`2 C_s sqrt(T/nu)`. The Duhamel coefficients obey the Catalan majorant
`||Um||<=Catalan_(m-1) L^(m-1)||U1||^m`, for this finite window and
`L=2 C_s sqrt(T/nu)`. A sufficiently small original amplitude gives
absolute convergence and an analytic solution map. Mean quadratic/cubic
observers are continuous there. Inclusion-exclusion and translation
symmetry remove degrees two and four and all odd degrees. This proves the
fixed-time remainder assertion. Standard small-data regularity additionally
permits choosing these examples globally regular. This continuous argument
is analytic here, not a new Lean existence or solution-map theorem.

### The next loop has positive work and a finite initial allowance

The complete eighth-degree mixed stretching coefficient gamma8 has

```text
gamma8^(j)(0)=0 for j<5,        gamma8^(5)(0)=473/20,
2 integral_0^infinity gamma8 = 541543/737280000 > 0.
```

The first complete loop depletes stretching; the next cannot be paid
by assigning each loop a nonpositive sign. This is an exact coefficient
calculation, not a statement that the full stretching difference is
positive for small alpha. Summing the higher coefficients requires an
additional bound.

Each computed coefficient has an original-amplitude absolute reserve.
If `gamma_m(tau)=sum c_(lambda,j) tau^j exp(-lambda*tau)`, define

```text
Rm(tau)=2 sum |c_(lambda,j)| exp(-lambda*tau)
                  sum_(ell=0..j) j! tau^ell / [ell! lambda^(j-ell+1)],
Rm>=0,       -Rm'=2 sum |c_(lambda,j)| tau^j exp(-lambda*tau)
                          >=2|gamma_m(tau)|.
```

The checker verifies both the exact tail derivative and the finite initial
value. Physical reserves scale as `alpha^m nu^(2-m) Rm(nu*t)`. In
particular `R6(0)=121/1152`, `R8(0)=33767731/245760000`. The same reserve
cancels across every compatible seam; a later segment does not receive
another original allowance. These finite coefficient reserves can overpay
signed cancellations. Convergence and finite payment of the entire
renewal sequence, outside small-data perturbation theory, remain open.

### Full nonlinear prefixes test the sign beyond the first loop

For the full datum `(sin y,sin z,sin x)`, `nu=1/5`, complete dealiased
prefixes change the mixed stretching sign. At `t=5.5`,

| Grid | Time step | G(full)-3G(pair) |
| --- | --- | --- |
| 24^3 | 0.0125 | 0.0019440249184904 |
| 32^3 | 0.0125 | 0.0019440249184858 |
| 32^3 | 0.00625 | 0.0019440249186963 |
| 48^3 | 0.00625 | 0.0019440249186963 |

The full stretching at this time is about `0.00309980`; a single pair
contributes about `0.000385259`. The pair flow is evolved throughout,
including its scalar gradients. The doubled-time resolution ledger error
is below `7.9e-11`; the 48-grid high-frequency enstrophy fraction over the
bounded prefix is below `1e-19`. A separate exact Fourier probe checks the
canonical RHS and literal curl observer used by the numerical tool.
These are convergence diagnostics, not validated continuum error bounds.
No continuum sign theorem or arbitrary-data payment is inferred from them.

```sh
python3 -O labs/paired_stretching_history.py
python3 labs/paired_stretching_history.py --prefix --n 32 --nu 0.2 --dt 0.00625 --final 6
```

The named open estimate remains the signed physical renewal budget of
`JointCubicRenewal`, with a reserve fixed by the full original datum,
viscosity and prescribed horizon before all compatible prefixes. These
cyclic data have zero mean original cubic label, as do their pair limits.
Mass conservation of the passive label identifies the mixed joined
chi/E renewal cost with `2 integral Delta G`. This periodic calibration
therefore retains the literal physical stretching required by continuation;
it supplies no whole-space finite-energy lift by itself.

A bounded next candidate is cumulative mixed depletion for the cyclic
class: `2 integral_0^t Delta G<=0` for every smooth prefix. Pointwise
sign reversal alone does not refute this history assertion. If proved,
the already paid triangular pair histories and the full enstrophy balance
would give a finite original-datum enstrophy bound for the cyclic class,
even with strong mutual feedback. For equal amplitude alpha, the pair
allowance `alpha^4/(6nu^2)` would give the explicit bound
`Z(full)<=3alpha^2/2+alpha^4/(2nu^2)` on every smooth prefix. This is the
actual periodic enstrophy continuation consumer. The history assertion
is an open candidate, not a theorem
or a claim for arbitrary original data. Its first test is the complete
signed cumulative ledger, followed by larger Reynolds ratios and different
profiles and scales. A failed zero-allowance bound would require a finite
original-datum correction rather than a fresh allowance at every renewal.
The subsequent unequal-parent tests below give positive cumulative mixed
cost, so that extension of the zero-allowance candidate is not supported.

The current tests require that a proposed correction retain changing geometry,
pressure, diffusion and previously spent resources. They neither realize
the imported forced blowup construction internally nor exclude every
possible unforced analogue of its mechanism.

## First reciprocal history at arbitrary parent scales

`anisotropic_pair_history.py` extends the preceding complete sixth-degree
history to unequal parent frequencies and separated profiles. The physical
observation is still the difference between the full cubic stretching and
the three complete two-parent stretchings. It is not the cubic of a
subtracted velocity, and no generated modes are discarded.

For initial velocity

```text
u0 = alpha (sin(p y), sin(q z), sin(r x)),
a=p^2, b=q^2, c=r^2, S=a+b+c, tau=nu*t,
```

the first mixed stretching coefficient is
`alpha^6/nu^3 * gamma6(a,b,c,tau)`. Frequencies are positive integers on
the normalized `2*pi` torus; the scalar formula and sign hold for every
positive real `a,b,c`. The coefficient includes all compatible generation
trees at this amplitude order. It does not represent the full solution
at finite amplitude.

### The signed formula

Put `k=2S/3` and define the degree-three Taylor remainder

```text
R(k,d,t) = (1-kt) exp(dt) - 1 - (d-k)t
           - (d^2-2kd)t^2/2 - (d^3-3kd^2)t^3/6,
w(a,b,c) = 3ab^2 / (32c^2 S).

gamma6 = exp(-2St) [ -abc*t^3/4
          + w(a,b,c) R(k,2c,t)
          + w(b,c,a) R(k,2a,t)
          + w(c,a,b) R(k,2b,t) ].
```

The fourth derivative of `R` is
`d^3(d-4k-kdt)exp(dt)`. It is nonpositive when
`k,d,t>=0` and `d<=4k`. The first four initial values through derivative
three are zero, so successive integration gives `R<=0`.
Every weight above is positive and every rate satisfies that condition.
Therefore

```text
gamma6(a,b,c,t) <= -(abc/4) t^3 exp(-2St),
gamma6(a,b,c,t) < 0 for t>0,
2 integral_0^infinity gamma6 <= -3abc/(16S^4) < 0.
```

The finite-time sign, quantitative rate bound, all-interval payment,
finite nonnegative sums and agreement with the preceding unit-frequency
formula are kernel-certified in `MettapediaNS.AnisotropicCycleHistory`.
The improper-integral evaluation displayed here is analytic. The scalar
proof does not assert its identification with a continuous PDE solution.

### Complete physical calculation and independent checks

The symbolic recurrence works over exact rational functions in `a,b,c`.
In base Fourier coordinates let `v_i=r_i u_i`, with
`(r_1^2,r_2^2,r_3^2)=(c,a,b)`. Advection has the ordinary integer-wavevector
form; the Leray projection uses `diag(c,a,b)` and physical energy uses
`diag(1/c,1/a,1/b)`. The mixed coefficient is multiplied by `abc` to
restore unit physical initial amplitudes. This uses the fact that its
amplitude degree is exactly two in each parent, as also checked in the
independent physical recurrence.

All Duhamel coefficients through degree five are retained, with exact
resonant heat convolutions. The generic counts are
`6,12,26,48,98` velocity modes and `0,0,8,24,68` pressure modes.
The checker verifies solenoidality, reality, the complete projected
equations, zero original generated data, the kinetic balance and the
enstrophy balance. Subtracting the three separately evolved pairs gives
the formula above and the signed identity `Z6'+2D6=2gamma6`.
`D6` is a difference of dissipation histories and may have either sign.

Independent rational runs evaluate literal `mean(omega^T grad(u) omega)`
and check both energy ledgers. They include equal-frequency resonances,
cyclic reorderings and well-separated frequencies `(1,2,17)`, `(1,17,2)`
and `(1,19,20)`. Examples of exact all-time integrals are

| Parent frequencies | `2 integral gamma6` |
| --- | --- |
| `(1,1,1)` | `-5/1152` |
| `(1,1,2)` | `-13/11520` |
| `(1,2,3)` | `-922149/2596921600` |
| `(1,3,2)` | `-848061/2596921600` |
| `(2,2,2)` | `-5/4608` |

Reversing the cyclic scale order changes the response; its sign survives.
The final formula has only positive-denominator factors for positive
`a,b,c`. Continuity of the finite Duhamel recurrence covers coincident
rates; the rational tests also compute those resonances directly.

The integrated magnitude has the sharp scale-uniform bound

```text
0 < -2 integral_0^infinity gamma6(a,b,c,t) dt
  <= 5 / [1152 min(a,b,c)].
```

For `a,b,c>=1`, write the exact twice-integral as `N/D`, with `N<0`
and `D>0`. Substitution `a=1+x,b=1+y,c=1+z` in `5D+1152N`
gives a polynomial with 273 nonnegative coefficients and zero constant
term. The checker verifies that exact identity. Homogeneity of degree
minus one extends it to every positive scale triple. Equality holds at
equal scales. This finite polynomial and improper-integral argument is
analytic/exact-symbolic here, not an additional Lean theorem.

### General separated profiles

Let `f,g,h` be real, mean-zero, smooth one-dimensional periodic profiles.
Write `F_p^2=4|f_hat(p)|^2`, and similarly for `G_q,H_r`, for positive
frequencies. For initial data `alpha*(f(y),g(z),h(x))`, the sixth mixed
coefficient is

```text
gamma6[f,g,h](t)
  = sum_(p,q,r>=1) F_p^2 G_q^2 H_r^2 gamma6(p^2,q^2,r^2,t) <= 0.
```

The quantitative bound also separates into the three original heat
histories. With normalized one-dimensional measure, let
`L_f(t)=||d/dy exp(t*d_y^2)f||_2^2`, and likewise for `g,h`.
Since `sum p^2 F_p^2 exp(-2p^2t)=2L_f(t)`, it gives

```text
gamma6[f,g,h](t) <= -2t^3 L_f(t)L_g(t)L_h(t).
```

This is an explicit first-cycle depletion measured by the heat-evolved
parent gradients. It does not replace those parents by heat flows in the
full nonlinear problem: their complete generated corrections are already
included at this coefficient order, and the later orders remain to be paid.

The integrated magnitude bound gives, for profiles on the `2*pi` torus,

```text
0 <= -2 integral_0^infinity gamma6[f,g,h]
  <= (5/144) ||f||_2^2 ||g||_2^2 ||h||_2^2.
```

For physical initial amplitude `alpha` and viscosity `nu`, multiply this
allowance by `alpha^6/nu^4`. It bounds this complete first interaction
order from the original parent energies. It supplies no energy-only
allowance for the complete nonlinear flow or for arbitrary 3D data.

Pair subtraction cancels terms that omit an original parent. Each
remaining spatial mean needs at least two inputs on each coordinate
axis: one nonzero Fourier input cannot have zero net frequency there.
At total degree six there are exactly two on each axis, and their
frequencies must be opposite. Their phases therefore cancel, leaving
the nonnegative squared spectral amplitudes above. No separate amplitude
parity is assumed for general multiharmonic profiles; it can fail at
higher orders.

This gives the identity first for Fourier polynomials. For smooth
profiles, truncate in a fixed Sobolev space above the algebra and
first-derivative embedding threshold. Each finite-order Duhamel map
and the cubic observation are continuous on every finite time window.
The polynomial identities pass to the smooth limit. All terms in the
displayed spectral sum have the same sign, and the truncation limit is
the continuous finite-order coefficient. These PDE and limiting
arguments are analytic here, not Lean-certified.

The exact fixture

```text
f = sin(y) + sin(2y)/2,
g = 2sin(z) - sin(3z)/3,
h = 3sin(x)/2 - 2sin(2x)
```

retains `12,48,156,424,1028` velocity modes through degree five.
The literal complete cubic history equals the predicted eight-triple
spectral sum exactly, including its whole viscous time dependence.
Its twice-integrated coefficient is
`-93960318393654866177/1481606133104691449856`.

Run the symbolic, rational and multiharmonic checks with

```sh
python3 -O labs/anisotropic_pair_history.py
python3 -O labs/paired_stretching_history.py
```

### What this pays, and what it leaves open

This proves a uniform favorable first interaction law across an unbounded
family of scales and profiles. It uses viscosity, the exact projection,
evolving generated modes and their common original clock. It strengthens
the geometric-history mechanism without assuming pancakes remain frozen
or that scales remain comparable.

It does not prove all-order mixed depletion. Even the unit-frequency
eighth coefficient has positive integrated stretching, as checked above.
The next physical obligation remains a reserve or cumulative comparison
for the complete reciprocal history, allowing later positive bursts and
tracking their earlier payment. Its constants must be fixed by the full
original datum and viscosity. Summability or another nonlinear control of
all higher orders is missing. Extending a cyclic-family result to arbitrary
divergence-free data is a further obligation, and these periodic examples
alone supply no whole-space finite-energy theorem.

## Positive mixed renewal with a finite original allowance

There are two distinct checks here: a numerical test within the preceding
three-axis cyclic class, and an analytic example in a different, globally
smooth 2.5D class. Neither refutes a finite full-datum continuation budget.

### Unequal cyclic parents: numerical cumulative sign reversal

`paired_stretching_history.py --unequal-prefix` evolves the full flow and
each of its three pairs separately. No equal-amplitude symmetry is used
to replace all pairs by three copies of one. For

```text
u0 = (sin y, sin z, 5sin x), nu=1/5,
```

the cumulative mixed stretching first becomes negative, then positive.
At time two the refinements give

| Grid | Time step | `2 integral_0^2 Delta G` |
| --- | --- | --- |
| `24^3` | `0.005` | `0.06094765143463` |
| `32^3` | `0.005` | `0.06099241335379` |
| `32^3` | `0.0025` | `0.06099241384804` |
| `48^3` | `0.0025` | `0.06099249989219` |

The last spatial difference is about `8.60e-8`, and the time-step
difference at `32^3` is about `4.94e-10`. At `48^3` the largest sampled
enstrophy fraction above 80% of the dealiased cutoff is `1.18e-11`;
the final mixed enstrophy ledger residual is `3.13e-10`.
These are refined numerical signs, not a continuum error enclosure.

Weaker parents `(epsilon sin y, epsilon sin z, 5sin x)` give positive
cumulative cost as well. At `32^3`, step `0.005`, time two, the cost divided
by `epsilon^4` is `0.1866641904` for `epsilon=1/2` and `0.2388825922` for
`epsilon=1/4`. These observations do not prove the sign of the limiting
coefficient at zero epsilon. They identify a concrete perturbative test
around a known decaying shear for further analytic work.

```sh
python3 -O labs/paired_stretching_history.py --unequal-prefix \
  --amplitudes 1 1 5 --n 48 --nu 0.2 --dt 0.0025 --final 2
```

The favorable sixth-degree law above is intact. Higher complete
interactions can reverse the cumulative sign in these numerical full
histories. This tests the unequal-parent extension of the comparison;
it does not settle the equal-amplitude special case or any bound with a
finite full-datum allowance.

### An analytic, globally smooth paid example

On the same torus, take real `a,b,c`, viscosity `nu>0`, and `sigma=+1` or
`-1`. Set

```text
u_h(t) = exp(-nu*t) (a sin y, b sin x),
p(t) = ab exp(-2nu*t) cos x cos y,
w0 = c(cos x + sigma cos y),
w_t + u_h.grad(w) = nu*Delta(w),
u = (u_h,w), independent of z.
```

The horizontal advection cancels the displayed pressure gradient exactly;
the horizontal components obey their heat equations. The vertical
component solves a linear advection-diffusion equation with smooth,
explicitly decaying drift. Higher Sobolev energy estimates, or its
stochastic representation, give a smooth solution for every time.
This constructs actual unforced 3D NS flows, in the restricted 2.5D class.

Use the three original parents
`(a sin y,0,0)`, `(0,b sin x,0)`, `(0,0,w0)` and their complete pair flows.
The full horizontal pair has zero stretching, while the other two pairs
advect the same scalar by a single shear. For each full or pair flow,

```text
G(t) = -exp(-nu*t) mean[(a cos y+b cos x) w_x w_y],
```

with the omitted horizontal amplitude set to zero for a pair. Their
initial cubic means vanish. Differentiating the actual equations gives

```text
G_full'(0) = c^2(a+sigma*b)^2/4,
sum_pairs G_pair'(0) = c^2(a^2+b^2)/4,
Delta G'(0) = sigma*ab*c^2/2,
2 integral_0^t Delta G = sigma*ab*c^2*t^2/2 + O(t^3).
```

Thus `a,b>0`, `c!=0`, `sigma=+1` gives strictly positive mixed cumulative
stretching on an actual short time interval, for every positive viscosity.
It refutes a zero-allowance comparison over arbitrary parent geometries.
It is not an analytic counterexample within the preceding three-axis
separated-profile class: here the vertical receiver depends on both `x`
and `y`. For `a=b` and `sigma=-1`, that receiver follows the horizontal
streamfunction and simply diffuses. The plus phase crosses the streamlines
and is deformed. Both phase choices have the same initial energy and
horizontal pressure; their joint placement changes the stretching.

The lab checks the complete pressure, horizontal NS right-hand side and
literal vorticity-stretching derivative in 18 exact rational fixtures,
including both phases, a reversed parent sign and three viscosities.
The general identities follow by differentiating the displayed scalar
equation and integrating periodic derivatives. The derivative's viscous
terms cancel because the original cubic means are zero. The time-interval
and global-solution arguments here are analytic, not Lean-certified.

### The original datum pays every compatible interval

Put `L=|a|+|b|` and `Z_w=mean(|grad w|^2)`. The exact scalar energy identity,
the strain bound and periodic Poincare give

```text
Z_w' + 2nu mean(|Delta w|^2) = 2G,
2|G| <= L exp(-nu*t) Z_w,
Z_w(t) <= c^2 exp[(L/nu)(1-exp(-nu*t))-2nu*t].
```

In particular the full gradient energy obeys

```text
Z_full(t) <= [(a^2+b^2)/2 + c^2 exp(L/nu)] exp(-2nu*t).
```

This is an explicit all-time continuation bound for the stated family,
with no smallness assumption on its amplitudes. The stochastic flow uses
the prescribed physical horizontal drift and diffusivity; it introduces
no force or independently chosen fluid control.
More explicitly, for fixed terminal time `t` and position `x`, solve
`dX_s=-u_h(t-s,X_s)ds+sqrt(2nu)dW_s`, `X_0=x`, on `0<=s<=t`.
Then `w(t,x)=E[w0(X_t)]`. This is the backward representation of the
actual scalar equation. The energy bound is obtained from that equation,
not by identifying an independently optimized bridge with NS.

For a compatible mixed-history interval use

```text
K = c^2/(3nu) [ L exp(L/nu)
                + |a| exp(|a|/nu) + |b| exp(|b|/nu) ],
R(t) = K exp(-3nu*t).
```

The full-flow and two single-shear bounds give `-R'(t)>=2|Delta G(t)|`.
Consequently `R>=0` and
`2 integral_s^t Delta G <= R(s)-R(t)` for every `0<=s<=t`.
This is one decreasing reserve fixed by the original data, not a new
allowance granted after every seam. It pays the positive burst above.
The same estimates allow any smooth mean-zero vertical initial pattern:
replace `c^2` throughout the bounds and reserve by its original gradient
energy `Z_w(0)`. The special two-mode pattern is used only to exhibit
the two opposite signs exactly.

The decisive special property is explicit control of the complete
horizontal parent strain: its integral is at most `L/(2nu)`. The parents
do interact through advection and pressure, but their joint horizontal
motion decays autonomously. The next section removes this restriction
within the planar class, while keeping three-dimensional feedback as
an explicit open source cost.

## A strain-paying reserve for interacting planar parents

The [exact checker](planar_parent_reserve.py) and
`MettapediaNS.PlanarParentReserve` connect a nonlinear parent reserve to
the actual mean/fluctuation split of NS. The positive result applies to
all smooth planar parents, rather than only Laplacian eigenfields.
The reserve's failure under genuine three-dimensional feedback identifies
a specific signed source bill; it does not refute an allowance depending
on the full initial fluid.

All spatial integrals here are normalized means on the `2*pi` torus.
Let `v=(v1,v2)` be a smooth mean-zero two-dimensional NS velocity,
`omega=partial_x v2-partial_y v1`, and put

```text
Z = ||omega||_2^2,  Y = ||grad omega||_2^2,  W = ||Delta omega||_2^2,
q = ||grad v||_{L-infinity,Frobenius},  nu > 0.
```

Mean zero is preserved; a constant mean velocity can also be removed
by a Galilean translation. Poincare gives `0<=Z<=Y<=W`.
Vorticity has no stretching source in this planar equation:

```text
Z' = -2nu Y,
Y' = -2nu W + 2T,
T = -mean sum_ij (partial_i omega)(partial_i v_j)(partial_j omega).
```

The following elementary estimates fix generous constants explicitly:

```text
||f||_4^2 <= 16 ||f||_2 ||grad f||_2       (mean-zero vector f on T2),
q <= 4 sqrt(W),
2|T| <= nu W + (256/nu) ZY.
```

For the first inequality, the one-dimensional fundamental theorem gives
`sup_x |f(x,y)|^2 <= mean_x |f|^2 + 4pi mean_x |f||partial_x f|`,
and similarly in `y`. Multiply these two bounds and average to get
`||f||_4^2 <= ||f||_2^2 + 4pi ||f||_2 ||grad f||_2`.
Poincare and `1+4pi<16` finish the estimate. This argument applies to
`f=grad omega`, for which `||grad f||_2^2=W` by Parseval.
For the second inequality, the Fourier multiplier from `omega` to
`grad v` has Frobenius norm one. Cauchy--Schwarz bounds its absolute
Fourier sum by `sqrt(sum_{k!=0}|k|^-4) sqrt(W)`. There are `8n` lattice
points with `max(|k1|,|k2|)=n`; hence the sum is at most
`8 sum n^-3 <= 12 < 16`. Finally `||grad v||_2=sqrt(Z)` and Young's
inequality give the bound on `T`. No future norm is assumed.

### A nonlinear original-state reserve

Define

```text
r(Z,Y) = (8/nu) sqrt(Y) exp(64 Z/nu^2) >= 0.
```

Where `Y>0`, the actual chain rule and the preceding physical estimates
give

```text
r'/r = Y'/(2Y) + 64 Z'/nu^2
      <= -nu W/(2Y) - (128/nu)(Y-Z),
-r' >= 4 exp(64 Z/nu^2) W/sqrt(Y) >= 4 sqrt(W) >= q.
```

Thus the same original reserve pays every compatible interval:
`integral_s^t q <= r(s)-r(t) <= r(s)`. No independent heat evolution,
fixed parent orientation or smallness assumption enters this estimate.
The exponential factor spends the parent vorticity norm to pay possible
growth of its gradient; it does not assume that `Y` decreases.
If `Y` reaches zero, the unforced planar velocity is zero and remains
zero. The estimate extends by continuity to that endpoint and beyond.
It first applies on every smooth prefix. The finite strain integral
then supplies ordinary smooth continuation of the planar parent.

The checker includes
`psi=cos x+(1/2)cos(2y)+(1/3)cos(x+2y)`, `v=(-psi_y,psi_x)`.
Its initial values are `Z=35/9`, `Y=139/9`, `W=605/9`, and `T=1`.
At `nu=1/100`, `Y'=59/90>0`. The parent vorticity advection is nonzero;
this is not an autonomously heat-decaying flow. The reserve still pays.

### Composition with the vertical receiver

Let `theta` solve the actual scalar equation
`theta_t+v.grad theta=nu Delta theta` from arbitrary smooth mean-zero
data. Then `u=(v1,v2,theta)`, independent of `z`, solves unforced 3D NS
with the parent's canonical pressure. The vertical component does not
feed the parent because its vertical derivatives vanish identically.
Set

```text
E = ||grad theta||_2^2, D = ||Delta theta||_2^2,
G = -mean sum_ij (partial_i theta)(partial_i v_j)(partial_j theta).
E' = 2G - 2nu D,     |G| <= q E.
V = E (exp(2r)-1) >= 0.
```

`G` is also the full physical cubic vorticity stretching of this 2.5D
flow: the horizontal parent enstrophy equation has no cubic production.
Direct differentiation, keeping the diffusion, gives

```text
V' + 2|G| + 2nu (exp(2r)-1)D <= 0,
2 integral_s^t |G| <= V(s)-V(t).
```

This is a compositional payment, using the parent's remaining reserve
and the receiver's actual gradient energy. It is never reset at a seam.
Also `(E exp(2r))' <= -2nu E exp(2r)`, since `D>=E`. Consequently

```text
||grad u(t)||_2^2 <= [Z(0)+E(0)exp(2r(0))] exp(-2nu t).
```

The constants can be large but are finite from the original smooth data
and viscosity. Global smooth realization follows by the planar strain
bound and the linear scalar equation. These are analytic statements;
they are not whole-space finite-energy consequences of a periodic lift.

The physical stochastic representation uses the actual parent drift:
for fixed `t,x`, solve `dX_s=-v(t-s,X_s)ds+sqrt(2nu)dB_s`, `X_0=x`.
Then `omega(t,x)=E[omega0(X_t)]` and `theta(t,x)=E[theta0(X_t)]`.
The same backward process transports both labels. Its spatial Jacobian
is bounded by `exp(integral_0^t q)<=exp(r(0))`. This identifies the
stochastic histories for this class. Differentiating the scalar formula
therefore gives the additional direct continuation bound

```text
||curl u(t)||_infty <= ||omega0||_infty
                      + ||grad theta0||_infty exp(r(0)).
```

It holds on every smooth prefix with one original-datum constant, so its
finite-horizon time integral satisfies the vorticity continuation
criterion. This is an analytic physical bridge, not an optimization over
independent fluid forces or a general Schroedinger-bridge identification.

### The complete three-dimensional replenishment defect

For any smooth 3D periodic NS prefix, average in `z`, write
`bar u=(v1,v2,theta)` and `a=u-bar u`. The Reynolds tensor and sources are

```text
R_ij = average_z(a_i a_j),
F_h = -div_h R_hh,  F_theta = -div_h R_zh,
F = curl_h F_h.
```

The parent momentum retains `-grad_h average_z p`; taking its curl
removes that gradient exactly. The mean equations are

```text
omega_t+v.grad omega = nu Delta omega+F,
theta_t+v.grad theta = nu Delta theta+F_theta.
A = <omega,F>, B = <grad omega,grad F>, C = <grad theta,grad F_theta>.
Z'=-2nu Y+2A,   Y'<=-nu W+(256/nu)ZY+2B,
E'=2G-2nu D+2C.
```

The same functions now satisfy, wherever `Y>0`,

```text
J = r [B/Y+128 A/nu^2],
r'+q <= J,
V'+2|G|+2nu(exp(2r)-1)D
  <= 2(exp(2r)-1)C + 2E exp(2r)J.
```

The signed `A`, `B` and `C` are literal actual-fluid work, not freely
chosen controls. Norms of smooth parent fields make `r` locally
absolutely continuous. On the zero-vorticity set its derivative is zero
almost everywhere; the source formulas may be defined as zero there.
The pointwise positive-`Y` theorem and this analytic almost-everywhere
passage must be distinguished.

The unresolved field also retains its complete enstrophy ledger. If
`E_a=||grad a||_2^2`, `D_a=||Delta a||_2^2` and `G_full` is the actual
full 3D stretching, orthogonality of the mean split gives

```text
E_a'/2 + nu D_a = G_full-G-A-C.
```

There is no assumption that this term or the replenishment bill has a
favorable sign. A sufficient global reserve still needs to pay their
joint history from the full original datum. The mean reserve by itself
does not control `E_a` or the full 3D continuation criterion.

An exact initial fixture makes the failure of unconditional decrease
visible. Take horizontal parent coefficients at `p=(1,2,0)` equal to
`i*(-1/5,1/10,0)`, vertical receiver `2sin x`, and hidden cosine modes
`epsilon*(1,-1,0)cos(x+y+z)` and
`sigma*epsilon*(1,1,1)cos(-y+z)`, `sigma=+1` or `-1`.
All fields are real and solenoidal. The full canonical NS source gives

```text
Z=1/2, Y=5/2, W=25/2, E=2, T=0, C=0,
A=2 sigma epsilon^2, B=10 sigma epsilon^2,
J/r=sigma epsilon^2 (4+256/nu^2).
```

At `nu=1/5`, `epsilon=1`, the actual `r'/r` is `4803` for the plus
phase and `-8005` for the minus phase. Thus the same unforced initial
energy can produce opposite reserve derivatives; the plus phase really
increases the candidate parent reserve on a smooth short-time interval.
This refutes dropping `J`, not a corrected joint reserve. Adding
`2sin(x+2y)` to the receiver gives the independent nonzero term
`C=-(5/2)sigma` and `E=12`. The checker verifies both source terms,
the exact mean PDE, full and fluctuation enstrophy balances, and equal
opposite kinetic transfers between mean and hidden modes.

The checker has 36 Gaussian-rational fixtures and symbolic derivative
identities; it runs with `python3 -O labs/planar_parent_reserve.py`.
Every nonlinear output is retained. These are exact initial PDE checks,
not a finite-mode evolution, numerical history enclosure or a recurrence
theorem. Scalar calculus, absorption and common-reserve interval payment
are Lean-certified under their displayed hypotheses. The periodic
functional inequalities, stochastic representation, full PDE passage
and zero-set argument above remain analytic.

## Full-energy Bellman payment and the high-strain remainder

The [joint-accounting checker](joint_parent_reserve.py) tests a positive
hidden-energy correction to the planar reserve and verifies a separate
Bellman payment from the complete kinetic energy. The latter applies
to arbitrary unforced 3D flows on their smooth prefixes, for observations
with a fixed finite norm bound. It does not supply the unresolved
high-strain estimate or global regularity.

### A tested adaptive hidden-energy correction

Use the preceding mean/fluctuation split and its planar function
`V(Z,Y,E)=E(exp(2r(Z,Y))-1)`. For the mean frequencies in the explicit
fixture, define positive weights and the joint state functional

```text
c_h = 5 V_Z + 25 V_Y, c_z = V_E,
K_h = mean |a_h|^2, K_z = mean |a_z|^2,
Phi = V + c_h K_h + c_z K_z >= 0.
```

The numbers `5` and `1` are the fixed original squared parent and
receiver frequencies. At this mean field the velocity cotangent of
`V` is `(2c_h v,2c_z theta)`, so its Reynolds work matches the negative
mean-strain work in the hidden energy. This is a motivated cancellation,
not a choice of independent forces. However, the pressure work and
the derivatives of `c_h,c_z` remain.

Take the preceding two-hidden-mode fixture with `nu=8`, put
`x=epsilon^2`, and write `S=exp(2r)` at its initial mean. Exact full NS
derivatives give

```text
Z=1/2, Y=5/2, E=2, r=sqrt(5/2)exp(1/2),
Z'=-40+4sigma x, Y'=-200+20sigma x, E'=-32,
K_h=2x, K_z=x/2,
K_h'=-(80+7sigma/10)x, K_z'=-(16+sigma/10)x.
```

The separate horizontal and vertical pressure works are `sigma x/10`
and `-sigma x/10`. Their sum is zero in unweighted kinetic energy,
but their weighted sum need not vanish. The cubic hidden self-work
is zero on this particular initial support, verified by the full source.
Differentiating both adaptive weights produces the quartic coefficient

```text
[epsilon^4] Phi' = sigma S r (1280r+328).
```

For `sigma=+1`, `epsilon=4`, the entire derivative is positive, including
diffusion, pressure and lower orders. Substitution `r=1+r1`, `S=1+S1`
leaves a polynomial with strictly positive rational coefficients; the
actual values satisfy `r>1`, `S>1`. No floating transcendental evaluation
is needed. Local smooth existence turns this into a positive interval
for an actual unforced flow. Thus this specific positive joint correction
is not a decreasing reserve. Finite bursts, a further correction and a
full-datum allowance are not refuted. Freezing the weights would have
removed the decisive quartic term incorrectly.

### Payment from the complete energy account

Let `Ekin(t)=||u(t)||_2^2`, `d(t)=||grad u(t)||_2^2`, and fix a prescribed
horizon `H`. On every actual smooth unforced prefix,
`Ekin'=-2nu d`. Unlike the observed parent's energy, this complete energy
already includes transfers to and from every hidden supplier.
For a nonnegative constant `C` define, when `t<H`,

```text
R(t) = C sqrt((H-t)Ekin(t)/(2nu)).
```

With `h=H-t`, `E=Ekin(t)>0`, its exact loss has the square completion

```text
-R' - C sqrt(d)
 = C [sqrt(E)-sqrt(2nu h d)]^2 / [2 sqrt(2nu h E)] >= 0.
```

Consequently every nonnegative observation satisfying `q<=C sqrt(d)`
obeys `integral_a^b q <= R(a)-R(b)`. The horizon and complete endpoint
energy are shared across composition seams; neither is restarted.

This is the value function of the relaxed scalar control problem
`E'=-2nu d`, `d>=0`, with reward `C sqrt(d)` and horizon `H`:

```text
R_t + sup_{d>=0} [-2nu d R_E + C sqrt(d)] = 0,
d_opt = E/[2nu(H-t)].
```

Along the optimizer, energy decreases linearly to zero and dissipation
is constant, attaining the Cauchy--Schwarz bound. The relaxation forgets
fluid constraints, so it provides an upper bound on the actual fluid
observation. Its control is a scalar dissipation rate, not a freely
applied fluid force; no fluid realization of every relaxed optimizer
or general Schroedinger-bridge identification is asserted.

`MettapediaNS.FullEnergyParentReserve` certifies the square completion
and derives the exact kinetic rate from `NSEvolution` on R3, including
the imported pressure and transport cancellations. Its
`actual_interval_payment` proves the payment on every `0<=a<=b<=T`,
`b<H`, without an assumed future energy or dissipation bound.
The native derivative uses `Ekin+epsilon` for any fixed `epsilon>0`,
so it remains valid at zero energy. `actual_initial_allowance` gives the
original bound with that cushion. Letting it decrease to zero gives the
displayed sharp allowance analytically by continuity. The periodic
analogue uses its actual normalized kinetic balance and is analytic here.

### Which geometric observations are paid

On the normalized periodic domain let `B_t` select at most `M` Fourier
modes of the actual velocity, with conjugate symmetry when a real field
is needed. Parseval and finite Cauchy--Schwarz give

```text
||grad B_t u(t)||_infty,F <= sqrt(M) ||grad u(t)||_2.
```

The selection may depend on the complete history and may move to
different frequencies. Only its uniform mode count is fixed. More
generally, a multiplier with `sum_k |m_t(k)|^2<=C^2` has this bound with
constant `C`. Measurability of the sampled observation is required for
integration. No derivative of the selector is used: this bounds an
instantaneous strain observation of the full evolving field, rather
than asserting an autonomous equation for the selected velocity.

On R3, heat smoothing at length `ell>0` gives another literal observer:
`u_ell=G_{ell^2}*u`. The Gaussian's L2 norm is
`(8pi)^(-3/4)ell^(-3/2)`, hence

```text
||grad u_ell(t)||_infty,F
 <= (8pi)^(-3/4)ell^(-3/2) ||grad u(t)||_2.
```

These spatial identifications are analytic; the native Lean history
theorem pays their common right-hand side. The supremum bound also
holds along any actual stochastic trajectory of the full velocity.
It does not replace that trajectory's drift by the selected velocity
or discard the deformation generated by the remaining strain.

The scale or multiplicity dependence cannot be erased. For the symmetric
box of modes with each positive coordinate in `[N,2N]`, together with
their negatives, set

```text
u_hat(k) = -i (k1/|k|^2) [e1-(k1/|k|^2)k].
```

This datum is real and divergence free, and exactly attains

```text
partial_1 u_1(0) = ||grad u||_2^2 = S_N,
S_N = sum_k [k1^2/|k|^2][1-k1^2/|k|^2]
    >= (11/144) * 2(N+1)^3.
```

Indeed `k1^2/|k|^2` lies between `1/12` and `2/3`; on that interval
`x(1-x)>=11/144`. Thus the optimal point-strain constant is at least
`sqrt(S_N)`, growing as `N^(3/2)`. Exact fixtures at `N=1,2,4,8` check
the dual norm and its attainment. The construction proves the general
lower bound analytically; it is not a blowup example or a refutation
of a different full-datum history estimate.

Increasing observational resolution also changes the reserve. For a
differentiable `C(t)`, the certified scalar identity retains

```text
R'+q <= C'(t) sqrt((H-t)Ekin(t)/(2nu)).
```

For shrinking heat length, this extra bill is
`-(3/2)(ell'/ell)R`. A growing mode count or shrinking length cannot
be paid by silently resetting a fixed-resolution reserve. Changing
the selected frequencies at fixed mode count does not incur this
particular cost; its uniform observer norm remains the same.

### The precise remaining continuation estimate

Keep the full physical vorticity as receiver, and split only the strain:
`grad u=grad B_t u+(grad u-grad B_t u)`. Let `G_low` and `G_high` be
their respective integrals against `omega tensor omega`. If
`X=||omega||_2^2=||grad u||_2^2` and `D=||grad omega||_2^2`, then

```text
X'=2G_low+2G_high-2nu D,    |G_low|<=q X,
(exp(2R)X)' <= 2exp(2R)G_high-2nu exp(2R)D.
```

`weighted_enstrophy_rate` certifies this scalar comparison. Since the
receiver is the full curl, no time derivative of a filtered receiver
or projector-transport commutator was omitted. The remaining production
uses the actual evolving field, with its pressure-dependent mode history.

A sufficient open target is to choose the observer and constants from
the full initial datum, viscosity and horizon, and prove for every
available smooth prefix `tau<H` that

```text
2 integral_0^tau exp(2R)G_high
 <= (2-delta)nu integral_0^tau exp(2R)D + K,
delta>0, K finite and fixed before the prefixes.
```

Then `X(tau)<=exp(2R(0))X(0)+K`, supplying the existing enstrophy
continuation criterion. This is a sufficient estimate, not a proved
geometric depletion or recurrent-cascade bound. The fixed-observer
payment cannot exclude forced blowup by itself: it uses only the
complete energy loss law. A complete unforced argument must still
control the remaining high-strain work using the exact evolution.

Run the exact checker with `python3 -O labs/joint_parent_reserve.py`.
There is no numerical time discretization in this checkpoint. The
adaptive-metric counterexample and spatial observer identifications are
analytic with exact algebraic checks. The actual whole-space energy
history payment and the scalar high-strain comparison are Lean-certified.

## Heat-gradient observations and physical evolution compatibility

The [heat-gradient observer checker](heat_gradient_observer.py) tests the
claim that a scalar heat/HJB evolution automatically induces an unforced
fluid evolution by reconstructing its gradient at one group element.
Initial velocity matching is insufficient. The examples below have a
positive heat profile and zero observed initial velocity, but their later
observed velocity is nonzero and has a solenoidal momentum source.
They are not unforced NS solutions from zero data.

### A complete finite-frame calculation

Fix `nu>0`. Use the normalized period-`2pi` torus and twelve fields, for `j!=k`:

```text
E_(j,k,c)(x)=e_j cos(x_k)/sqrt(2),
E_(j,k,s)(x)=e_j sin(x_k)/sqrt(2).
```

Each field is divergence free. The complete sums satisfy
`sum E_i tensor E_i=I` and `sum (E_i.grad)E_i=0`. Thus their scalar
sum-of-squares operator is exactly the Laplacian. Their reconstruction
kernel has first column

```text
K(x,0)e_1 = sum_i E_i(x) E_i(0)_1
         = ((cos y+cos z)/2,0,0) = v(x).
```

Consider the positive heat solution

```text
phi(t,x)=2+exp(-nu t)sin x_1-(1/2)exp(-4nu t)sin(2x_1).
```

For `nu,t>=0`, `phi>=1/2`. The log potential `w=-2nu log phi` solves
`w_t=nu Delta w-|grad w|^2/2`. Its initial gradient at the origin is zero.
There are two distinct composition conventions on volume-preserving maps;
neither may be substituted for the other:

1. With `D_E F(g)=d/ds F(exp(sE) composed with g)|_0`, take
   `Phi(t,g)=phi(t,g(0))`. Evaluation intertwines the group generator
   with the base scalar Laplacian, and its squared gradient with the
   base squared gradient. Hence `W=-2nu log Phi` solves the group HJB.
2. With `D_E F(g)=d/ds F(g composed with exp(sE))|_0`, take
   `Phi(t,g)=P_t(phi(0) composed with g)(0)`, where `P_t=exp(nu t Delta)`.
   Differentiating inside this spatial heat average gives
   `L_g Phi=P_t(Delta(phi(0) composed with g))(0)=Phi_t/nu`.
   Positivity and the chain rule again give a group HJB solution.

For the second convention the frame derivative is
`D_i Phi(t,id)=P_t(E_i.grad phi(0))(0)`. It is not generally
`E_i(0).grad P_t(phi(0))(0)`. Both conventions have `Phi(t,id)=2`.
Define the identity-gradient observation by
`u(t,x)=-sum_i D_i W(t,id) E_i(x)`. The exact outputs are

```text
u_post(t,x)=a_0(t)v(x),  a_0=nu[exp(-nu t)-exp(-4nu t)],
u_pre(t,x) =a_1(t)v(x),  a_1=nu[exp(-2nu t)-exp(-5nu t)].
```

The extra heat rate in the second line comes from the transverse
frequency of the frame itself. Both velocities are zero at time zero,
positive multiples of `v` for every `t>0`, and divergence free.
For this shear, `(u.grad)u=0` and `Delta u=-u`. Its full projected fluid
residual is therefore `f=(a'+nu a)v`, with

```text
f_post=3nu^2 exp(-4nu t)v,
f_pre =nu^2[-exp(-2nu t)+4exp(-5nu t)]v.
```

At zero both equal `3nu^2 v`, which is nonzero for `nu>0` and has nonzero
curl. Pressure cannot remove it. The normalized kinetic energy is `a^2/4`,
and the exact energy ledger retains the work `a(a'+nu a)/4` from this
source. A constant heat profile instead gives the identically zero
observed velocity. Thus the two heat data have the same initial observed
fluid state and different observed evolutions.

### The obstruction is not an artifact of an incomplete frame

Suppose a possibly infinite solenoidal frame obeys the same tight-frame
and transport identities, with convergence sufficient for these derivatives
and reconstruction in `C^2`. Let `K(x,0)=sum_i E_i(x) tensor E_i(0)`.
For the same two-mode initial profile, either composition convention has

```text
u(0,x)=0,    partial_t u(0,x)=3nu^2 K(x,0)e_1,
partial_t u(0,0)=3nu^2 e_1,
```

because `K(0,0)=I`. In the precomposition calculation, the first two
spatial derivatives of `phi(0)` vanish at the origin, so the only term
in `Delta(E_i.grad phi(0))(0)` is `3 E_i(0)_1`.
An unforced periodic NS solution starting from zero has zero initial
acceleration: its convective and viscous terms vanish and its periodic
pressure is harmonic. This gives an initial contradiction for every
such complete frame as well. The required sum convergence is an explicit
analytic hypothesis, not supplied by the finite checker.

### Arbitrarily many initial compatibility tests can pass

For any integer `m>=1`, replace the initial heat profile by
`phi_m(0,x)=2+sin(x_1)^(2m+1)>=1`. Its finite sine expansion is

```text
sin(x)^(2m+1)=sum_(j=0)^m c_j sin(n_j x),
n_j=2j+1,   c_j=(-1)^j binomial(2m+1,m-j)/4^m.
```

For the twelve-field frame, the two observed amplitudes are

```text
a_(m,kappa)(t)=nu sum_j c_j n_j exp[-(n_j^2+kappa)nu t],
kappa=0 or 1.
```

The zero of order `2m+1` in the initial sine power implies

```text
a^(r)(0)=0 for 0<=r<m,
a^(m)(0)=(2m+1)! nu^(m+1)>0.
```

Indeed the lower odd derivatives give the vanishing Fourier moments;
in `(n_j^2+kappa)^m` only its highest power survives. These are finite
exponential formulas, so Taylor expansion gives a nonzero observed
velocity on a positive time interval. Given any finite number of initial
velocity jets to match to the zero fluid, choose m so that `r<m` includes
every tested derivative order. Matching those jets still does not ensure
evolution compatibility. The exact checker tests `m=1,...,6`; the moment
argument covers every m analytically. No uniform window across m is
required or asserted.

There is a stronger analytic obstruction in the precomposition cylinder
class. For any smooth positive periodic profile `phi0(x_1)`, put
`c(t)=P_t phi0(0)` and `b(t)=P_t phi0'(0)`. The same frame gives

```text
a(t)=2nu exp(-nu t)b(t)/c(t).
```

The scalar heat equation has `b(t)->0` and `c(t)->mean(phi0)>0`.
An unforced shear would require `a(t)exp(nu t)` to be constant.
Therefore no such profile with `a(0)!=0` yields an unforced shear for
all time. In fact it cannot do so on any open positive-time interval:
the quotient is real analytic for `t>0`, so constancy on an interval
would extend to all positive times, contradicting its limiting value
and continuity at zero.

Even every initial time derivative can match. Choose a smooth periodic
cutoff potential `w0(x)=c0 x` near zero, constant near the period seam,
with `c0!=0`, and take `phi0=exp(-w0/(2nu))`. Write `alpha=-c0/(2nu)`;
then `phi0^(r)(0)=alpha^r phi0(0)` for every r. Consequently
`b^(r)(0)=alpha c^(r)(0)` for every r, and

```text
a^(r)(0)=2nu alpha(-nu)^r for every r>=0.
```

These are precisely the time jets of the unforced shear
`2nu alpha exp(-nu t)v`. Nevertheless the preceding limiting argument
excludes actual agreement on a positive interval. Smooth heat evolution
need not be time analytic at its initial endpoint; the global cutoff
can affect later observations while remaining invisible to all these
initial jets. This argument concerns the stated cylinder class, not
every possible group chart or selected lift. It is analytic, not part
of the finite checker or the Lean certification below.

### What a physical lift must additionally prove

For `Ev(W)=-sum_i D_i W(id)E_i`, an admissible class of potentials must
satisfy the projected evolution identity

```text
Ev(nu L W-Gamma(W)/2)
  = nu Delta Ev(W)-P[(Ev(W).grad)Ev(W)],
```

and must be preserved by the HJB evolution. Initial matching alone
proves neither property. The examples refute the unrestricted implication
from a scalar group HJB solution to an unforced NS observation. They do
not refute a selected invariant class of compatible lifts, a construction
based directly on actual fluid histories, or arbitrary-data regularity.
They also do not construct an internal realization of a forced singularity.

`MettapediaNS.HeatGradientObserver` certifies the scalar heat profile and
its positive lower bound, the log-gradient observation, both explicit
fluid-source amplitudes, and the delayed case with initial source zero
but source derivative `120nu^3`. The spatial frame, group identifications,
complete-frame passage and general delayed family are analytic with exact
finite checks, not Lean theorems. Run
`python3 -O labs/heat_gradient_observer.py`.

## A physical covector HJB equation and its mean-action payment

The [covector Bellman checker](covector_bellman_bridge.py) tests a coupled
HJB representation that uses the actual fluid drift and pressure. Its
consumer is the physical covector reconstruction in
`MettapediaNS.CovectorFluidBridge`. It does not use the unrestricted
identity-gradient observation refuted above.

### Identification on every smooth physical prefix

Work on the normalized period-`2pi` torus with positive viscosity. Let
`u,p` be a smooth unforced NS evolution on an available finite interval,
with `div u=0` and spatial `mean p=0`. Write
`D=partial_t+u.grad-nu Delta` and `B=grad u`. Solve the linear scalar
equation on that same interval:

```text
D S = |u|^2/2-p,       S(0)=0,
m = u-grad S.
```

Smooth periodic coefficients give this scalar solution on each smooth
prefix. Commuting a gradient through D gives the complete equations

```text
D grad S = B^T m-grad p,
D m = -B^T m,        m(0)=u(0),
P m = u,            curl m = curl u.
```

Here P is the Helmholtz projection. The first equation retains the
pressure gradient; the cancellation in the second is exact. Projection
identifies this RHS with the nonlinear NS RHS. The periodic identification
here is analytic; the existing covector theorem certifies the corresponding
whole-space smooth-field algebra, not a torus existence theorem. These
identities do not assume existence beyond the available smooth lifespan.

Completing the kinetic square gives a physical HJB equation:

```text
S_t-nu Delta S+|grad S|^2/2 = V,
V = |m|^2/2-p.
```

The positive transform `Phi=exp(-S/(2nu))` satisfies

```text
Phi_t = nu Delta Phi - (V/(2nu)) Phi,       Phi(0)=1.
```

Thus the scalar heat representation retains a potential supplied by
the same fluid and covector. Dropping V changes the equation. It is an
internal term of this representation, not an externally imposed force.
For a solenoidal applied fluid force f, the scalar construction instead
gives `D m=-B^T m+f`; its projection retains f. The force is not hidden
in a freely chosen scalar gauge.

### What the auxiliary control does

For a fixed smooth physical prefix, the elementary square completion

```text
a.grad S+|a|^2/2 = -|grad S|^2/2+|a+grad S|^2/2
```

gives the usual control verification. Starting at x, let
`dX_s=a_s ds+sqrt(2nu)dB_s`, using periodic positions, over `0<=s<=t`.
For progressively measurable controls of finite expected quadratic cost,
Ito's formula applied to `S(t-s,X_s)` gives

```text
S(t,x) = inf_a E integral_0^t [|a_s|^2/2+V(t-s,X_s)] ds.
```

The smooth feedback `a_s=-grad S(t-s,X_s)` attains equality. The initial
value S(0)=0 removes the terminal term. On each compact smooth prefix,
the required coefficients and derivatives are bounded, so this
verification has finite integrals. It is an analytic argument, not a
new Lean stochastic-control theorem.

This auxiliary drift is `m-u`, not the physical velocity u. The fluid
history fixes V before this auxiliary optimization; varying a does not
independently vary the fluid pressure or its parents. This identifies a
control representation of actual prefixes, not an independently prescribed
Schrodinger-bridge optimizer or an arbitrary-data global construction.

### A finite original-data payment, with its exact limitation

Let `E(t)=mean |u(t)|^2` and `d(t)=mean |grad u(t)|^2`. Integration by
parts and `div u=0` give

```text
mean |m|^2 = E+mean |grad S|^2,
(mean S)' = E/2,             E'=-2nu d.
```

The hidden gradient's kinetic square cancels the HJB control square
in the spatial mean. No assumption of noninteracting parents is used.
Consequently `0<=mean S(t)<=t E(0)/2`. For a horizon H fixed from the
start, the nonnegative remaining reserve

```text
R(t)=(H-t)E(t)/2,
R'(t)+E(t)/2 = -nu(H-t)d(t)<=0
```

pays every compatible interval `0<=a<=b<=H` in the smooth lifespan:

```text
mean S(b)-mean S(a) = integral_a^b E(t)/2 dt <= R(a)-R(b).
```

Every seam uses the same horizon and complete kinetic energy. This is
a consequence of the standard energy identity, not a new regularity
criterion. It pays the signed spatial mean, not `mean |S|`, its pointwise
supremum, its spatial derivatives or cubic vorticity stretching. The
mean identity uses the stated zero-mean pressure normalization; a time
dependent pressure constant changes S's mean but not the physical u.
No whole-space integral of S is asserted here.

### Exact physical tests and the next cost

For the unforced shear `u=A exp(-nu t)sin y e_1`, pressure is zero and
the canonical scalar is explicitly

```text
S=A^2/(8nu) [1-exp(-2nu t)
             -(exp(-2nu t)-exp(-4nu t))cos(2y)].
```

The checker verifies the complete covector and HJB equations for all
time, with its nonzero hidden gradient and unchanged physical shear.
It also checks both signed 3D interacting fixtures at viscosities
`1/10` and `1`, their complete first and second NS/covector jets,
nonconstant scalar gauges, mean cancellations and a retained
solenoidal applied force. No Fourier output is discarded.

The raw value S itself is not a nonnegative reserve. For the exact
Taylor-Green flow `u=A exp(-2nu t)(sin x cos y,-cos x sin y,0)` with
`p=A^2 exp(-4nu t)(cos 2x+cos 2y)/4`, the canonical initial HJB source
at the origin is `V(0,0)=-A^2/2`. Hence S becomes negative there on a
short smooth interval. This excludes that particular pointwise reserve
interpretation; it does not exclude a corrected reserve or another
pressure gauge. Such a gauge change does not control spatial derivatives.

For `g=grad S`, the remaining derivative-level production is explicitly

```text
(mean |g|^2)' = 2 mean g.(B^T m-grad p)-2nu mean |grad g|^2.
```

Its source and geometry must be paid together with the physical curl
history. In particular, `curl grad S=0`: a bound on this gauge gradient
alone is not a bound on `curl m=curl u`. A continuation estimate must
retain the vector covector and its deformation or the existing joint
original-gradient tensor. The preceding mean payment supplies no such
bound. The original-datum signed renewal estimate used by
`JointCubicRenewal.hasNSEvolution_of_signed_renewal` remains open.
The physical PDE/control identification and interval estimates in this
section are analytic. The new checker certifies exact finite identities,
not a continuous stochastic theorem or a new Lean regularity result.
Run `python3 -O labs/covector_bellman_bridge.py`.

## HJB curvature completion and the physical curl quotient

The [curvature-completion checker](hjb_curvature_completion.py) tests
one explicit reserve following the physical covector/HJB construction.
Its proposed source cancellation is exact; its proposed signed payment
fails on an actual positive-viscosity unforced shear. This separates a
geometric cost of the representation from physical vortex stretching.

### The candidate and the retained source

Keep the original stochastic tensor `A`, its joint metric
`C=E[(F^T F) tensor (F^T F)]`, `W=C^-1`, and the physical covector
`m=u-grad S`. Write `B=grad u`, `P=Hess p`, `E=A-B`, and

```text
K=E+Hess S=A-grad m,     T=sum_l m_l Hess(u_l).
```

For `D=partial_t+u.grad-nu Delta`, the complete physical equations give

```text
D E=-B^T E-EB+P-B^T B,
D Hess S=-B^T Hess S-(Hess S)B+B^T B-P+T,
D K=-B^T K-KB+T,        K(0)=0.
```

The pressure Hessian and quadratic parent matrix cancel, but T remains.
All these tensors use the same fluid and original stochastic history.
The checker verifies the resulting first and second complete time jets
on both signs of an interacting 3D datum, including canonical pressure,
viscosity, changing parents and every generated Fourier output.

For a tensor Z set `q_Z=vec(Z)^T W vec(Z)` and let `Q_Z=mean q_Z`.
The joint metric gives the complete production

```text
D q_K=2 vec(K)^T W vec(T)-2nu F_K,
F_K=sum_j |partial_j vec(K)-C_j W vec(K)|_W^2>=0.
```

Here `C_j=partial_j C`, so the changing spatial metric remains in the
diffusion cost.

The existing original-tensor channel `Q_A` is nonincreasing after
spatial integration. The tested nonnegative candidate adds curvature
and the preceding mean-action reserve:

```text
R(t)=Q_A(t)+alpha Q_K(t)+beta(H-t)E_kin(t)/2,
alpha>0, beta>=0 fixed, E_kin=mean |u|^2.
```

Its proposed Bellman inequality is `R'+q<=0`, with the actual signed
continuation cost

```text
q(t)=2[G(t)-G(0)]-nu D_omega(t),
G=mean omega^T B omega,   D_omega=mean |grad omega|^2.
```

Nonnegativity and a finite initial reserve would make this a sufficient
payment of that cost. The claim quantified over all smooth unforced
data, with the displayed fixed coefficients, is false.

### Exact shear and its joint stochastic frame

Take `u=a exp(-nu t)sin y e_1`, `a,nu>0`. This is a globally smooth
unforced periodic flow with p=0 and G=0. The previous section gives S.
Its original packet and curvature are exactly

```text
A_12=a exp(-nu t)cos y,
A_22=-a^2/(4nu)[1-exp(-2nu t)
                  +(exp(-2nu t)-exp(-4nu t))cos(2y)],
K_22=-2S,
```

with all other entries zero. They satisfy their full positive-viscosity
equations; in particular `T_22=-a^2 exp(-2nu t)sin^2 y` is not zero.

At `t=1/a` put `epsilon=nu/a`. The exact common backward Brownian
representation, in scaled time `0<=s<=1`, is

```text
Y_s=y+sqrt(2epsilon)B_s,
b_epsilon=integral_0^1 exp[-epsilon(1-s)]cos(Y_s) ds,
F_epsilon=[[1,-b_epsilon,0],[0,1,0],[0,0,1]],
A/a=E[cos(Y_1) F_epsilon^T (e_1 tensor e_2) F_epsilon].
```

The same samples give C; replacing C by a product of independent
averages is not part of this test. As epsilon tends to zero, uniformly
in y, `b_epsilon` tends to `b_0=cos y`. In this coherent limit,

```text
q_A/a^2=cos^2 y,      q_K/a^2=sin^4 y,
Q_A/a^2=1/2,         Q_K/a^2=3/8.
```

Initially `Q_A/a^2=1/2` and K=0. Curvature has grown, while the
physical stretching has stayed exactly zero.

### Explicit positive-viscosity bounds

For `0<epsilon<=1`, Brownian Cauchy--Schwarz and the Lipschitz bound
for cosine give, uniformly in y,

```text
E|b_epsilon-b_0| <= epsilon/2+(2sqrt(2)/3)sqrt(epsilon)
                 <= (3/2)sqrt(epsilon),
E|cos(Y_1)-cos y| <= sqrt(2epsilon).
```

For `|b|<=1`, let `G_b=F_b^T F_b`. Its eigenvalues lie between 1/3
and 3: its two-dimensional block has determinant 1 and trace at most 3,
and the third eigenvalue is 1. Also
`||G_b-G_c||_F<=sqrt(6)|b-c|` for `|c|<=1`.
Consequently C and its coherent limit have eigenvalues at least 1/9;
their inverses have operator norm at most 9. The tensor-product
difference and inverse identity give

```text
||C_epsilon-C_0||op <=24sqrt(epsilon),
||W_epsilon-W_0||op <=1944sqrt(epsilon).
```

The original packet divided by a has Frobenius norm at most sqrt(2)
and differs from its coherent limit by at most `4sqrt(epsilon)`.
The curvature divided by a has norm at most 1. Its exact scalar heat
formula, or the source `-exp(-2epsilon s)sin^2 y`, bounds its difference
from `-sin^2 y e_2 tensor e_2` by `2epsilon`. Thus

```text
|Q_A/a^2-1/2| <=4000sqrt(epsilon),
|Q_K/a^2-3/8| <=2000sqrt(epsilon).
```

For example, the first bound follows from
`9*4*3+2*1944=3996<=4000`; the second uses
`9*2*2+1944=1980<=2000`. These deliberately generous bounds retain
the entire joint metric and its inverse. They do not require a
time-Taylor approximation or a numerical stochastic ensemble.

For `a>=max(nu,1/H)`, the integrated Bellman defect therefore satisfies

```text
[R(1/a)-R(0)+integral_0^(1/a) q(t)dt]/a^2
 >=3alpha/8-(4000+2000alpha)sqrt(nu/a)-L/a,
L=beta(H nu/2+1/4)+nu/2.
```

Here the physical viscous cost is included exactly:
`integral q=-a^2[1-exp(-2nu/a)]/4`. The mean-action reserve's decrease
is included as well. For every fixed alpha>0, beta>=0, nu>0 and H>0,
the displayed lower bound is positive for sufficiently large a.
One explicit choice `alpha=beta=nu=H=1`, `a=10^10`, gives the rational
lower bound `2519999999/8000000000>1/8` for this normalized defect.
The checker verifies its arithmetic, not the analytic Brownian estimates.

This refutes the displayed fixed-coefficient supersolution, including
the full physical dissipation credit. It does not refute coefficients
adapted to the full initial datum, an additional allowance, a different
functional, or regularity. The datum has large finite energy; this is
not a unit-energy counterexample. All these shears are regular.

### What the physical observation actually needs

K is symmetric: its initial value is zero, its source T is symmetric,
and its full evolution preserves symmetry. Hence
`tensorCurl(grad m)=tensorCurl(A-K)=tensorCurl A=omega`. The
existing same-frame metric preserves the symmetric/skew decomposition,
so this curvature lies entirely in the symmetric channel. Its growing
positive norm need not be charged in order to reconstruct physical curl.
For the tested shear, every path satisfies `J^T e_3=e_3` and omega is
parallel to e_3, so the actual curl-direction frame cost is exactly 1.
The established invariant-direction conversion already pays that flow.

Removing that unnecessary charge does not bound the directional frame
moment `M=E[J J^T]`, with `J=F^-1`. The original physical conversion still requires
control of the coupled curl geometry, such as the already stated
`integral omega^T M omega` target, or the weaker signed renewal payment.
Nor does this cancellation remove pressure's influence on u and its
parents. The result directs a geometric Bellman reserve toward the
physical observation rather than every derivative of its representation.

The PDE/stochastic argument and interval counterexample in this section
are analytic. The exact checker covers finite matrix algebra, full
initial 3D jets, the all-time shear formulas and the bound constants.
No Lean declarations or axioms are added. Run
`python3 -O labs/hjb_curvature_completion.py`.

## A rotational curl reserve and its internal source

The [rotational curl checker](rotational_curl_reserve.py) works with a
physical vorticity observation rather than the symmetric HJB curvature.
Its positive calibration uses classical axisymmetric analysis, with a
reserve supplied by the existing `PlanarParentReserve` scalar theorem.
The NS identification and stochastic argument here are analytic.

### Changing direction with a paid geometric normalization

Let u be an actual smooth, decaying, axisymmetric unforced evolution on
R3 with nu>0, initially without swirl. Symmetry and zero swirl persist on its smooth
lifespan. Write

```text
u=u_r e_r+u_z e_z,     omega=omega_theta e_theta,
eta=omega_theta/r,    L5=partial_rr+(3/r)partial_r+partial_zz.
```

The direction e_theta varies in space. The equation
`eta_t+u_r eta_r+u_z eta_z=nu L5 eta` removes its stretching without
assuming that the parents evolve independently. For smooth axisymmetric
data the quotient extends evenly to r=0. Assume the initial N and L below
are finite, and sufficient decay for the integrals; smooth Schwartz
initial data provide one such class. The classical bounds give

```text
N(t)=integral |eta| r dr dz <= N(0),
L(t)=||eta||_infinity <= L(0),
||u_r/r||_infinity <= C_B N(t)^(1/3) L(t)^(2/3).
```

Here N equals `||omega_theta||_(L1(dr dz))`, not its L1 norm in physical
three-dimensional volume. A factor 2pi converts N to the physical L1
norm of eta. The estimates and the universal constant C_B are from
[Gallay--Sverak, Proposition 2.6 and Section 5](https://www.numdam.org/article/CML_2015__7_2_67_0.pdf).
This is a use of the established no-swirl theory, not a new regularity
result for that class.

For example the smooth whole-space streamfunction
`psi=r^2 exp(-r^2-z^2)` gives

```text
u_r=2rz exp(-r^2-z^2),
u_z=2(1-r^2)exp(-r^2-z^2),
eta=2(5-2r^2-2z^2)exp(-r^2-z^2),
u_r eta_r+u_z eta_z=(16(r^2+z^2)-56)z exp(-2r^2-2z^2).
```

Its nonlinear vorticity transport is nonzero. The argument applies along
its evolving solution, not just to the displayed initial field.

Set `c=C_B N(0)^(1/3)L(0)^(2/3)`, finite from the original datum. For a
prescribed horizon H, let Z be the full physical enstrophy, D its ordinary
vorticity dissipation, and G the full cubic stretching. In this class,

```text
G=integral (u_r/r) omega_theta^2 dx,    |G|<=c Z,
Z'=2G-2nu D,
R(t)=Z(t)[exp(2c(H-t))-1]>=0,          0<=t<=H.
```

Taking `r=c(H-t)`, `E=Z`, `q=c`, `r'=-c` in the existing
`PlanarParentReserve.unforced_receiver_payment` gives

```text
R'+2|G|+2nu[exp(2c(H-t))-1]D <= 0.
```

Thus `2 integral_a^b |G| <= R(a)-R(b)` on every compatible interval.
Neither the horizon nor the initial resource is reset at a seam.
In particular the signed-renewal consumer has the finite original-datum
allowance `K=R(0)+2H|G(0)|`. The direct BKM estimate is also immediate:
`||omega(t)||_infinity <= ||omega(0)||_infinity exp(ct)`.
Both connections are analytic here. Applying the scalar Lean theorem
does not certify the cylindrical PDE, Biot--Savart estimate or physical
continuation hypotheses in Lean.

### Stochastic meaning and the correct volume

For a fixed actual smooth prefix, the backward diffusion representing eta
has the radial/axial generator `nu L5-u_r partial_r-u_z partial_z`, with
the fluid coefficients evaluated at backward physical time. Equivalently
lift r to the radius of four Cartesian coordinates and use ordinary
five-dimensional Brownian motion. Then eta is the expectation of its
original value along those paths. This gives the maximum bound without
any freedom to replace the parents by an independently chosen control.

The lifted drift is not incompressible in five dimensions: its divergence
is `2u_r/r`. The physical measure corresponds to the weight `r^-2` there.
Off the axis this weight is harmonic and the weighted drift divergence
vanishes. At the axis, the integration by parts must keep its boundary
term. For a smooth convex chi with chi(0)=0, decay at infinity gives

```text
integral chi'(eta) L5 eta r dr dz
 = -integral chi''(eta)|grad_(r,z) eta|^2 r dr dz
   -2 integral chi(eta(0,z)) dz.
```

Convex approximations to absolute value give the L1 contraction. Treating
the lifted drift as solenoidal, or discarding the singular-axis issue
before this calculation, would not justify that bound.

### What returns when swirl or asymmetry is admitted

On an axisymmetric evolution with swirl, set `b=u_theta/r` and
`Gamma=r u_theta`. The full equations retain

```text
(partial_t+u_r partial_r+u_z partial_z-nu L5)eta = partial_z(b^2),
(partial_t+u_r partial_r+u_z partial_z-nu L5)b = -2(u_r/r)b,
Gamma_t+u_r Gamma_r+u_z Gamma_z
  = nu(Gamma_rr-Gamma_r/r+Gamma_zz).
```

The meridional fluid creates and transports swirl gradients, and those
gradients create meridional vorticity. These are coupled unforced
equations. A force adds `(curl f)_theta/r` to the eta equation and
`r f_theta` to the Gamma equation. Pressure cancels from curl; it is
still part of the actual velocity evolution.

The smooth Schwartz initial datum
`u=A(-y,x,0)exp(-|x|^2)` has eta=0 but

```text
eta_t(0,r,z)=-4z A^2 exp(-2r^2-2z^2).
```

Thus the observer is not source-free even on actual unforced solutions
with bounded angular momentum. This strict derivative gives nonzero eta
on a short local solution interval; it is not a blowup example.

The source cannot have an unweighted time-integrated supremum allowance
uniform over all smooth data with bounded energy and bounded Gamma.
Indeed use the exact NS scaling `u_lambda(t,x)=lambda u(lambda^2 t,lambda x)`
on a fixed local solution from the preceding datum. Initial energy scales
as `lambda^-1`, `||Gamma||_infinity` is invariant, and the source scales
as `lambda^5`. Its positive integral over a fixed base interval, rescaled
to length `tau/lambda^2`, grows as `lambda^3`. This refutes that particular
uniform source allowance, not an arbitrary function of the full datum
or an allowance allowed to diverge as energy tends to zero. In contrast,
`integral ||u_r/r||_infinity dt` is scaling invariant. The source test
therefore does not refute a circulation-based payment of that different,
critical observation.

There is a signed source pairing that is paid even when swirl and
meridional motion interact. Let chi be the scaled meridional
streamfunction, fixed by the actual velocity:

```text
u_r=-r partial_z chi,  u_z=2chi+r partial_r chi,  -L5 chi=eta.
```

Writing `S=partial_z(b^2)`, integration by parts in z identifies

```text
T=integral r^2 chi S dx = integral (u_r/r)u_theta^2 dx.
R_swirl=||u_theta||_2^2/2,
D_swirl=integral (|grad_(r,z)u_theta|^2+u_theta^2/r^2) dx,
R_swirl'+T+nu D_swirl=0.
```

The final identity follows from the actual angular velocity equation.
Consequently `integral_a^b T <= R_swirl(a)-R_swirl(b)`, and the cost from
time zero is at most `R_swirl(0)`, the original swirl kinetic energy.
This is the standard kinetic transfer expressed as a payment of the
geometric source, not a new energy law. It allows both directions of
exchange and retains the complete evolving meridional parents. Inward
transfer can replenish the reserve only while T is negative; the same
signed cost is retained across each seam. No positive-part or absolute
transfer estimate follows.

This supplies a concrete paid pairing of the internal source on all
smooth axisymmetric prefixes with the stated decay. It pairs S with
chi, whereas the azimuthal enstrophy balance below pairs it with
`eta=-L5 chi`. The latter asks for two additional spatial derivatives.
The kinetic payment does not automatically pay that higher pairing or
the full continuation cost. The joint calculation below retains the
swirl's own vorticity energy and cancels this higher source; its remaining
directional deformation still needs payment.

For a general three-dimensional smooth solenoidal field, the exact
observer equation on r>0 is

```text
[partial_t+u_r partial_r+b partial_theta+u_z partial_z
 -nu(partial_rr+3/r partial_r+1/r^2 partial_theta_theta+partial_zz)]eta
 = partial_z(b^2)
   +[(partial_theta u_z) partial_r b
      -(partial_theta u_r) partial_z b]/r
   +eta partial_theta b
   +(2nu/r^3)partial_theta omega_r.
```

The checker derives this from the complete vector Laplacian and
convection, retaining the moving cylindrical basis. These angular terms
cannot be deleted by calling the flow incompressible. Also a fixed-axis
quotient can itself be singular for smooth general data: for
`u=(0,-2z,2y)exp(-|x|^2)`, eta along `(0,y,0)` behaves as `-4/y`.
Rotating the observer with the flow adds its own rate. For
`eta=k.omega/|k|^2`, its contribution with omega held fixed is
`(k_t.omega-2eta k.k_t)/|k|^2`.

### The remaining physical payment

There is an exact destination for the new costs. Write
`Z_theta=integral omega_theta^2 dx`,
`D_theta=integral (|grad_(r,z)omega_theta|^2+omega_theta^2/r^2) dx`,
`G_theta=integral (u_r/r)omega_theta^2 dx`, and
`C_theta=integral r omega_theta partial_z(b^2) dx`.
The axisymmetric balance is
`Z_theta'=2G_theta-2nu D_theta+2C_theta`.
If an evolving bound c(t) is used in `r(t)=c(t)(H-t)`, the same existing
reserve theorem retains both costs:

```text
R_theta'+2|G_theta|+2nu(exp(2r)-1)D_theta
 <= 2(exp(2r)-1)C_theta + 2Z_theta exp(2r)(H-t)c'(t),
provided |G_theta|<=c(t)Z_theta, c(t)>=0, t<=H.
```

Bounding these terms from the full original fluid is open. With swirl,
`Z_theta` is only one vorticity component: the other components also need
payment before the full continuation theorem applies. For arbitrary
flows one must additionally pay the angular terms, handle chart/axis
regularity, and retain the cost of evolving geometric choices. The
no-swirl calculation does not supply these missing estimates.

Run `python3 -O labs/rotational_curl_reserve.py`. The checker verifies exact
differential identities, the signed kinetic-transfer pairing, Gaussian
data, scaling and scalar reserve algebra. The maximum principle,
stochastic representation, norm estimates and interval arguments are
analytic; no new Lean declaration is claimed.

## Joint rotational enstrophy and the remaining directional work

The [joint enstrophy checker](rotational_joint_enstrophy.py) retains both
vorticity components of an actual smooth, sufficiently decaying,
axisymmetric unforced flow on R3, at viscosity nu>0. It uses the preceding
physical equations for eta and b and their full meridional parent.
No new external control or closed Fourier model is introduced.

Set `v=(u_r,u_z)`, `a=u_r/r`, `b=u_theta/r`, `eta=omega_theta/r`,
and let chi be the actual scaled streamfunction:

```text
u_r=-r chi_z,    u_z=2chi+r chi_r,    eta=-L5 chi,
L5=partial_rr+3/r partial_r+partial_zz,
<f>_5=integral r^2 f dx=2pi integral f r^3 dr dz.
```

Smoothness at the axis and the stated decay justify the boundary terms
below. In particular the meridional velocity may not be chosen independently
of eta: the elliptic relation is part of the physical state.

### A higher source cancels when its supplying vorticity is retained

The meridional velocity has azimuthal vorticity `r eta`. The swirl velocity
has vorticity components `(-r b_z, 2b+r b_r)`. Integration by parts gives

```text
Z_m=<eta^2>_5,       Z_s=<|grad b|^2>_5,
Z_m+Z_s=||omega||_2^2,
D_m=<|grad eta|^2>_5, D_s=<(L5 b)^2>_5,
D_m+D_s=||grad omega||_2^2.
```

These are the actual physical norms, including the cylindrical basis
derivatives, not norms of a surrogate tensor. Let

```text
C_theta=<eta partial_z(b^2)>_5,
G_m=<a eta^2>_5,
H_s=-<grad(b)^T [grad(v)+a I] grad(b)>_5.
```

Using `eta_z=L5 a` and the weighted Green identity gives

```text
C_theta=-2<a b L5 b>_5-2<a |grad b|^2>_5.
```

The first term cancels the reaction in the gradient energy of b. Its
transport also retains `div_5 v=2a`. The resulting complete balances are

```text
Z_m'/2 = G_m+C_theta-nu D_m,
Z_s'/2 = H_s-C_theta-nu D_s,
G = integral omega^T grad(u) omega dx = G_m+H_s.
```

Thus adding the genuine supplying vorticity energy cancels C_theta
exactly. The earlier isolated source need not be purchased separately.
The full enstrophy balance still contains `G_m+H_s`; no favorable sign
is asserted for that remaining physical deformation.

The compatibility behind the cancellation is especially direct if
`g=grad b`. The actual gradient equation is

```text
(partial_t+v.grad-nu L5)g
 = -(grad v)^T g-2a g-2b grad a-(3nu/r^2)g_r e_r,
C_theta=2<b g.grad a>_5.
```

Its last nondiffusive source cancels the eta source in the joint norm.
Both `g=grad b` and `eta_z=L5 a` are essential; the channels are not
independent controls. The complete gradient diffusion is nonnegative:

```text
D_s=<|Hess_(r,z)b|_F^2+3 b_r^2/r^2>_5=<(L5 b)^2>_5.
```

The radial diffusion term comes from differentiating the actual L5
operator. Dropping it would change the physical gradient history.

The checker also verifies the universal local identity relating the
literal three-dimensional stretching density to this split:

```text
r omega^T grad(u) omega
 -r^3[a eta^2-grad(b)^T(grad(v)+a I)grad(b)]
 = partial_r(2r^2 b^2 partial_z u_z)
   -partial_z(2r^2 b^2 partial_r u_z).
```

It does not infer the physical equality merely because two reduced
equations happen to have matching terms.

### The remaining work observes a direction

The matrix `S0=sym(grad v)+(a/2)I` is traceless. Consequently

```text
G=<a[eta^2-|grad b|^2/2]-grad(b)^T S0 grad(b)>_5.
```

The second contraction retains the direction of the swirl gradient
relative to the meridional strain. It is distinct from the paid kinetic
transfer `T=<chi partial_z(b^2)>_5`, and from C_theta. Calling either
source zero does not delete this directional term.

The cancelled coupling is a spatial flux, not an absent interaction.
Set `F=(a_r,a_z-eta)` and
`div_5 j=r^-3 partial_r(r^3 j_r)+partial_z j_z`. Elliptic compatibility
gives `div_5 F=0`. For `e=eta^2+|g|^2`,
`d=|grad eta|^2+|Hess b|_F^2+3 b_r^2/r^2`, and the preceding signed
deformation density `g_rot`, the complete local equation is

```text
partial_t(e/2)+div_5[v e/2+b^2 F]-nu L5(e/2)=g_rot-nu d.
```

The checker verifies this directly from the actual eta,b equations.
A local history summary must retain the normal flux of
`v e/2+b^2 F-nu grad(e/2)` across its boundary. Its b^2 F part depends on
the surrounding meridional field through the elliptic parent relation.
Cancelling that transfer after integration over all space does not
authorize deleting it on a local region or when composing regions.

A spatially varying reserve weight must preserve this coupling too.
For a smooth positive weight w(t,r,z), put

```text
Q_w=<w(eta^2+|g|^2)>_5,
G_w=<w[a eta^2-g^T(grad(v)+a I)g]>_5,
D_w=<w[|grad eta|^2+|Hess b|_F^2+3 b_r^2/r^2]>_5,
J_w=<b^2[grad w.grad a-eta partial_z w]>_5,
A_w=partial_t w+v.grad w+nu L5 w.
```

The actual weighted equation is

```text
Q_w'/2+nu D_w = G_w+J_w+<A_w(eta^2+|g|^2)>_5/2.
```

The positive diffusion sign in A_w comes from integration by parts;
it is the adjoint weight evolution, not the material heat operator.
The new term J_w is the compatibility defect of the weighted source
cancellation and is checked with its complete local boundary flux.
The unweighted identity has J_w=0. If w>=1, Q_w controls the full physical
enstrophy, but choosing w to reduce G_w must also pay J_w and A_w. No
such arbitrary-history weight with an original-datum bound is supplied.
This gives a concrete derivative test for a geometric Bellman reserve
without interpreting the weight as a new force on the fluid.

There is a nonconstant family that preserves the source cancellation.
The actual parent quantity `I=r^3 chi_r` satisfies

```text
grad I = r^3(F_z,-F_r),     F.grad I=0.
```

Hence `w=Phi(t,I)` has J_w=0 for any smooth scalar Phi. In particular,
`w=1+alpha I^2`, alpha>=0, is nonnegative, dominates one, and retains
the compatibility exactly. This is a physical geometric candidate, not
a completed reserve: its A_w term includes the evolving nonlocal parent
I, and its remaining G_w has no established payment. If alpha is fixed,

```text
A_w=2alpha I(I_t+v.grad I+nu L5 I)+2alpha nu |grad I|^2.
```

Both terms must be retained in the next derivative test. Choosing weights
along these parent level sets removes J_w; it does not remove their
time evolution or prove a finite original-datum bound for Q_w.
Bounded choices, such as `w=1+alpha I^2/(ell^2+I^2)` with ell>0, preserve
the same cancellation and satisfy `1<=w<=1+alpha`. Their initial Q_w is
therefore finite for finite initial enstrophy without an extra weighted
moment assumption. A sufficient derivative estimate for such a weight,
with parameters fixed from the original datum, remains open.

### Two actual smooth data with the same source totals and opposite stretching

Let sigma be +1 or -1 and set

```text
rho=r^2+2z^2,
b=exp(-rho),
chi_sigma=(sigma/2)z(1-3r^2+4z^2)exp(-rho).
```

Recover the meridional velocity through chi and set `u_theta=r b`.
In Cartesian coordinates this is
`u=(-x chi_z-y b,-y chi_z+x b,2chi+r chi_r)`, a smooth Schwartz
divergence-free field on all of R3. These data start actual local
unforced NS evolutions. Their canonical pressures are not assumed zero;
pressure drops out of the curl equations used for the instantaneous test.

Put `K_j=2pi sqrt(pi/(2j))`. Exact Gaussian integration gives

| Quantity | sigma=+1 | sigma=-1 | Integral factor |
| --- | ---: | ---: | --- |
| T | 0 | 0 | K_3 |
| C_theta | 0 | 0 | K_3 |
| G_m | -28/729 | 28/729 | K_3 |
| H_s | 4/81 | -4/81 | K_3 |
| Full physical G | 8/729 | -8/729 | K_3 |
| `||u||_2^2` | 249/512 | 249/512 | K_2 |
| Full physical enstrophy | 1893/256 | 1893/256 | K_2 |
| Full physical vorticity dissipation | 19537/128 | 19537/128 | K_2 |

The source field `partial_z(b^2)` itself is also identical. At
`nu=1/100000`, the positive member has

```text
Z'(0)/(2K_2) = (8/729)sqrt(2/3)-19537/12800000 > 0.
```

The parent meridional stretching is negative, yet the full stretching
and enstrophy derivative are positive. Reversing the meridional field
reverses G without changing either source total or the quadratic norms.
This shows that these summaries do not reconstruct stretching's sign;
it does not exclude an upper bound using richer original-data resources.

In particular the proposed instantaneous implication
`T=C_theta=0 and G_m<=0 implies G<=nu D` is false. Multiplying the
positive datum by A preserves the zero pairings and the sign of G_m,
while G scales as A^3 and D as A^2. For any fixed viscosity and any
fixed coefficient on nu D, sufficiently large A refutes absorption
using only diffusion and these vanishing source totals. Strict failure
persists briefly on a local smooth solution by continuity. No uniform
interval across that amplitude family is claimed. These tests do not
refute the signed-renewal estimate with its G(0) subtraction and a
full-original-datum allowance.

The checker includes a separate nonzero-C_theta Gaussian fixture. It
verifies both individual evolution balances before cancellation,
complete viscosity, full Cartesian tensor components expressed in the
cylindrical orthonormal frame, and the ordinary vorticity dissipation.
Gaussian moments are exact; no grid, mode truncation or quadrature is used.
It also checks the complete weighted equation for `w=1+r^2`; on the sign
pair, `J_w` equals `sigma*(8/81)K_3` despite both unweighted source
pairings vanishing. The adjoint weight term and its viscous Laplacian
are retained in that check.

The next physical obligation is payment of the remaining directional
contraction along the coupled evolving eta,b system, including their
nonlocal parent relation, and then the angular/geometric defects of
general three-dimensional flows. The joint cancellation removes a
separate source bill; it does not close that history estimate.

Run `python3 -O labs/rotational_joint_enstrophy.py`. The PDE integrations
and local-solution consequences are analytic and the identities are
checked symbolically. No new Lean declarations or axioms are claimed.

## Generated parents and an initially empty geometric reserve

The [parent-generation checker](rotational_parent_generation.py) tests the
compatible weight above against actual unforced whole-space dynamics.
Write `I=r^3 chi_r`, `e=eta^2+|grad b|^2`, `Z=<e>_5`, and consider

```text
psi(I)=I^2/(ell^2+I^2),       ell>0,
w=1+alpha(H-t)psi(I),        alpha>=0, 0<=t<=H,
R=<(w-1)e>_5,               Q=Z+R.
```

Parameters may depend on the full original datum, viscosity and horizon.
The proposed sufficient claims are that Q is nonincreasing, or that R
pays the existing signed renewal cost:

```text
R(t)+2 integral_0^t [G(s)-G(0)] ds-nu integral_0^t D(s) ds <= R(0).
```

Both claims fail for this reserve family, including all such parameter
choices. The failure is not a refutation of an additional initially
positive allowance drawn from the full datum. The weight still preserves
the spatial source cancellation proved above.

### Complete evolution of the weight

Let `K=(-L5)^-1` be the decaying whole-space inverse and
`N_eta=-v.grad eta+partial_z(b^2)`. The actual parent evolves by

```text
chi_t=nu L5 chi+K N_eta,
I_t=nu(I_rr-3 I_r/r+I_zz)+r^3 partial_r K N_eta.
```

Consequently the adjoint weight term in the full weighted balance is

```text
A_w=-alpha psi(I)
    +alpha(H-t)[psi'(I)(I_t+v.grad I+nu L5 I)
                 +nu psi''(I)|grad I|^2],
psi'(I)=2 I ell^2/(ell^2+I^2)^2,
psi''(I)=2 ell^2(ell^2-3I^2)/(ell^2+I^2)^3.
```

In particular `I_t+nu L5 I` contains `2nu(I_rr+I_zz)` and the full
nonlocal source. The spatial identity `F.grad I=0` does not eliminate
this evolution. Neither that source nor the changing-sign second
derivative may be dropped from a Bellman test.

### Smooth pure swirl creates the missing parent

Take the fixed Schwartz initial datum

```text
b=exp(-r^2-2z^2), chi=0,
u0(x,y,z)=(-y b,x b,0), r^2=x^2+y^2.
```

It is smooth and divergence free on all of R3, including the axis. At
time zero the meridional velocity, eta and I vanish; physical stretching
G also vanishes pointwise. Nevertheless the source `S=partial_z(b^2)`
does not vanish. The actual initial meridional acceleration has
streamfunction `chi_1=K S`. It is the pressure-corrected centrifugal
acceleration, not an independently prescribed force. Indeed its components
are `v_1=(-r partial_z chi_1,2chi_1+r partial_r chi_1)`, and

```text
p_r=r b^2+r partial_z chi_1,
p_z=-2chi_1-r partial_r chi_1
```

are compatible precisely because `-L5 chi_1=S`.

The inverse is explicit as a heat integral. With `A=1+8s`, `C=1+16s`,

```text
chi_1 = integral_0^infinity
          -8z A^(-2) C^(-3/2) exp(-2r^2/A-4z^2/C) ds.
```

The checker verifies the heat equation and its initial value. The kernel
decays integrably at infinity, so integrating the heat equation gives the
stated inverse relation. It also gives

```text
I_1=r^3 partial_r chi_1
   =integral_0^infinity 32r^4 z A^(-3) C^(-3/2)
                         exp(-2r^2/A-4z^2/C) ds,
```

which is strictly positive for r,z>0. Thus parent generation is present
even though the proposed reserve sees no initial parent.

The resulting physical stretching derivative is

```text
G(0)=0,
G'(0)=gamma=3 sqrt(2) pi^(3/2) (11pi-34)/128 > 0.
```

This expression includes every term in the derivative of
`integral omega^T grad(u) omega`. Its value is independent of viscosity:
the viscous part of the initial acceleration remains pure swirl, whose
stretching is identically zero. The checker independently compares the
literal three-dimensional derivative with the joint-vorticity expression.
After the substitution `y=sqrt(1+8s)` its inverse-elliptic integral,
divided by `sqrt(2) pi^(3/2)`, has rational integrand

```text
-(6y^4-11y^2-9)/(16y^4(y^2+1)^3),  1<=y<infinity.
```

An exact antiderivative certificate gives `3(11pi-34)/128`. This is not
a numerical quadrature or a closed-mode approximation.

### A positive-viscosity interval, including the remainder

Use the ordinary physical quantities
`D=||grad omega||_2^2` and `L=||Delta omega||_2^2`. At the initial datum,

```text
Z0=(3/4)pi^(3/2), D0=(13/2)pi^(3/2), L0=75pi^(3/2),
Z'(0)=-2nu D0,
D'(0)=-2nu L0,
Z''(0)=2gamma+4nu^2 L0.
```

The nonlinear contribution to D'(0) is zero: the newly generated curl
is azimuthal, orthogonal in the full dissipation pairing to the initial
meridional curl. The checker retains the cylindrical basis derivatives.

For this fixed smooth datum, local existence and Sobolev estimates give a
common interval `[0,T0]` and an H^12 bound for `0<=nu<=1`. One can obtain
these from the usual estimate `d/dt ||u||_{H^12}^2 <= C||u||_{H^12}^3`, with
viscosity nonpositive in that estimate. The lane's
`WholeSpaceViscousFlow.regularizedViscous_all_order` already gives
viscosity-independent spatial bounds on the regularized Euler interval,
and `localNSEvolution` uses that same interval for every nonnegative
viscosity. Differentiating the projected PDE through three time orders
loses at most six spatial derivatives. Sobolev products therefore bound
`|Z'''(t)|` by a constant M of the original datum, uniformly on a shorter
common interval. This Taylor-bound application is analytic, not a new
Lean theorem.

It follows uniformly as nu decreases to zero that

```text
Z(t)=Z0-2nu D0 t+(gamma+2nu^2 L0)t^2+O(t^3),
Z(1000nu)-Z0=nu^2[10^6 gamma-2000D0]+O(nu^3)>0.
```

For example `pi>157/50` and `sqrt(2)>7/5` give
`gamma/pi^(3/2)>567/32000`; the displayed leading coefficient is at
least `(18875/4)pi^(3/2)`. Choose nu positive, small enough that
`1000nu<min(T0,H)` and the uniform Taylor remainder is smaller than half
that positive leading term. All constants in that choice come from the
fixed datum and prescribed horizon. This proves an actual smooth
positive-viscosity interval, rather than inferring one from a second
derivative without controlling its remainder.

The exact enstrophy balance also gives a positive signed renewal excess:

```text
2 integral_0^t G ds-nu integral_0^t D ds
  =Z(t)-Z0+nu integral_0^t D ds>0.
```

For any fixed viscosity nu>0 and horizon H>0 the same failure occurs for
sufficiently large amplitude A of the initial datum. Apply the previous
argument at viscosity `mu=nu/A` and set `u_A(t)=A u_mu(At)`. The test
time becomes `1000nu/A^2`, which lies inside H for large A. These remain
actual unforced flows. This amplitude argument does not claim an
unbounded energy-normalized excess.

### Exact scope of the reserve obstruction

For these data, R(0)=0 for every alpha,ell in the stated family, whereas
R(t)>=0 for t<=H. Since Z(t)>Z0, Q cannot be nonincreasing. Since the
signed renewal excess is positive, R cannot pay that cost either. More
generally any nonnegative proposed reserve that starts at zero on these
data fails the same payment claim. The G(0) subtraction offers no escape
here because G(0)=0.

For alpha>0 the reserve itself initially grows quadratically:
`R(t)=alpha H t^2 <I_1^2 |grad b|^2>_5/ell^2+O(t^3)`.
Its strictly positive leading coefficient measures the newly generated
parent, but provides no initial payment for creating it.

This is a finite generated burst, not indefinite renewal or a blowup
construction. It leaves the sufficient signed budget with a positive
full-datum allowance open. The missing initial resource is concrete:
the existing swirl already has the nonzero source S and projected parent
acceleration K S, before any meridional parent is present. A repaired
reserve must account for that capacity and its later replenishment.
The source itself evolves through the same coupled fluid; treating it
as fixed or freely selectable would lose the original physical question.
Its exact equation, also checked, is

```text
(partial_t+v.grad-nu L5)S
  =-(partial_z v).grad(b^2)-4aS-4a_z b^2
    -2nu partial_z(|grad b|^2).
```

Here `partial_z v` differentiates both meridional velocity components.
The nonlocal forecast `J=r^3 partial_r K S` already contributes at the
pure-swirl initial time. Adding a reserve term depending on J would
restore an initial resource, but also restores the boundary defect
`<b^2 F.grad(weight)>_5` and the full evolution of J. The parent-only
cancellation does not pay these terms. The next section supplies a
separate, short-interval payment using their complete local derivatives.

Run `python3 -O labs/rotational_parent_generation.py`. Differential and
Gaussian/resolvent identities are exact symbolic checks. The local
Sobolev estimates, interval argument and scaling consequence are analytic.
No new Lean declarations, axioms or arbitrary-data bound are asserted.

## A source-funded reserve pays the first generated interval

The [forecast checker](rotational_forecast_reserve.py) and
`MettapediaNS.RotationalForecastReserve` repair the initially empty
reserve for the pure-swirl datum above. The result is a local physical
calibration with a fixed original horizon; it does not bound the cost of
repeatedly generating new parents.

Keep the actual evolving quantities

```text
I=r^3 partial_r chi, S=partial_z(b^2), J=r^3 partial_r (-L5)^-1 S,
e=eta^2+|grad b|^2, psi_ell(q)=q^2/(ell^2+q^2),
U(t)=<psi_ellI(I(t)) e(t)>_5,
V(t)=<psi_ellJ(J(t)) e(t)>_5.
```

Both ellI and ellJ are fixed positive numbers. J is the response to the
current internally generated source, not a prescribed future field. In
particular `J_t=r^3 partial_r (-L5)^-1 S_t` retains the complete source
equation in the preceding section.

### The full new defect stays in the calculation

For any scalar weight w and `h=e/2`, the exact weighted local balance is

```text
partial_t(w h)
  +div_5[w(v h+b^2 F-nu grad h)+nu h grad w]
  =w(g_rot-nu d)+b^2 F.grad w
    +h(w_t+v.grad w+nu L5 w),
F=(a_r,a_z-eta).
```

The checker verifies this identity against the actual eta,b equations.
For the J weight, its integrated flux defect is
`<b^2 psi'_ellJ(J) F.grad J>_5`, and the adjoint rate is

```text
psi'_ellJ(J)(J_t+v.grad J+nu L5 J)
  +nu psi''_ellJ(J)|grad J|^2.
```

Unlike the I weight, this term has no asserted flux cancellation. The
local proof below bounds the complete derivative V', including this
defect, rather than setting it to zero.

### Physical initial coefficients

For the preceding pure swirl, I(0)=0 and I_t(0)=J(0)=I_1. Define

```text
C=<J(0)^2 e(0)>_5/ellI^2 > 0,
M=<psi_ellJ(J(0)) e(0)>_5 > 0,
gamma=3 sqrt(2) pi^(3/2)(11pi-34)/128 > 0.
```

These are finite quantities of the full original datum. Positivity
follows from the explicit I_1 kernel on r,z>0. Direct differentiation
gives

```text
U(0)=U'(0)=0, U''(0)=2C,
V(0)=M,
G(0)=0, G'(0)=gamma.
```

The derivatives remain those of the actual viscous evolution. In
particular V'(0) need not vanish at positive viscosity.

### Uniform local control of the nonlocal observables

The following analytic argument supplies the local remainders; it is not
part of the scalar Lean theorem. Use a common local interval `[0,T0]`
with sufficiently high spatial Sobolev bounds, uniform for `0<=nu<=1`,
from the fixed initial datum. Such local bounds are the ones constructed
in `WholeSpaceViscousFlow`, and they give bounded spatial derivatives of
u and the time derivatives obtained from its projected equation.

It would be incorrect to assume the velocity remains Schwartz. Smooth
rapidly decaying velocity data can develop algebraic spatial tails; see
[Brandolese, Theorem 1.2 and Section 2](https://arxiv.org/html/math/0304436v1).
Instead use the actual scalar transport-diffusion equations

```text
(partial_t+v.grad-nu L5)b=-2ab,
(partial_t+v.grad-nu L5)eta=S.
```

Lift the radial variable to four dimensions, so L5 is the ordinary
five-dimensional Laplacian. The lifted drift is bounded on the common
local interval, its divergence is 2a, and its derivatives and those of a
are controlled by sufficiently high physical velocity derivatives.
Multiply differentiated equations by polynomial spatial weights. Weighted
transport costs involve bounded logarithmic derivatives of the weights
and the bounded drift; stretching and commutators involve its bounded
derivatives. Diffusion is nonpositive apart from weighted commutators,
which are absorbed with a remainder bounded uniformly for nu<=1.
Thus, for each fixed N,m, the weighted b norm obeys

```text
d/dt ||<x>^N b||_{H^m(R5)}^2
  <= A_Nm ||<x>^N b||_{H^m(R5)}^2.
```

For eta there is also the weighted source norm, controlled by one higher
weighted b order and Sobolev products. The Gaussian initial b and zero
initial eta have all these weighted norms finite. Gronwall therefore
supplies uniform local bounds at each required order. Differentiating the
actual equations supplies the corresponding weighted bounds on their
first few time derivatives. The constants here come from the initial
Sobolev and weighted norms and the prescribed local interval.

These estimates also control the nonlocal weights. The regular-axis
streamfunction identity gives, for each needed time derivative j,

```text
partial_t^j I=r^2 partial_t^j u_z
              -2 integral_0^r s partial_t^j u_z(s,z) ds,
|partial_t^j I| <= 2r^2 ||partial_t^j u_z||_infinity.
```

The gradient of the Newtonian kernel in five dimensions is locally
integrable and bounded away from its origin. Hence
`||grad K f||_infinity <= C_K (||f||_infinity+||f||_1)`.
Apply this to the actual time derivatives of S to bound each needed
time derivative of J by a constant times r^3. The weighted eta,b bounds
integrate these polynomial factors, and all derivatives of psi_ell are
bounded for fixed ell>0. Differentiating U,V under their integrals is
therefore justified with uniform integrable majorants.

In particular the preceding estimates construct finite constants
`B_U,B_V,B_G` from the original data such that
`|U'''|<=B_U`, `|V'|<=B_V`, and `|G''|<=B_G` on a common shorter interval,
uniformly in `0<=nu<=1`. These constants are upper bounds obtained from
the local estimates, not suprema over an uncontrolled future solution.

### A complete first-interval payment

Fix an original horizon H within that local interval and put tau=H-t.
Choose the coefficients of the tested two-part reserve to be

```text
R(t)=4gamma/(H C) tau U(t)+14gamma/(3H M) tau^3 V(t).
```

The source term now supplies `R(0)=14gamma H^2/3>0`, R is nonnegative
for 0<=t<=H, and R(H)=0. These coefficients and the whole clock are fixed
from the original datum and H.

Normalize s=t/H and set

```text
p(s)=U(Hs)/(C H^2), q(s)=V(Hs)/M, g(s)=G(Hs)/(gamma H),
r(s)=2(1-s)p(s)+(7/3)(1-s)^3 q(s), R(t)=2gamma H^2 r(t/H).
```

The exact leading shapes are `p=s^2`, `q=1`, `g=s`. Their payment is

```text
r'(s)+g(s)=-13s^2+19s-7
          =-(26s-19)^2/52-3/52 <= -3/52.
```

This strict margin pays all five Taylor errors. Lean proves that, for
0<=s<=1, if

```text
|p-s^2|, |p'-2s|, |q-1|, |q'|, |g-s| <= epsilon,
0<=epsilon<=9/4472,
```

then `r'+g<=-3/104`. The general error bound is
`r'+g<=-3/52+(43/3)epsilon`. Set

```text
L=1+B_U/(2C)+B_V/M+B_G/(2gamma),
0<H<=min(T0,9/(4472L)).
```

Taylor's theorem and the preceding derivative bounds give all five
errors at most LH. Consequently, along the actual unforced evolution,

```text
R'(t)+2G(t)-nu D(t) <= -3gamma H/52,
R(t)+2 integral_0^t G ds-nu integral_0^t D ds <= 14gamma H^2/3.
```

The scalar differentiation, error absorption and physical rescaling are
Lean-certified. `PlanarParentReserve.interval_payment` integrates the
inequality without introducing a new allowance at intermediate seams.
The application to these nonlocal physical U,V and the uniform local
moment estimates above is analytic. The sufficient signed-renewal
observable is exactly the existing one, with G(0)=0 for this datum.

This payment includes the earlier positive-viscosity burst: the local
horizon bound is uniform in nu, so choose small H and nu=H/2000. At
t=H/2=1000nu the preceding counterexample has positive enstrophy and
renewal excess, and the new initial source allowance pays it. Thus the
test is not restricted to intervals where diffusion alone wins.

Both pieces matter for this particular clock. The parent-only leading
payment fails at s=1/2; the source-only cubic clock has zero derivative
at s=1 and leaves positive stretching unpaid. The combined polynomial
has a strict margin on the entire interval.

The two earlier Gaussian phases have U(0)>0 and V(0)>0: at r=z=1,
their I values are `-5sigma exp(-3)`, the density is positive, and J has
the same strictly positive source kernel. They therefore admit a simpler
local calibration of the same family. Use datum-controlled local bounds
`|U'|<=B_1`, `|V'|<=B_2`, `|G'|<=B_3`. Choose H small enough that
`U>=U(0)/2`, `V>=V(0)/2`, `H B_1<=U(0)/4`, and
`H B_2<=V(0)/2`. With
`alpha=8(1+B_3)H/U(0)` and beta=1, the complete derivatives give

```text
[alpha(H-t)U]' <= -2(1+B_3)H,
[(H-t)^3 V]' <= 0,
2(G(t)-G(0)) <= 2B_3 H.
```

Thus the signed renewal cost is paid locally on both phases as well.
This uses their full evolving derivatives and does not infer a sign from
their identical source totals. It supplies no prescribed-large-horizon
bound and adds no new local existence theorem.

### Remaining history obligation

This construction repairs one generated-parent interval; it does not
improve the classical local existence time or prove global regularity.
The estimates used to make LH small hold on the original datum-controlled
local interval. At its end, setting a new H and recomputing C,M,gamma
would grant a fresh reserve. A proof for arbitrary prescribed horizons
must pay for that change and for the continued nonlocal source and
geometric defects. There is no bound here on the sum of those renewals.

Run `python3 -O labs/rotational_forecast_reserve.py`. Its exact checks
retain the full spatial flux, adjoint diffusion, the two-part polynomial
and its error tolerance. The scalar certificate is in
`MettapediaNS.RotationalForecastReserve`; the physical application remains
analytic and the arbitrary-history continuation hypothesis remains open.

## Circulation pays source histories with a radial weight

The [circulation source checker](circulation_source_reserve.py) connects a
physical resource to repeated parent generation. This estimate holds on
every available smooth axisymmetric whole-space solution prefix, with
constants fixed from the original datum. It does not restart a local clock.
It pays a source norm and its linear elliptic response, not the complete
stretching or the derivative of the preceding forecast reserve.

The input is the classical circulation equation for
`Gamma=r u_theta=r^2 b`; see [Wei, equations (1.3)--(1.4)](https://arxiv.org/html/1508.03318v1).
The calculation below uses its quartic diffusion balance. Related quadratic
circulation and radial-weight distinctions are discussed in
[Shahmurov, Section 11](https://arxiv.org/html/2606.07869v2#S11).
No new general regularity result is claimed.

### A resource that is not replenished by meridional transport

Fix nu>0. Assume regularity at the axis and sufficient decay for the
following identities, with `C4(0)<infinity`. Schwartz initial velocities
satisfy that moment condition. Finite kinetic energy alone does not imply
it. Use the actual coupled velocity v, with physical divergence zero:

```text
Gamma_t+v.grad Gamma=nu(Gamma_rr-Gamma_r/r+Gamma_zz),
C4(t)=integral Gamma^4 dx,
D_Gamma(t)=integral Gamma^2 |grad Gamma|^2 dx,
C4'=-12nu D_Gamma.
```

Here `dx=2pi r dr dz`. Transport cancels after spatial integration, even
when the meridional parents amplify one another. The exact local entropy
flux is

```text
partial_t(Gamma^4)
  +div_3[v Gamma^4-nu grad(Gamma^4)+2nu Gamma^4 e_r/r]
  =-12nu Gamma^2 |grad Gamma|^2.
```

The singular radial drift has a boundary flux. It vanishes at the axis
because Gamma=O(r^2) for a smooth axisymmetric field, and at infinity under
the stated decay. One may first use spatial cutoffs on each compact smooth
prefix. The scalar equation propagates the initial moment, and its energy
identity removes the auxiliary cutoff bounds from the final estimate.
No bound on a future strain supremum enters the allowance.

For the actual meridional-vorticity source `S=partial_z(b^2)`, define
`||f||_5^2=2pi integral |f|^2 r^3 dr dz`, as above. Then

```text
<r^6 S^2>_5=4 integral Gamma^2 Gamma_z^2 dx,
C4'+3nu <r^6 S^2>_5
  +12nu integral Gamma^2 Gamma_r^2 dx=0.
```

Consequently the nonnegative reserve `R=C4/(3nu)` satisfies

```text
R(t)+integral_0^t <r^6 S^2>_5 ds <= R(0).
```

This is a payment for the whole source history on every smooth prefix.
For disjoint time intervals, their nonnegative costs add under this single
initial allowance. The result does not require any intermediate reserve
reinitialization. Diffusion supplies the loss in the quartic chain rule;
transport by the interacting fluid does not create new circulation stock.

### Fixed-radius source and nonlocal response

Let rho>0 be fixed from the original data. Choose a smooth radial cutoff
`0<=zeta_rho<=1`, zero for r<=rho and one for r>=2rho. Filter the source:

```text
S_rho=zeta_rho S=partial_z(zeta_rho b^2),
Phi_rho=(-L5)^-1 S_rho,
J_rho=r^3 partial_r Phi_rho.
```

In the actual parent equation these are the source contributions

```text
chi_t=nu L5 chi+(-L5)^-1(-v.grad eta)+Phi_rho+Phi_core,
Phi_core=(-L5)^-1((1-zeta_rho)S).
```

S_rho includes every source at r>=2rho and a portion of the transition
annulus rho<r<2rho. The complementary source is supported in r<=2rho.
The estimates below use the smaller support radius rho of the paid part.

This decomposition retains the exact inverse-Laplacian response throughout
space. It does not identify distant source support with a localized
pressure field. The complementary source has its own complementary
nonlocal response.

The source inequality and its resulting reserve are

```text
||S_rho||_5^2 <= 4 rho^(-6) D_Gamma,
R_rho=C4/(3nu rho^6),
R_rho(t)+integral_0^t ||S_rho||_5^2 ds <= C4(0)/(3nu rho^6).
```

L5 is the radial restriction of the five-dimensional Laplacian. Plancherel
therefore gives the full Hessian estimate

```text
||Hess_5 Phi_rho||_5^2=||S_rho||_5^2.
```

The Hessian includes its radial tangential components. Its Fourier symbol
has squared Frobenius norm `sum_ij xi_i^2 xi_j^2/|xi|^4=1` away from zero.
The homogeneous inverse fixes the response; this assertion does not demand
an L2 bound for the inverse potential itself. The measure used in ||.||_5
is a constant multiple of the usual radial R5 measure, so the same equality
holds with this normalization.

There is also a uniform bound for the current forecast. Since zeta is
independent of z, the multiplier for
`grad_horizontal(-Delta_5)^-1 partial_z` has norm at most 1/2. Thus

```text
||J_rho/r^3||_5^2
  <= (1/4)||zeta_rho b^2||_5^2
  <= C4(t)/(4rho^6) <= C4(0)/(4rho^6).
```

The scalar symbol bound follows from
`4|xi_horizontal|^2 xi_z^2 <= (|xi_horizontal|^2+xi_z^2)^2`.
These estimates control this part of the source and response repeatedly,
but do not bound its product with arbitrary high vorticity, its full time
derivative J_t, or the near-axis source left in the complementary field.

### Transported histories give an accumulated radial-strain bound

The same resource controls more than the instantaneous elliptic response.
Assume also `eta(0) in L2(dx)`, as for smooth axisymmetric Schwartz data.
Fix an original horizon H>0, and on each available smooth prefix solve
the linear equation with the actual full meridional drift:

```text
g_t+v.grad g=nu L5 g+S_rho,       g(0)=eta(0),
eta_core=eta-g,
(eta_core)_t+v.grad eta_core=nu L5 eta_core+(1-zeta_rho)S,
eta_core(0)=0.
```

This is a split by source history. A source created outside r=2rho may
subsequently be transported inside it and remains part of g. Both parts
retain the same fully coupled v; neither is asserted to solve an independent
Navier--Stokes equation. Uniqueness of the linear evolution makes the split
consistent under restriction to shorter prefixes.

The physical L2 energy law has a favorable axis term:

```text
(1/2)d_t ||g||_2^2+nu ||grad g||_2^2
  +2pi nu integral g(0,z,t)^2 dz=integral g S_rho dx.
```

The checker retains the full flux
`v g^2/2-nu grad(g^2/2)-nu g^2 e_r/r` before integration. Incompressibility
cancels transport in the physical measure. Since the source is supported
at r>=rho, its earlier bound implies

```text
integral_0^t ||S_rho||_2^2 ds <= C4(0)/(3nu rho^8),
Y=||eta(0)||_2+sqrt(H C4(0)/(3nu rho^8)),
sup_[0,t] ||g||_2 <= Y,
integral_0^t ||grad g||_2^2 ds <= Y^2/(2nu),       t<=H.
```

For the last estimate use
`||g(s)||_2<=||g(0)||_2+integral_0^s ||S_rho||_2`, integrate the product
with `||S_rho||_2`, and then apply Cauchy--Schwarz in time. No bound on
the actual drift's size appears in Y.

Let `a_paid=-partial_z(-L5)^-1 g`. The axisymmetric elliptic estimates
`||grad a_paid||_2<=||g||_2` and
`||grad^2 a_paid||_2<=||partial_z g||_2` are those of
[Wei, Lemma 2.1](https://arxiv.org/html/1508.03318v1#S2).
The homogeneous three-dimensional Sobolev interpolation bound then gives

```text
||a_paid||_infinity <= C_BS ||g||_2^(1/2) ||grad g||_2^(1/2),
integral_0^t ||a_paid||_infinity ds
  <= M_H := C_BS H^(3/4) (2nu)^(-1/4) Y,       t<=H.
```

C_BS is a universal constant. The time exponent follows from Holder
applied to `||grad g||_2^(1/2)`. Every quantity in M_H is fixed from the
original datum, nu, H and rho. Smoothness of the available prefix justifies
constructing g; its unknown future norms do not enter this estimate.

The actual radial strain decomposes exactly as

```text
a=a_paid+a_core,
a_core=-partial_z(-L5)^-1 eta_core.
```

Thus all initial meridional vorticity and all subsequent source histories
generated at r>=2rho have a bounded contribution to accumulated radial strain,
even under the actual interacting drift. The residual is generated by
the source supported in r<=2rho, retains its subsequent transport and acts nonlocally.
It is not a spatial cutoff of the current strain. Neither this bound nor
the decomposition controls the full three-dimensional strain tensor.

### Removing the radial weight restores the compression bill

For a radial test weight `w=r^(-beta)`, the full integrated defect is

```text
E_beta=integral r^(-beta) Gamma^4 dx,
E_beta'=-12nu integral r^(-beta) Gamma^2 |grad Gamma|^2 dx
        -beta integral a r^(-beta) Gamma^4 dx
        +nu beta(beta-2) integral r^(-beta-2) Gamma^4 dx.
```

This formula assumes its integrability and vanishing boundary terms; the
checker retains the complete local flux before those assumptions.
The exponent beta=0 removes the compression term. The source-scale
exponent beta=6 gives `B=<b^4>_5`. In the b variables its exact balance is
particularly simple:

```text
B'+3nu ||S||_5^2+12nu <b^2 b_r^2>_5=-6<a b^4>_5,
a=u_r/r.
```

Thus the full source reserve `B/(3nu)` has the signed radial-compression
cost `-(2/nu)<a b^4>_5`. This term is not replaced by its absolute value or
set to zero. Bounding its accumulated contribution from the original datum
would extend the source payment into the axis region; that estimate remains
open here and would still need to be connected to full stretching.

A moving tube radius also has a cost. With rho=rho(t)>0,

```text
R_rho'+||S_rho||_5^2 <= -6(rho'/rho)R_rho.
```

Shrinking the tube makes the right side positive. Dropping it would
replenish the allowance by changing the observation scale.
Differentiating the moving filtered response would additionally introduce
`(partial_t zeta_rho)S`; the displayed resource inequality is not an
estimate for that response derivative.

### A conditional compression potential with an exact physical consumer

The full source payment has a direct backward-weight formulation. Let
W(t,r,z)>=1 be a smooth weight with the necessary moments and boundary
limits, along the actual solution. Its exact physical balance is

```text
d/dt <W b^4>_5
  =<b^4 (W_t+v.grad W+nu L5 W-6aW)>_5
    -12nu <W b^2 |grad b|^2>_5.
```

Thus the sufficient inequality

```text
W_t+v.grad W+nu L5 W-6aW <= 0,       W>=1
```

makes `R=<W b^4>_5/(3nu)` pay `||S||_5^2` on every compatible segment.
The initial allowance must be bounded from the original datum uniformly
over all available prefixes. No such general bound is established here.
This is a physical source criterion, not yet the full signed-stretching
criterion used by continuation.

For W=exp(psi) the exact logarithmic condition is

```text
psi_t+v.grad psi+nu L5 psi+nu |grad psi|^2-6a <= 0,
psi>=0.
```

Its quadratic Hamiltonian has the identity

```text
nu |p|^2 = sup_q [q.p-|q|^2/(4nu)],
nu |p|^2-[q.p-|q|^2/(4nu)]=|q-2nu p|^2/(4nu).
```

Here v and a remain the actual fluid fields. A drift q in this variational
description changes the auxiliary sampling process; it is not a force
added to Navier--Stokes.

There is also a direct stochastic interpretation without identifying
arbitrary auxiliary controls with fluids. Lift the meridional drift to
R5 as `(a x_1,...,a x_4,u_z)` and use the diffusion with this drift and
covariance `2nu I`. It exactly represents the scalar L5 operator; it is
not a claim that the physical fluid lives in five dimensions. Ito's formula
shows that

```text
exp(-6 integral_t^s a(q,X_q) dq) W(s,X_s)
```

is a local supermartingale under the displayed weight inequality.
Localization, integrability and optional stopping imply that W dominates
the corresponding expectations stopped before the horizon, because W>=1.
An un-stopped backward Feynman--Kac solution need not be >=1; that obstacle
cannot be omitted when paying the unweighted source cost.

Bounding this weighted compression history from the full initial fluid is
the remaining construction problem for this criterion. Merely solving a
backward equation using the unknown future velocity, or defining its
initial value by an uncontrolled supremum, supplies no finite a priori
allowance. The differential identities and Hamiltonian are symbolically
checked; the stochastic implication is analytic and conditional on the
stated hypotheses.

The paid radial history can be removed from this conditional construction
without giving it a new allowance. Put

```text
Lambda(t)=6 integral_0^t ||a_paid(s)||_infinity ds <=6M_H,
W_paid(t)=exp(6M_H-Lambda(t)) >=1.
```

If W_core>=1 satisfies the same weight inequality with a_core in place of
a and the actual full drift v, then W=W_paid W_core satisfies it for a.
The exact extra term is
`-6 W_paid W_core (||a_paid||_infinity+a_paid)<=0`.
The initial allowance is multiplied by the finite factor exp(6M_H), fixed
from the original datum. The remaining task is to bound the initial
weighted cost of W_core through the actual inside-tube generation history.
This is still a source-budget task; full stretching and general angular
defects remain separate continuation obligations.

### Two adversarial checks

For the earlier phases
`b=exp(-r^2-2z^2)` and
`chi=sigma z(1-3r^2+4z^2)b/2`, sigma=+1 or -1, exact Gaussian integration
gives, with `K_j=2pi sqrt(pi/(2j))`,

```text
B=K4/32, C4=3K4/256,
<b^2 |grad b|^2>_5=3K4/32,
D_Gamma=3K4/128, ||S||_5^2=K4/8,
<a b^4>_5=-(2sigma/625)K5.
```

At nu=1/1000 the complete physical rates are

```text
B'/K4=-9nu/8+(12sigma/625)sqrt(4/5),
C4'/K4=-9nu/32.
```

B grows on the positive phase and falls on the negative phase, while C4
decreases on both. These are actual initial rates of smooth unforced data;
continuity gives short intervals with the same strict signs. This refutes
monotonicity of the unweighted source-scale stock, not a full-datum
integrated allowance.

Concentration supplies a second exact test. Under the physical NS scaling,
C4 has degree -3, D_Gamma degree -1, and ||S||_5^2 degree 5. On the scaled
Gaussian data,

```text
||S_lambda||_5^2 / D_Gamma_lambda=(16/3)lambda^6.
```

No one fixed coefficient C>=0 makes `C C4/(3nu)` pay the full source norm
for all these data: its initial payment fails when `lambda^6>3C/4`.
The factor rho^(-6) is therefore not removable by a uniform comparison.
This does not refute a coefficient or cutoff chosen from the full datum.

### Exact scope in forced and general three-dimensional flows

Without axisymmetry, the same physical circulation variable satisfies
an equation with the additional term

```text
A_Gamma=2nu partial_theta(u_r)/r-partial_theta(p)+r f_theta.
```

Its quartic balance gains `4 integral Gamma^3 A_Gamma dx`. Angular pressure
and vector diffusion are genuine defects even when the fluid force is zero.
They are checked from the full cylindrical vector equation.

Even in exact axisymmetry, a meridional external force can add
`curl(f)_theta/r` to the eta equation while f_theta=0. The circulation
budget may then remain valid but pays only S, not this extra source.
It cannot, by itself, distinguish every forced construction from an
unforced flow. The coupled pressure/strain evolution and the full signed
stretching remain necessary for the regularity goal.

Run `python3 -O labs/circulation_source_reserve.py`. The differential,
Gaussian and Fourier-symbol identities are checked exactly. Spatial and
time integration, moment propagation and the Fourier norm consequences
are analytic, not Lean-certified. No Lean declarations or axioms change.

## Physical compression weight and its continuation consumer

`physical_compression_weight.py` checks the physical-measure version of the
preceding source criterion, including the axis boundary, its sampling
generator and adversarial Gaussian data. The resulting **analytic conditional
criterion reaches gradient-energy continuation in the axisymmetric whole-space
class**. A uniformly funded weight is not constructed. General three-dimensional
angular defects and the periodic problem remain outside this reduction.

Use the same actual unforced axisymmetric equations, positive viscosity,
regular axis and sufficient decay. Write `dx=2pi r dr dz`,
`b=u_theta/r`, `eta=omega_theta/r`, `a=u_r/r`, `v=(u_r,u_z)` and
`S=partial_z(b^2)`. Initial quantities used below are finite for smooth
axisymmetric Schwartz data. None of the following constants uses a norm
read off the unknown future solution.

### Physical balance, boundary and uniform funding obligation

Define `Lminus=partial_rr-partial_r/r+partial_zz`. For a smooth even radial
weight W with the requisite integrability and vanishing flux at infinity,

```text
I(t)=integral W b^4 dx,
D_W=W_t+v.grad W+nu Lminus W-8aW,
I'+12nu integral W b^2 |grad b|^2 dx
   +4pi nu integral W(t,0,z)b(t,0,z)^4 dz
 =integral b^4 D_W dx.
```

The local flux before integration is
`W[v b^4-nu grad(b^4)-2nu b^4 e_r/r]+nu b^4 grad W`.
Its outward flux through r=epsilon tends to the displayed positive axis
term. The axis cannot be discarded on the grounds that it has zero volume.
The conjugation `W_5=r^(-2)W` gives

```text
(partial_t+v.grad+nu L5-6a)(r^(-2)W)
 =r^(-2)(partial_t+v.grad+nu Lminus-8a)W.
```

W_5 is singular at the axis. Its lifted flux has the same nonzero limit,
so the previous smooth lifted-weight formula cannot be applied with its
boundary silently set to zero.

For an original H>0 the precise funding obligation is: there is a finite
`B_H(u0,nu)` such that, on **every** available smooth prefix `[0,T]`,
`0<T<=H`, a weight satisfies

```text
W>=1,       D_W<=0,
integral W(0,x)b(0,x)^4 dx <= B_H(u0,nu).
```

The weight also satisfies the smoothness, moment and boundary hypotheses
of the balance. The same B_H must work for all prefixes. Weights may depend
on the prefix; their initial bounds cannot depend on its unknown solution
norms. The balance uses one weight over each complete prefix and does not
give a new allowance at intermediate seams. It yields

```text
I(t)+3nu integral_0^t ||S||_2^2 ds <= I(0),
integral_0^t ||S||_2^2 ds <= P_H:=B_H/(3nu).
```

All these source norms now use physical dx. Constructing weights from a
future-dependent equation without proving the bound B_H does not meet
the funding obligation.

### From this source payment to full gradient energy

Here is the analytic continuation implication, with finite constants
displayed to make the quantifiers explicit. Define

```text
Y_H=||eta0||_2+sqrt(H P_H),
A_H=C_BS H^(3/4)(2nu)^(-1/4)Y_H.
```

Apply the preceding physical L2 propagator estimate to the **full** eta
equation, with source S. It gives
`sup||eta||_2<=Y_H`, `integral||grad eta||_2^2<=Y_H^2/(2nu)` and
`integral_0^t||a||_infinity<=A_H`. This uses the actual interacting v.
The elliptic step is the axisymmetric estimate of
[Wei, Lemma 2.1](https://arxiv.org/html/1508.03318v1#S2), followed by
homogeneous Sobolev interpolation as above.

The two angular-velocity equations and maximum principles give

```text
b_t+v.grad b=nu L5 b-2ab,
(u_theta)_t+v.grad u_theta=nu(Delta_3-r^(-2))u_theta-a u_theta,
sup||b||_infinity <= L_H:=||b0||_infinity exp(2A_H),
sup||u_theta||_infinity <= D_H:=||u_theta0||_infinity exp(A_H).
```

The angular velocity vanishes at the axis; its singular diffusion term
has the favorable sign. No initial circulation moment is needed for this
particular conditional implication. The earlier outside-tube payment
still has its separately stated circulation-moment hypothesis.

For `Omega=omega_theta=r eta`, the actual angular-vorticity equation gives

```text
(1/2)d_t||Omega||_2^2
 +nu(||grad Omega||_2^2+||Omega/r||_2^2)
 =integral a Omega^2 dx-integral b u_theta partial_z Omega dx.
```

Absorb the second term using half the gradient dissipation and the original
kinetic energy `E0=||u0||_2^2`. Gronwall yields the uniform bound

```text
sup||Omega||_2^2 <= Q_H
 :=exp(2A_H)[||Omega0||_2^2+H L_H^2 E0/nu].
```

The meridional velocity `V=u_r e_r+u_z e_z` is divergence free and has
curl `Omega e_theta`. Hence `||V||_6<=C_S||Omega||_2`. Interpolation between
the swirl's L2 energy and L-infinity bound gives

```text
sup||u||_6 <= U_H:=C_S sqrt(Q_H)+E0^(1/6)D_H^(2/3).
```

Finally test the full NS equation against `-Delta u`. With
`Z=||grad u||_2^2` and `D=||Delta u||_2^2`, incompressibility removes the
pressure and Sobolev interpolation bounds its nonlinear term by
`C U_H Z^(1/4)D^(3/4)`. Young's inequality and Gronwall imply

```text
sup_[0,T] Z <= Z(0) exp(C nu^(-3)H U_H^4),       T<=H.
```

C_BS, C_S and C are universal constants. This is precisely a bound of the
form consumed by `WholeSpaceViscousFlow.hasNSEvolution_of_orderOne_bound`
in `WholeSpaceEnstrophyContinuation.lean`. Rotational invariance and
uniqueness preserve the axisymmetric class. This argument is analytic;
the axisymmetric hypotheses, weighted PDE calculations and norm estimates
have not been assembled into a new Lean theorem. In particular the
formal consumer's arbitrary-data hypothesis is not discharged.

### The actual sampling process and its axis deformation

For `W=exp(psi)` the condition is

```text
psi_t+v.grad psi+nu Lminus psi+nu|grad psi|^2-8a<=0,
psi>=0.
```

The physical-measure adjoint changes the sampling geometry. In squared
radius `Y=r^2`, its diffusion can be written, before localization limits,

```text
dY=2a(t,sqrt(Y),Z)Y dt+sqrt(8nu Y)dB1,
dZ=u_z(t,sqrt(Y),Z)dt+sqrt(2nu)dB2.
```

B1 and B2 are independent Brownian motions. Y=0 is absorbing in radius;
axial motion continues there. For smooth regular coefficients, the
squared-radius generator is
`2aY partial_Y+u_z partial_Z+4nu Y partial_YY+nu partial_ZZ`.
This is the sampling process of the weighted adjoint, not the physical
three-dimensional particle process.
Ito's formula makes `exp(-8 integral a)W` a local supermartingale under
the weight inequality. With localization and the stated integrability,
W dominates the corresponding stopped exponential expectations. Killing
the entire process with zero payoff on reaching the axis would lose the
required boundary value `W>=1`.

The quadratic Hamiltonian is equally explicit. Writing
`psi(t,r,z)=Psi(t,Y,z)`, maximize
`2sqrt(Y)q1 Psi_Y+q2 Psi_z-(q1^2+q2^2)/(4nu)` over q1,q2. Its value is
`nu(4Y Psi_Y^2+Psi_z^2)`. Radial control vanishes at Y=0. These controls
alter the auxiliary sampling process; physical v and a are held fixed.

Let `w(t,z)=W(t,0,z)` and `U(t,z)=u_z(t,0,z)`. Smooth even radial
regularity and actual incompressibility imply the necessary axis condition

```text
w_t+U w_z+nu w_zz+4U_z w<=0,       w>=1,
U_z=-2a(t,0,z).
```

Radial curvature cancels here: `Lminus W|axis=w_zz`. Along the additive
one-dimensional diffusion `dZ=U dt+sqrt(2nu)dB`, the derivative J with
respect to its starting point satisfies `dJ=U_z J dt`, `J(t)=1`.
Consequently w must dominate the stopped expectations of J^4, under
the same localization and integrability conditions. This identifies a
specific stochastic deformation moment required by the candidate weight.
Neither that moment nor its initial weighted cost is bounded here.

The true axial momentum equation, differentiated before taking the axis,
also identifies what can sustain this deformation. With `q=U_z`,

```text
q_t+U q_z=nu(Delta_3 partial_z u_z)|axis-q^2-p_zz|axis.
```

The quadratic term damps positive axial expansion. The full radial second
derivatives in the diffusion term and the nonlocal pressure curvature
remain. Dropping either would replace the actual fluid by a different
model. This is a deterministic physical evolution law; inserting it into
the stochastic process additionally requires its complete Ito correction.

### Paid histories and failed static radial weights

The earlier history decomposition still applies. If the paid radial strain
has `integral||a_paid||_infinity<=M_H`, its physical-measure factor is now

```text
W_paid(t)=exp(8M_H-8 integral_0^t||a_paid||_infinity ds)>=1.
```

If W_core satisfies the physical weight inequality with a_core and the
same full v, `W_paid W_core` satisfies it with a. The extra defect is
`-8W_paid W_core(||a_paid||_infinity+a_paid)<=0`. The initial multiplier
is exp(8M_H), fixed from the original datum; the inside-tube history weight
still needs its own funding.

On the earlier Gaussian phases, with `K_j=2pi sqrt(pi/(2j))`, the physical
quartic and source quantities are

```text
integral b^4 dx=K4/8,
integral b^2|grad b|^2 dx=K4/4,
||S||_2^2=K4/2,
integral a b^4 dx=-sigma K5/25,
d_t integral b^4 dx /K4=-5nu+(8sigma/25)sqrt(4/5).
```

At nu=1/1000 the positive phase grows and the negative phase decays.
The axis contributes `2nu K4` to the dissipative balance; omitting it
already fails this exact Gaussian calculation.

There is a stronger pointwise failure for this particular sufficient
weight ansatz. In the positive phase, `a(0,0)=-1/2`. Every smooth,
time-independent radius-only weight with W(0)>0 has

```text
D_W(0,0)=4W(0)>0.
```

Its radial shape, even if chosen from the full datum, cannot change this
axis defect. Smoothness makes the defect positive in a neighborhood as
well. Thus such weights cannot satisfy the proposed pointwise inequality
for all these actual unforced data. This does not refute time-dependent
or z-dependent weights, integrated cancellations in another reserve,
finite datum-dependent allowances, or regularity.

Run `python3 -O labs/physical_compression_weight.py`. It checks the local
balances, both boundary representations, sampling generator, Hamiltonian,
physical evolution identities and Gaussian tests with exact symbolic
arithmetic. PDE integration, stochastic implications and the continuation
argument are analytic, not Lean-certified. No Lean declarations or axioms
change. The central open task is the uniform initial funding of an evolving
weight through the coupled pressure and source histories.

## Axial deformation retains its actual pressure suppliers

`axis_deformation_pressure.py` tests a specific proposed payment for the
fourth deformation moment required by the preceding axis condition.
It derives the complete forward Ito generator, calculates the canonical
whole-space pressure of smooth Gaussian data, and refutes pointwise
monotonicity of every frozen positive quadratic metric squared on this
deformation state. A datum-funded horizon factor still pays the already
controlled distant-pressure contribution. The remaining signed pressure
work and quadratic variation are explicit and unpaid.

### Complete stochastic acceleration

Along an available smooth axisymmetric unforced prefix, set
`U(t,z)=u_z(t,0,z)` and `q=partial_z U`. Use the axis sampling process
`dZ=U dt+sqrt(2nu)dB`. Its derivative J in the initial axial coordinate
satisfies `dJ=qJ dt`, with J initially one. Define `V=Jq`. The full laws are

```text
dJ=V dt,
dV=J F dt+sqrt(2nu)J q_z dB,
F=-p_zz|axis+nu[(Delta_3 partial_z u_z)|axis+q_zz].
```

All fluid quantities are evaluated along the same Z. The additional
`nu q_zz` is from forward stochastic sampling. It adds to the physical
viscous term; it does not cancel it. The deterministic `-q^2` cancels
when differentiating V=Jq, but does not make the deformation dissipative.
In particular,

```text
drift(V^2)=2VJ F+2nu J^2 q_z^2,
drift(JV)=V^2+J^2 F.
```

The noise-square term is nonnegative. Treating the deterministic strain
equation as an ordinary differential equation along the noisy path would
miss both this term and the extra axial diffusion.

For a fixed time scale ell>0, the proposed nonnegative observable is

```text
Q=J^2+ell^2 V^2,       E=Q^2>=J^4.
L E=4JVQ(1+ell^2 F)
    +4nu ell^2 J^2 q_z^2(J^2+3ell^2 V^2).
```

L denotes the generator along the actual fluid-driven sampling process.
A bound `L E<=k_ell E` follows with
`k_ell=2|1+ell^2 F|/ell+(9/2)nu ell^2 q_z^2`. The diffusion constant
comes from the exact identity

```text
9Q^2-8J^2(J^2+3ell^2 V^2)=(J^2-3ell^2 V^2)^2.
```

This is only a conditional comparison: k_ell depends on the future fluid
and is not an initial-data allowance. The signed expression for L E is
retained in the actual payment target.

### Canonical pressure with unchanged initial axis data

Consider the whole-space family

```text
chi=z(A/2+C r^4) exp(-r^2-z^2),
b=B exp(-r^2-z^2),
u_r=-r chi_z,    u_z=2chi+r chi_r,    u_theta=r b.
```

In Cartesian coordinates all components are polynomials times a Gaussian.
They are smooth, divergence free and finite energy, and therefore start
actual local unforced solutions at every positive viscosity. The pressure
is the decaying canonical pressure, determined by
`-Delta_3 p=tr[(grad u)^2]`; it is not a supplied force or a free Hessian.

Varying C leaves the entire initial axis velocity and strain unchanged:

```text
U0(z)=A z exp(-z^2),
q0(z)=A(1-2z^2) exp(-z^2).
```

It also leaves `(Delta_3 partial_z u_z)|axis` unchanged. Nevertheless,
the actual pressure curvature at the origin is

```text
p_zz(0)=-9A^2/14-8AC/385+2B^2/5-128C^2/455,
F(0)=9A^2/14+8AC/385-2B^2/5+128C^2/455-20nu A.
```

The checker calculates this curvature from the three-dimensional heat
resolvent of the complete pressure source. For each Gaussian monomial it
checks a rational antiderivative after `x=sqrt(1+8h)` and an independent
factorial endpoint formula. A separate computation of the transverse
pressure Hessian verifies `2p_xx+p_zz=-tr[(grad u)^2]` at the origin.
The divergence of the full vector convection independently reproduces
the pressure source, including the swirl basis terms.

Thus local axis data, even with the displayed lateral-diffusion trace,
do not determine the pressure supplier. The C-dependent field vanishes
to high radial order on the axis, but is not supported beyond a fixed
positive radius. No spatial-separation claim is made for this family.
Its full initial energy records the hidden parent:

```text
||u0||_2^2=pi^(3/2)sqrt(2)
           [7A^2+18AC+16B^2+162C^2]/128.
```

The examples do not have equal full energy and do not refute an allowance
depending on the full datum.

### A realized expanding state defeats every frozen quadratic metric

Take the exact parameters

```text
A=B=1, C=2, nu=4101/200200>0.
```

At the origin the actual values are

```text
q=1, q_z=0, p_zz=-14111/10010, F=1.
```

At the initial deformation state `(J,V)=(1,1)`, the stochastic velocity
noise vanishes and the drift of `(J,V)` is exactly `(1,1)`. Consequently,
for **every fixed positive definite matrix P**, including one selected
from this full datum,

```text
X=(J,V)^T,       E_P(J,V)=(X^T P X)^2,
(L E_P)(1,1)=4E_P(1,1)>0.
```

This also follows from Euler's identity for homogeneous functions; the
checker verifies the polynomial identity for arbitrary matrix entries.
For the diagonal family it becomes
`(L E_ell)(1,1)=4(1+ell^2)^2>0` for every ell>0.
Local smoothness and stopping in a compact neighborhood give an actual
short-time increase of the corresponding stopped expectation. This
interval implication is analytic; no uniform turnover time is claimed.

With A=B=1 and the same viscosity, varying C gives
`F(0)=(1408C^2+104C-835)/5005`. Thus C=0 gives `-167/1001`, whereas C=2
gives 1, with the same initial axial velocity, strain and diffusion trace.
The variation is generated by surrounding unforced fluid through its
canonical pressure. It does not realize an arbitrary forcing history or
embed a forced singular solution.

The same expanding state is realized with no swirl: take A=1, B=0, C=2
and nu=1621/40040. Then the earlier source-free eta history already has a
finite datum-controlled bound. This separates failure of the proposed
monotonicity from failure of finite history payment.

The refuted assertion is a nonpositive pointwise/local-stopped drift for
a frozen homogeneous metric on `(J,V)`. A time-dependent or spatially
adaptive metric has additional derivative terms and is not covered.
Neither a finite initial allowance for J^4 nor a reserve retaining the
pressure suppliers is refuted. Growth of E_P also does not by itself
show that J^4 exceeds E_P's initial value.

### A whole-horizon payment survives for distant pressure

Reuse the earlier `PressureBoundaryResponse` estimate at a fixed radius
R>0, with the same physical pressure normalization:

```text
|p_zz_far(t,x)|<=K_R:=6||u0||_2^2/(pi R^5).
```

It holds at arbitrary observation positions, including the random Z.
Write
`F=F_near-p_zz_far`, where
`F_near=-p_zz_near+nu[(Delta_3 partial_z u_z)|axis+q_zz]`.
The full actual fluid and q_z remain unchanged in this decomposition.

For the quartic metric E, the distant contribution is
`-4ell^2 JVQ p_zz_far<=2ell K_R E`. Its kinematic contribution satisfies
`4JVQ<=2E/ell`. Hence, for an original H and

```text
c=2/ell+2ell K_R,
Psi(t,J,V)=exp(c(H-t))E(J,V),
C_near=4ell^2 JVQ F_near
       +4nu ell^2 J^2 q_z^2(J^2+3ell^2 V^2),
```

the actual generator obeys

```text
(partial_t+L)Psi <= exp(c(H-t))C_near.
```

The initial multiplier exp(cH) uses only the original energy, R, ell and
H. It pays these two contributions throughout every available prefix,
without a new clock at intermediate seams. Under localized optional
stopping the remaining obligation is the signed expectation of the
integrated right side. Absolute values have not been inserted into
C_near. Its pressure work and its positive quadratic variation remain
uncontrolled from the initial datum.

The calibrated Gaussian still detects the missing part after this payment.
Set ell=1 and choose the datum-fixed radius `R^5=12||u0||_2^2/pi`, so
K_R=1/2 and c=3. At the initial state, the full clocked generator is
`(4-3)Psi=Psi>0`. Thus the already paid distant pressure and kinematic
terms do not alone close this reserve.

An external axial force adds `partial_z f_z|axis` to F, using the actual
pressure of the forced equation, and adds
`4ell^2 JVQ partial_z f_z|axis` to the quartic drift. In unforced flow
that term is absent, but the internal pressure example shows that absence
alone does not give a sign to C_near. A quantitative bound must use the
evolution of its physical suppliers.

### Remove the parents that already have a payment

The Gaussian meridional parents above are included in the earlier
circulation/propagator payment. They are not a new obstruction to the
remaining source-history problem. Use that complete history split before
introducing extra derivative costs for already controlled fields:

```text
q=q_paid+q_core,       q_paid=-2a_paid|axis,
integral_0^t||a_paid||_infinity ds<=M_H,
J_paid=exp(integral q_paid along Z),
J_core=exp(integral q_core along Z),
J=J_paid J_core,       J^4<=exp(8M_H)J_core^4.
```

This split follows generation and transport histories; it is distinct
from the fixed-distance pressure split above.
This is a pathwise bound along the same actual sampling trajectory. It
does not factor expectations or discard a covariance. It removes all
initial meridional parents and all outside-cutoff source histories at
their already established, original-datum cost. It requires no separate
estimate of derivatives of q_paid. The pure no-swirl example has q_core=0
and is therefore paid despite its frozen-metric failure.

### A positive burst remains in the generated core

To test this residual directly, start from the actual pure-swirl datum

```text
chi0=0,       b0=exp(-r^2-z^2),       nu>0.
```

Initially eta and q vanish. The actual unforced equation gives
`eta_t=partial_z(b0^2)`. The five-dimensional heat resolvent therefore
gives the initial axial-strain production

```text
q_1(z):=partial_t q(0,0,z)
 =2partial_zz(-L5)^(-1)(b0^2)(0,z)
 =integral_0^1 tau^(3/2)(4z^2 tau-1) exp(-2z^2 tau) d tau.
```

This calculation includes the canonical meridional response; it is not a
pressure-free model. It is independent of nu at this initial instant
because the initial meridional field is zero.

At z=1 a simple analytic lower bound suffices. The absolute negative
contribution on `[0,1/4]` is at most 1/80. On `[1/2,1]`, use
`tau^(3/2)>=1/4`, `4tau-1>=1` and `exp(-2tau)>1/9`, the last following
from e<3. This positive portion exceeds 1/72; the remaining interval is
nonnegative. Thus `q_1(1)>1/720`.

The positivity survives removal of an actually paid outside source.
Choose the previous smooth cutoff with rho=5, zero for r<=5 and one
for r>=10. At t=0 its contribution is
`q_paid_prime=2partial_zz(-L5)^(-1)(zeta b0^2)` on the axis. The fundamental
solution `N5=|x|^(-3)/(8pi^2)` satisfies
`|2partial_zz N5(x)|<=3/(pi^2|x|^5)`. Every source in this component is
at distance at least rho from the axis observation. Consequently,

```text
|q_paid_prime(0,0,1)|
 <=3sqrt(pi)/(2^(5/2)rho^5)<3/(2rho^5)=3/6250,
delta:=q_core_prime(0,0,1)>1/720-3/6250>0.
```

This uses the full five-dimensional Gaussian mass and pi<4, without
assuming that the response is supported where its source is.

Initially q_core and all its spatial derivatives vanish. Along the actual
axis sampling path started at z=1, a localized short-time Ito expansion
therefore gives

```text
E[J_core(t)^4]=1+2delta t^2+O(t^3).
```

For the diagonal residual metric with V_core=J_core q_core, its expectation
has second derivative `4delta+4ell^2 delta^2>0` at zero. This is a real
finite burst generated by the residual source after the paid history has
been removed. The expansion is analytic for each fixed positive viscosity;
no uniform long-time remainder or recurrent growth is inferred.

It refutes a residual comparison with initial allowance exactly one and
no source payment, and refutes monotonicity of this normalized diagonal
residual metric. A positive allowance based on the initial swirl's ability
to generate parents is not refuted. The existing first-interval forecast
reserve already illustrates that kind of prefunding for a different
physical observable; renewing it over arbitrary horizons remains open.

The residual itself is not an independent NS solution. Its later equation
comes from `eta_core_t+v.grad eta_core=nu L5 eta_core+(1-zeta)S` under the
same full v. Applying `T=2partial_z(-L5)^(-1)` retains the commutator
`[v.grad,T]eta_core`, the full viscosity and `T((1-zeta)S)`.
Substituting q_core into the full-fluid Riccati law without those terms
would discard its hidden suppliers.

Run `python3 -O labs/axis_deformation_pressure.py`. Differential,
generator, Gaussian-resolvent, energy and scaling calculations are exact
symbolic checks. The residual-source calculation also checks its heat
kernel, change of variables and rational comparison constants. Local PDE
existence, resolvent identification, integral bounds, stochastic stopping
and history consequences are analytic. No Lean declarations or
axioms change. The original-data bound on the signed core history,
construction of a funded interior compression weight, and general
three-dimensional continuation remain open.

## Residual source funding retains parent transport

`residual_parent_transport.py` follows the generated component after the
previous paid-parent factorization. It supplies a finite allowance for
one direct source contribution and identifies the transport that remains.
The setting is an available smooth unforced axisymmetric whole-space
prefix, with regular axis and sufficient decay for the stated inverses,
integrations and stopped stochastic identities. It does not establish
arbitrary-data regularity or fund the entire residual.

### The residual is transported by the full fluid

Keep the same original cutoff and actual source-history split:

```text
beta=1-zeta_rho,   f=beta b^2>=0,
(partial_t+v.grad-nu L5)eta_core=partial_z f,
eta_core(0)=0,
K5=(-L5)^(-1),   T=2partial_z K5,
q_core=T eta_core=-2a_core.
```

The last field is defined off the axis by its elliptic formula. Its axis
trace is the residual axial strain; it is not asserted to equal a full
velocity's axial derivative away from the axis. The full lifted drift
has `div_5 v=2a`, although the physical three-dimensional velocity is
incompressible. The actual residual equation is

```text
(partial_t+v.grad-nu L5)q_core=C+sigma,
C=[v.grad,T]eta_core,
sigma=2partial_zz K5 f.
```

For `N5(y)=|y|^(-3)/(8pi^2)` and `k=2partial_z N5`, its commutator is

```text
C(x)=integral [(v(x)-v(y)).grad k(x-y)+2a(y)k(x-y)] eta_core(y) dy.
```

Integration by parts gives the second term. Dropping it would impose
incompressibility in the wrong dimension. The velocity difference makes
the differentiated kernel locally integrable for smooth v, retaining
the actual transport of the generated parents. The paid part of v has
not disappeared from this expression.

The current source stock also retains its physical evolution:

```text
(partial_t+v.grad-nu L5)f
 =-4a f-2nu beta|grad b|^2
   +b^2(v_r beta_r-nu L5 beta)-2nu beta_r partial_r(b^2).
```

Here the cutoff is fixed; no moving cutoff or clock is introduced. These
terms explain why a reserve depending on the current source must still
account for its parents and diffusion.

Along the same axis process `dZ=U dt+sqrt(2nu)dB`, write J for J_core
in this section and set `V=J q_core`. Its complete laws are

```text
dJ=V dt,
dV=J F_core dt+sqrt(2nu)J partial_z q_core dB,
F_core=q_core^2+nu(L5 q_core+partial_zz q_core)|axis+C|axis+sigma|axis.
```

The residual has no automatic full-fluid Riccati cancellation. In
particular, the displayed positive square must remain unless an actual
identity with the commutator or other terms pays it.

### Original energy funds a separated direct source

Fix delta>0. Split sigma by its Newtonian kernel at distance delta from
the observation. The far part uses the ordinary kernel

```text
2partial_zz N5(y)=(-3+15 y_z^2/|y|^2)/(4pi^2|y|^5), y!=0.
```

The near part retains both the principal value and the local contact
term `-2f(x)/5`. No singular contribution is discarded. Since beta is
between zero and one, the complete lifted mass obeys

```text
integral_R5 f <= integral_R5 b^2
  =pi ||u_theta(t)||_L2(R3)^2 <= pi E0,
E0=||u0||_L2(R3)^2.
```

Thus at every position, including the random observation,

```text
|sigma_far|<=K_delta:=3E0/(pi delta^5).
```

This pays a direct contribution to newly generated strain. It does not
pay every future transported effect of those source elements; C is
still present. The distance split is distinct from the original radial
source-history cutoff rho. Neither parameter varies with time.

For ell>0 set `Q=J^2+ell^2 V^2`, `E=Q^2>=J^4` and

```text
G=q_core^2+nu(L5 q_core+partial_zz q_core)|axis+C|axis+sigma_near|axis,
D_core=4ell^2 JVQ G
       +4nu ell^2 J^2(partial_z q_core)^2(J^2+3ell^2 V^2),
c=2/ell+2ell K_delta,
Psi=exp(c(H-t))E.
```

The mixed-moment bound `2ell|JV|<=Q` gives the actual inequality

```text
(partial_t+L)Psi<=exp(c(H-t))D_core.
```

One original-horizon factor pays the kinematic term and the separated
source. For E0>0, the choice `ell=1/sqrt(K_delta)` minimizes this comparison
rate and gives `c=4sqrt(K_delta)`. Since the residual initially vanishes,
`J(0)=1,V(0)=0,E(0)=1`. The corresponding initial multiplier for the full
deformation, including the preceding paid history, is

```text
exp(8M_H+4H sqrt(K_delta)).
```

The zero-energy datum gives the zero fluid and requires no such choice.
There is no reset at a history seam. The remaining sufficient axis
obligation is a finite original-datum bound A_H on

```text
E integral_0^tau exp(c(H-s))D_core(s) ds <= A_H,
```

uniformly over the initial axis position, available smooth prefixes up
to H and their localized stopping times tau. If established, it would
bound the full fourth deformation moment by
`exp(8M_H)[exp(cH)+A_H]`. This signed bound remains open. Defining A_H as
an uncontrolled future supremum would not prove it. Even this axis bound
would still need a funded interior physical weight and the subsequent
general three-dimensional and periodic obligations.

### Hidden parents change the next generated response

The test uses genuine compact smooth data. Let R^2=r^2+z^2 and take a
nonzero smooth radial B supported in R<1. Choose a smooth radial kappa
equal to one for R<=3 and zero for R>=4. Set

```text
b0=B(R^2),
chi0=C z r^4 kappa(R^2),
u_r=-r chi0_z, u_z=2chi0+r chi0_r, u_theta=r b0.
```

Both signs of C give smooth finite-energy divergence-free data and
actual local unforced solutions at every fixed nu>0. On the initial
source support, the meridional velocity is exactly
`v=(-C r^5,6C z r^4)`, with `a=-C r^4`. Along the entire initial axis,
U and q vanish, as does the trace `Delta_3 partial_z u_z`. For rho=5,
the initial source and its first time derivative are wholly assigned to
the core. This statement concerns these initial jets, not later support.

Define the positive finite initial moments

```text
M_j=integral_R5 |y|^j b0(y)^2 dy,
D=integral_R5 |grad b0|^2 dy.
```

Outside the swirl support, radial Newtonian integration gives, on z>1,

```text
K5(b0^2)(0,z)=M0/(8pi^2 z^3),
partial_t q_core(0,0,z)=sigma(z)=3M0/(pi^2 z^5)>0.
```

The next derivative retains both source evolution and transport:

```text
partial_tt q_core(0,0,z)=C H(z)-6nu D/(pi^2 z^5),
H(z)=1/(8pi^2) [3456M4/(35z^5)+4992M6/(7z^7)
                -21760M8/(11z^9)+161280M10/(143z^11)].
```

For z>=2 this coefficient is strictly positive. Indeed M8<=M6 because
the swirl support has R<1, and
`4*(4992/7)-21760/11>0`, so the M6 term pays the negative M8 term.
In particular `H(z)>=432M4/(35pi^2 z^5)>0`.

To identify every contribution, the table gives coefficients after
factoring `C M_(l+4)/(8pi^2 z^(l+5))`:

| l | sigma_t, nonviscous | T(v.grad S) | Difference |
|---|---:|---:|---:|
| 0 | 1152/35 | -2304/35 | 3456/35 |
| 2 | 384 | -2304/7 | 4992/7 |
| 4 | -11008/11 | 10752/11 | -21760/11 |
| 6 | 80640/143 | -80640/143 | 161280/143 |

These are finite angular moments of the Newtonian expansion. The source
stock derivative has angular degree at most six, and v.grad S at most
seven. Gegenbauer orthogonality removes all higher terms. Radial
integration by parts reduces them to the displayed M_j; smooth compact
support removes all boundary terms. Also `L5 sigma=0` outside the initial
source, so no physical diffusion of sigma was omitted there. The
remaining viscous term follows from the radial source-gradient mass D.

Start the actual axis sampling path at any fixed z>=2. The complete
time-dependent Ito generator gives

```text
d_tt E[J_core^4]|0=4sigma(z),
d_ttt E[J_core^4]|0
 =4[C H(z)+nu(-6D/(pi^2 z^5)+180M0/(pi^2 z^7))].
```

The coefficient 180 includes both time-ordered sampling-diffusion
contributions. Choose |C| large enough to dominate the displayed finite
viscous offset. Opposite signs of C then give opposite third moment
derivatives, while the positive second derivative is unchanged. These
localized short-time expansions are analytic for each fixed datum;
they do not assert a uniform turnover window or recurrent growth.

The two signs have the same b0, current source and its elliptic forecast,
entire initial axis velocity, axis diffusion trace, total energy,
initial eta L2 norm and previous scalar allowance M_H. They even have
the same initial canonical pressure: the meridional/swirl cross term
in `tr[(grad u)^2]` vanishes, so meridional reversal leaves its complete
Poisson source unchanged. The full initial velocities differ.

Thus those snapshots and scalar payments do not determine the next
generated deformation. Treating the paid parents as absent from
transport would give the wrong coefficient. An allowance can still
bound both signs using the original datum; this does not refute such
an allowance, the paid-parent factorization, or regularity.

### Test a source-funded forecast against the actual parent response

One specific candidate for the residual axis weight uses its first
stochastic strain rate rather than only the current strain. Write

```text
A=partial_t+U partial_z+nu partial_zz,
h=A q_core, tau=H-t,
psi=4tau q_core+2tau^2 h+Lambda tau^3, w=exp(psi).
```

The first two terms give a nonzero initial allocation for the newly
generated source. The complete logarithmic supersolution defect is

```text
A psi+nu psi_z^2+4q_core
 =2tau^2 A h-3Lambda tau^2
   +nu(4tau partial_z q_core+2tau^2 partial_z h)^2.
```

For the compact-parent test, initially h=sigma and
`A h=C H(z)+nu B_visc(z)`, where
`B_visc=-6D/(pi^2 z^5)+180M0/(pi^2 z^7)`. Thus the uncorrected choice
Lambda=0 fails for sufficiently large positive C. At the tested point
its initial psi is `2H^2 sigma>0`, so imposing the obstacle psi>=0 does
not remove this differential failure. A constant cubic correction must
at least satisfy, at this initial state,

```text
Lambda >= (2/3)[C H(z)+nu B_visc(z)]
          +(4/3)nu H^2 sigma_z(z)^2.
```

This is a necessary initial payment, not a sufficient full-history bound.
The scalar formula accounts for source generation but its evolution still
depends on the parent's phase. A dynamic correction must control A h and
the displayed gradient cost along the actual evolution. Choosing Lambda
from an uncontrolled future bound merely relocates the open estimate.
Failure of this particular forecast does not rule out other stochastic
weights or original-datum reserves.

Run `python3 -O labs/residual_parent_transport.py` for the exact symbolic
checks. Add `--quadrature` for an independent numerical integration of
the original kernels with the compact smooth profile
`B(R^2)=exp(-1/(1-R^2))` inside R<1. At quadrature orders 80 and 128,
both z=2 and z=3 agree with the moment formula to relative error below
`1.1e-14`. This is supporting numerical evidence, not a certified error
bound. PDE evolution, elliptic identification, integral inequalities and
stochastic interval conclusions remain analytic. No Lean declarations
or axioms change. The signed residual history and its original-datum
funding remain open.

## Smooth receivers and the complete generated-parent history

`source_receiver_duality.py` pairs the residual with an entire smooth
observation history before estimating it. In the same axisymmetric
whole-space class, it bounds both source generation and full parent
transport for this observable. Constants retain the receiver's first
two axial derivatives. Controlling those derivatives for the actual
deformation receiver, and passing to point observations, remain open.

Take a smooth unforced prefix `[0,T]`, `T<=H`, positive viscosity,
regular axis and sufficient decay for the integrals below. Fix the
original source cutoff rho and the compatible history split

```text
eta=omega_theta/r=g+eta_core,    eta_core(0)=0,
(partial_t+v.grad-nu L5)eta_core=partial_z f,
f=(1-zeta_rho)b^2>=0,    b=u_theta/r,
q_core=𝒯 eta_core,    𝒯=2partial_z(-L5)^(-1).
```

The axis trace of q_core is the residual axial strain. Both histories
retain the same full interacting v. The earlier
source estimate supplies

```text
sup_t ||g(t)||_L2(R3)<=Y,
Y=||eta(0)||_2+sqrt(H C4(0)/(3nu rho^8)),
C4(0)=integral_R3 (r u_theta(0))^4.
```

### The full source has a paid logarithmic concentration

Write `E=||u||_2^2`, `d=||grad u||_2^2`, so `E'=-2nu d`.
The lifted measure is `dy5=pi r^2 dx3`. The physical angular derivative
of u has components `(-b,u_r/r,0)` in the cylindrical orthonormal frame.
Consequently `integral_R3 b^2<=d`, and for any fixed L>0,

```text
B_L(t)=integral_R5 f(t) [1+log(1+L^2/r^2)] dy5
      <=pi [E(t)+L^2 d(t)],
R_L(t)=pi [H-t+L^2/(2nu)] E(t)>=0,
R_L'(t)+pi[E(t)+L^2 d(t)]=-2pi nu(H-t)d(t)<=0.
```

Here `log(1+x)<=x`, `0<=1-zeta_rho<=1`, and the angular gradient
comparison pay all source scales, including the axis limit. Thus

```text
integral_a^b B_L <= R_L(a)-R_L(b),
integral_0^T B_L <= pi [H+L^2/(2nu)] E0.
```

The same reserve is spent at every seam; there is no renewed allowance.
In particular L^2=4nu H costs at most `3pi E0 H`. This weaker observable
does not contradict the earlier failures of energy-only stretching or
caloric-renewal budgets.

`MettapediaNS.LogSourceReserve` certifies the scalar logarithmic comparison
and the reserve derivative, nonnegativity, interval payment and original
allowance along the existing whole-space `NSEvolution`. In particular,
`actual_interval_payment` pays `C(E+L^2 d)` on every compatible subinterval
using the same horizon, and `actual_initial_allowance` removes the final
nonnegative reserve. The spatial identification of B_L with this cost,
the physical source history and the receiver estimates below remain
analytic. This energy adapter does not certify those additional steps.

For a forced evolution the reserve rate has the additional term
`2pi[H-t+L^2/(2nu)]<u,force>`. The residual's equation also retains its
additional vorticity source and hence another receiver pairing. Finite
energy work alone does not remove that source; no forced construction
is ruled out by this partial observation estimate.

### Exact duality retains transport

Let m(t,z) be a smooth receiver with enough axial decay and prescribed
bounds `M1=sup|m_z|`, `M2=sup|m_zz|`. Define the signed observation and
its backward heat receiver on this prefix:

```text
I=integral_0^T integral_R m(t,z) q_core(t,0,z) dz dt,
w(t)=𝒯* [delta_R4 m(t)],      𝒯*=-2partial_z(-L5)^(-1),
rho(s)=integral_s^T exp(nu(t-s)Delta5) w(t) dt.
```

The residual's actual PDE and `eta_core(0)=rho(T)=0` give

```text
I = -integral_0^T integral_R5 f rho_z
    +integral_0^T integral_R5 eta_core div_5(v rho).
```

The second term is essential. Replacing the fluid propagator by heat
without this correction would erase the hidden parents. Set `A=r^2 rho`.
Physical incompressibility gives the exact identities, off the axis,

```text
L5(r^-2 A)=r^-2 Lminus A,
div_5(v r^-2 A)=r^-2 v.grad A,
I=pi integral_0^T integral_R3 [-f A_z+eta_core v.grad A],
Lminus=partial_rr-partial_r/r+partial_zz.
```

The Green boundary flux is also retained:

```text
r(A L5 eta-eta Lminus A)
 =partial_r[r(A eta_r-eta A_r)+2A eta]
  +partial_z[r(A eta_z-eta A_z)].
```

An instantaneous receiver has a nonzero renormalized axis trace:
`r^2 w=-(P_r*m_z)/(2pi^2)`, where
`P_r(z)=r^2/[2(r^2+z^2)^(3/2)]` has mass one. Its limit is
`-m_z/(2pi^2)`. The history receiver instead has
`A=O(r^2(1+|log r|))` and `r A_r=O(r^2(1+|log r|))` for bounded M1,
so its displayed Green axis flux vanishes for regular eta. These two
boundary behaviors must not be interchanged.

### Heat integration reduces the source singularity to a logarithm

The factorized heat kernel and the resolvent give

```text
|rho_z(s,r,z)| <= M2 K_nu(T-s,r),
K_nu(h,r)=2 integral_0^h da integral_(nu a)^infinity
                      (4pi u)^(-2) exp(-r^2/(4u)) du
 =[E1(x)+(1-exp(-x))/x]/(8pi^2 nu),
x=r^2/(4nu h),      E1(x)=integral_x^infinity exp(-u)/u du.
```

Since `exp(-u)<=1/(1+u)` and `1-exp(-x)<=x`,

```text
K_nu(h,r)<=[1+log(1+4nu h/r^2)]/(8pi^2 nu),
|integral_0^T integral_R5 f rho_z|<=3 M2 E0 H/(8pi nu).
```

The bound uses the actual evolving source, not its initial value. Heat
integration weakens its spatial singularity enough for the kinetic-energy
reserve to pay it over the full horizon.

### The full transport correction also has a smooth-receiver bound

Differentiate the explicit positive kernel before estimating. Uniformly
on the prefix, with deliberately conservative constants,

```text
|A_r|<=B_r=2M1 sqrt(H/nu)/pi^2,
|A_z|/r<=B_z=3M2 sqrt(H/nu)/(4pi^2),
|A_z|<=C_z=M2 H/(2pi^2).
```

For verification write `F(x)=E1(x)+(1-exp(-x))/x`. Then
`F'(x)=-(1-exp(-x))/x^2`. The radial bound is obtained from
`|A_r|<=M1(2r K-r^2 K_r)`. Use
`sqrt(x)E1(x)<=2`, `(1-exp(-x))/sqrt(x)<=1`, and
`x E1(x)<=exp(-x)`. The first follows from
`E1(x)<=log(1+1/x)<=2/sqrt(x)`; the logarithmic inequality follows by
integrating `1/(1+y)<=1/sqrt(y)`. The other two follow from
`1-exp(-x)<=min(x,1)` and the defining integral of E1.

Now retain `eta_core=omega_theta/r-g` in physical measure:

```text
integral_R3 |eta_core v.grad A|
 <=sqrt(2) B_r d + sqrt(2) B_z sqrt(E d)
   +(B_r+C_z) Y sqrt(E).
```

Indeed `||omega_theta||_2<=sqrt(2d)`, `||u_r/r||_2<=sqrt(d)` and
`||v||_2<=sqrt(E)`. These are physical derivative/energy estimates;
no bound on a fictitious independent residual fluid is used. The original
energy law yields `integral d<=E0/(2nu)` and
`integral sqrt(E d)<=E0 sqrt(H/(2nu))`. Therefore the complete transport
allowance is

```text
B_transport=pi sqrt(2) E0 [B_r/(2nu)+B_z sqrt(H/(2nu))]
            +pi(B_r+C_z) Y sqrt(E0) H,
|I|<=3M2 E0 H/(8pi nu)+B_transport.
```

This includes all mutually interacting meridional parents for this smooth
averaged observation. The constants depend on E0, Y, nu, H, M1 and M2.
If M1 and M2 come from an uncontrolled future receiver norm, it is only
a conditional estimate, not an original-datum payment for deformation.

### The remaining receiver obligation

For the actual axis process `dZ=U dt+sqrt(2nu)dB`, `U=u_z|axis`, and
`dJ=q_core(t,Z)J dt`, the J^4-weighted density from a smooth normalized
initial density satisfies, under the usual stopped/decay hypotheses,

```text
m_t=nu m_zz-partial_z(U m)+4q_core m,
E[J(T)^4]=1+4I.
```

The estimate above consequently gives a conditional averaged-moment
bound. It does not establish datum-uniform M1 or M2 for that density.
Nor does it bound the point-started moment uniformly: approximating a
Dirac initial density makes its initial derivative bounds diverge.
The physical compression-weight criterion needs stronger control than
this averaged observation. The missing estimate is how the actual
receiver's concentration evolves, with its full drift and potential.

This obligation has explicit physical defects. Since `U_z=q_core+q_paid`,
the equations for `n=m_z` and `p=m_zz` are

```text
n_t=nu n_zz-U n_z+2(q_core-q_paid)n+(3q_core_z-q_paid_z)m,
p_t=nu p_zz-U p_z+(q_core-3q_paid)p
    +(5q_core_z-3q_paid_z)n+(3q_core_zz-q_paid_zz)m.
```

The already paid integral of `|q_paid|` does not alone control these
derivative sources. A weighted derivative identity avoids differentiating
the parents: for positive m, `ell=log m` and
`Fisher=integral m ell_z^2`, with finite integrals and vanishing boundary
flux,

```text
Fisher'=-2nu integral m ell_zz^2
        -4 integral q_core m ell_z^2
        -2 integral (3q_core-q_paid)m ell_zz.
```

This retains the complete diffusion. Completing its square leaves
`integral m(3q_core-q_paid)^2/(2nu)-4 integral q_core m ell_z^2`,
which has no established favorable sign or original-datum payment.
The identity supplies a concrete next history estimate; it does not
bound Fisher or, by itself, the receiver's second derivative supremum.

The old parents nevertheless have a finite payment in this identity.
The same elliptic interpolation estimate used for M_H implies

```text
integral_0^T ||q_paid||_infinity^2
 <=P2_H=4 C_BS^2 Y^2 sqrt(H/(2nu)).
```

Indeed `||q_paid||_infinity^2<=4 C_BS^2 Y ||grad g||_2`; apply the
previous dissipation bound for g and Cauchy--Schwarz in time. For a fixed
length L>0, use the joint receiver quantity and paid clock

```text
S=integral m+L^2 Fisher >= integral m,
kappa(t)=L^2 ||q_paid(t)||_infinity^2/nu,
K_H=L^2 P2_H/nu,
C_core=integral m[4q_core(1-L^2 ell_z^2)
                   -6L^2 q_core ell_zz-nu L^2 ell_zz^2].
```

Completing only the paid-parent square gives

```text
S'<=C_core+kappa S,
d_t[exp(K_H-integral_0^t kappa) S]
 <=exp(K_H-integral_0^t kappa) C_core.
```

The multiplier stays at least one. Its initial allowance is the explicit
`exp(K_H)(1+L^2 Fisher(0))` for normalized m(0). Thus old-parent work is
paid without a bound on its spatial derivatives. The exact remaining
question is an original-datum upper bound on the time integral of this
weighted, signed C_core, using the actual generated-parent equation.
No such bound is proved here. This joint quantity is not assumed to be
monotone, and its point-started limit requires additional work.

### A heat reference avoids infinite Gaussian startup cost

`receiver_heat_reference.py` tests a refinement with an explicit changing
length. Start the actual receiver with a normalized Gaussian of variance
eps^2 centered at z0, and retain its entire history. Define

```text
M=integral m,   F=Fisher,   k(t)=eps^2+2nu t,
delta=ell_zz+1/k,   S=M+kF,   B=max(S,2M).
```

For every eps>0, `M(0)=1`, `F(0)=eps^-2` and `B(0)=2` exactly.
The additional `k'F` term is included. With `c=q_core`, `p=q_paid`,
the complete shifted rate is

```text
S'=(2nu/k)(2M-S)
   +integral m[10c-4kc ell_z^2-6kc delta
                -2p+2kp delta-2nu k delta^2].
```

The identity uses `integral m ell_zz=-F`. Spending only the old-parent
square leaves

```text
C_k=integral m[10c-4kc ell_z^2-6kc delta-nu k delta^2],
kappa=2||p||_infinity+(k/nu)||p||_infinity^2,
S'<=(2nu/k)(2M-S)+C_k+kappa M.
```

On the S branch of B the relaxation term is nonpositive; on the 2M branch
its rate is `8integral c m`. The maximum of these absolutely continuous
quantities consequently satisfies, almost everywhere,

```text
B'<=D_k+kappa B,       D_k=max(C_k,8integral c m).
```

The clock is uniformly funded for `0<eps<=eps_max`:

```text
integral_0^T kappa <= K_star=4M_H+(eps_max^2/nu+2H)P2_H,
W(t)=exp(K_star-integral_0^t kappa)>=1,
W(T)B(T)<=2exp(K_star)+integral_0^T W D_k.
```

The actual old-parent estimates, viscosity and the original elapsed time
are retained. No fresh Gaussian or initial allowance is introduced when
histories are composed. An original-datum upper bound A on the last
signed integral, uniform in center z0, eps and all available prefixes,
would give `M(T)<=2exp(K_star)+A` uniformly. On each smooth prefix with
bounded regular coefficients, continuity of the stopped moment in its
initial position then passes this bound to the point-started limit.
Smooth-prefix bounds justify that limit; they are not allowed to enter A.
Construction, integrability and stopping assumptions for the receiver
remain part of this analytic implication.

The exact tests recover ordinary heat spreading with `B=2`, `delta=0`
and zero D_k. They also check affine parent transport for either sign of
its strain; this is a receiver calibration, not a finite-energy NS
example. Whenever the actual generated component c is zero, `C_k<=0`
and `D_k=0`, so the old parents are paid by the clock. For nonzero c the
signed D_k is the explicit missing payment; the previous positive-burst
examples give no reason to expect it to vanish. This reduction does not
bound D_k. An axis moment also does not by itself construct the interior
compression weight or establish general three-dimensional continuation.

The earlier compact hidden-parent pair is a direct consistency test.
With `q_core=t sigma+t^2 kappa/2+O(t^3)` and initial U=0, the receiver
pairing expands as

```text
I=T^2 <m0,sigma>/2+T^3 <m0,kappa+2nu sigma_zz>/6+O(T^4),
kappa=sigma_t-𝒯(v0.grad S0)+nu Delta5 sigma.
```

Outside the initial source support the last Laplacian vanishes. The full
parent-dependent coefficient from the previous calculation is recovered;
the new finite allowance bounds both parent phases rather than asserting
their responses coincide. This Taylor check supplies no uniform remainder.

Run `python3 -O labs/source_receiver_duality.py --quadrature`.
Run `python3 -O labs/receiver_heat_reference.py` for the growing-length
identities and exact Gaussian/affine receiver calibrations.
Symbolic identities, physical gradient columns, kernel derivatives,
time ordering and constants pass. Independent positive-kernel integration
agrees with the closed expression to relative discrepancy below `4e-16`
at the six tested scales; these are numerical checks, not error certificates.
The PDE duality, semigroup identification, integral bounds, axis limiting
arguments and stochastic density formula remain analytic. No new Lean
certification is claimed for these physical estimates. Arbitrary-history
funding and arbitrary-data R3/T3 regularity remain open.

## Positive return from a swirl to its own source

`swirl_self_return.py` tests the following possible sign shortcut:
an initially pure swirl always generates meridional strain that makes a
nonpositive contribution to its own quartic source. This statement is false
for smooth finite-energy unforced whole-space data. The calculation concerns
this nonlinear contribution, not the complete viscous derivative, the
deformation receiver's D_k, or indefinite renewal.

Write `b=u_theta/r`, `eta=omega_theta/r`, `a=u_r/r`, and `s=-2a`.
For initially pure swirl, meridional velocity and eta vanish. The actual
unforced curl equation and canonical elliptic reconstruction give

```text
eta_t(0)=partial_z(b0^2),
L5=partial_rr+(3/r)partial_r+partial_zz,  K5=(-L5)^-1,
s_t(0)=sigma=2partial_zz K5 f=-2 A f,  f=b0^2,
A=-partial_zz K5,  multiplier m(rho,xi)=xi^2/(rho^2+xi^2).
```

Here rho is the horizontal Fourier radius in R4. The initial viscous
contribution to eta_t is zero for every nu>0. Pressure is retained through
the elliptic reconstruction, rather than omitted from the velocity equation.
For the local smooth axisymmetric solution with sufficient decay,

```text
B4=integral_R3 b^4,
B4'=N-12nu integral_R3 b^2 |grad b|^2-4pi nu integral_axis b^4,
N=4integral_R3 s b^4,
N(0)=0,  N'(0)=4I,  I=integral_R3 f^2 sigma.
```

Thus I>0 gives a positive actual nonlinear contribution N on some short
interval. It does not imply B4'>0. No uniform interval length is claimed.

### Exact radial family

For `0<beta<=1`, set `alpha=beta^2`, `y=r^2`, and

```text
P_alpha(y)=-48+(32+alpha)y-4y^2,
Q_alpha(y)=(P_alpha(y)-20)^2+21,
q=r^6 exp(-r^2),
h=r^4 exp(-r^2) P_alpha(r^2),
F=r^4 exp(-r^2) Q_alpha(r^2).
```

The exact identities

```text
h=(beta^2-Delta_R4)q,
Q-P=(P-41/2)^2+3/4,   Q+P=(P-39/2)^2+163/4
```

give `F>|h|` for r>0. First consider the axially periodic profile
`f=F+h cos(beta z)`. This intermediate profile is not the final
whole-space datum. Its strain acceleration is `-2beta^2 q cos(beta z)`.
Before taking any absolute values, the axial average of f^2 sigma is
`-2beta^2 F h q`. The physical radial moment is exactly

```text
J(alpha)=integral_0^infinity r F h q dr
 =2240(90alpha^3-288alpha^2+1485alpha-5222)/19683 < 0.
```

Its degree-three Bernstein coefficients on [0,1] are
`(-11697280,-10588480,-9694720,-8814400)/19683`, all negative.
This uses the physical measure r dr, not the lifted measure r^3 dr.
The positive return retains its beta^2 suppression as axial variation slows.

### Finite-energy localization and its quantitative error

Let `chi(Z)=exp(-Z^2)`, `chi_L(z)=chi(z/L)`, and use the literal datum

```text
f_L=chi_L(F+h cos(beta z)),
b0,L=r^2 exp(-(r^2+z^2/L^2)/2) sqrt(Q_alpha+P_alpha cos(beta z)),
u0,L=(-x2 b0,L, x1 b0,L, 0).
```

The radicand is uniformly positive. This is a real smooth Schwartz
divergence-free velocity, regular on the axis, with finite energy and
zero initial meridional velocity. Define `sigma_L=-2A f_L` and
`I_L=integral_R3 f_L^2 sigma_L`. The reference acceleration is
`sigma_app=-2beta^2 chi_L q cos(beta z)`.

The multiplier satisfies, for rho>0 and beta>0,

```text
m(rho,xi)<=|xi|/(2rho),
|m(rho,xi)-m(rho,beta)|<=|xi-beta|/beta.
```

For the second bound put e=|xi| and use
`(rho^2+e^2)(rho^2+beta^2)-rho^2(e+beta)^2=(rho^2-e beta)^2`.
The same bound around -beta controls the other cosine mode. Plancherel
and `||chi_L'||_2=L^-1/2||chi'||_2` now give

```text
||A f_L-beta^2 chi_L q cos(beta z)||_L2(R5)
 <=L^-1/2 ||chi'||_2 [ ||rF||_L2(R4)/2+||h||_L2(R4)/beta ].
```

The zero-mode estimate uses `|| |D_h|^-1 F||_2<=||rF||_2`.
For completeness, `div(x/r^2)=2/r^2` in R4 implies
`||phi/r||_2<=||grad phi||_2` by integration by parts and Cauchy--Schwarz;
duality proves the stated inverse-derivative bound. Approximation extends
these bounds to the present Gaussian profiles.

The measure identity `dx3=dy5/(pi r^2)` and `F>=|h|` imply

```text
||f_L^2/r^2||_L2(R5)
 <=4 sqrt(L) ||chi^2||_2 ||r^-2 F^2||_L2(R4).
```

There is no singular-axis integrability assumption hidden here: F vanishes
to order four in r. Cauchy--Schwarz therefore bounds the normalized physical
pairing error by a constant times 1/L. Exact Gaussian axial integration gives

```text
I_infinity=-4pi beta^2 J(beta^2) sqrt(pi/3)>0,
I_L/L -> I_infinity                 (fixed beta>0).
```

Here are explicit constants for beta=1. All integrals below have variable y:

```text
X=integral y^7 exp(-4y) Q^4 =191912289955843275/2097152,
R=integral y^6 exp(-2y) Q^2 =3882780,
D=integral y^5 exp(-2y) P^2 =6075/16,
A0=(1/2)integral y^7 exp(-3y) Q^2 =4395411160/59049,
J=-8814400/19683.
```

The corresponding radial norms are `pi sqrt(X)`, `pi sqrt(R)` and
`pi sqrt(D)`. The roots `sqrt(X)`, `sqrt(R)` and `sqrt(D)` are bounded
by 302508, 1971 and 20.
Since `||chi^2||_2 ||chi'||_2=sqrt(pi)/2^(3/4)`, the normalized multiplier
pairing error divided by I_infinity is at most C1/L, where

```text
C1=4*302508*(1971/2+20)/|J|=2993506710651/1101800.
```

To bound axial averaging, set `B0=integral r q h^2 dr<=A0` and
`v=beta^2 L^2/12`. The reference pairing differs from its limit by

```text
-4pi beta^2 sqrt(pi/3) *
 [exp(-v) A0+exp(-4v) J+(3exp(-v)+exp(-9v)) B0/4].
```

Since `|J|<=A0` and `exp(-v)<=1/v`, its relative magnitude for beta=1
is bounded by `C2/L^2`, with `C2=36A0/|J|=47093691/7870`.
For the explicit integer `L=2^24`, exact rational comparisons give

```text
C1/L<1/4,   C2/L^2<1/4,
I_L/L >= I_infinity/2 > 0.
```

For every other fixed beta in (0,1], the same estimates have finite
constants and give positivity for sufficiently large L. This asserts
arbitrarily slow axial variation, not exact support in a Fourier cone or
a limit uniform as beta tends to zero.

The initial energy is also explicit:
`E=2pi^(3/2)L[EF+12beta^2 exp(-beta^2 L^2/4)]`, where
`EF=(1/2)integral y^3 exp(-y)Q_alpha(y)dy` and EF=3339 at beta=1.
Replacing u0 by `u0/sqrt(E)` gives energy one and multiplies I_L by
E^-3. Its sign persists at the same prescribed viscosity. This normalization
does not make the positive return large or defeat a finite datum allowance.

Run `python3 -O labs/swirl_self_return.py --quadrature`. The algebra,
Cartesian initial curl, inverse relation, positivity certificates, moments,
localization constants and heat-kernel identities are exact symbolic checks.
Optional quadrature evaluates the localized heat resolvent independently
of the localization bound; it has no certified numerical error estimate.
The Fourier/Hardy estimates, reconstruction, local solution and short-time
implication are analytic, not Lean-certified.

### The favorable energy exchange and the concentration defect

There is a favorable sign at the kinetic-energy weight. For the same
initially pure swirl define `R_z=partial_z(-Delta5)^(-1/2)`, so
`A=R_z^* R_z`. At time zero,

```text
I_energy=integral_R3 r^2 f sigma
        =-(2/pi) integral_R5 f A f
        =-(2/pi) ||R_z f||_L2(R5)^2 <= 0.
```

This is the initial derivative of the nonlinear swirl-energy contribution
`integral_R3 s r^2 b^2`. The opposite work goes into the meridional kinetic
energy. In fact `||partial_t v_mer(0)||_L2(R3)^2=||R_z f||_L2(R5)^2/pi`:
the meridional reconstruction satisfies
`||v_mer||_L2(R3)^2=||grad K5 eta||_L2(R5)^2/pi`, by radial integration
by parts. Thus the initially zero meridional energy has second derivative
`-I_energy`. The nonlinear exchange conserves total kinetic energy even
while a higher concentration measure receives a positive contribution.

The distinction has an exact operator expression. For the constructed
profile, `w=f/r^2` is smooth, bounded and nonnegative, and

```text
I=-(2/pi) <w f,A f>_L2(R5)
 =-(2/pi) [ ||sqrt(w) R_z f||_2^2
            + <[R_z,w]f,R_z f>_L2(R5) ],
[R_z,w]f=R_z(w f)-w R_z f.
```

The first term is favorable. The spatially varying concentration weight
introduces the commutator; the positive example shows it can outweigh
that favorable term. This identity is an initial-data diagnostic, not a
closed evolution law for a new reserve. An evolving version must also
retain transport, diffusion, and the derivative of its weight. Controlling
those terms over full generated-parent histories is the remaining physical
obligation. The example rules out discarding the concentration defect on
sign grounds; it leaves quantitative geometric depletion and finite
full-datum payment open.

## An actual source law with funded action and entropy

`swirl_source_entropy.py` supplies an analytic stochastic identification
and an original-datum reserve for a source observation. Assume an actual
smooth axisymmetric unforced whole-space NS prefix, nu>0, a regular axis,
and the integrability stated below. No bound on a future strain supremum
enters its constants. All five-dimensional integrals here use ordinary
Lebesgue measure `dy=2pi^2 r^3 dr dz`.

Write `b=u_theta/r`, `Gamma=r^2 b`, and `q=-2u_r/r`. Lift the actual
meridional velocity to `v5=(u_r*x_h/r,u_z)` on `R4 x R`. Incompressibility
gives `div5(v5)=-q`; the actual swirl equation is exactly

```text
b_t=nu Delta5 b-div5(v5 b).
```

Thus nonnegative b, normalized by its conserved mass, is a probability
density with the actual drift v5. For sign-changing b, construct the
positive envelope B by this same linear equation along the actual drift,
with `B(0)=|b0|`. Order preservation gives `|b|<=B`. This construction
does not replace the drift by a separately chosen control. The equation
for `Gamma_B=r^2 B` is the existing circulation equation, so

```text
0<=Gamma_B(t)<=G0=||r^2 b0||_infinity,
M=integral_R5 B(t)=integral_R5 |b0|,
rho=B/M,                       0<M<infinity.
```

Require G0 finite, finite kinetic energy E0, and finite initial relative
entropy to the heat reference below. Smooth rapidly decaying data have
these properties when b0 is nonzero. The case b0=0 has no swirl source
and does not require normalization by M. On a compact smooth prefix the
lifted drift is bounded and regular; scalar parabolic construction and
uniqueness identify the envelope, preserve its mass and justify the
maximum principle. Approximation handles zeros of b0. These prefix-local
regularity facts justify the construction; their bounds are not used in
the final allowance.

### Action paid by the actual fluid

The lifted and physical measures give a direct estimate:

```text
W(t)=integral_R5 rho |v5|^2
    =(pi/M) integral_R3 Gamma_B |v_mer|^2
    <=C E(t),                  C=pi G0/M,
E(t)=||u(t)||_2^2,              E'=-2nu d,
d=||grad u||_2^2.
```

For a prescribed H and every available prefix t<=H,
`R_A(t)=C(H-t)E(t)>=0` satisfies `R_A'+W<=0`. Consequently all
compatible subinterval action costs are paid by `R_A(0)=C H E0`.
Mutual amplification of meridional parents does not change this estimate.

Let P be the path law of
`dX=v5(t,X)dt+sqrt(2nu)dW5`, with initial density rho0. Its marginals
are rho. Let R be Brownian motion with the same initial density and
diffusivity. Girsanov's entropy identity gives

```text
KL(P_[0,T] || R_[0,T])=(1/(4nu)) integral_0^T W(t)dt
                    <=pi G0 H E0/(4nu M),       T<=H.
```

The normalization follows, for example, from
[Léonard, equation (4.7)](https://arxiv.org/html/1308.0215v1#S4.E7)
after changing the noise amplitude to sqrt(2nu) and using the same
initial law. On each bounded smooth prefix the ordinary bounded-drift
Girsanov argument applies; the displayed action estimate removes the
prefix-dependent coefficient bound from its result. Conditional action
costs compose along the same law without restarting the reserve.

This is a finite-action stochastic law identified with an actual fluid
observable. It is not asserted to minimize a Schrödinger bridge problem.
The five-dimensional source observer is also distinct from ordinary
three-dimensional fluid-particle diffusion and from the one-dimensional
axis deformation receiver.

### A nonnegative reserve for relative Fisher information

Fix L>0 from the initial data and let

```text
gamma_L(t,y)=N(0,(L^2+2nu t)I5),
K(t)=KL(rho(t)||gamma_L(t))>=0,
I(t)=integral rho |grad log(rho/gamma_L)|^2.
```

The complete relative entropy identity and its square completion are

```text
K'=-nu I+integral rho v5.grad log(rho/gamma_L)
   =-(nu/2)I+W/(2nu)-Q,
Q=(1/(2nu)) integral rho |v5-nu grad log(rho/gamma_L)|^2>=0.
```

The local computation retains all transport and heat-reference fluxes.
Integrating with cutoffs and approximation yields the corresponding
entropy inequality if a classical entropy derivative is unavailable.
Define the actual joint reserve

```text
R(t)=K(t)+C(H-t)E(t)/(2nu)>=0.
```

Its exact smooth ledger is

```text
R'+(nu/2)I+Q+(CE-W)/(2nu)+C(H-t)d=0.
```

Every term after R' is nonnegative. Therefore

```text
R(T)+(nu/2) integral_0^T I(t)dt <= R(0)
 =KL(rho0||gamma_L(0))+pi G0 H E0/(2nu M).
```

This controls the complete source-envelope history from the original datum,
including all interacting parents. The same fixed H, L and M apply at
every seam. It does not yet control the deformation-weighted receiver.

### Concentration separates this reserve from the needed higher moments

There is an actual unforced family showing why an additional transfer
estimate is necessary. Let `g(y)=exp(-|y|^2/2)` in R5 and, for lambda>=1,

```text
b0,lambda(y)=g(y)+lambda^2 g(lambda y),
u0,lambda(x)=u_base(x)+lambda u_base(lambda x),
u_base(x)=(-x2 g(x),x1 g(x),0).
```

Here g(x) denotes the same radial formula in physical R3. The velocities
are smooth Schwartz, divergence-free and initially pure swirl, with
nonnegative b. Their initial resources obey

```text
M_lambda=(2pi)^(5/2)(1+lambda^-3),
E0,lambda<=4pi^(3/2),          G0,lambda<=4/e.
```

The normalized source is the mixture of N(0,I5) and N(0,lambda^-2 I5)
with concentrated weight `w=1/(1+lambda^3)`. Convexity of relative entropy
and the Gaussian formula give

```text
KL(rho0,lambda||N(0,I5))
 <=w*(5/2)(lambda^-2-1+2log lambda)<=5/(3e).
```

Taking L=1, every initial reserve is bounded by
`5/(3e)+sqrt(2)H/(e nu)`, independent of lambda. Thus their actual
available histories have uniformly paid action and relative Fisher cost.

Nevertheless their third-moment covariance source
`V3=integral_R5 b |grad b|^2` has arbitrarily large integrated cost on
short actual unforced prefixes. This is an interval statement, not just
an initial derivative. Under NS scaling the rescaled initial velocity is

```text
U0,lambda(y)=lambda^-1 u0,lambda(y/lambda)
           =u_base(y)+lambda^-1 u_base(y/lambda)
           ->u_base in C_b^1(R3).
```

There is a common local C_b^1 mild-solution interval with continuous
dependence in that norm; use its subspace with bounded uniformly
continuous first derivatives, which contains this family. One can
obtain it directly by contraction:
the heat--Leray divergence kernel has L1 norm at most a constant times
`(nu t)^(-1/2)`, and C_b^1 is an algebra. The kernel estimate follows
by writing its nonlocal part as the integral of the third derivative of
the heat kernel from nu*t to infinity; its L1 bound is the integral of
`Cs^(-3/2)`. The constants in this argument are uniform for this bounded
C_b^1 initial family. The smooth finite-energy solutions agree with
these local solutions.

Choose a compact annulus away from the axis where the base initial b
is positive and has nonzero radial derivative. On a sufficiently short
common interval [0,tau], continuity and the C_b^1 convergence give a
fixed positive lower bound for the rescaled integral of b|grad b|^2
on that annulus. Positivity of b persists. The exact scalings are
`b=lambda^2 B`, `grad b=lambda^3 grad B`, `dy=lambda^-5 dY`,
and `dt=lambda^-2 ds`. Thus, for some c,tau>0 depending on the base
datum and nu, but not lambda,

```text
integral_0^(tau/lambda^2) V3(t)dt >=c lambda -> infinity.
```

For large lambda this available prefix lies below any fixed H>0.
This refutes uniform payment of the raw nonnegative cubic diffusion
correction by the bounded entropy/action reserve just constructed.
It does not refute an allowance depending on higher resources of the
full initial datum, or a signed estimate with additional cancellations.
Indeed `integral b0,lambda^3` grows at order lambda. Its actual balance is

```text
d_t integral_R5 b^3 +6nu integral_R5 b|grad b|^2
 =2 integral_R5 q b^3                 (b>=0).
```

The initial cubic resource has the size needed for this burst. The
remaining question is how to pay the signed work that replenishes it
over repeated parent renewal. Finite relative entropy alone also does
not supply an exponential deformation moment or a uniform point-started
axis bound. No such inference is used here.

Run `python3 -O labs/swirl_source_entropy.py`. The differential and reserve
identities, normalization, Gaussian scaling and algebraic bounds are
symbolically checked. Envelope construction, entropy inequalities,
stochastic identification and the local-solution interval argument are
analytic, not Lean-certified. The finite-action part is a partial bridge;
it is not a sufficient regularity criterion and need not, by itself,
exclude every forced singular construction. For an azimuthal force the
source equation acquires `f_theta/r`; forcing also changes the kinetic
energy law used in both reserves.

## Source moments and the axis receiver

`swirl_receiver_reference.py` tests a tempting direct bridge. At the axis,
write `U=u_z|axis`, `q=U_z`, and `L_b=nu Delta_R4 b|axis`. Then

```text
b_t+U b_z=nu b_zz+q b+L_b,
m_t=nu m_zz-(Um)_z+4q m=nu m_zz-U m_z+3q m.
```

This uses the full strain q. On the same axis path, the previously paid
bound on `integral |q_paid|` compares full and core fourth deformation
moments in both directions by the factor `exp(8M_H)`. Neither moment
is bounded merely by the source-reference identities below.

The source cube h=b^3 has the same strain coefficient as this full-strain
receiver, but its complete defect is

```text
h_t-[nu h_zz-U h_z+3q h]=3b^2 L_b-6nu b b_z^2.
```

For positive h, put `e=3L_b/b-6nu(b_z/b)^2`. The exact ratio equation is

```text
(m/h)_t=nu(m/h)_zz+[2nu(log h)_z-U](m/h)_z-e(m/h).
```

Thus equality of the strain coefficients is insufficient. For the actual
unforced Gaussian pure-swirl datum `b0=exp(-(r^2+z^2)/2)`, normalize
`m0=sqrt(3/(2pi))*b0(0,z)^3`. Initial U=q=0, and the literal NS equation
gives

```text
[m-sqrt(3/(2pi))*b_axis^3]_t(0,z)
 =sqrt(3/(2pi))*6nu(z^2+2)exp(-3z^2/2)>0.
```

The proposed comparison by the bare cube fails on a short actual interval.
The stochastic third-moment lift instead solves

```text
H_t+v.grad H=nu Delta5 H+3q H,       H0=b0^3,
(H-b^3)_t+v.grad(H-b^3)
 =nu Delta5(H-b^3)+3q(H-b^3)+6nu b|grad b|^2.
```

For nonnegative b the retained source gives H>=b^3 by comparison.
This is the positive moment correction, not a product of averaged
fields. At a fixed terminal observation, their Feynman--Kac formulas
use the same backward-representation paths: b is the first moment and
H the third moment of the same weighted initial amplitude. Those paths
are not the forward source-density law used for the entropy estimate.
Its axis trace still has the additional term
`nu Delta_R4 H|axis` relative to the receiver equation. For the Gaussian
initial datum, the normalized initial mass rates of the receiver, cube
trace and lifted trace are respectively `0`, `-14nu` and `-12nu`.

In the diffusion-only calibration these two defects can be repaired
exactly. If `H_heat=heat5(b0^3)` and m_heat is the one-dimensional heat
receiver from the normalized cube trace, then

```text
m_heat(t,z)=sqrt(3/(2pi))*(1+6nu t)^2*H_heat(t,0,z).
```

The factor is transverse dilution in four dimensions; its logarithmic
rate is `12nu/(1+6nu t)`. This calibration is not asserted to be an
NS evolution of the Gaussian swirl. In the actual flow, both the moment
correction and lateral transport/diffusion must be retained. The funded
source Fisher information above has a different weight from the cubic
correction and from the point-started deformation receiver.

Run `python3 -O labs/swirl_receiver_reference.py`. Differential identities,
the literal NS initial rate and the heat calibration pass exact symbolic
checks. Local comparison, stochastic representation and the positive-time
implication remain analytic. General three-dimensional and periodic
continuation, and the arbitrary-history moment transfer, remain open.

## A critical cubic-source clock and its internally generated rebound

`swirl_cubic_clock.py` connects the actual cubic source stock to a
continuation criterion and tests a joint kinetic/source reserve. All PDE,
Sobolev, localization and continuation arguments in this section are
analytic. The checker certifies the displayed algebra and rational moment
comparisons, not these analytic arguments in Lean.

### The actual stock has a continuation consumer

Consider a smooth axisymmetric unforced whole-space evolution, regular at
the axis, with positive viscosity and sufficient integrability for the
identities below. Smooth Schwartz initial data satisfy the initial
requirements. Retain the physical meridional velocity, pressure and all
generated components. Use ordinary five-dimensional measure
`dy5=2pi^2 r^3 dr dz=pi r^2 dx3` for axisymmetric integrands. Set

```text
b=u_theta/r, q=-2u_r/r, G0=||r u_theta(0)||_infinity,
S=integral_R5 |b|^3, D=integral_R5 |b||grad b|^2,
P=integral_R5 q|b|^3,
E=||u||_L2(R3)^2, d=||grad u||_L2(R3)^2.
```

S uses the **actual** signed swirl through its absolute cube. It is not
the larger passive envelope B from the entropy construction. The
circulation maximum principle gives `r^2|b|<=G0`. Consequently,

```text
|u_theta|^4=r^4|b|^4 <= G0 r^2|b|^3,
||u_theta||_4^4 <= G0 S/pi,
integral_0^T ||u_theta||_4^8 <= (G0/pi)^2 integral_0^T S^2.       (1)
```

Thus a uniform original-datum bound on the last integral suffices for
axisymmetric continuation: apply [Peng Wang, Theorem 1.1, EJDE 2015/250](https://ejde.math.txstate.edu/Volumes/2015/250/wang.pdf)
with time/space exponents `(8,4)`, to the maximal smooth H2 solution.
Every shorter prefix has the same bound, so the criterion applies at a
candidate finite maximal time. This is an analytic use of the published
theorem, not a new Lean import. It supplies an alternative axisymmetric
consumer; it does not establish the uniform deformation receiver or the
general three-dimensional/periodic continuation obligations.

Energy already pays one power of S. The angular column of the physical
velocity gradient has squared norm `b^2+(u_r/r)^2`. Hence

```text
S=pi integral_R3 (r^2|b|)|b|^2 <= pi G0 d,
integral_0^T S <= pi G0 E0/(2nu).                               (2)
```

This identifies the remaining concentration in time: L1 payment alone
does not bound the L2 clock in (1). For any fixed datum-chosen threshold A,
`S^2<=A S+S(S-A)_+`, so only the latter excess needs additional payment.
The first power payment is not asserted for the passive envelope B.

### A joint reserve with the same scaling as the critical clock

The actual equations give the complete balances

```text
E'=-2nu d,                 S'=2P-6nu D.                       (3)
```

For signs in b, use the C2 function `|b|^3`; its second derivative is
`6|b|`. No singular measure at b=0 is discarded. The lifted drift has
divergence `-q`, which changes the pointwise reaction coefficient three
to the integrated coefficient two in (3).

Let C5 be a fixed five-dimensional Sobolev constant with
`||f||_(10/3)^2<=C5||grad f||_2^2`. Apply it to `f=|b|^(3/2)`:

```text
||b||_5^3 <= (9/4) C5 D,
||b||_3 <= ||b||_2^(4/9) ||b||_5^(5/9),
||b||_L2(R5)^2=pi ||u_theta||_L2(R3)^2 <= pi E,
S^(9/5) <= (9/4) C5 (pi E)^(6/5) D.                          (4)
```

The initially finite nonnegative candidate is `R=(E S)^(6/5)`. Its exact
derivative retains both viscous losses:

```text
R' = (12/5) E^(6/5) S^(1/5) P
     -(12nu/5) E^(1/5) S^(6/5) d
     -(36nu/5) E^(6/5) S^(1/5) D.
```

Define the signed remaining cost

```text
Q = (12/5) E^(6/5) S^(1/5) P
    -(12nu/5) E^(1/5) S^(6/5) d
    -(18nu/5) E^(6/5) S^(1/5) D.
```

Equations (3)--(4) imply on every compatible subinterval

```text
R(T) + [8nu/(5 C5 pi^(6/5))] integral_a^T S^2
 <= R(a)+integral_a^T Q.                                      (5)
```

There is no restart of the reserve at a seam. A bound
`integral_0^T Q<=K(u0,nu,H)` for every available prefix `T<=H`, with K
finite from the full original datum, would therefore imply (1) and
axisymmetric continuation. This signed payment is **open**. Defining K
as the unknown future supremum would not prove it.

Under the physical NS scaling `u_lambda(t,x)=lambda u(lambda^2 t,lambda x)`,
E scales as `lambda^-1`, S as lambda, and both R and `integral S^2 dt`
are unchanged. The concentration family in the previous section has a
fixed broad background and is not a single NS rescaling; its S0 and R0
grow and record the concentration missed by the entropy reserve.

For an azimuthal fluid force, the stock rate in (3) has the additional
term `3 integral_R5 |b|b f_theta/r`, and the energy rate has
`2 integral_R3 u.f`. Both enter the derivative of R. This calculation
does not identify a non-axisymmetric forced construction with an
axisymmetric evolution or discard its forcing terms.

### Positive feedback for this stock from initially pure swirl

The following test includes the full parent response. For `0<beta<=1`,
put `alpha=beta^2`, `y=r^2` and

```text
p_alpha=-48+(32+alpha)y-4y^2,  Q_alpha=(p_alpha-20)^2+21,
q_rad=r^6 exp(-r^2), h=r^4 exp(-r^2)p_alpha,
F=r^4 exp(-r^2)Q_alpha^2.
```

Here `h=(beta^2-Delta_R4)q_rad`, `Q_alpha>=21` and `Q_alpha>|p_alpha|`.
For the intermediate axially periodic source `f=F+h cos(beta z)` one has
`|h|/F<=1/21`. Its actual strain acceleration is
`sigma=-2beta^2 q_rad cos(beta z)`. This follows from the unforced curl
equation and canonical elliptic reconstruction:
`eta_t(0)=partial_z(b0^2)` and `q_t(0)=2partial_zz(-Delta5)^-1 b0^2`.
Initial meridional velocity and its viscous contribution vanish.

Let the phase average use normalized measure on `[0,2pi]`. Taylor's
theorem, retaining the quadratic term whose contribution averages to zero,
gives

```text
|average cos(theta)(F+h cos(theta))^(3/2)-(3/4)sqrt(F)h|
 <= |h|^3/[16(F-|h|)^(3/2)].
```

Since `(21/20)^(3/2)<2` and `|p_alpha|/Q_alpha<1`, the radial phase
average of `f^(3/2)sigma` is bounded below by

```text
beta^2*(-3 J(alpha)/2-Z/4),
J(alpha)=integral_0^infinity r^3 sqrt(F)h q_rad dr
 =2064384*(9000alpha^3-25200alpha^2+94165alpha-214819)/244140625,
Z=(1/2)integral_0^infinity y^7 exp(-5y/2)dy=129024/78125.
```

The Bernstein coefficients of J on `[0,1]` are
`(-443468906496,-378671333376,-331214585856,-282519207936)/244140625`.
The lower bound is positive, with its beta=1 margin
`m=423678011904/244140625`. Slow axial variation retains beta-squared
depletion, but does not impose a nonpositive feedback sign.

### Localization with an explicit finite length

Use the literal whole-space datum

```text
f_L=exp(-z^2/L^2)*(F+h cos(beta z)),
b0,L=r^2 exp(-(r^2+z^2/L^2)/2)*sqrt(Q_alpha^2+p_alpha cos(beta z)),
u0,L=(-x2 b0,L,x1 b0,L,0).
```

It is smooth, Schwartz, divergence-free and purely azimuthal. Define
`I_L=integral_R5 b0,L^3 sigma_L`, with the literal whole-space
`sigma_L=2partial_zz(-Delta5)^-1 f_L`. The radial norm below uses `r^3 dr`.
The Fourier/Hardy estimates proved in the preceding swirl-return test give

```text
||sigma_L+2beta^2 exp(-z^2/L^2)q_rad cos(beta z)||_L2(R5)
 <=2sqrt(2pi^2)L^(-1/2)||chi'||_2
       *(||rF||_rad/2+||h||_rad/beta),  chi(Z)=exp(-Z^2).
```

Pairing with `f_L^(3/2)` gives a normalized error at most `Cmult/L`.
At beta=1, an upward bound is
`Cmult=12||F^(3/2)||_rad*(||rF||_rad/2+||h||_rad)`.
All three norms have exact polynomial/Gaussian squares. Their upward
integer bounds are `41847079250,90535142,14`, respectively, giving
`Cmult<=22731794603413335000`.

The remaining phase averaging has error at most `Cavg/L`. Indeed, a
zero-mean periodic function has a primitive bounded by four pi times
its supremum; integration against `exp(-5Z^2/2)`, whose derivative has
L1 norm two, gives this estimate. Here it suffices to take

```text
Cavg=192*(1/2)integral_0^infinity y^7 exp(-5y/2)Q_1(y)^3 dy
 =347013594597589887614976/762939453125.
```

The pairing contains `chi^(3/2)` from the stock and one more chi from
the strain response. Its phase-averaged limit therefore includes the
factor `sqrt(2pi/5)>1`. For the
explicit finite length `L=2^55`, exact rational comparisons give
`(Cmult+Cavg)/L<m/2`. Thus `I_L/(2pi^2 L)>=m/2>0`.
These deliberately loose constants certify a finite-energy witness;
they do not estimate a physically sharp length. For every fixed beta
in `(0,1]` the same proof has finite constants and works for sufficiently
large L. No uniform limit as beta approaches zero is claimed.

### A rebound after both viscous losses

Fix the localized beta=1 datum above and write its positive constants as
`E0,S0,d0,D0,I`, where `I=I_L`. For a specified physical viscosity nu>0,
consider actual initial velocities `A u0`, with A tending to infinity.
Write the actual solution as
`u_A(t,x)=A v_epsilon(A t,x)`, where `epsilon=nu/A` and `v_epsilon(0)=u0`.
This is the exact amplitude/time change of the unforced equation.

The usual local Sobolev energy argument gives a common smooth existence
interval and bounded high Sobolev norms for `0<=epsilon<=1`; the viscous
term is nonpositive in that argument. Taking sufficiently many derivatives
also bounds the required time derivatives uniformly. Only that common
short interval is used. The integrals in these
time derivatives are controlled by physical norms: `||b||_L2(R5)^2`
equals pi times swirl kinetic energy, `||grad b||_L2(R5)^2` equals pi
times swirl vorticity energy, and their time-differentiated versions have
the same identities. Axis regularity controls the remaining bounded
coefficients b, q and their time derivatives by high Sobolev norms.
These observations justify, uniformly on that common short interval,

```text
P(tau)=I tau+O(tau^2),   D(tau)=D0+O(tau),   d(tau)=d0+O(tau).
```

At `tau=k epsilon`, integration of the complete balances (3) yields

```text
E=E0-2k epsilon^2 d0+O(epsilon^3),
S=S0+epsilon^2*(I k^2-6D0 k)+O(epsilon^3),
ES-E0 S0=epsilon^2*[E0 I k^2-(6E0 D0+2d0 S0)k]+O(epsilon^3).
```

Set `k=2(6E0 D0+2d0 S0)/(E0 I)`. The last quadratic coefficient is
`2(6E0 D0+2d0 S0)^2/(E0 I)>0`. For sufficiently large A, at the actual
time `t=k nu/A^2`, the complete joint reserve R is therefore larger
than its initial value. Its signed Q integral is positive as well.

This refutes a monotone joint reserve, or a zero remainder in (5), even
when all initial meridional parents vanish and viscosity is positive.
It proves one internally generated rebound, not indefinite recurrence,
singularity, or failure of an allowance depending on the full datum.
The test strengthens the requirement on a history correction: it must
account for newly generated parents and cannot rely only on the already
included kinetic and cubic viscous losses.

Run `python3 -O labs/swirl_cubic_clock.py --quadrature`. The optional
radial/phase quadrature checks the periodic average independently and is
numerical evidence, not a localization or PDE error certificate. The
signed Q budget, its generalization beyond axisymmetry, and the full
arbitrary-data regularity goal remain open.

## Swirl-channel transfer, spatial composition, and a critical source moment

`swirl_channel_reserve.py` tests whether retaining swirl kinetic energy
repairs the preceding global product. It then identifies an additive
critical moment with a sufficient diffusion budget. A separate family
shows that the funded entropy/action reserve alone does not uniformly
bound even the physical swirl continuation norm. These are analytic
arguments with exact algebraic checks, not new Lean theorems.

### Keeping the actual transfer between velocity components

Continue in the smooth axisymmetric unforced whole-space setting and use
the same five-dimensional measure. Define

```text
Z=integral_R5 b^2=pi E_theta, E_theta=||u_theta||_L2(R3)^2,
S=integral_R5 |b|^3,
P_j=integral_R5 q|b|^j, D_j=integral_R5 |b|^(j-2)|grad b|^2,
q=-2u_r/r.
```

The exact equations are `Z'=P_2-2nu D_2`, `S'=2P_3-6nu D_3`.
In particular, replacing total energy by swirl energy does not simply
replace one nonincreasing scalar by another: P_2 is the signed transfer
between swirl and meridional motion. The candidate
`R_theta=(E_theta S)^(6/5)` has, up to the constant `pi^(-6/5)`, the rate

```text
d_t (Z S)^(6/5)
 =(6/5)(Z S)^(1/5)
   [S P_2+2Z P_3-2nu S D_2-6nu Z D_3].                       (6)
```

For initially pure swirl, let `sigma=q_t(0)=-2A b0^2`, with
`A=-partial_zz(-Delta5)^-1=R_z^*R_z`. Then

```text
T=P_2'(0)=integral b0^2 sigma=-2||R_z(b0^2)||_2^2<=0,
I=P_3'(0)=integral b0^3 sigma,
J=S0 T+2Z0 I.
```

The preceding localized example has nonnegative b0 and I>0. Negative
transfer T is now retained, but it does not make the global product
monotone for all such data.

### A distant weak source exposes a global-product defect

Fix that localized source b_* and its finite constants `Z_*,S_*,T_*,I_*`,
with I_*>0. Let `g(X)=exp(-|X|^2/2)` on R5 and add

```text
g_lambda,R(X)=lambda^2 g(lambda(X-R e_z)),
b0=b_*+g_lambda,R,                    0<lambda<=1.
```

This is the initial source of one literal Schwartz pure-swirl velocity.
It is not a superposition of independently evolved NS solutions. For
each fixed lambda, take the spatial separation R sufficiently large.
Schwartz translation decoupling and the bounded translation-invariant
L2 multiplier A give the limits

```text
Z0 -> Z_*+lambda^-1 Zg,  S0 -> S_*+lambda Sg,
T  -> T_*+lambda^3 Tg,   I  -> I_*+lambda^5 Ig,
Zg=pi^(5/2),                  Sg=(2pi/3)^(5/2),
Tg=-(2/5)(pi/2)^(5/2),        Ig=-(2/5)(2pi/5)^(5/2).
```

The Gaussian return constants use rotational symmetry in five
dimensions: a pairing of radial functions with A is one fifth of their
ordinary pairing. For the decoupling, `b0^2` converges in L2 to the sum
of the separated squares, and `b0^3` to the sum of the separated cubes.
Cross pairings with A tend to zero by weak convergence of translations
in L2. Thus the nonlocal pressure response is retained in the limit.

Let

```text
J_lambda=(S_*+lambda Sg)(T_*+lambda^3 Tg)
          +2(Z_*+lambda^-1 Zg)(I_*+lambda^5 Ig).
```

Then `lambda J_lambda -> 2 Zg I_*>0`. This gives finite parameters:
with
`C=(S_*+Sg)(|T_*|+|Tg|)+2(Z_*+Zg)|Ig|`, one has
`J_lambda>=2Zg I_*/lambda-C` for `0<lambda<=1`. Choose
`lambda=Zg I_*/(C+2Zg I_*)`, then a sufficiently large finite separation R.
The resulting actual datum has `J=S0 T+2Z0 I>0`.

This is the precise aggregation defect: weak distant swirl contributes
large kinetic energy, almost no cubic stock or return, and multiplies
the active region's positive I in the global product. The observation
does not rule out a spatially compatible payment.

### The separate-channel product also rebounds with positive viscosity

Fix this composite datum and viscosity nu>0. As before, amplify its
velocity by A and write the actual unforced solution as
`u_A(t)=A v_epsilon(A t)`, `epsilon=nu/A`. Uniform local Sobolev estimates
for `epsilon in [0,1]` give, at `tau=k epsilon`,

```text
Z=Z0+epsilon^2(T k^2/2-2D2,0 k)+O(epsilon^3),
S=S0+epsilon^2(I k^2-6D3,0 k)+O(epsilon^3),
ZS-Z0S0=epsilon^2(J k^2/2-L k)+O(epsilon^3),
L=2S0 D2,0+6Z0 D3,0.
```

All quantities here belong to the complete composite evolution. Set
`k=4L/J`; the positive leading coefficient is `4L^2/J`. At the actual
time `t=k nu/A^2`, for sufficiently large A, R_theta exceeds its initial
value. Both diffusive losses and the signed swirl-to-parent transfer have
been included. This refutes automatic monotonicity of this global product,
not a full-datum history allowance, regularity, or indefinite renewal.
The product itself increases, so a different positive outer power does
not repair its unconditional monotonicity.

### An additive moment that has a sufficient diffusion budget

The next physical target avoids multiplication of independent global
resources. Define, using the actual b rather than its passive envelope,

```text
M=integral_R5 |b|^(5/2)=pi integral_R3 |u_theta|^(5/2)/sqrt(r),
Dcrit=integral_R5 |b|^(1/2)|grad b|^2,
Pcrit=integral_R5 q|b|^(5/2).
```

M is finite for the stated data, adds across disjoint spatial regions,
and is unchanged by NS spatial scaling: b acquires a factor lambda^2,
while the five-dimensional measure acquires lambda^-5. These two powers
select the exponent 5/2. Its complete balance is

```text
M'=(3/2)Pcrit-(15nu/4)Dcrit.                                  (7)
```

The absolute power is C2, so this identity also applies to sign-changing
smooth b with the stated integrability. No nonpositive sign for Pcrit,
automatic monotonicity of M, or history payment is assumed.

There is a direct continuation implication for a signed absorption bound.
Apply five-dimensional Sobolev to `|b|^(5/4)`, using the same constant C5,
and interpolate L3 between L(5/2) and L(25/6):

```text
||b||_(25/6)^(5/2) <= (25/16)C5 Dcrit,
||b||_3 <= ||b||_(5/2)^(7/12) ||b||_(25/6)^(5/12),
S^2 <= (25/16)C5 M^(7/5) Dcrit.                              (8)
```

Suppose a finite allowance K(u0,nu,H), fixed from the original datum,
satisfies, for every available smooth prefix T<=H,

```text
(3/2)integral_0^T Pcrit <= (15nu/8)integral_0^T Dcrit+K.        (9)
```

Putting `N0=M(0)+K`, equations (7)--(8) give

```text
M(T)+(15nu/8)integral_0^T Dcrit <= N0,
integral_0^T S^2 <= (5C5/(6nu))*N0^(12/5).                   (10)
```

With finite initial circulation maximum G0, the preceding physical swirl
comparison converts (10) to the L8_t L4_x continuation criterion. This
is an analytic conditional implication. **The signed estimate (9) is
unproved.** Its allowance must apply to the full compatible history;
it cannot be renewed each time a region or time interval is summarized.
The general three-dimensional and periodic obligations also remain open.

This target treats the earlier single concentrated Gaussian correctly:
for `b0=g+lambda^2 g(lambda X)`, convexity gives
`M(0)<=2^(5/2)integral g^(5/2)`, uniformly in lambda. Concentration by
NS rescaling does not create fictitious critical resources. This fact
alone proves no control of the subsequent dynamics.

### The previously paid parent histories can be removed

The earlier transported-history split applies throughout the meridional
space, not just on the axis. For an original fixed radial cutoff rho,
write `eta=g+eta_core`, where g contains the initial eta and all source
histories created outside the cutoff, and eta_core starts at zero with
source `partial_z[(1-zeta_rho)b^2]`. Both solve their linear equations
along the same actual interacting drift. Elliptic reconstruction gives
`q=q_paid+q_core`, with the original-datum bound

```text
integral_0^T ||q_paid||_infinity <= A_H=2M_H,
M_H=C_BS H^(3/4)(2nu)^(-1/4)Y,
Y=||eta(0)||_L2(R3)+sqrt(H C4(0)/(3nu rho^8)),
C4(0)=integral_R3 (r u_theta(0))^4.
```

These are the analytic estimates in the transported-history section;
they retain the later motion of each created source. Put

```text
a(t)=||q_paid(t)||_infinity,
w(t)=exp[-(3/2)integral_0^t a],
Pcrit_core=integral_R5 q_core |b|^(5/2).
```

Since the paid pairing is at most a M, the full balance (7) implies

```text
(w M)' +(15nu/8)w Dcrit
 <= w[(3/2)Pcrit_core-(15nu/8)Dcrit].                         (11)
```

The factor satisfies `exp(-3A_H/2)<=w<=1`. If the signed right-hand
side of (11) has an original-datum integrated allowance K, equations
(8) and (11) give the explicit conditional clock bound

```text
integral_0^T S^2
 <= (5C5/(6nu))*exp(36M_H/5)*(M(0)+K)^(12/5).                (12)
```

This removes the entire already-paid parent class from the new target.
It leaves a signed production estimate for parents born near the axis,
including their subsequent transport and nonlocal action. The source
split and w continue from the original time zero at every seam; neither
is restarted. No bound on the right-hand side of (11) is established.

### Many actual bursts with bounded source entropy and action

The distinction from the funded entropy reserve can also be tested on
the physical continuation norm. For an integer N>=2, put `lambda=N^2`
and take the literal nonnegative source

```text
b0,N(X)=g(X)+sum_(j=1)^N lambda^2 g(lambda(X-j e_z)),
u0,N=(-x2 b0,N,x1 b0,N,0).
```

Every datum is a finite Schwartz pure swirl. Write `u_base=(-x2 g,x1 g,0)`
in physical three-dimensional space. Each translated narrow velocity is
`lambda u_base(lambda(x-j e_z))`, whose L2 norm is
`lambda^-1/2 ||u_base||_2`. The triangle inequality and `lambda=N^2`
therefore give `E0,N<=4pi^(3/2)`.

Circulation has a uniform bound as well. The radial maximum of
`lambda^2 r^2 exp(-lambda^2 r^2/2)` is `2/e`. For lambda>=1, choosing
the nearest point of the axial lattice gives

```text
sum_j exp(-lambda^2(z-j)^2/2)
 <=1+2 sum_(k>=1) exp(-k^2/8)
 <=1+2sqrt(2pi)<7.
```

Including the broad background yields `G0,N<=16/e`.
The five-dimensional source mass is exactly
`M1,N=(2pi)^(5/2)(1+N^-5)`. Normalize the source to rho0,N as in the
entropy construction, with the fixed reference N(0,I5). Its Gaussian
mixture includes the means j e_z; they must not be discarded. Convexity
of relative entropy gives

```text
KL(rho0,N || N(0,I5))
 <=lambda^-3 [5N log(lambda)+(1/2)sum_(j=1)^N j^2]
 <=10 log(N)/N^5+1/(2N^3) <=2/e+1/2.
```

For each fixed nu,H, the previously constructed actual-source entropy
reserve consequently has the same upper bound for every N:

```text
R_entropy(0)<=2/e+1/2+4sqrt(2)H/(e nu).                       (13)
```

Its complete path-action and relative-Fisher payments remain valid on
every available smooth prefix. Nevertheless, both continuation clocks
below are unbounded over this family on actual unforced intervals.

Here is a uniform interval argument. Rescale the complete solution by

```text
v_N(tau,y)=lambda^-1 u_N(tau/lambda^2,y/lambda),
v_N(0,y)=lambda^-1 u_base(y/lambda)
         +sum_(j=1)^N u_base(y-lambda j e_z).
```

The viscosity is unchanged. Gaussian lattice sums, also for every fixed
derivative order, give uniform C_b^m bounds for this entire initial field,
independent of N. Smooth bounded uniformly continuous data admit a common
local mild evolution in C_b^1: the L1 norm of the heat--Leray divergence
kernel is at most `C(nu t)^(-1/2)`. Its nonlocal part is an integral of
third heat derivatives, whose L1 norm is bounded by `C s^(-3/2)`.
The resulting Picard estimate and the uniform C_b^2 initial bound give
`||v_N(tau)-v_N(0)||_C1<=C sqrt(tau)` on a common positive interval.
For each finite N, this is the actual smooth finite-energy NS solution
by local uniqueness. No independent packet trajectories are glued.

On each of the N disjoint rescaled annuli
`1<=r<=2`, `|z-lambda j|<=1`, the initial source is at least `exp(-5/2)`.
Choose a common tau0(nu)>0 small enough that the evolving b there stays
above `c0=exp(-5/2)/2`. Division by r costs at most one on these annuli.
For `0<=tau<=tau0`, direct integration gives

```text
integral_R5 |b(v_N)|^3 >= a3 N,     a3=15pi^2 c0^3,
||v_N,theta||_L4(R3)^4 >= a4 N,     a4=42pi c0^4.
```

Both spatial quantities acquire a factor lambda on returning to the
physical solution; time acquires `lambda^-2`. Hence

```text
integral_0^(tau0/lambda^2) S_N(t)^2 dt >=tau0 a3^2 N^2,
integral_0^(tau0/lambda^2) ||u_N,theta(t)||_4^8 dt >=tau0 a4^2 N^2.   (14)
```

These intervals lie below any prescribed H>0 for all sufficiently large N.
Thus no finite uniform bound for these clocks follows from the displayed
common upper bounds on source entropy/action, initial energy, circulation
and source mass alone, at fixed viscosity and horizon. This statement
concerns bounds from those upper bounds; it does not exclude arbitrary
encodings of the datum in exact scalar values or a full-datum allowance.
It is a family of regular short evolutions, not blowup of a single datum.
The concentrated packets are initially prepared and act simultaneously;
this does not establish repeated renewal from one packet.

The new moment records what is missing. Positivity and the power law give
`M(0)>=N integral g^(5/2)`. It is also at most a constant times N+1:
after rescaling, the packet sum is bounded by seven and its L1 mass is
N times the Gaussian mass; the background contributes a fixed critical
moment. Thus multiplicity is present in the original critical resource
even when (13) stays bounded. The signed production needed to control
its subsequent renewal remains the physical question in (9).

Run `python3 -O labs/swirl_channel_reserve.py`. The balances, scales,
Gaussian constants, algebraic separation bound, viscous rebound coefficient
and conditional clock constants pass exact checks. Translation decoupling,
uniform local existence, entropy convexity and continuation are analytic.
No new Lean certification or unconditional regularity is claimed.

## Axial ordering, signed parent histories, and its dynamical defect

`swirl_order_history.py` identifies a class of generated-parent work with
a favorable sign along the **actual interacting evolution**. It also
constructs smooth unforced data showing that initial membership in this
geometric class need not persist. The exact history decomposition retains
the terms created when ordering fails. The PDE and interval arguments here
are analytic, not new Lean theorems.

### Positive propagators retain the nonlinear parent history

Continue with the preceding axisymmetric whole-space variables. Assume
reflection symmetry about z=0: b and u_r are even in z, u_z is odd, and
eta=omega_theta/r is odd. These parities are preserved by uniqueness of
the smooth unforced NS evolution. Smoothness at the axis and sufficient
decay justify the integrals below. Let

```text
D=R4 times (0,infinity),  beta(r)=1-zeta_rho(r),
f=beta b^2,  F=|b|^(5/2),
(partial_t+v.grad-nu Delta5)eta_core=partial_z f,
eta_core(0)=0,  eta_core|_(z=0)=0.
```

On each available smooth prefix, let U_v(t,s) be the Dirichlet propagator
of `nu Delta5-v.grad` on D with this same complete meridional drift.
The maximum principle makes U_v positive; no bound on its operator norm
or on future drift derivatives is inferred. In particular, this is not
the heat propagator and does not remove parent transport.

Let K_D be the Dirichlet inverse of -Delta5 on D. Its kernel is

```text
G5(X-Y)-G5(X-Y_reflected),  G5(X)=1/(8pi^2 |X|^3).
```

It is positive for X,Y in D because reflection increases their distance.
The full-space potential of an odd function restricts to K_D. Thus
the actual nonlocal reconstruction and history are

```text
q_core=2partial_z K_D eta_core,
eta_core(t)=integral_0^t U_v(t,s) partial_z f(s) ds.
```

The full-space production is consequently

```text
Pcrit_core(t)
 =-4 integral_0^t <partial_z F(t),K_D U_v(t,s) partial_z f(s)>_D ds. (15)
```

The factor four includes the two reflected half-spaces and the factor
two in q_core. The integration-by-parts boundary term vanishes because
K_D eta_core has zero trace at z=0. The receiver F(t) is the actual
evolving swirl at the observation time; it is not frozen at time zero.

Equivalently, full-space adjoint duality uses
`-psi_t=nu Delta5 psi+div5(v psi)+h`, `psi(T)=0`. Here `div5(v)=-q`
must be retained. With `h=w(t)*(-2partial_z K5)F`, it gives
`integral w Pcrit_core=-integral f psi_z`. The checker verifies the
complete local identity, including its diffusive and transport fluxes.

### Ordered histories deplete the critical moment

Suppose `partial_z(b^2)<=0` on D throughout the prefix. Since beta is
nonnegative and radial, the source derivative is nonpositive. Positivity
of U_v implies eta_core<=0, and positivity of K_D then implies
K_D eta_core<=0. The receiver has the same derivative sign, since

```text
partial_z |b|^(5/2)=(5/4)|b|^(1/2) partial_z(b^2).
```

Equation (15) gives `Pcrit_core<=0`. This controls the entire generated
history, including full parent transport and elliptic response. It does
not require small swirl or small drift.

Combining this sign with the preceding paid-parent factor w leaves the
entire critical diffusion available:

```text
(w M)' +(15nu/4)w Dcrit<=0,
integral_0^T S^2 <=(5C5/(12nu))*exp(36M_H/5)*M(0)^(12/5).       (16)
```

Thus persistence of the stated geometric ordering supplies the sufficient
axisymmetric continuation bound. For initially pure swirl one may instead
use beta=1 and the full generated eta, with no paid class: then w=1,
M_H=0 and M itself is nonincreasing while the ordering persists. The same
argument allows initially nonpositive eta on D. These are conditional
physical implications, not a proof that arbitrary initial order persists.

### Which departures from ordering can produce positive work?

Formula (15) also applies without axial monotonicity. Put
`d=partial_z F`, `j=partial_z f`, and split each into positive and negative
parts, `d=d_+-d_-`, `j=j_+-j_-`. For a,b in {+,-}, define

```text
C_ab(t)=integral_0^t <d_a(t),K_D U_v(t,s) j_b(s)>_D ds >=0.
```

The exact identity is

```text
Pcrit_core=4(C_{+,-}+C_{-,+}-C_{+,+}-C_{-,-}).                (17)
```

Matching derivative signs deplete this moment; opposite signs at the
source and its later receiver can increase it. The spatial coupling and
the complete intervening drift remain inside K_D U_v. This is a signed
comparison of compatible histories, not a sum of independent bursts.

In this reflection-symmetric class, the current open allowance is exactly

```text
integral_0^T w[6(C_{+,-}+C_{-,+}-C_{+,+}-C_{-,-})-(15nu/8)Dcrit]
 <= K(u0,nu,H,rho).                                          (18)
```

The negative terms in (18) may matter; discarding them gives a stronger
and still unproved target. No initial bound for (18) is supplied here.

### Initial ordering can fail through internally generated pressure

For n=b_z, differentiating the actual swirl equation and using
incompressibility gives

```text
n_t+v.grad n-nu Delta5 n
 =-(r/2)q_r n+q_z(b+(r/2)b_r).                               (19)
```

The last factor is half the axial vorticity. The term involving q_z is
not sign-controlled by n<=0. The following datum makes it strictly
positive at a flat part of the initial profile, without external force.

Choose a nonnegative smooth a(r), nonzero and supported in 4<r<5.
Choose h(z) smooth and even, equal to one for |z|<=1, zero for |z|>=2,
with h'<0 on (1,2). Set

```text
b0(r,z)=[a(r)+delta exp(-r^2/2)]h(z),
u0=(-x2 b0,x1 b0,0),                        delta>0.
```

This is a Schwartz divergence-free pure swirl with initially nonincreasing
b0^2 on D. Evaluate at r=0,z0=1/2. Initially the meridional velocity is
zero and
`sigma=q_t(0)=2partial_zz K5(b0^2)`, independent of viscosity. Write
`B(r)=a(r)+delta exp(-r^2/2)` and `g(R,w)=(R^2+w^2)^(-3/2)`. Moving one
axial derivative to h^2 gives the nonsingular formula

```text
sigma_z(0,z0)
 =(1/2)integral_0^infinity R^3 B(R)^2 integral_1^2 (h^2)'(s)
     [g_ww(R,s-z0)-g_ww(R,s+z0)] ds dR,
g_www(R,w)=15w(3R^2-4w^2)/(R^2+w^2)^(9/2).
```

For 4<=R<=5 and 1/2<=w<=5/2, `3R^2-4w^2>=23`. Thus g_ww increases
strictly across this interval. The bracket is negative, whereas (h^2)'
is negative. The annular term and the annulus/Gaussian cross term in
sigma_z are both strictly positive.

Let A>0 be the annular contribution and D the absolute Gaussian-only
contribution. Both are finite. Choosing `delta=A/[2(A+D)]` gives

```text
sigma_z[full datum]>=A-delta^2 D>=15A/16>0.
```

This fixes a single smooth datum. Its local axial flatness gives
`n(0)=n_t(0)=0` near the test point: all initial axial diffusion terms
vanish there. Differentiating (19) once in time then yields

```text
n_tt(0,0,1/2)=delta*sigma_z(0,1/2)>0.                         (20)
```

For every fixed nu>0, local smooth NS existence and time differentiability
therefore give n(t,0,1/2)>0 for all sufficiently small positive times.
Continuity gives a neighboring region of increasing b^2 as well. This
is an actual interval argument from a strict initial second derivative;
it assumes no viscosity-free evolution or long Taylor window.

The example refutes preservation of initial axial ordering. It does not
refute the conditional sign theorem, the signed compensation in (18),
a finite original-datum allowance, or regularity. In particular, newly
positive cross terms need not dominate the remaining negative work.
The annulus can be placed within any prescribed core radius by NS spatial
rescaling. The underlying profile may change while its total signed work
remains paid; a quantitative history estimate must allow that possibility.

Indeed this same example has favorable **net** production initially.
Use the full source beta=1; the entire meridional parent starts at zero.
Both `d0=partial_z F0` and `j0=partial_z(b0^2)` are nonpositive on D
and nonzero on sets of positive measure. Strict positivity of K_D gives

```text
Pcrit'(0)=-4<d0,K_D j0>_D<0.
```

Hence Pcrit(t)<0 on a sufficiently short positive interval, and the
complete moment M decreases there. During that same interval the axial
ordering is already broken near the test point. Persistent pointwise
ordering is therefore stronger than the signed payment actually needed.
Controlling the compensation in (18), rather than forbidding every
geometric departure, remains a viable and distinct question.

Run `python3 -O labs/swirl_order_history.py --quadrature`. Exact checks
cover the local equations, complete initial second derivative, full adjoint
flux, Green derivatives, kernel normalization and algebraic margins.
The optional quadrature uses `a(r)=exp[4-1/((r-4)(5-r))]` on (4,5),
zero outside, and `h(s)=1/[1+exp(1/(2-s)-1/(s-1))]` on (1,2), with
the stated plateau, zero extension and reflection. The 64/96/128-point
quadratures give `n_tt(0)` approximately
`0.0003070871013`. It supports the kernel calculation and has no certified
quadrature error; it is not a numerical evolution. Propagator positivity,
PDE existence, physical interval and continuation claims remain analytic.
