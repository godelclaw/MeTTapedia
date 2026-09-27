# Navier–Stokes interaction labs

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
