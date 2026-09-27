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
