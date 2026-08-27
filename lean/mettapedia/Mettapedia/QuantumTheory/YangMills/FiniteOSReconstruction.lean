import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite Osterwalder-Schrader reconstruction step

This module proves the finite algebraic core of the OS reconstruction used by
the Yang-Mills lane.  A reflection-positive finite kernel gives a positive
pairing on observables.  If a transfer operator is self-adjoint for that
pairing, then it descends to the pairing quotient and remains self-adjoint
there.

No continuum Yang-Mills measure or mass gap is asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

universe u

/-- Real finite observables on a finite lattice/sample space. -/
abbrev FiniteObservable (Ω : Type u) := Ω → ℝ

/-- The OS bilinear pairing induced by a finite reflection-positive kernel. -/
def osBilinearForm {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ) (f g : FiniteObservable Ω) : ℝ :=
  ∑ x : Ω, ∑ y : Ω, f x * K x y * g y

/-- Reflection positivity for the finite OS kernel. -/
def OSReflectionPositive {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ) : Prop :=
  ∀ f : FiniteObservable Ω, 0 ≤ osBilinearForm K f f

/-- Symmetry of the finite OS pairing. -/
def OSSymmetric {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ) : Prop :=
  ∀ f g : FiniteObservable Ω, osBilinearForm K f g = osBilinearForm K g f

/-- Two observables are identified when every OS pairing against them agrees. -/
def OSPairingEquivalent {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ) (f g : FiniteObservable Ω) : Prop :=
  ∀ h : FiniteObservable Ω, osBilinearForm K f h = osBilinearForm K g h

/-- The quotient relation as an explicit binary relation on finite observables. -/
abbrev OSPairingRel {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ) :
    FiniteObservable Ω → FiniteObservable Ω → Prop :=
  fun f g => OSPairingEquivalent K f g

/-- The finite OS quotient of observables by the pairing radical. -/
abbrev OSQuotient {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ) : Type u :=
  Quot (OSPairingRel K)

/-- Well-definedness of the OS pairing on the quotient. -/
def OSInnerWellDefined {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ) : Prop :=
  ∀ {f f' g g' : FiniteObservable Ω},
    OSPairingEquivalent K f f' →
      OSPairingEquivalent K g g' →
        osBilinearForm K f g = osBilinearForm K f' g'

/-- A transfer operator is self-adjoint for the finite OS pairing. -/
def OSTransferSelfAdjoint {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ)
    (T : FiniteObservable Ω → FiniteObservable Ω) : Prop :=
  ∀ f g : FiniteObservable Ω,
    osBilinearForm K (T f) g = osBilinearForm K f (T g)

/-- A transfer operator respects the OS quotient relation. -/
def OSTransferWellDefined {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ)
    (T : FiniteObservable Ω → FiniteObservable Ω) : Prop :=
  ∀ {f g : FiniteObservable Ω},
    OSPairingEquivalent K f g → OSPairingEquivalent K (T f) (T g)

/-- Symmetry of the OS pairing makes the pairing well-defined in both
arguments on the quotient. -/
theorem osInnerWellDefined_of_symmetric {Ω : Type u} [Fintype Ω]
    {K : Ω → Ω → ℝ}
    (hsym : OSSymmetric K) :
    OSInnerWellDefined K := by
  intro f f' g g' hff hgg
  calc
    osBilinearForm K f g = osBilinearForm K f' g := hff g
    _ = osBilinearForm K g f' := hsym f' g
    _ = osBilinearForm K g' f' := hgg f'
    _ = osBilinearForm K f' g' := (hsym f' g').symm

/-- Self-adjointness for the OS pairing forces the transfer operator to
descend through the pairing quotient. -/
theorem osTransferWellDefined_of_selfAdjoint {Ω : Type u} [Fintype Ω]
    {K : Ω → Ω → ℝ}
    {T : FiniteObservable Ω → FiniteObservable Ω}
    (hself : OSTransferSelfAdjoint K T) :
    OSTransferWellDefined K T := by
  intro f g hfg test
  calc
    osBilinearForm K (T f) test = osBilinearForm K f (T test) := hself f test
    _ = osBilinearForm K g (T test) := hfg (T test)
    _ = osBilinearForm K (T g) test := (hself g test).symm

/-- The transfer operator induced on the finite OS quotient. -/
def osTransferOnQuotient {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ)
    (T : FiniteObservable Ω → FiniteObservable Ω)
    (hwell : OSTransferWellDefined K T) :
    OSQuotient K → OSQuotient K :=
  Quot.map T (by
    intro f g hfg
    exact hwell hfg)

@[simp] theorem osTransferOnQuotient_mk {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ)
    (T : FiniteObservable Ω → FiniteObservable Ω)
    (hwell : OSTransferWellDefined K T)
    (f : FiniteObservable Ω) :
    osTransferOnQuotient K T hwell (Quot.mk (OSPairingRel K) f) =
      Quot.mk (OSPairingRel K) (T f) := by
  rfl

/-- The finite OS reconstruction packet produced from reflection positivity,
pairing symmetry, and transfer self-adjointness. -/
structure FiniteOSReconstruction {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ)
    (T : FiniteObservable Ω → FiniteObservable Ω) where
  reflectionPositive : OSReflectionPositive K
  symmetric : OSSymmetric K
  transferSelfAdjoint : OSTransferSelfAdjoint K T
  innerWellDefined : OSInnerWellDefined K
  transferWellDefined : OSTransferWellDefined K T
  quotientTransfer : OSQuotient K → OSQuotient K
  quotientTransfer_mk :
    ∀ f : FiniteObservable Ω,
      quotientTransfer (Quot.mk (OSPairingRel K) f) =
        Quot.mk (OSPairingRel K) (T f)

/-- Finite reflection positivity plus the transfer dagger condition constructs
the OS quotient data and a descended self-adjoint transfer operator. -/
def finiteOSReconstruction_of_reflectionPositive_selfAdjoint
    {Ω : Type u} [Fintype Ω]
    {K : Ω → Ω → ℝ}
    {T : FiniteObservable Ω → FiniteObservable Ω}
    (hpos : OSReflectionPositive K)
    (hsym : OSSymmetric K)
    (hself : OSTransferSelfAdjoint K T) :
    FiniteOSReconstruction K T where
  reflectionPositive := hpos
  symmetric := hsym
  transferSelfAdjoint := hself
  innerWellDefined := osInnerWellDefined_of_symmetric hsym
  transferWellDefined := osTransferWellDefined_of_selfAdjoint hself
  quotientTransfer :=
    osTransferOnQuotient K T (osTransferWellDefined_of_selfAdjoint hself)
  quotientTransfer_mk := by
    intro f
    rfl

/-- Public packet for the finite OS step: the quotient pairing and transfer
operator are well-defined, and the transfer is self-adjoint for the OS pairing. -/
theorem finiteOSReconstruction_reflectionPositive_transfer_packet
    {Ω : Type u} [Fintype Ω]
    {K : Ω → Ω → ℝ}
    {T : FiniteObservable Ω → FiniteObservable Ω}
    (hpos : OSReflectionPositive K)
    (hsym : OSSymmetric K)
    (hself : OSTransferSelfAdjoint K T) :
    OSReflectionPositive K ∧
      OSInnerWellDefined K ∧
      OSTransferWellDefined K T ∧
      OSTransferSelfAdjoint K T := by
  exact
    ⟨hpos,
      osInnerWellDefined_of_symmetric hsym,
      osTransferWellDefined_of_selfAdjoint hself,
      hself⟩

end YangMills
end QuantumTheory
end Mettapedia
