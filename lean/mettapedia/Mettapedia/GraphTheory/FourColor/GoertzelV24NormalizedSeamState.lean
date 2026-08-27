import Mettapedia.GraphTheory.FourColor.GoertzelV24NormalizedTaitSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamExchange

/-!
# The finite normalized seam-and-support state

The exact tree-descent receipt has two independent components:

* the hub rotation transported to a standard finite boundary carrier; and
* the finite set of genuine Tait boundary words realized by the inner piece.

Equality of the first component transports orientation reversal through a
replacement.  Equality of the second component transports zero Count.  Keeping
the two fields visibly separate prevents support equality from silently being
used as a topological statement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24NormalizedSeamState

open GoertzelV24OpenTangleComposition
open GoertzelV24NormalizedTaitSupport
open GoertzelV24RawNooseCountPumping
open GoertzelV24SeamExchange

universe u

/-- The exact finite receipt at a `k`-port cut. -/
structure State (k : Nat) where
  hubRotation : Equiv.Perm (StandardPort.{u} k)
  support : Finset (CutWord (StandardPort.{u} k))
deriving DecidableEq

/-- The receipt is equivalent to the product of its two finite fields. -/
def stateEquiv (k : Nat) :
    State.{u} k ≃
      Equiv.Perm (StandardPort.{u} k) ×
        Finset (CutWord (StandardPort.{u} k)) where
  toFun state := (state.hubRotation, state.support)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv state := by cases state; rfl
  right_inv fields := by cases fields; rfl

noncomputable instance instFintypeState (k : Nat) :
    Fintype (State.{u} k) :=
  Fintype.ofEquiv
    (Equiv.Perm (StandardPort.{u} k) ×
      Finset (CutWord (StandardPort.{u} k)))
    (stateEquiv.{u} k).symm

/-- Raw cardinality of the full normalized receipt: one permutation of the
`k` ports and one subset of the `3^k` genuine colour words. -/
theorem card_state (k : Nat) :
    Fintype.card (State.{u} k) = Nat.factorial k * 2 ^ (3 ^ k) := by
  rw [Fintype.card_congr (stateEquiv.{u} k), Fintype.card_prod,
    Fintype.card_perm, card_normalizedSupportType]
  simp [StandardPort]

/-- Transport the two intrinsic fields of an inner open tangle to the standard
`k`-port coordinate carrier. -/
noncomputable def ofInnerTangle (k : Nat)
    {W J R : Type u} [Fintype W] [DecidableEq W]
    [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]
    (right : OpenTangleData W J R) (hubRotation : Equiv.Perm R)
    (coordinate : R ≃ StandardPort.{u} k) : State k where
  hubRotation := coordinate.permCongr hubRotation
  support := normalizedTaitInnerSupport k right coordinate

/-- Equality of normalized rotations says that the coordinate change between
the two literal boundary carriers conjugates their hub rotations. -/
theorem hubRotation_transport_of_normalized_eq
    (k : Nat) {R R' : Type u}
    (ρ : Equiv.Perm R) (ρ' : Equiv.Perm R')
    (coordinate : R ≃ StandardPort.{u} k)
    (coordinate' : R' ≃ StandardPort.{u} k)
    (hrotation : coordinate.permCongr ρ = coordinate'.permCongr ρ')
    (port : R) :
    ρ' ((coordinate.trans coordinate'.symm) port) =
      (coordinate.trans coordinate'.symm) (ρ port) := by
  have happly := congrArg (fun permutation => permutation (coordinate port))
    hrotation
  have hback := congrArg coordinate'.symm happly
  simpa [Equiv.permCongr_apply] using hback.symm

/-- An orientation-reversing old seam remains orientation-reversing after
replacing its inner piece by one with the same normalized hub rotation. -/
theorem orientationReversing_replacement
    (k : Nat) {L R R' : Type u}
    (matching : L ≃ R)
    (ρL : Equiv.Perm L) (ρ : Equiv.Perm R) (ρ' : Equiv.Perm R')
    (coordinate : R ≃ StandardPort.{u} k)
    (coordinate' : R' ≃ StandardPort.{u} k)
    (hrev : OrientationReversing matching ρL ρ)
    (hrotation : coordinate.permCongr ρ = coordinate'.permCongr ρ') :
    OrientationReversing
      (matching.trans (coordinate.trans coordinate'.symm)) ρL ρ' := by
  intro port
  calc
    ρ' ((matching.trans (coordinate.trans coordinate'.symm)) port) =
        (coordinate.trans coordinate'.symm) (ρ (matching port)) :=
      hubRotation_transport_of_normalized_eq k ρ ρ' coordinate coordinate'
        hrotation (matching port)
    _ = (coordinate.trans coordinate'.symm)
          (matching (ρL.symm port)) := congrArg _ (hrev port)
    _ = (matching.trans (coordinate.trans coordinate'.symm))
          (ρL.symm port) := rfl

/-- Equality of full normalized states exposes exactly the support equality
consumed by the physical replacement theorem. -/
theorem normalizedSupport_eq_of_state_eq
    (k : Nat)
    {W J R : Type u} [Fintype W] [DecidableEq W]
    [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]
    (right : OpenTangleData W J R) (ρ : Equiv.Perm R)
    (coordinate : R ≃ StandardPort.{u} k)
    {W' J' R' : Type u} [Fintype W'] [DecidableEq W']
    [Fintype J'] [DecidableEq J'] [Fintype R'] [DecidableEq R']
    (right' : OpenTangleData W' J' R') (ρ' : Equiv.Perm R')
    (coordinate' : R' ≃ StandardPort.{u} k)
    (hstate : ofInnerTangle k right ρ coordinate =
      ofInnerTangle k right' ρ' coordinate') :
    normalizedTaitInnerSupport k right coordinate =
      normalizedTaitInnerSupport k right' coordinate' :=
  congrArg State.support hstate

/-- Equality of full normalized states also exposes exactly the conjugacy
needed to transport orientation reversal. -/
theorem normalizedHubRotation_eq_of_state_eq
    (k : Nat)
    {W J R : Type u} [Fintype W] [DecidableEq W]
    [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]
    (right : OpenTangleData W J R) (ρ : Equiv.Perm R)
    (coordinate : R ≃ StandardPort.{u} k)
    {W' J' R' : Type u} [Fintype W'] [DecidableEq W']
    [Fintype J'] [DecidableEq J'] [Fintype R'] [DecidableEq R']
    (right' : OpenTangleData W' J' R') (ρ' : Equiv.Perm R')
    (coordinate' : R' ≃ StandardPort.{u} k)
    (hstate : ofInnerTangle k right ρ coordinate =
      ofInnerTangle k right' ρ' coordinate') :
    coordinate.permCongr ρ = coordinate'.permCongr ρ' :=
  congrArg State.hubRotation hstate

/-- The full finite state simultaneously preserves normalized zero Count and
the orientation equation required by the spherical seam constructor. -/
theorem replacement_receipt
    (k : Nat)
    {L R R' : Type u}
    (matching : L ≃ R)
    (ρL : Equiv.Perm L) (ρ : Equiv.Perm R) (ρ' : Equiv.Perm R')
    (coordinate : R ≃ StandardPort.{u} k)
    (coordinate' : R' ≃ StandardPort.{u} k)
    {W J : Type u} [Fintype W] [DecidableEq W]
    [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]
    (right : OpenTangleData W J R)
    {W' J' : Type u} [Fintype W'] [DecidableEq W']
    [Fintype J'] [DecidableEq J'] [Fintype R'] [DecidableEq R']
    (right' : OpenTangleData W' J' R')
    (hrev : OrientationReversing matching ρL ρ)
    (hstate : ofInnerTangle k right ρ coordinate =
      ofInnerTangle k right' ρ' coordinate') :
    OrientationReversing
        (matching.trans (coordinate.trans coordinate'.symm)) ρL ρ' ∧
      normalizedTaitInnerSupport k right coordinate =
        normalizedTaitInnerSupport k right' coordinate' := by
  constructor
  · exact orientationReversing_replacement k matching ρL ρ ρ' coordinate
      coordinate' hrev
      (normalizedHubRotation_eq_of_state_eq k right ρ coordinate right' ρ'
        coordinate' hstate)
  · exact normalizedSupport_eq_of_state_eq k right ρ coordinate right' ρ'
      coordinate' hstate

end GoertzelV24NormalizedSeamState

end Mettapedia.GraphTheory.FourColor
