import Mettapedia.GraphTheory.FourColor.GoertzelV24CanonicalHubClosure
import Mathlib.GroupTheory.Perm.Fin

/-!
# Cyclic bond boundaries

The canonical hub construction closes facial boundary-return arcs for any
finite interface.  A geometric noose supplies one additional fact: all of
those ports occur in one cyclic boundary order.  This file isolates that
fact as a small finite witness and proves its exact permutation-theoretic
consequences.

Nothing here constructs a noose.  The point is to make the interface from
noose geometry to the already-verified cap algebra explicit: an exhaustive
cyclic enumeration whose successor is the retained facial first return.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CyclicBondBoundary

open Equiv Equiv.Perm
open GoertzelV24CanonicalHubClosure
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24VertexSideOpenTangle

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- An exhaustive cyclic coordinate system for the exposed darts of one
literal vertex shore.  The equality says that retained facial first return
is exactly the positive cyclic shift in these coordinates. -/
structure CyclicBondBoundaryData
    (RS : RotationSystem V E) (keep : V → Prop) where
  length : Nat
  two_le_length : 2 ≤ length
  order : Fin length ≃ BoundaryDart RS keep
  successor_eq :
    order.permCongr (finRotate length) =
      retainedRegionBoundarySuccessor RS keep

namespace CyclicBondBoundaryData

variable {RS : RotationSystem V E} {keep keepL keepR : V → Prop}

/-- Transporting a cycle across an equivalence of finite carriers preserves
the cycle property. -/
theorem isCycle_permCongr
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (coordinate : A ≃ B) (perm : Equiv.Perm A)
    (hcycle : perm.IsCycle) :
    (coordinate.permCongr perm).IsCycle := by
  rcases hcycle with ⟨root, hroot, hreach⟩
  refine ⟨coordinate root, ?_, ?_⟩
  · rw [Equiv.permCongr_apply, coordinate.symm_apply_apply]
    exact coordinate.injective.ne hroot
  · intro target htarget
    let source := coordinate.symm target
    have hsource : perm source ≠ source := by
      intro hfixed
      apply htarget
      have := congrArg coordinate hfixed
      simpa only [source, Equiv.apply_symm_apply,
        Equiv.permCongr_apply] using this
    have hsame := hreach hsource
    have htransport :=
      (GoertzelV24OrderedCutFaceReturnProfile.permCongr_sameCycle_iff
        coordinate perm root source).2 hsame
    simpa only [source, Equiv.apply_symm_apply] using htransport

/-- The witness records the exact number of boundary darts. -/
theorem card_boundary_eq_length
    (data : CyclicBondBoundaryData RS keep) :
    Fintype.card (BoundaryDart RS keep) = data.length := by
  simpa using Fintype.card_congr data.order.symm

/-- Retained facial first return is one nontrivial cycle. -/
theorem successor_isCycle
    (data : CyclicBondBoundaryData RS keep) :
    (retainedRegionBoundarySuccessor RS keep).IsCycle := by
  rw [← data.successor_eq]
  exact isCycle_permCongr data.order (finRotate data.length)
    (isCycle_finRotate_of_le data.two_le_length)

/-- Every exposed dart is moved by retained facial first return.  Together
with `successor_isCycle`, this says the single cycle exhausts the boundary. -/
theorem successor_apply_ne
    (data : CyclicBondBoundaryData RS keep)
    (dart : BoundaryDart RS keep) :
    retainedRegionBoundarySuccessor RS keep dart ≠ dart := by
  let index := data.order.symm dart
  have hindex : finRotate data.length index ≠ index := by
    have hmem : index ∈ (finRotate data.length).support := by
      rw [support_finRotate_of_le data.two_le_length]
      simp
    simpa only [Equiv.Perm.mem_support] using hmem
  rw [← data.successor_eq, Equiv.permCongr_apply]
  intro heq
  apply hindex
  apply data.order.injective
  simpa only [index, Equiv.apply_symm_apply] using heq

/-- The inverse first-return order used by the canonical cap is one cycle. -/
theorem canonicalHubRotation_isCycle
    (data : CyclicBondBoundaryData RS keep) :
    (canonicalHubRotation RS keep).IsCycle := by
  exact data.successor_isCycle.inv

/-- The canonical hub rotation moves every boundary dart. -/
theorem canonicalHubRotation_apply_ne
    (data : CyclicBondBoundaryData RS keep)
    (dart : BoundaryDart RS keep) :
    canonicalHubRotation RS keep dart ≠ dart := by
  intro hfixed
  apply data.successor_apply_ne dart
  have happly := congrArg
    (retainedRegionBoundarySuccessor RS keep) hfixed
  simpa only [canonicalHubRotation, Equiv.Perm.coe_inv,
    Equiv.apply_symm_apply] using happly.symm

/-- Opposite first-return orders make the right successor the transported
inverse of the left successor. -/
theorem rightSuccessor_eq_permCongr_inv_of_opposite
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (hopposite : ∀ b : BoundaryDart RS keepL,
      retainedRegionBoundarySuccessor RS keepR
          (matching (retainedRegionBoundarySuccessor RS keepL b)) =
        matching b) :
    retainedRegionBoundarySuccessor RS keepR =
      matching.permCongr
        (retainedRegionBoundarySuccessor RS keepL)⁻¹ := by
  apply Equiv.ext
  intro right
  let left := matching.symm right
  have h := hopposite
    ((retainedRegionBoundarySuccessor RS keepL)⁻¹ left)
  simpa only [Equiv.permCongr_apply, left, Equiv.Perm.coe_inv,
    Equiv.apply_symm_apply] using h

/-- One cyclic shore and the opposite-return equation force the other shore
to be cyclic as well. -/
theorem rightSuccessor_isCycle_of_opposite
    (leftData : CyclicBondBoundaryData RS keepL)
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (hopposite : ∀ b : BoundaryDart RS keepL,
      retainedRegionBoundarySuccessor RS keepR
          (matching (retainedRegionBoundarySuccessor RS keepL b)) =
        matching b) :
    (retainedRegionBoundarySuccessor RS keepR).IsCycle := by
  rw [rightSuccessor_eq_permCongr_inv_of_opposite matching hopposite]
  exact isCycle_permCongr matching
    (retainedRegionBoundarySuccessor RS keepL)⁻¹
    leftData.successor_isCycle.inv

/-- Opposite transport also shows that the right successor moves every one
of its boundary darts. -/
theorem rightSuccessor_apply_ne_of_opposite
    (leftData : CyclicBondBoundaryData RS keepL)
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (hopposite : ∀ b : BoundaryDart RS keepL,
      retainedRegionBoundarySuccessor RS keepR
          (matching (retainedRegionBoundarySuccessor RS keepL b)) =
        matching b)
    (dart : BoundaryDart RS keepR) :
    retainedRegionBoundarySuccessor RS keepR dart ≠ dart := by
  rw [rightSuccessor_eq_permCongr_inv_of_opposite matching hopposite,
    Equiv.permCongr_apply]
  intro hfixed
  have hinvFixed :
      (retainedRegionBoundarySuccessor RS keepL)⁻¹ (matching.symm dart) =
        matching.symm dart := by
    apply matching.injective
    simpa only [Equiv.apply_symm_apply] using hfixed
  exact leftData.canonicalHubRotation_apply_ne
    (matching.symm dart) hinvFixed

/-- Hence the right canonical hub rotation also moves every boundary dart. -/
theorem rightCanonicalHubRotation_apply_ne_of_opposite
    (leftData : CyclicBondBoundaryData RS keepL)
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (hopposite : ∀ b : BoundaryDart RS keepL,
      retainedRegionBoundarySuccessor RS keepR
          (matching (retainedRegionBoundarySuccessor RS keepL b)) =
        matching b)
    (dart : BoundaryDart RS keepR) :
    canonicalHubRotation RS keepR dart ≠ dart := by
  intro hfixed
  have happly := congrArg
    (retainedRegionBoundarySuccessor RS keepR) hfixed
  have hsuccessorFixed :
      retainedRegionBoundarySuccessor RS keepR dart = dart := by
    simpa only [canonicalHubRotation, Equiv.Perm.coe_inv,
      Equiv.apply_symm_apply] using happly.symm
  exact rightSuccessor_apply_ne_of_opposite
    leftData matching hopposite dart hsuccessorFixed

/-- Under opposite first-return orders, one cyclic boundary witness proves
that both canonical caps add a single cyclic hub vertex. -/
theorem canonicalHubRotations_isCycle_of_opposite
    (leftData : CyclicBondBoundaryData RS keepL)
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (hopposite : ∀ b : BoundaryDart RS keepL,
      retainedRegionBoundarySuccessor RS keepR
          (matching (retainedRegionBoundarySuccessor RS keepL b)) =
        matching b) :
    (canonicalHubRotation RS keepL).IsCycle ∧
      (canonicalHubRotation RS keepR).IsCycle := by
  constructor
  · exact leftData.canonicalHubRotation_isCycle
  · exact (rightSuccessor_isCycle_of_opposite
      leftData matching hopposite).inv

/-- Strong form: each canonical hub rotation is one cycle whose support is
the entire boundary carrier. -/
theorem canonicalHubRotations_singleCycle_of_opposite
    (leftData : CyclicBondBoundaryData RS keepL)
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (hopposite : ∀ b : BoundaryDart RS keepL,
      retainedRegionBoundarySuccessor RS keepR
          (matching (retainedRegionBoundarySuccessor RS keepL b)) =
        matching b) :
    ((canonicalHubRotation RS keepL).IsCycle ∧
        ∀ b : BoundaryDart RS keepL,
          canonicalHubRotation RS keepL b ≠ b) ∧
      ((canonicalHubRotation RS keepR).IsCycle ∧
        ∀ b : BoundaryDart RS keepR,
          canonicalHubRotation RS keepR b ≠ b) := by
  rcases canonicalHubRotations_isCycle_of_opposite
    leftData matching hopposite with ⟨hleft, hright⟩
  exact ⟨⟨hleft, leftData.canonicalHubRotation_apply_ne⟩,
    ⟨hright,
      rightCanonicalHubRotation_apply_ne_of_opposite
        leftData matching hopposite⟩⟩

end CyclicBondBoundaryData

end

end GoertzelV24CyclicBondBoundary

end Mettapedia.GraphTheory.FourColor
