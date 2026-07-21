import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Wilson-polymer recombination: exact operator and the factor-14 audit

The manuscript's recombination map sends a connected cumulant family to the
union of its block supports and sums all contributions with the same union.
This file formalizes that map on a finite block carrier.

For any nonnegative target weight, regrouping by union has operator norm at
most one from the family majorant weighted by that same union to the activity
majorant.  Consequently, a factor such as `14` cannot be the norm of the
regrouping operation itself.  It must arise earlier, in a theorem controlling
which connected cumulant families are generated from input activities.

The manuscript motivates `14 = 2(2d-1)` by saying that two polymers can become
connected in at most fourteen ways in four dimensions.  Under the literal
nearest-neighbor-contact interpretation this is false: two connected rails in
a `2 × 16` lattice strip have sixteen distinct contact edges.  The number
fourteen can still serve as the nonbacktracking branching degree at one marked
edge, but that is a different, rooted tree-graph estimate and requires its own
statement and proof.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-! ## Exact regrouping by union support -/

variable {Block : Type*} [Fintype Block] [DecidableEq Block]

/-- A finite polymer is a finite set of blocks. -/
abbrev FinitePolymer (Block : Type*) := Finset Block

/-- A cumulant family is a finite set of finite polymers. -/
abbrev FinitePolymerFamily (Block : Type*) := Finset (FinitePolymer Block)

/-- Union support of all factors in a cumulant family. -/
def polymerFamilyUnion (family : FinitePolymerFamily Block) :
    FinitePolymer Block :=
  family.biUnion id

/-- The manuscript's recombination operation: group family contributions by
their exact union support.  Connectedness may be enforced by setting the
contribution of nonconnected families to zero. -/
def recombineByUnion
    (contribution : FinitePolymerFamily Block → ℝ) :
    FinitePolymer Block → ℝ :=
  fun X => ∑ family, if polymerFamilyUnion family = X then contribution family else 0

/-- Weighted `ℓ¹` norm on output polymer activities. -/
def polymerActivityMajorant
    (weight : FinitePolymer Block → ℝ)
    (activity : FinitePolymer Block → ℝ) : ℝ :=
  ∑ X, |activity X| * weight X

/-- Weighted source majorant on cumulant families, using the weight of the
union to which each family will be recombined. -/
def polymerFamilyMajorant
    (weight : FinitePolymer Block → ℝ)
    (contribution : FinitePolymerFamily Block → ℝ) : ℝ :=
  ∑ family, |contribution family| * weight (polymerFamilyUnion family)

/-- **Exact recombination theorem.**  Regrouping connected-family
contributions by union support has weighted `ℓ¹` operator norm at most one.
All nontrivial combinatorics therefore belong in the preceding map that
produces family contributions from input activities. -/
theorem polymerActivityMajorant_recombineByUnion_le
    (weight : FinitePolymer Block → ℝ)
    (hweight : ∀ X, 0 ≤ weight X)
    (contribution : FinitePolymerFamily Block → ℝ) :
    polymerActivityMajorant weight (recombineByUnion contribution) ≤
      polymerFamilyMajorant weight contribution := by
  classical
  unfold polymerActivityMajorant recombineByUnion polymerFamilyMajorant
  calc
    ∑ X, |∑ family,
        if polymerFamilyUnion family = X then contribution family else 0| * weight X
      ≤ ∑ X, (∑ family,
          |if polymerFamilyUnion family = X then contribution family else 0|) * weight X := by
        exact Finset.sum_le_sum fun X _ =>
          mul_le_mul_of_nonneg_right
            (Finset.abs_sum_le_sum_abs _ _) (hweight X)
    _ = ∑ X, ∑ family,
          |if polymerFamilyUnion family = X then contribution family else 0| * weight X := by
        apply Finset.sum_congr rfl
        intro X _
        rw [Finset.sum_mul]
    _ = ∑ family, ∑ X,
          |if polymerFamilyUnion family = X then contribution family else 0| * weight X := by
        rw [Finset.sum_comm]
    _ = ∑ family,
          |contribution family| * weight (polymerFamilyUnion family) := by
        apply Finset.sum_congr rfl
        intro family _
        rw [Finset.sum_eq_single (polymerFamilyUnion family)]
        · simp
        · intro X _ hX
          simp [Ne.symm hX]
        · simp

/-! ## Literal contact-count refutation for the advertised factor fourteen -/

/-- Vertices of a `2 × 16` nearest-neighbor lattice strip.  It embeds in the
four-dimensional cubic lattice by setting the other two coordinates to zero. -/
abbrev ContactStripVertex := Fin 2 × Fin 16

/-- Nearest-neighbor relation on the finite strip, without periodic wraparound. -/
def contactStripAdjacent (u v : ContactStripVertex) : Prop :=
  (u.1 = v.1 ∧
      (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
    (u.2 = v.2 ∧ u.1 ≠ v.1)

instance contactStripAdjacentDecidable (u v : ContactStripVertex) :
    Decidable (contactStripAdjacent u v) := by
  unfold contactStripAdjacent
  infer_instance

/-- The left connected rail. -/
def contactStripLeft : Finset ContactStripVertex :=
  Finset.univ.filter fun v => v.1 = 0

/-- The right connected rail. -/
def contactStripRight : Finset ContactStripVertex :=
  Finset.univ.filter fun v => v.1 = 1

/-- Number of nearest-neighbor contacts from polymer `X` to polymer `Y`. -/
def polymerContactCount
    (X Y : Finset ContactStripVertex) : ℕ :=
  ∑ u ∈ X, ∑ v ∈ Y, if contactStripAdjacent u v then 1 else 0

/-- The two rails have one cross-contact at each of their sixteen sites. -/
theorem contactStrip_rails_have_sixteen_contacts :
    polymerContactCount contactStripLeft contactStripRight = 16 := by
  decide

/-- **Literal factor-14 obstruction.**  Two nearest-neighbor polymers can have
more than fourteen distinct connecting contacts, already in a finite lattice
strip embedded in four dimensions. -/
theorem fourteen_lt_contactStrip_rail_contacts :
    14 < polymerContactCount contactStripLeft contactStripRight := by
  decide

/-! ## The natural rooted meaning of `2(2d-1)` -/

/-- An oriented coordinate direction in four dimensions. -/
abbrev OrientedDirection4 := Fin 4 × Bool

/-- Reverse the orientation while preserving the coordinate axis. -/
def reverseOrientedDirection4 (direction : OrientedDirection4) :
    OrientedDirection4 :=
  (direction.1, !direction.2)

/-- After one marked oriented edge, a nonbacktracking next edge may use any of
the eight oriented lattice directions except the reverse edge. -/
def nonbacktrackingDirectionChoices
    (previous : OrientedDirection4) : Finset OrientedDirection4 :=
  Finset.univ.erase (reverseOrientedDirection4 previous)

theorem nonbacktrackingDirectionChoices_card
    (previous : OrientedDirection4) :
    (nonbacktrackingDirectionChoices previous).card = 7 := by
  classical
  simp [nonbacktrackingDirectionChoices]

/-- The leading Boolean records which of two marked polymers supplies the
rooted endpoint; the second coordinate is its nonbacktracking direction. -/
def rootedTwoPolymerConnectionChoices
    (previous : OrientedDirection4) :
    Finset (Bool × OrientedDirection4) :=
  Finset.univ.product (nonbacktrackingDirectionChoices previous)

/-- **Natural factor-fourteen theorem.**  At one rooted marked edge in four
dimensions there are exactly `2 * (2*4-1) = 14` endpoint/direction choices.
This local branching number is not a uniform bound on the total contacts of
two extended polymers. -/
theorem rootedTwoPolymerConnectionChoices_card
    (previous : OrientedDirection4) :
    (rootedTwoPolymerConnectionChoices previous).card = 14 := by
  classical
  simp [rootedTwoPolymerConnectionChoices,
    nonbacktrackingDirectionChoices_card]

end YangMills
end QuantumTheory
end Mettapedia
