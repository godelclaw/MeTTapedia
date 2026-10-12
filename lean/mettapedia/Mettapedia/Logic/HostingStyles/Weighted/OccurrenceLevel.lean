import Mettapedia.Logic.HostingStyles.Catamorphisms
import Mettapedia.Logic.HostingStyles.ProofNodes

/-!
# Occurrences, between derivations and provability

`ProofCongruence.identity` keeps derivations apart. `ProofCongruence.total`
keeps only provability. Counting rule nodes sits between them: equal
derivations have equal size, equal size does not decide the derivation, and
provability does not decide the size.

`coarsen_hosting_iff` turns that order into hosting. Forgetting distinctions
is hosting only when the coarser congruence still makes them. Along both
strict steps of this order, it does not. The identity map is hosting at every
level. Size factors through the occurrence quotient and does not factor
through provability.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Logic.HostingStyles
open Mettapedia.Logic.HostingStyles.RuleSignature

inductive OccShape where
  | ax
  | bx
  | succ
  deriving DecidableEq

def occPremises : OccShape → Type
  | .ax => Empty
  | .bx => Empty
  | .succ => Unit

def occArity : OccShape → ℕ
  | .ax => 0
  | .bx => 0
  | .succ => 1

def finZero : Fin 0 ≃ Empty where
  toFun := Fin.elim0
  invFun := Empty.elim
  left_inv := fun index => index.elim0
  right_inv := fun empty => empty.elim

def finOne : Fin 1 ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => ⟨0, Nat.zero_lt_one⟩
  left_inv := fun index => by
    fin_cases index
    rfl
  right_inv := fun _ => rfl

def occIndex : (shape : OccShape) → Fin (occArity shape) ≃ occPremises shape
  | .ax => finZero
  | .bx => finZero
  | .succ => finOne

/-- One judgment, two axioms, and a unary successor. -/
def occSignature : RuleSignature Unit where
  Shape := fun _ _ => OccShape
  Position := fun shape => occPremises shape
  next := fun shape =>
    match shape with
    | .ax => fun position => position.elim
    | .bx => fun position => position.elim
    | .succ => fun _ => ()

def occFinitary : occSignature.Finitary where
  arity := fun shape => occArity shape
  position := fun shape => occIndex shape

def axProof : occSignature.Proof () :=
  occSignature.node .ax fun position => position.elim

def bxProof : occSignature.Proof () :=
  occSignature.node .bx fun position => position.elim

def succAx : occSignature.Proof () :=
  occSignature.node .succ fun _ => axProof

theorem ax_ne_bx : axProof ≠ bxProof :=
  occSignature.node_ne_of_shape_ne (by decide : OccShape.ax ≠ OccShape.bx) _ _

theorem positions_ax :
    occFinitary.positions (j := ()) OccShape.ax = ([] : List (occPremises OccShape.ax)) := by
  simp [Finitary.positions, occFinitary, occArity, occIndex, finZero, List.ofFn_zero]
  rfl

theorem positions_bx :
    occFinitary.positions (j := ()) OccShape.bx = ([] : List (occPremises OccShape.bx)) := by
  simp [Finitary.positions, occFinitary, occArity, occIndex, finZero, List.ofFn_zero]
  rfl

theorem positions_succ :
    occFinitary.positions (j := ()) OccShape.succ = ([()] : List (occPremises OccShape.succ)) := by
  simp [Finitary.positions, occFinitary, occArity, occIndex, finOne, List.ofFn_succ, List.ofFn_zero]
  rfl

theorem size_ax : size occFinitary axProof = 1 := by
  have expanded :=
    size_node (j := ()) occFinitary OccShape.ax
      (fun position : occPremises OccShape.ax => position.elim)
  have same : axProof =
      occSignature.node OccShape.ax (fun position : occPremises OccShape.ax => position.elim) := rfl
  rw [same, expanded, positions_ax]
  rfl

theorem size_bx : size occFinitary bxProof = 1 := by
  have expanded :=
    size_node (j := ()) occFinitary OccShape.bx
      (fun position : occPremises OccShape.bx => position.elim)
  have same : bxProof =
      occSignature.node OccShape.bx (fun position : occPremises OccShape.bx => position.elim) := rfl
  rw [same, expanded, positions_bx]
  rfl

theorem size_succAx : size occFinitary succAx = 2 := by
  have expanded :=
    size_node (j := ()) occFinitary OccShape.succ
      (fun _ : occPremises OccShape.succ => axProof)
  have same : succAx =
      occSignature.node OccShape.succ (fun _ : occPremises OccShape.succ => axProof) := rfl
  rw [same, expanded, positions_succ]
  change 1 + size occFinitary axProof = 2
  rw [size_ax]

/-- **Occurrences counted**: two derivations are congruent when they have the
same number of rule nodes. -/
noncomputable def occurrences : occSignature.ProofCongruence where
  setoid := fun _ => {
    r := fun first second => size occFinitary first = size occFinitary second
    iseqv := ⟨fun _ => rfl, fun related => related.symm, fun left right => left.trans right⟩
  }
  node := fun shape first second related => by
    show size occFinitary (occSignature.node shape first) =
      size occFinitary (occSignature.node shape second)
    have leftSize := size_node occFinitary shape first
    have rightSize := size_node occFinitary shape second
    rw [leftSize, rightSize]
    refine congrArg (fun count => 1 + count) ?_
    refine congrArg List.sum ?_
    refine congrArg (fun sizes => List.map sizes (occFinitary.positions shape)) ?_
    funext position
    exact related position

/-- **Positive.** The two axioms have one node each, so occurrences identify them. -/
theorem occurrences_identify_axioms :
    (occurrences.setoid ()).r axProof bxProof := by
  show size occFinitary axProof = size occFinitary bxProof
  rw [size_ax, size_bx]

/-- **Negative.** A successor has two nodes, so occurrences keep it apart from an axiom. -/
theorem occurrences_separate_sizes :
    ¬ (occurrences.setoid ()).r axProof succAx := by
  intro related
  have relatedSizes : size occFinitary axProof = size occFinitary succAx := related
  rw [size_ax, size_succAx] at relatedSizes
  exact absurd relatedSizes (by decide)

theorem occurrences_refines_total :
    occurrences.Refines (ProofCongruence.total occSignature) :=
  fun _ => trivial

/-- The three congruences, in the existing refinement order. -/
theorem occurrence_order :
    (ProofCongruence.identity occSignature).Refines occurrences ∧
      occurrences.Refines (ProofCongruence.total occSignature) ∧
      (ProofCongruence.identity occSignature).Refines (ProofCongruence.total occSignature) :=
  ⟨ProofCongruence.identity_refines occurrences, occurrences_refines_total,
    ProofCongruence.refines_total (ProofCongruence.identity occSignature)⟩

theorem occurrences_not_refines_identity :
    ¬ occurrences.Refines (ProofCongruence.identity occSignature) := by
  intro refines
  exact ax_ne_bx (refines occurrences_identify_axioms)

theorem total_not_refines_occurrences :
    ¬ (ProofCongruence.total occSignature).Refines occurrences := by
  intro refines
  exact occurrences_separate_sizes (refines trivial)

/-- The identity map is hosting at each of the three levels. -/
theorem each_level_hosts_itself :
    (ContextMap.id (occSignature.proofTheory (ProofCongruence.identity occSignature))).Hosting ∧
      (ContextMap.id (occSignature.proofTheory occurrences)).Hosting ∧
      (ContextMap.id (occSignature.proofTheory (ProofCongruence.total occSignature))).Hosting :=
  ⟨ContextMap.hosting_id _, ContextMap.hosting_id _, ContextMap.hosting_id _⟩

/-- Forgetting derivations down to occurrence classes identifies the two axioms,
so it is not hosting. It is still exhausting. -/
theorem occurrence_coarsening_exhaustive_not_hosting :
    (occSignature.coarsen (ProofCongruence.identity_refines occurrences)).Exhausting ∧
      ¬ (occSignature.coarsen (ProofCongruence.identity_refines occurrences)).Hosting :=
  ⟨occSignature.coarsen_exhausting _,
    ContextMap.not_hosting_of_identifies
      (occSignature.coarsen (ProofCongruence.identity_refines occurrences))
      ax_ne_bx occurrences_identify_axioms⟩

/-- Forgetting occurrence counts down to provability is not hosting. -/
theorem provability_coarsening_not_hosting :
    ¬ (occSignature.coarsen occurrences_refines_total).Hosting := by
  rw [occSignature.coarsen_hosting_iff]
  exact total_not_refines_occurrences

/-- Hosting the map that forgets all the way to provability would force hosting
of the map that forgets only as far as occurrences. Refinement alone does not
give that hosting: identity refines occurrences, and the coarsening is still
not hosting. -/
theorem hosted_provability_forgetting_implies_occurrence_forgetting :
    (occSignature.coarsen
        (ProofCongruence.refines_total (ProofCongruence.identity occSignature))).Hosting →
      (occSignature.coarsen (ProofCongruence.identity_refines occurrences)).Hosting := by
  intro hosted
  rw [occSignature.coarsen_hosting_iff] at hosted ⊢
  intro _ first second _
  exact hosted trivial

theorem refinement_does_not_give_hosting :
    (ProofCongruence.identity occSignature).Refines occurrences ∧
      ¬ (occSignature.coarsen (ProofCongruence.identity_refines occurrences)).Hosting :=
  ⟨ProofCongruence.identity_refines occurrences,
    (occurrence_coarsening_exhaustive_not_hosting).2⟩

/-- The occurrence quotient determines the number of rule nodes. -/
noncomputable def sizeAlgebra : occSignature.Algebra (fun _ _ => Nat) where
  act := fun _ _ layer => 1 + ((occFinitary.positions layer.1).map layer.2).sum

theorem size_eq_fold (proof : occSignature.Proof ()) :
    size occFinitary proof =
      Fix.fold occSignature sizeAlgebra.act PUnit.unit () proof := by
  rfl

/-- **Positive.** Size factors through occurrences. -/
theorem size_factors_occurrences :
    Factors (fun proof : occSignature.Proof () => Quotient.mk (occurrences.setoid ()) proof)
      (Fix.fold occSignature sizeAlgebra.act PUnit.unit ()) :=
  (occSignature.fold_factors_quotient_iff occurrences sizeAlgebra ()).mpr
    fun first second related => by
      change size occFinitary first = size occFinitary second
      exact related

/-- **Negative.** Size does not factor through provability. -/
theorem size_not_factors_provability :
    ¬ Factors (fun proof : occSignature.Proof () =>
        Quotient.mk ((ProofCongruence.total occSignature).setoid ()) proof)
      (fun proof => size occFinitary proof) :=
  NonTrivialFiber.not_factors
    { left := axProof
      right := succAx
      sameShadow := Quotient.sound trivial
      differentValue := by
        rw [size_ax, size_succAx]
        decide }

end Mettapedia.Logic.HostingStyles.Weighted
