import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeFixedPointComparison
import Mettapedia.OSLF.NativeTypes.Generation.NativeEquality

/-!
# Exact diagonal meaning of generated Leibniz equality

The common formula quantifies actual native predicate functions. Its forward
direction uses restriction of the two supplied sections. Its converse names
the genuine singleton predicate in the same full predicate family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeEqualityComparison

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers NativeLocalTypeOperations PredicateVariables PredicateNaming
open FixedPointEvaluation PresheafNativePropositionReadout DisplayedPresheafComprehension

universe u v
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}
variable {S : Symbols.{v}} {n : Nat}

def diagonal (A : NativeType P) (first second : A.decoded.sections) : Subfunctor P where
  obj world := {parameter | first.val ⟨world, parameter⟩ = second.val ⟨world, parameter⟩}
  map := by
    intro world future arrow parameter held
    let lifted := CategoryOfElements.homMk (F := P) ⟨world, parameter⟩
      ⟨future, P.map arrow parameter⟩ arrow rfl
    exact (first.property lifted).symm.trans
      ((congrArg (A.decoded.map lifted) held).trans (second.property lifted))

def singleton (A : NativeType P) (value : A.decoded.sections) :
    Subfunctor (totalSpace A.decoded) where
  obj world := {parameter | parameter.2 = value.val ⟨world, parameter.1⟩}
  map := by
    intro world future arrow parameter held
    let lifted := CategoryOfElements.homMk (F := P) ⟨world, parameter.1⟩
      ⟨future, P.map arrow parameter.1⟩ arrow rfl
    exact (congrArg (A.decoded.map lifted) held).trans (value.property lifted)

noncomputable def leibniz (A : NativeType P) (first second : A.decoded.sections) :
    Subfunctor P :=
  forallAlong (totalProjection (predicate A).decoded)
    (testedMembership A first ⇨ testedMembership A second)

theorem application_same_at (A : NativeType P) (function : (predicate A).decoded.sections)
    (first second : A.decoded.sections) (world : Cᵒᵖ) (parameter : P.obj world)
    (same : first.val ⟨world, parameter⟩ = second.val ⟨world, parameter⟩) :
    parameter ∈ (nativeHolds (FixedPointSyntax.applicationValue A function first)).obj world ↔
      parameter ∈ (nativeHolds (FixedPointSyntax.applicationValue A function second)).obj world := by
  rw [FixedPointSyntax.applicationValue_holds, FixedPointSyntax.applicationValue_holds]
  let meaning := nativeHolds ((functionEquiv A (nativeOmega (totalSpace A.decoded))).symm function)
  change (⟨parameter, first.val ⟨world, parameter⟩⟩ : (totalSpace A.decoded).obj world) ∈ meaning.obj world ↔
    (⟨parameter, second.val ⟨world, parameter⟩⟩ : (totalSpace A.decoded).obj world) ∈ meaning.obj world
  rw [same]

theorem tested_same_at (A : NativeType P) (first second : A.decoded.sections)
    (world : Cᵒᵖ) (parameter : (totalSpace (predicate A).decoded).obj world)
    (same : first.val ⟨world, parameter.1⟩ = second.val ⟨world, parameter.1⟩) :
    parameter ∈ (testedMembership A first).obj world ↔
      parameter ∈ (testedMembership A second).obj world := by
  apply application_same_at
  have before := substituteTerm_value A first (totalProjection (predicate A).decoded)
    (show (totalSpace (predicate A).decoded).Elements from ⟨world, parameter⟩)
  have after := substituteTerm_value A second (totalProjection (predicate A).decoded)
    (show (totalSpace (predicate A).decoded).Elements from ⟨world, parameter⟩)
  exact eq_of_heq (before.trans ((heq_of_eq same).trans after.symm))

theorem diagonal_le_leibniz (A : NativeType P) (first second : A.decoded.sections) :
    diagonal A first second ≤ leibniz A first second := by
  intro world parameter held future restriction function over
  rw [← himpPointwise_eq_himp]
  intro target arrow accepted
  have restricted := (diagonal A first second).map (restriction ≫ arrow) held
  have sameBase : ((totalSpace (predicate A).decoded).map arrow function).1 =
      P.map (restriction ≫ arrow) parameter := by
    change P.map arrow function.1 = _
    change function.1 = P.map restriction parameter at over
    rw [over, P.map_comp_apply]
  apply (tested_same_at A first second target
    ((totalSpace (predicate A).decoded).map arrow function) ?_).mp accepted
  rw [sameBase]
  exact restricted

theorem singleton_self (A : NativeType P) (first : A.decoded.sections) :
    (singleton A first).preimage (sectionLift A.decoded first) = ⊤ := by
  ext world parameter
  change first.val ⟨world, parameter⟩ = first.val ⟨world, parameter⟩ ↔ True
  simp

theorem singleton_other (A : NativeType P) (first second : A.decoded.sections) :
    (singleton A first).preimage (sectionLift A.decoded second) = diagonal A first second := by
  ext world parameter
  exact eq_comm

theorem leibniz_le_diagonal (A : NativeType P) (first second : A.decoded.sections) :
    leibniz A first second ≤ diagonal A first second := by
  let naming := sectionLift (predicate A).decoded
    (NativeLocalTypeOperations.lam (nativeQuote (singleton A first)))
  have before : (testedMembership A first).preimage naming = ⊤ :=
    (tested_reified A first (singleton A first)).trans (singleton_self A first)
  have after : (testedMembership A second).preimage naming = diagonal A first second :=
    (tested_reified A second (singleton A first)).trans (singleton_other A first second)
  have deduction := (galois_preimage_forallAlong (totalProjection (predicate A).decoded)).l_u_le
    (testedMembership A first ⇨ testedMembership A second)
  intro world parameter held
  have result : parameter ∈ ((testedMembership A first ⇨ testedMembership A second).preimage
      naming).obj world := deduction world (show naming.app world parameter ∈
        ((leibniz A first second).preimage (totalProjection (predicate A).decoded)).obj world from held)
  rw [preimage_himp, before, after, top_himp] at result
  exact result

/-- The generated quantified predicate is exactly equality of the actual
dependent section values; there is no independent graph oracle. -/
theorem leibniz_eq_diagonal (A : NativeType P) (first second : A.decoded.sections) :
    leibniz A first second = diagonal A first second :=
  le_antisymm (leibniz_le_diagonal A first second) (diagonal_le_leibniz A first second)

/-- Actual common-grammar evaluation computes the independent diagonal. -/
theorem evaluate_equal (model : ModelData S C) (context : Scope C n)
    (carrier : TypeExpr S n) (first second : TermExpr S n) (A : NativeType context.1)
    (left right : A.decoded.sections)
    (carrierRead : model.evaluateType context carrier = some A)
    (leftRead : model.evaluateTerm context first = some ⟨A, left⟩)
    (rightRead : model.evaluateTerm context second = some ⟨A, right⟩) :
    model.evaluatePredicate context (Generation.NativeEquality.equal carrier first second) =
      some (diagonal A left right) := by
  have implication := model.evaluate_implies _ _ _ _ _
    (evaluate_application_under_predicate model context carrier first A left carrierRead leftRead)
    (evaluate_application_under_predicate model context carrier second A right carrierRead rightRead)
  rw [himpPointwise_eq_himp] at implication
  have result := model.evaluate_all _ _ _ _ _
    (FixedPointSyntax.evaluate_predicateType model context carrier A carrierRead) implication
  exact result.trans (congrArg some (leibniz_eq_diagonal A left right))

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeEqualityComparison
