import Mettapedia.OSLF.NativeTypes.Structural.Semantics
import Mettapedia.OSLF.NativeTypes.Structural.SpatialLaws

open Mettapedia.OSLF.Framework

/-!
# Rho spatial formers through the generated structural language

The actual parallel declaration has one hash-bag parameter, rather than two
ordinary parameters. The computed spatial former exposes its separating
interpretation, and its declared algebra earns the commutative and associative
laws under every ambient binding context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

private def rhoParallelFormer : Former := ⟨3, rhoCalc.terms[3]'(by decide)⟩
private def rhoParallelShape : SpatialShape :=
  ⟨"ps", { flatten := true, unit := some "PZero" }⟩
private def noAtoms : Nat → Option TypeExpr := fun _ => none

private theorem rhoParallel_member : rhoParallelFormer ∈ structuralFormers rhoCalc := by
  apply (mem_structuralFormers_iff _ _).mpr
  rfl

/-- The spatial admission is calculated from the real authored declaration,
including the authored unit, rather than entered as a predicate. -/
theorem rho_spatial_shape_computed :
    spatialShape? rhoCalc rhoParallelFormer.declaration = some rhoParallelShape := by
  decide

theorem rho_spatial_elaborates :
    ∃ judgment, elaborate rhoCalc noAtoms finiteLimitFragment (.base "Proc")
      (.spatial 3 .top .top) = .ok judgment := by
  apply (elaborate_success_iff _ _ _ _ _).mpr
  apply (checkFormation_iff _ _ _ _ _).mp
  decide

/-- Applying ordinary positional splitting to the one-parameter bag grammar
is malformed; the generated spatial operation is its correct representation. -/
theorem rho_parallel_is_not_fake_binary :
    elaborate rhoCalc noAtoms finiteLimitFragment (.base "Proc") (.split 3 .top .top) =
      .error (.malformedJudgment (.base "Proc")) := by
  decide

/-- The two sides of a generated spatial judgment are actual typed process
values, joined by the underlying bare collection. -/
theorem rho_spatial_concrete_join (base : BasePremiseEvaluator) (free : FreeTypeContext)
    (bound : List TypeExpr) :
    Holds rhoCalc free bound (fun _ => EquationEquiv base rhoCalc) (fun _ _ _ => False)
      (.base "Proc") (.spatial 3 .top .top)
      (.collection .hashBag [.apply "PZero" [], .apply "PZero" []] none) := by
  apply (holds_spatial_exact (declaration := rhoParallelFormer.declaration)
    (index := 3) (by rfl) .top .top _).mpr
  exact ⟨rhoParallel_member, rhoParallelShape, rho_spatial_shape_computed,
    .apply "PZero" [], .apply "PZero" [], rho_zero_hasSort free bound,
    rho_zero_hasSort free bound, (equationSetoid base rhoCalc).iseqv.refl _, trivial, trivial⟩

/-- Association and commutation hold for all typed decompositions, not only
for the concrete pair above. -/
theorem rho_spatial_separating_laws (base : BasePremiseEvaluator) (free : FreeTypeContext)
    (bound : List TypeExpr) (first second third : Pattern → Prop) (term : Pattern) :
    (SpatialHolds rhoCalc free bound (EquationEquiv base rhoCalc) rhoParallelFormer
        first second term ↔
      SpatialHolds rhoCalc free bound (EquationEquiv base rhoCalc) rhoParallelFormer
        second first term) ∧
    (SpatialHolds rhoCalc free bound (EquationEquiv base rhoCalc) rhoParallelFormer first
        (SpatialHolds rhoCalc free bound (EquationEquiv base rhoCalc) rhoParallelFormer second third) term ↔
      SpatialHolds rhoCalc free bound (EquationEquiv base rhoCalc) rhoParallelFormer
        (SpatialHolds rhoCalc free bound (EquationEquiv base rhoCalc) rhoParallelFormer first second) third term) := by
  exact ⟨authored_spatial_commutative base rhoParallelFormer first second term,
    authored_spatial_associative base rhoParallel_member rho_spatial_shape_computed first second third term⟩

end Mettapedia.OSLF.NativeTypes.Structural.Controls
