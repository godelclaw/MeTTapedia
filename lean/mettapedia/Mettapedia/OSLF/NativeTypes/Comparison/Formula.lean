import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.NativeTypes.Semantics.Operational

open Mettapedia.OSLF.Framework

/-!
# The existing finite formula syntax in the generated native semantics

Generated native predicates can be the atoms of the existing formula
language. The complete formula denotes an equation-invariant predicate of
the same scoped GSLT, including its incoming adjoint box and its frame-relative
scope generator. This is a semantic comparison; it does not enable syntax
outside a selected generator fragment.

The existing predecessor-aware checker transports its soundness theorem
through this comparison. Its predecessor completeness premise is explicit;
it is not inferred from a partial outgoing frontier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Comparison.Formula

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.Formula
open OSLFFormula
open GSLTTypeSynthesis Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Semantics.Operational (theory)

def predicate (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (atoms : String → EquationPredicate (theory generated bound carrier)) (formula : OSLFFormula) :
    EquationPredicate (theory generated bound carrier) where
  val := semEnv (theory generated bound carrier).Step
    (setoidFrame (theory generated bound carrier).equations) (fun atom => atoms atom) ScopeEnv.empty formula
  property := semEnv_setoidInvariant _ _ (theory generated bound carrier).rewrites_resp_left
    (theory generated bound carrier).rewrites_resp_right (fun atom => atoms atom)
    (fun atom => (atoms atom).property) formula ScopeEnv.empty (fun _ _ _ _ => Iff.rfl)

def nativeType (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (atoms : String → EquationPredicate (theory generated bound carrier)) (formula : OSLFFormula) :
    GSLTNativeType (theory generated bound carrier) :=
  ⟨(), predicate generated bound carrier atoms formula⟩

theorem formula_native_exact (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (atoms : String → EquationPredicate (theory generated bound carrier)) (formula : OSLFFormula)
    (term : Pattern) :
    (gsltOSLF (theory generated bound carrier)).satisfies (S := ()) term
        (nativeType generated bound carrier atoms formula).pred ↔
      semEnv (theory generated bound carrier).Step
        (setoidFrame (theory generated bound carrier).equations) (fun atom => atoms atom)
        ScopeEnv.empty formula term := Iff.rfl

theorem native_diamond_comparison (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (atoms : String → EquationPredicate (theory generated bound carrier)) (body : OSLFFormula)
    (term : Pattern) :
    predicate generated bound carrier atoms (.dia body) term ↔
      semanticDiamond (theory generated bound carrier) (predicate generated bound carrier atoms body) term := by
  change (∃ target, (theory generated bound carrier).Step term target ∧
    predicate generated bound carrier atoms body target) ↔ _
  exact (gsltDiamond_spec (theory generated bound carrier) (predicate generated bound carrier atoms body) term).symm

theorem native_incoming_box_comparison (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (atoms : String → EquationPredicate (theory generated bound carrier)) (body : OSLFFormula)
    (term : Pattern) :
    predicate generated bound carrier atoms (.box body) term ↔
      semanticBox (theory generated bound carrier) (predicate generated bound carrier atoms body) term := by
  change (∀ source, (theory generated bound carrier).Step source term →
    predicate generated bound carrier atoms body source) ↔ _
  exact (gsltBox_spec (theory generated bound carrier) (predicate generated bound carrier atoms body) term).symm

theorem formula_native_adjunction (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (atoms : String → EquationPredicate (theory generated bound carrier))
    (first second : OSLFFormula) :
    semanticDiamond (theory generated bound carrier) (predicate generated bound carrier atoms first) ≤
        predicate generated bound carrier atoms second ↔
      predicate generated bound carrier atoms first ≤
        semanticBox (theory generated bound carrier) (predicate generated bound carrier atoms second) :=
  semanticGalois _ _ _

theorem equation_invariant_frame_closed (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (atoms : String → EquationPredicate (theory generated bound carrier)) :
    FrameClosed (theory generated bound carrier).Step
      (setoidFrame (theory generated bound carrier).equations) (fun atom => atoms atom) := by
  intro environment formula invariant
  exact semEnv_setoidInvariant _ _ (theory generated bound carrier).rewrites_resp_left
    (theory generated bound carrier).rewrites_resp_right (fun atom => atoms atom)
    (fun atom => (atoms atom).property) formula environment invariant

/-- The predecessor-aware checker already supports a positive incoming box
when its supplied predecessor list really covers the incoming relation. -/
theorem predecessor_checker_native_sound {generated : Generated} {bound : List TypeExpr} {carrier : TypeExpr}
    (atoms : String → EquationPredicate (theory generated bound carrier))
    {step predecessor : Pattern → List Pattern} {checkAtom : AtomCheck}
    (atomsSound : ∀ atom term, checkAtom atom term = true → atoms atom term)
    (stepSound : ∀ source target, target ∈ step source → (theory generated bound carrier).Step source target)
    (predecessorComplete : ∀ source target, (theory generated bound carrier).Step source target →
      source ∈ predecessor target)
    {fuel : Nat} {term : Pattern} {formula : OSLFFormula}
    (accepted : checkWithPred step predecessor checkAtom fuel term formula = .sat) :
    (gsltOSLF (theory generated bound carrier)).satisfies (S := ()) term
      (nativeType generated bound carrier atoms formula).pred :=
  checkWithPred_semEnv_sat_sound (equation_invariant_frame_closed generated bound carrier atoms)
    (fun _ _ _ _ => Iff.rfl) atomsSound stepSound (fun target source => predecessorComplete source target) accepted

end Mettapedia.OSLF.NativeTypes.Comparison.Formula
