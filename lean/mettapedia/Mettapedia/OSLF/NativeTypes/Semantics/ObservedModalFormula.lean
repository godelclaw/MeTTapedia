import Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
import Mettapedia.Logic.ModalMuCalculusBuchi

/-!
# Native types for observed modal fixed-point formulas

The existing modal μ-calculus is interpreted on the actual represented
material states and pulled back through the existing native-predicate
construction. Covered traversals identify its meaning with source action
semantics; when those actions present the full GSLT step relation, the same
type has the authored GSLT meaning.

Future-only Büchi formulas require outgoing coverage, supplied by faithful
material readings. Incoming modalities retain their independent coverage
obligation. These semantic comparisons impose no finiteness assumption and
do not supply a finite enumeration or an executable table for the material
carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.ObservedModalFormula

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ObservedMaterialization
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Bridges.TypeTheory.ObservedNativeTypes
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open ModalFormula

universe u
variable {S : GSLT.{u}} {M : System.{u, u} S}

section AuthoredSteps

variable (occurrences : ActionOccurrences M)

/-- The action occurrence supplies the witness of its authored GSLT step.
This map preserves states and forgets only the additional action witness. -/
def actionToGSLT (complete : ActionsPresentSteps (M := M)) :
    SpanMap occurrences.sourceSpan (gsltSpan S) where
  states := id
  events event := ⟨event.source, event.target,
    (actionSpan_step_iff occurrences complete _ _).mp ⟨event, rfl, rfl⟩⟩
  source_comm _ := rfl
  target_comm _ := rfl

theorem actionToGSLT_sourceLifts (complete : ActionsPresentSteps (M := M)) :
    (actionToGSLT occurrences complete).SourceLifts := by
  intro source event starts
  obtain ⟨lifted, first, second⟩ :=
    (actionSpan_step_iff occurrences complete source ((gsltSpan S).target event)).mpr
      ((gsltSpan_edge_iff_step S _ _).mp ⟨event, starts, rfl⟩)
  exact ⟨lifted, first, second⟩

theorem actionToGSLT_targetLifts (complete : ActionsPresentSteps (M := M)) :
    (actionToGSLT occurrences complete).TargetLifts := by
  intro target event ends
  obtain ⟨lifted, first, second⟩ :=
    (actionSpan_step_iff occurrences complete ((gsltSpan S).source event) target).mpr
      ((gsltSpan_edge_iff_step S _ _).mp ⟨event, rfl, ends⟩)
  exact ⟨lifted, second, first⟩

theorem actionToGSLT_covers (complete : ActionsPresentSteps (M := M))
    {n : Nat} (formula : Formula Traversal n) :
    CoversFormula (actionToGSLT occurrences complete) formula := by
  induction formula with
  | tt | ff | var _ => trivial
  | neg _ ih | mu _ ih | nu _ ih => exact ih
  | conj _ _ il ir | disj _ _ il ir => exact ⟨il, ir⟩
  | diamond direction _ ih | box direction _ ih =>
      refine ⟨?_, ih⟩
      cases direction with
      | future => exact actionToGSLT_sourceLifts occurrences complete
      | past => exact actionToGSLT_targetLifts occurrences complete

/-- Independently authored action events and GSLT steps agree on all admitted
modal fixed-point formulas, including past traversals. -/
theorem action_formula_iff_gslt (complete : ActionsPresentSteps (M := M))
    {n : Nat} (formula : Formula Traversal n)
    (positive : fixedPointsPositive formula = true)
    (environment : Env S.Term n) (source : S.Term) :
    satisfies (transitionSystem occurrences.sourceSpan) environment formula source ↔
      satisfies (transitionSystem (gsltSpan S)) environment formula source := by
  have environmentEq : pullEnvironment id environment = environment := rfl
  simpa only [actionToGSLT, id_eq, environmentEq] using
    (satisfies_pullback (actionToGSLT occurrences complete) formula
      (actionToGSLT_covers occurrences complete formula) positive environment source).symm

end AuthoredSteps

variable (readings : LabelReadings M) (occurrences : ActionOccurrences M)

/-- An actual generated native type whose predicate is the existing material
formula interpretation pulled back along the readout. -/
def formulaType {n : Nat} (formula : Formula Traversal n)
    (environment : Env (MaterialState readings) n) : GSLTNativeType S where
  sort := ()
  pred := pullNative readings
    (sat (transitionSystem (ObservedFamilyEnclosure.Events.memberSpan readings occurrences))
      environment formula)

theorem formulaType_invariant {n : Nat} (formula : Formula Traversal n)
    (environment : Env (MaterialState readings) n) :
    BehaviourInvariant (M := M) (formulaType readings occurrences formula environment).pred :=
  pullNative_invariant readings _

/-- The native predicate has exactly the actual material formula as its
image, rather than a new semantic carrier. -/
theorem formulaType_image (faithful : readings.Faithful)
    {n : Nat} (formula : Formula Traversal n)
    (environment : Env (MaterialState readings) n) (member : MaterialState readings) :
    nativeImage readings (formulaType readings occurrences formula environment).pred member ↔
      satisfies (transitionSystem (ObservedFamilyEnclosure.Events.memberSpan readings occurrences))
        environment formula member := by
  obtain ⟨source, rfl⟩ := materialState_covered readings member
  exact nativeImage_beta readings faithful _
    (formulaType_invariant readings occurrences formula environment) source

/-- Covered traversals give source action semantics to the generated native
type. Atoms are the supplied predicates on represented material states. -/
theorem formulaType_actions {n : Nat} (formula : Formula Traversal n)
    (coverage : CoversFormula (ObservedFamilyEnclosure.Events.observation readings occurrences)
      formula) (positive : fixedPointsPositive formula = true)
    (environment : Env (MaterialState readings) n) (source : S.Term) :
    (gsltOSLF S).satisfies (S := ()) source
        (formulaType readings occurrences formula environment).pred ↔
      satisfies (transitionSystem occurrences.sourceSpan)
        (pullEnvironment (ObservedFamilyEnclosure.valueMember readings) environment)
        formula source :=
  satisfies_pullback (ObservedFamilyEnclosure.Events.observation readings occurrences)
    formula coverage positive environment source

/-- If labelled actions present all authored steps, the same native type
has the full source GSLT formula meaning. -/
theorem formulaType_source (complete : ActionsPresentSteps (M := M))
    {n : Nat} (formula : Formula Traversal n)
    (coverage : CoversFormula (ObservedFamilyEnclosure.Events.observation readings occurrences)
      formula) (positive : fixedPointsPositive formula = true)
    (environment : Env (MaterialState readings) n) (source : S.Term) :
    (gsltOSLF S).satisfies (S := ()) source
        (formulaType readings occurrences formula environment).pred ↔
      satisfies (transitionSystem (gsltSpan S))
        (pullEnvironment (ObservedFamilyEnclosure.valueMember readings) environment)
        formula source :=
  (formulaType_actions readings occurrences formula coverage positive environment source).trans
    (action_formula_iff_gslt occurrences complete formula positive _ source)

/-- Büchi's outgoing traversals need no predecessor-coverage premise. -/
theorem buchi_covered (faithful : readings.Faithful) :
    CoversFormula (ObservedFamilyEnclosure.Events.observation readings occurrences)
      (Formula.buchi .future) := by
  have outgoing := ObservedFamilyEnclosure.Events.sourceLifts readings faithful occurrences
  simpa only [Formula.buchi, CoversFormula, CoversDirection, true_and, and_true] using
    And.intro outgoing outgoing

/-- Native Büchi recurrence is interpreted over all authored source steps.
No finite source or material carrier is assumed by this comparison. -/
theorem buchiType_source (faithful : readings.Faithful)
    (complete : ActionsPresentSteps (M := M)) (accepting : Set (MaterialState readings))
    (source : S.Term) :
    (gsltOSLF S).satisfies (S := ()) source
        (formulaType readings occurrences (Formula.buchi .future) (fun _ => accepting)).pred ↔
      satisfies (transitionSystem (gsltSpan S))
        (fun _ => ObservedFamilyEnclosure.valueMember readings ⁻¹' accepting)
        (Formula.buchi .future) source :=
  formulaType_source readings occurrences complete _ (buchi_covered readings occurrences faithful)
    (Formula.buchi_positive Traversal.future) (fun _ => accepting) source

end Mettapedia.OSLF.NativeTypes.Semantics.ObservedModalFormula
