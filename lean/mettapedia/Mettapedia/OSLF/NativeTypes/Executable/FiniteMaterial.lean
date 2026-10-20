import Mettapedia.OSLF.NativeTypes.Executable.Finite
import Mettapedia.OSLF.NativeTypes.Semantics.ObservedModalFormula
import Mettapedia.OSLF.NativeTypes.Semantics.BuchiTransport

/-!
# Finite execution of actual observed native types

The existing public finite checker is exact for the native type generated
from a material formula. Its caller supplies a finite enumeration of the
actual material carrier and a table exact for all its retained events.
Covered traversals and an exact action presentation further identify the
verdict with the authored GSLT formula meaning.

These are conditional qualification theorems, not a construction of a
finite material quotient for an arbitrary source language. The source
carrier itself need not be finite. Occurrence receipts remain distinct from
the predicate truth computed by the Boolean transition table.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.FiniteMaterial

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ObservedMaterialization
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Bridges.TypeTheory.ObservedNativeTypes
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.ObservedModalFormula
open Reference.Core (Outcome)

universe u
variable {S : GSLT.{u}} {M : System.{u, u} S}
variable (readings : LabelReadings M) (occurrences : ActionOccurrences M)
variable [Fintype (MaterialState readings)] [DecidableEq (MaterialState readings)]
variable (table : FiniteGraph.Table
  (ObservedFamilyEnclosure.Events.memberSpan readings occurrences))

/-- A completed positive public verdict is exactly satisfaction of the
generated native type. The material enumeration and table are explicit. -/
theorem check_positive_iff_native {n : Nat} (formula : Formula Traversal n)
    (positive : fixedPointsPositive formula = true)
    (environment : FiniteMuCalculus.Environment (MaterialState readings) n)
    (budget : Nat) (source : S.Term)
    (enough : FiniteMuCalculus.requiredBudget (State := MaterialState readings) formula ≤ budget) :
    (Finite.check table formula environment budget
        (ObservedFamilyEnclosure.valueMember readings source)).map Outcome.answer =
          some (some true) ↔
      (gsltOSLF S).satisfies (S := ()) source
        (formulaType readings occurrences formula environment.meaning).pred :=
  Finite.check_positive_iff table formula positive environment budget _ enough

/-- A completed negative verdict refutes that same generated native type;
an exhausted allowance is not used as refutation evidence. -/
theorem check_negative_iff_native {n : Nat} (formula : Formula Traversal n)
    (positive : fixedPointsPositive formula = true)
    (environment : FiniteMuCalculus.Environment (MaterialState readings) n)
    (budget : Nat) (source : S.Term)
    (enough : FiniteMuCalculus.requiredBudget (State := MaterialState readings) formula ≤ budget) :
    (Finite.check table formula environment budget
        (ObservedFamilyEnclosure.valueMember readings source)).map Outcome.answer =
          some (some false) ↔
      ¬ (gsltOSLF S).satisfies (S := ()) source
        (formulaType readings occurrences formula environment.meaning).pred :=
  Finite.check_negative_iff table formula positive environment budget _ enough

/-- The finite checker answers the authored source formula when the retained
action relation and all traversals used by the formula are covered. -/
theorem check_positive_iff_source (complete : ActionsPresentSteps (M := M))
    {n : Nat} (formula : Formula Traversal n)
    (coverage : CoversFormula (ObservedFamilyEnclosure.Events.observation readings occurrences)
      formula) (positive : fixedPointsPositive formula = true)
    (environment : FiniteMuCalculus.Environment (MaterialState readings) n)
    (budget : Nat) (source : S.Term)
    (enough : FiniteMuCalculus.requiredBudget (State := MaterialState readings) formula ≤ budget) :
    (Finite.check table formula environment budget
        (ObservedFamilyEnclosure.valueMember readings source)).map Outcome.answer =
          some (some true) ↔
      satisfies (transitionSystem (gsltSpan S))
        (pullEnvironment (ObservedFamilyEnclosure.valueMember readings) environment.meaning)
        formula source :=
  (check_positive_iff_native readings occurrences table formula positive environment budget source enough).trans
    (formulaType_source readings occurrences complete formula coverage positive environment.meaning source)

theorem check_negative_iff_source (complete : ActionsPresentSteps (M := M))
    {n : Nat} (formula : Formula Traversal n)
    (coverage : CoversFormula (ObservedFamilyEnclosure.Events.observation readings occurrences)
      formula) (positive : fixedPointsPositive formula = true)
    (environment : FiniteMuCalculus.Environment (MaterialState readings) n)
    (budget : Nat) (source : S.Term)
    (enough : FiniteMuCalculus.requiredBudget (State := MaterialState readings) formula ≤ budget) :
    (Finite.check table formula environment budget
        (ObservedFamilyEnclosure.valueMember readings source)).map Outcome.answer =
          some (some false) ↔
      ¬ satisfies (transitionSystem (gsltSpan S))
        (pullEnvironment (ObservedFamilyEnclosure.valueMember readings) environment.meaning)
        formula source :=
  (check_negative_iff_native readings occurrences table formula positive environment budget source enough).trans
    (not_congr (formulaType_source readings occurrences complete formula coverage positive environment.meaning source))

/-- Future-only Büchi queries need faithful outgoing readings, without an
incoming coverage premise or a finite source-state assumption. -/
theorem check_buchi_iff_source (faithful : readings.Faithful)
    (complete : ActionsPresentSteps (M := M))
    (accepting : Finset (MaterialState readings)) (budget : Nat) (source : S.Term)
    (enough : FiniteMuCalculus.requiredBudget (State := MaterialState readings)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check table (Formula.buchi .future) (fun _ => accepting) budget
        (ObservedFamilyEnclosure.valueMember readings source)).map Outcome.answer =
          some (some true) ↔
      satisfies (transitionSystem (gsltSpan S))
        (fun _ => ObservedFamilyEnclosure.valueMember readings ⁻¹' (↑accepting : Set (MaterialState readings)))
        (Formula.buchi .future) source :=
  check_positive_iff_source readings occurrences table complete _
    (buchi_covered readings occurrences faithful) (Formula.buchi_positive Traversal.future)
    (fun _ => accepting) budget source enough

/-- A qualified finite material verdict is exactly an accepting infinite
path in the full authored source GSLT, even when its carrier is infinite. -/
theorem check_buchi_iff_source_path (faithful : readings.Faithful)
    (complete : ActionsPresentSteps (M := M))
    (accepting : Finset (MaterialState readings)) (budget : Nat) (source : S.Term)
    (enough : FiniteMuCalculus.requiredBudget (State := MaterialState readings)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check table (Formula.buchi .future) (fun _ => accepting) budget
        (ObservedFamilyEnclosure.valueMember readings source)).map Outcome.answer =
          some (some true) ↔
      BuchiPath (transitionSystem (gsltSpan S)) .future
        (ObservedFamilyEnclosure.valueMember readings ⁻¹' (↑accepting : Set (MaterialState readings)))
        source := by
  refine (Finite.check_buchi_iff table accepting budget _ enough).trans ?_
  refine (Semantics.BuchiTransport.path_pullback
    (ObservedFamilyEnclosure.Events.observation readings occurrences)
    (ObservedFamilyEnclosure.Events.sourceLifts readings faithful occurrences)
    (↑accepting : Set (MaterialState readings)) source).trans ?_
  have acceptingEq : id ⁻¹'
      (ObservedFamilyEnclosure.valueMember readings ⁻¹' (↑accepting : Set (MaterialState readings))) =
      ObservedFamilyEnclosure.valueMember readings ⁻¹' (↑accepting : Set (MaterialState readings)) := rfl
  simpa only [actionToGSLT, ObservedFamilyEnclosure.Events.observation, id_eq, acceptingEq] using
    (Semantics.BuchiTransport.path_pullback (actionToGSLT occurrences complete)
      (actionToGSLT_sourceLifts occurrences complete)
      (ObservedFamilyEnclosure.valueMember readings ⁻¹' (↑accepting : Set (MaterialState readings))) source).symm

end Mettapedia.OSLF.NativeTypes.Executable.FiniteMaterial
