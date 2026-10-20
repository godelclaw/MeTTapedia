import Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls
import Mettapedia.OSLF.NativeTypes.Runtime.Search
import Mettapedia.OSLF.NativeTypes.Runtime.Local

open Mettapedia.OSLF.Framework

/-!
# Comparison with the original bounded OSLF formula checkers

The shared finite Partrec fragment has the same independent meaning in both
checkers. A positive answer from either original checker transfers to the
generated native checker. A certified native refutation excludes such a
positive answer. An original negative answer is not transferred without an
independent completeness argument for its successor provider.

The predecessor-aware checker has the same answer on the translated fragment,
which contains no incoming box. This comparison does not identify an incoming
adjoint box with the outgoing universal modality.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Comparison.LegacyChecker

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison

def noAtoms : AtomCheck := fun _ _ => false

def legacyStep (source : Pattern) : List Pattern :=
  NonrecursiveReduction.rootReducts Mettapedia.Languages.PartrecMachine.partrecMachine source

theorem legacy_step_sound {source target : Pattern} (listed : target ∈ legacyStep source) :
    Mettapedia.Languages.PartrecMachine.Reduces source target :=
  Mettapedia.Languages.PartrecMachine.reduces_iff_mem_rootReducts.mpr listed

def legacyCheck (fuel : Nat) (source : Pattern) (formula : OSLFFormula) : CheckResult :=
  Mettapedia.OSLF.Formula.check legacyStep noAtoms fuel source formula

def legacyCheckWithPred (pred : Pattern → List Pattern) (fuel : Nat)
    (source : Pattern) (formula : OSLFFormula) : CheckResult :=
  checkWithPred legacyStep pred noAtoms fuel source formula

/-- No predecessor branch occurs in a translated formula. This equality
therefore needs no assumption that an arbitrary supplied predecessor list is
complete for the original machine. -/
theorem shared_predecessors_irrelevant
    (step pred : Pattern → List Pattern) (atoms : AtomCheck)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (fuel : Nat) (source : Pattern) :
    checkWithPred step pred atoms fuel source formula =
      Mettapedia.OSLF.Formula.check step atoms fuel source formula := by
  induction formula generalizing generated fuel source with
  | top | bot => cases fuel <;> rfl
  | and first second firstIH secondIH =>
    simp only [fromLegacy?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at translated
    obtain ⟨left, leftTranslated, right, rightTranslated, _⟩ := translated
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [checkWithPred, Mettapedia.OSLF.Formula.check,
        firstIH leftTranslated, secondIH rightTranslated]
  | or first second firstIH secondIH =>
    simp only [fromLegacy?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at translated
    obtain ⟨left, leftTranslated, right, rightTranslated, _⟩ := translated
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [checkWithPred, Mettapedia.OSLF.Formula.check,
        firstIH leftTranslated, secondIH rightTranslated]
  | dia body ih =>
    obtain ⟨inner, innerTranslated, _⟩ := Option.map_eq_some_iff.mp translated
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [checkWithPred, Mettapedia.OSLF.Formula.check, ih innerTranslated]
  | atom | imp | box | var | mu | emptyColl | cut | headed =>
    simp [fromLegacy?] at translated

theorem legacy_positive_native (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (fuel : Nat)
    (source : Pattern) (typed : Source bound source)
    (positive : legacyCheck fuel source formula = .sat) :
    denotation (noLeaves bound) generated (.empty _) source := by
  apply (denotation_iff_original bound (fun _ _ => False) translated source typed).mpr
  exact Mettapedia.OSLF.Formula.check_sat_sound
    (R := Mettapedia.Languages.PartrecMachine.Reduces)
    (step := legacyStep) (I_check := noAtoms) (I_sem := fun _ _ => False)
    (h_atoms := by intro atom term accepted; cases accepted)
    (h_step := fun first second listed => @legacy_step_sound first second listed) positive

theorem legacy_predecessor_positive_native (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (pred : Pattern → List Pattern)
    (fuel : Nat) (source : Pattern) (typed : Source bound source)
    (positive : legacyCheckWithPred pred fuel source formula = .sat) :
    denotation (noLeaves bound) generated (.empty _) source := by
  have same := shared_predecessors_irrelevant legacyStep pred noAtoms translated fuel source
  change legacyCheckWithPred pred fuel source formula = legacyCheck fuel source formula at same
  rw [same] at positive
  exact legacy_positive_native bound translated fuel source typed positive

theorem legacy_positive_eventually_checked (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (fuel : Nat)
    (source : Pattern) (typed : Source bound source)
    (positive : legacyCheck fuel source formula = .sat) :
    run bound generated source (effectiveBound bound generated source) = some true := by
  have supported := (translation_recognizes_fragment formula).mp ⟨generated, translated⟩
  have native := legacy_positive_native bound translated fuel source typed positive
  have original := (denotation_iff_original bound (fun _ _ => False) translated source typed).mp native
  rw [executable_answers_agree bound translated source typed,
    (Mettapedia.OSLF.SatisfactionUndecidable.decideModalSearch_iff supported source).mpr original]

theorem native_refutation_excludes_legacy_positive (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (nativeBudget legacyFuel : Nat)
    (source : Pattern) (typed : Source bound source)
    (refuted : run bound generated source nativeBudget = some false) :
    legacyCheck legacyFuel source formula ≠ .sat := by
  intro positive
  exact checked_negative (backend bound) (noLeaves bound) generated source nativeBudget refuted
    (legacy_positive_native bound translated legacyFuel source typed positive)

theorem native_refutation_excludes_predecessor_positive (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (pred : Pattern → List Pattern)
    (nativeBudget legacyFuel : Nat) (source : Pattern) (typed : Source bound source)
    (refuted : run bound generated source nativeBudget = some false) :
    legacyCheckWithPred pred legacyFuel source formula ≠ .sat := by
  intro positive
  exact checked_negative (backend bound) (noLeaves bound) generated source nativeBudget refuted
    (legacy_predecessor_positive_native bound translated pred legacyFuel source typed positive)

theorem zero_fuel_claims_no_membership (source : Pattern) (formula : OSLFFormula) :
    legacyCheck 0 source formula = .unknown := rfl

/-- A sound but incomplete successor provider can report an old negative
answer at a program where the original machine really has a successor. -/
theorem incomplete_provider_negative :
    Mettapedia.OSLF.Formula.check (fun _ => []) noAtoms 1
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source (.dia .top) = .unsat := rfl

namespace Retained

/-- The shared atom-free syntax embeds in the public generated leaf syntax.
No interpretation of a structural leaf is invented by this embedding. -/
def liftEmpty {Leaf : Type} : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty →
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf
  | .atom impossible => nomatch impossible
  | .top => .top
  | .bottom => .bottom
  | .conj left right => .conj (liftEmpty left) (liftEmpty right)
  | .disj left right => .disj (liftEmpty left) (liftEmpty right)
  | .neg formula => .neg (liftEmpty formula)
  | .imp left right => .imp (liftEmpty left) (liftEmpty right)
  | .possibility formula => .possibility (liftEmpty formula)
  | .outgoingUniversal formula => .outgoingUniversal (liftEmpty formula)
  | .separating index left right => .separating index (liftEmpty left) (liftEmpty right)

theorem lifted_meaning {Leaf : Type} (bound : List TypeExpr)
    (tests : Leaf → Test (theory bound) (Source bound))
    (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty) :
    denotation tests (liftEmpty formula) = denotation (noLeaves bound) formula := by
  induction formula with
  | atom impossible => cases impossible
  | top | bottom => rfl
  | conj left right ihl ihr | disj left right ihl ihr | imp left right ihl ihr =>
    simp only [liftEmpty, denotation, ihl, ihr]
  | separating index left right ihl ihr =>
    simp only [liftEmpty, denotation, ihl, ihr]
  | neg formula ih | possibility formula ih | outgoingUniversal formula ih =>
    simp only [liftEmpty, denotation, ih]

def decoded (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    (source : Pattern) (typed : Source bound source) :
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound).Decoded source := ⟨source, typed, rfl⟩

def check (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty) (source : Pattern)
    (typed : Source bound source) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Runtime.check (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound)
    (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound) (liftEmpty formula)
    (decoded configuration bound source typed) budget

def decisionBound (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty) (source : Pattern)
    (typed : Source bound source) : Nat :=
  Mettapedia.OSLF.NativeTypes.Runtime.decisionBound (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound)
    (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound) (liftEmpty formula)
    (decoded configuration bound source typed)

theorem native_meaning (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (source : Pattern) (typed : Source bound source) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound)
      (liftEmpty generated) source ↔
      sem Mettapedia.Languages.PartrecMachine.Reduces (fun _ _ => False) formula source := by
  rw [Mettapedia.OSLF.NativeTypes.Runtime.Description.meaning_at_decoded (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound)
    (liftEmpty generated) source (decoded configuration bound source typed)]
  exact (Iff.of_eq (congrArg (fun predicate : GSLTTypeSynthesis.EquationPredicate (theory bound) => predicate source)
    (lifted_meaning bound (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.tests configuration bound) generated))).trans
      (denotation_iff_original bound (fun _ _ => False) translated source typed)

theorem machine_meaning (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (source : Pattern) (typed : Source bound source) :
    Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation
      (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound).leaves
      (liftEmpty generated) (.empty _) source ↔
      sem Mettapedia.Languages.PartrecMachine.Reduces (fun _ _ => False) formula source := by
  have comparison := Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation_comparison
    (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound).leaves
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.tests configuration bound)
    (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound).leaf_meaning (liftEmpty generated)
  exact (Iff.of_eq (congrArg (fun predicate : GSLTTypeSynthesis.EquationPredicate (theory bound) => predicate source)
    comparison)).trans
    ((Iff.of_eq (congrArg (fun predicate : GSLTTypeSynthesis.EquationPredicate (theory bound) => predicate source)
      (lifted_meaning bound (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.tests configuration bound) generated))).trans
        (denotation_iff_original bound (fun _ _ => False) translated source typed))

/-- The public retained checker eventually reproduces every sound old
positive answer, provided the chosen generated logic admits the shared formula.
The two checkers' fuel counters and unresolved answers are not equated. -/
theorem legacy_positive_eventually_checked
    (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed
      (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound).generated.logicFragment
      (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound).leafAdmission (liftEmpty generated))
    (fuel : Nat) (source : Pattern) (typed : Source bound source)
    (positive : legacyCheck fuel source formula = .sat) :
    (check configuration bound generated source typed
      (decisionBound configuration bound generated source typed)).readout =
        .judgment (.decided true) := by
  have satisfies : Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning
      (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound) (liftEmpty generated) source := by
    apply (native_meaning configuration bound translated source typed).mpr
    exact (denotation_iff_original bound (fun _ _ => False) translated source typed).mp
      (legacy_positive_native bound translated fuel source typed positive)
  obtain ⟨answer, read⟩ := Mettapedia.OSLF.NativeTypes.Runtime.check_complete
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.driver configuration bound)
    (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound) (liftEmpty generated)
    (decoded configuration bound source typed) formed
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.admitted_cube configuration) _ (Nat.le_refl _)
  cases answer with
  | true => exact read
  | false => exact (Mettapedia.OSLF.NativeTypes.Runtime.negative
      (check configuration bound generated source typed (decisionBound configuration bound generated source typed))
      read satisfies).elim

theorem machine_refutation_excludes_legacy_positive
    (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (machineBudget legacyFuel : Nat)
    (source : Pattern) (typed : Source bound source)
    (refuted : (check configuration bound generated source typed machineBudget).readout =
      .judgment (.decided false)) :
    legacyCheck legacyFuel source formula ≠ .sat := by
  intro positive
  apply Mettapedia.OSLF.NativeTypes.Runtime.negative (check configuration bound generated source typed machineBudget) refuted
  apply (native_meaning configuration bound translated source typed).mpr
  exact (denotation_iff_original bound (fun _ _ => False) translated source typed).mp
    (legacy_positive_native bound translated legacyFuel source typed positive)

theorem machine_refutation_excludes_predecessor_positive
    (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    {formula : OSLFFormula} {generated : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Empty}
    (translated : fromLegacy? formula = some generated) (pred : Pattern → List Pattern)
    (machineBudget legacyFuel : Nat) (source : Pattern) (typed : Source bound source)
    (refuted : (check configuration bound generated source typed machineBudget).readout =
      .judgment (.decided false)) :
    legacyCheckWithPred pred legacyFuel source formula ≠ .sat := by
  intro positive
  have same := shared_predecessors_irrelevant legacyStep pred noAtoms translated legacyFuel source
  change legacyCheckWithPred pred legacyFuel source formula = legacyCheck legacyFuel source formula at same
  rw [same] at positive
  exact machine_refutation_excludes_legacy_positive configuration bound translated machineBudget legacyFuel
    source typed refuted positive

#guard (check {} [] (.possibility .top) Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source_admitted 0).readout == .judgment .unknown
#guard (check {} [] (.possibility .top) Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source_admitted 1000).readout == .judgment (.decided true)
#guard (check {} [] (.possibility (.possibility .top)) Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source_admitted 1000).readout == .judgment (.decided true)
#guard (check {} [] (.possibility .top) Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.stopped
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.stopped_admitted 1000).readout == .judgment (.decided false)

end Retained

#guard legacyCheck 0 Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source (.dia .top) == .unknown
#guard legacyCheck 2 Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source (.dia .top) == .sat
#guard legacyCheck 3 Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source (.dia (.dia .top)) == .sat
#guard legacyCheck 2 Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.stopped (.dia .top) == .unsat
#guard legacyCheckWithPred (fun _ => []) 2 Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source (.dia .top) == .sat
#guard Mettapedia.OSLF.Formula.check (fun _ => []) noAtoms 1
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source (.dia .top) == .unsat
#guard run [] (.possibility .top) Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source 300 == some true
#guard run [] (.possibility .top) Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.stopped 300 == some false

#print axioms shared_predecessors_irrelevant
#print axioms legacy_positive_native
#print axioms legacy_positive_eventually_checked
#print axioms native_refutation_excludes_legacy_positive
#print axioms Retained.native_meaning
#print axioms Retained.legacy_positive_eventually_checked
#print axioms Retained.machine_refutation_excludes_legacy_positive

end Mettapedia.OSLF.NativeTypes.Comparison.LegacyChecker
