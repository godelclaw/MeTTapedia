import Mettapedia.OSLF.NativeTypes.Structural.PropositionalReadout

open Mettapedia.OSLF.Framework

/-!
# Component execution for generated decomposition judgments

Every component is checked in its actual carrier with the unchanged language,
provider and operational permissions. The component's bounded execution is
retained; unresolved component questions do not certify a negative split.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
open Mettapedia.GSLT.LanguageDef.WellSorted

def componentRequest (parent : Request) (expected : TypeExpr) (source : Pattern) : Request :=
  ⟨parent.plan, parent.bound, expected, source⟩

def componentState (parent : Request) (expected : TypeExpr) (source : Pattern) (budget : Nat) :
    State (componentRequest parent expected source) :=
  run _ budget (start _)

theorem componentState_resume (parent : Request) (expected : TypeExpr) (source : Pattern)
    (first second : Nat) :
    componentState parent expected source (first + second) =
      run (componentRequest parent expected source) second
        (componentState parent expected source first) :=
  run_add _ _ _ _

/-- The same retained engine state exposes pending equation, rule, matcher
and provider work when a component answer is unresolved. -/
structure ComponentRun (parent : Request) (expected : TypeExpr) (source : Pattern) where
  state : State (componentRequest parent expected source)
  answer : Option Bool

/-- This test includes canonical binder metadata, sorting and scope of the
actual component, so the component request reads that same value. -/
def componentAdmission (parent : Request) (expected : TypeExpr) (source : Pattern) : Bool :=
  checkOpenPatternWellSorted parent.plan.snapshot.language parent.plan.snapshot.free
    parent.bound expected source

def readComponentFormula (parent : Request) (expected : TypeExpr) (source : Pattern)
    (budget : Nat) (formula : Formula) : Option Bool :=
  if componentAdmission parent expected source then
    readFrontierFormula (componentRequest parent expected source)
      (componentState parent expected source budget) formula
  else none

def executeComponentFormula (parent : Request) (expected : TypeExpr) (source : Pattern)
    (budget : Nat) (formula : Formula) : ComponentRun parent expected source :=
  ⟨componentState parent expected source budget,
    readComponentFormula parent expected source budget formula⟩

theorem component_admitted {parent : Request} (admitted : Admitted parent)
    {expected : TypeExpr} {source : Pattern}
    (checked : componentAdmission parent expected source = true) :
    Admitted (componentRequest parent expected source) := by
  have typed := checkOpenPatternWellSorted_sound checked
  have same := Pattern.eraseBinderMetadata_eq_self_of_canonical typed.2.1
  refine ⟨admitted.compiled, admitted.accepted, ?_⟩
  change OpenPatternWellSorted _ _ _ _ source.eraseBinderMetadata
  rw [same]
  exact typed

theorem readComponentFormula_sound {parent : Request} (admitted : Admitted parent)
    (atom : TypeExpr → Nat → Pattern → Prop) (expected : TypeExpr)
    (source : Pattern) (budget : Nat) (formula : Formula) :
    ReadoutCorrect (readComponentFormula parent expected source budget formula)
      (Holds parent.plan.snapshot.language parent.plan.snapshot.free parent.bound
        (frontierEquation parent) atom expected formula source) := by
  unfold readComponentFormula
  split
  · rename_i checked
    have typed := checkOpenPatternWellSorted_sound checked
    have same := Pattern.eraseBinderMetadata_eq_self_of_canonical typed.2.1
    have sound := readFrontierFormula_sound
      (state := componentState parent expected source budget)
      (component_admitted admitted checked) atom formula
    change ReadoutCorrect (readFrontierFormula (componentRequest parent expected source)
      (componentState parent expected source budget) formula)
      (Holds parent.plan.snapshot.language parent.plan.snapshot.free parent.bound
        (frontierEquation parent) atom expected formula source.eraseBinderMetadata) at sound
    simpa only [same] using sound
  · simp [ReadoutCorrect]

theorem representedPattern_equivalent {request : Request} {state : State request}
    {term : Pattern} (member : term ∈ representedPatterns request state) :
    frontierEquation request request.expected request.root term := by
  obtain ⟨representative, _, same⟩ := List.mem_map.mp member
  rw [← same]
  exact representative.justified.equivalent

theorem first_represented (request : Request)
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true) :
    representedPatterns request (run request 1 (start request)) = [request.root] := by
  simp [representedPatterns, run, start, checked, tick, expand]

theorem first_unfinished (request : Request)
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true) :
    complete request (run request 1 (start request)) = false := by
  simp [complete, run, start, checked, tick, expand]

theorem first_structural_readout {request : Request}
    (checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected request.root = true) {former : Former}
    (lookup : request.plan.snapshot.language.terms[former.index]? = some former.declaration)
    {arguments : List Pattern}
    (constructed : constructorArguments? request.plan.snapshot.language request.plan.snapshot.free
      request.bound former.declaration request.root = some arguments) :
    readFrontierStructural request (run request 1 (start request)) former = some true := by
  unfold readFrontierStructural checkFrontierStructural checkStructural
  rw [first_represented request checked]
  simp only [lookup, beq_self_eq_true, List.any_cons, List.any_nil,
    constructed, Option.isSome_some, Bool.or_false, Bool.and_self, if_true]

theorem first_component_root {parent : Request} {expected : TypeExpr} {source : Pattern}
    (checked : componentAdmission parent expected source = true)
    {index : Nat} {declaration : GrammarRule}
    (lookup : parent.plan.snapshot.language.terms[index]? = some declaration)
    (sameSort : expected = .base declaration.category) {arguments : List Pattern}
    (constructed : constructorArguments? parent.plan.snapshot.language parent.plan.snapshot.free
      parent.bound declaration source = some arguments) :
    readComponentFormula parent expected source 1 (.root index) = some true := by
  have typed := checkOpenPatternWellSorted_sound checked
  have same := Pattern.eraseBinderMetadata_eq_self_of_canonical typed.2.1
  let request := componentRequest parent expected source
  have rootSame : request.root = source := same
  have rootChecked : checkOpenPatternWellSorted request.plan.snapshot.language
      request.plan.snapshot.free request.bound request.expected request.root = true := by
    change checkOpenPatternWellSorted _ _ _ _ source.eraseBinderMetadata = true
    rw [same]
    exact checked
  unfold readComponentFormula
  rw [if_pos checked]
  change readFrontierFormula request (run request 1 (start request)) (.root index) = some true
  simp only [readFrontierFormula, show request.plan.snapshot.language.terms[index]? =
      some declaration from lookup, show request.expected = .base declaration.category from sameSort,
    beq_self_eq_true, if_true]
  apply first_structural_readout (former := ⟨index, declaration⟩) rootChecked lookup
  rw [rootSame]
  exact constructed

/-- Positive existential discovery needs no completeness flag. Negative
answers require checked outer coverage and conclusive answers for every case. -/
def readExistential (answers : List (Option Bool)) (outerComplete : Bool) : Option Bool :=
  if answers.any (· == some true) then some true
  else if outerComplete && answers.all Option.isSome then some false else none

def existentialCoverage (answers : List (Option Bool)) (outerComplete : Bool) : Bool :=
  outerComplete && answers.all Option.isSome

theorem readExistential_true {answers : List (Option Bool)} {outerComplete : Bool}
    (read : readExistential answers outerComplete = some true) :
    some true ∈ answers := by
  unfold readExistential at read
  split at read
  · rename_i positive
    obtain ⟨answer, member, same⟩ := List.any_eq_true.mp positive
    have equal : answer = some true := by simpa using same
    simpa only [equal] using member
  · split at read <;> cases read

theorem readExistential_false {answers : List (Option Bool)} {outerComplete : Bool}
    (read : readExistential answers outerComplete = some false) :
    outerComplete = true ∧ (∀ answer ∈ answers, ∃ value, answer = some value) ∧
      some true ∉ answers := by
  unfold readExistential at read
  split at read
  · cases read
  · rename_i noPositive
    split at read
    · rename_i complete
      simp only [Bool.and_eq_true] at complete
      refine ⟨complete.1, ?_, ?_⟩
      · intro answer member
        have checked := (List.all_eq_true.mp complete.2) answer member
        cases answer with
        | none => cases checked
        | some value => exact ⟨value, rfl⟩
      · intro member
        exact noPositive (List.any_eq_true.mpr ⟨some true, member, rfl⟩)
    · cases read

theorem existentialCoverage_conclusive {answers : List (Option Bool)} {outerComplete : Bool}
    (checked : existentialCoverage answers outerComplete = true) :
    ∃ value, readExistential answers outerComplete = some value := by
  unfold readExistential
  split
  · exact ⟨true, rfl⟩
  · unfold existentialCoverage at checked
    rw [if_pos checked]
    exact ⟨false, rfl⟩

end Mettapedia.OSLF.NativeTypes.Structural
