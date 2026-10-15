import Mettapedia.OSLF.NativeTypes.Structural.SplitReadout

open Mettapedia.OSLF.Framework

/-!
# Executable spatial partitions with checked equation witnesses

Every closed represented bag supplies all of its prefix/suffix partitions.
The join of the two parts must itself be a represented equation witness.
Singleton parts retain their actual process; other parts are whole bags.
This admits the selected algebra laws without assuming extra flattening.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
open Mettapedia.GSLT.LanguageDef.WellSorted

def spatialPart : List Pattern → Pattern
  | [term] => term
  | elements => .collection .hashBag elements none

def spatialCase? (request : Request) (state : State request) (elements : List Pattern)
    (cut : Nat) : Option SplitCase :=
  let first := spatialPart (elements.take cut)
  let second := spatialPart (elements.drop cut)
  let joined := Pattern.collection .hashBag [first, second] none
  if (representedPatterns request state).contains joined &&
      checkHasType request.plan.snapshot.language request.plan.snapshot.free request.bound
        first request.expected &&
      checkHasType request.plan.snapshot.language request.plan.snapshot.free request.bound
        second request.expected then
    some ⟨joined, first, second⟩
  else none

def spatialCasesFrom (request : Request) (state : State request) : Pattern → List SplitCase
  | .collection .hashBag elements none =>
      (List.range (elements.length + 1)).filterMap (spatialCase? request state elements)
  | _ => []

def spatialCases (request : Request) (state : State request) : List SplitCase :=
  (representedPatterns request state).flatMap (spatialCasesFrom request state)

theorem spatialCase?_sound {request : Request} {state : State request}
    {elements : List Pattern} {cut : Nat} {candidate : SplitCase}
    (checked : spatialCase? request state elements cut = some candidate) :
    candidate.representative = .collection .hashBag [candidate.first, candidate.second] none ∧
      candidate.representative ∈ representedPatterns request state ∧
      HasType request.plan.snapshot.language request.plan.snapshot.free request.bound
        candidate.first request.expected ∧
      HasType request.plan.snapshot.language request.plan.snapshot.free request.bound
        candidate.second request.expected := by
  unfold spatialCase? at checked
  dsimp only at checked
  split at checked
  · rename_i accepted
    simp only [Bool.and_eq_true, List.contains_iff_mem] at accepted
    cases checked
    exact ⟨rfl, accepted.1.1, checkHasType_sound accepted.1.2,
      checkHasType_sound accepted.2⟩
  · cases checked

theorem spatialCases_member {request : Request} {state : State request}
    {candidate : SplitCase} (member : candidate ∈ spatialCases request state) :
    candidate.representative = .collection .hashBag [candidate.first, candidate.second] none ∧
      candidate.representative ∈ representedPatterns request state ∧
      HasType request.plan.snapshot.language request.plan.snapshot.free request.bound
        candidate.first request.expected ∧
      HasType request.plan.snapshot.language request.plan.snapshot.free request.bound
        candidate.second request.expected := by
  obtain ⟨term, _, partition⟩ := List.mem_flatMap.mp member
  cases term with
  | collection kind elements rest =>
      cases kind with
      | hashBag =>
          cases rest with
          | none =>
              obtain ⟨cut, _, checked⟩ := List.mem_filterMap.mp partition
              exact spatialCase?_sound checked
          | some name => simp [spatialCasesFrom] at partition
      | vec => simp [spatialCasesFrom] at partition
      | hashSet => simp [spatialCasesFrom] at partition
  | bvar index => simp [spatialCasesFrom] at partition
  | fvar name => simp [spatialCasesFrom] at partition
  | apply label arguments => simp [spatialCasesFrom] at partition
  | lambda binder body => simp [spatialCasesFrom] at partition
  | multiLambda count binders body => simp [spatialCasesFrom] at partition
  | subst body replacement => simp [spatialCasesFrom] at partition

private theorem object_pair_components {first second : Pattern}
    (object : isObjectPattern (.collection .hashBag [first, second] none) = true) :
    isObjectPattern first = true ∧ isObjectPattern second = true := by
  simpa only [isObjectPattern, isObjectPatternList, Option.isNone_none,
    Bool.true_and, Bool.and_true,
    Bool.and_eq_true] using object

/-- A semantic binary join is itself one represented bag. The enumerated
cut at one recovers its exact two process values, so coverage is not limited
to one hand-written decomposition or a two-element input language. -/
theorem spatialCases_cover {request : Request} {state : State request}
    (admitted : Admitted request) (certificate : checkCertificate request state = true)
    {first second : Pattern}
    (firstTyped : HasType request.plan.snapshot.language request.plan.snapshot.free
      request.bound first request.expected)
    (secondTyped : HasType request.plan.snapshot.language request.plan.snapshot.free
      request.bound second request.expected)
    (related : frontierEquation request request.expected request.root
      (.collection .hashBag [first, second] none)) :
    ⟨.collection .hashBag [first, second] none, first, second⟩ ∈ spatialCases request state := by
  have represented := (certified_representatives_exact admitted certificate _).mpr related
  have objects := object_pair_components (certified_class_objects admitted certificate related)
  have firstChecked := checkHasType_complete_of_object firstTyped objects.1
  have secondChecked := checkHasType_complete_of_object secondTyped objects.2
  have contains : (representedPatterns request state).contains
      (.collection .hashBag [first, second] none) = true :=
    List.contains_iff_mem.mpr represented
  apply List.mem_flatMap.mpr
  refine ⟨.collection .hashBag [first, second] none, represented, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨1, by simp, ?_⟩
  simp only [spatialCase?, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, spatialPart, contains, firstChecked, secondChecked,
    Bool.true_and, if_true]

def spatialAnswers (request : Request) (state : State request) (first second : Formula)
    (budget : Nat) : List (Option Bool) :=
  (spatialCases request state).map fun candidate => readBinary Bool.and
    (readComponentFormula request request.expected candidate.first budget first)
    (readComponentFormula request request.expected candidate.second budget second)

def spatialCoverage (request : Request) (state : State request) (first second : Formula)
    (budget : Nat) : Bool :=
  existentialCoverage (spatialAnswers request state first second budget)
    (checkCertificate request state)

def readSpatialCases (request : Request) (state : State request) (first second : Formula)
    (budget : Nat) : Option Bool :=
  readExistential (spatialAnswers request state first second budget) (checkCertificate request state)

theorem readSpatialCase_sound {request : Request} (admitted : Admitted request)
    (atom : TypeExpr → Nat → Pattern → Prop) (first second : Formula)
    (budget : Nat) (candidate : SplitCase) :
    ReadoutCorrect (readBinary Bool.and
      (readComponentFormula request request.expected candidate.first budget first)
      (readComponentFormula request request.expected candidate.second budget second))
      (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom request.expected first candidate.first ∧
        Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom request.expected second candidate.second) :=
  readBinary_conjunction_sound (readComponentFormula_sound admitted atom _ _ budget first)
    (readComponentFormula_sound admitted atom _ _ budget second)

theorem readSpatialCases_sound {request : Request} {state : State request}
    (admitted : Admitted request) {index : Nat} {declaration : GrammarRule}
    (lookup : request.plan.snapshot.language.terms[index]? = some declaration)
    (expected : request.expected = .base declaration.category) {shape : SpatialShape}
    (shapeChecked : spatialShape? request.plan.snapshot.language declaration = some shape)
    (atom : TypeExpr → Nat → Pattern → Prop) (first second : Formula) (budget : Nat) :
    ReadoutCorrect (readSpatialCases request state first second budget)
      (SpatialHolds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (frontierEquation request request.expected) ⟨index, declaration⟩
        (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom request.expected first)
        (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom request.expected second) request.root) := by
  intro answer read
  cases answer with
  | true =>
      obtain ⟨candidate, member, observed⟩ := List.mem_map.mp (readExistential_true read)
      have components := (readSpatialCase_sound admitted atom first second budget candidate
        true observed).mp rfl
      obtain ⟨joined, represented, firstTyped, secondTyped⟩ := spatialCases_member member
      have related := representedPattern_equivalent represented
      constructor
      · intro _
        refine ⟨(mem_structuralFormers_iff _ _).mpr lookup, shape, shapeChecked,
          candidate.first, candidate.second, ?_, ?_, ?_, components⟩
        · simpa only [expected] using firstTyped
        · simpa only [expected] using secondTyped
        · simpa only [joined] using related
      · intro _; rfl
  | false =>
      obtain ⟨certificate, conclusive, noPositive⟩ := readExistential_false read
      constructor
      · intro impossible; cases impossible
      · intro holds
        obtain ⟨_, _, _, left, right, leftTyped, rightTyped, related, firstHolds, secondHolds⟩ := holds
        have member := spatialCases_cover admitted certificate
          (expected ▸ leftTyped) (expected ▸ rightTyped) related
        let candidate : SplitCase := ⟨.collection .hashBag [left, right] none, left, right⟩
        have answerMember : readBinary Bool.and
            (readComponentFormula request request.expected left budget first)
            (readComponentFormula request request.expected right budget second) ∈
            spatialAnswers request state first second budget :=
          List.mem_map.mpr ⟨candidate, member, rfl⟩
        obtain ⟨answer, observed⟩ := conclusive _ answerMember
        have positive := (readSpatialCase_sound admitted atom first second budget candidate
          answer observed).mpr ⟨firstHolds, secondHolds⟩
        subst answer
        exfalso
        apply noPositive
        simpa only [observed] using answerMember

def readFrontierSpatial (request : Request) (state : State request) (index : Nat)
    (first second : Formula) (budget : Nat) : Option Bool :=
  match request.plan.snapshot.language.terms[index]? with
  | none => none
  | some declaration =>
      if request.expected == .base declaration.category then
        match spatialShape? request.plan.snapshot.language declaration with
        | none => none
        | some _ => readSpatialCases request state first second budget
      else none

theorem readFrontierSpatial_sound {request : Request} {state : State request}
    (admitted : Admitted request) (atom : TypeExpr → Nat → Pattern → Prop)
    (index : Nat) (first second : Formula) (budget : Nat) :
    ReadoutCorrect (readFrontierSpatial request state index first second budget)
      (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (frontierEquation request) atom request.expected (.spatial index first second) request.root) := by
  unfold readFrontierSpatial
  cases lookup : request.plan.snapshot.language.terms[index]? with
  | none => simp [ReadoutCorrect]
  | some declaration =>
      dsimp only
      split
      · rename_i same
        have equal : request.expected = .base declaration.category := by
          simpa only [beq_iff_eq] using same
        cases checked : spatialShape? request.plan.snapshot.language declaration with
        | none => simp [ReadoutCorrect]
        | some shape =>
            dsimp only
            have sound := readSpatialCases_sound (state := state) admitted lookup equal
              checked atom first second budget
            simpa only [equal, holds_spatial_exact lookup] using sound
      · simp [ReadoutCorrect]

theorem checked_spatial_conclusive {request : Request} {state : State request}
    {first second : Formula} {budget : Nat}
    (coverage : spatialCoverage request state first second budget = true) :
    ∃ answer, readSpatialCases request state first second budget = some answer :=
  existentialCoverage_conclusive coverage

end Mettapedia.OSLF.NativeTypes.Structural
