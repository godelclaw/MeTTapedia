import Mettapedia.OSLF.NativeTypes.Structural.ComponentReadout

open Mettapedia.OSLF.Framework

/-!
# Executable positional splitting over equation frontiers

The checker enumerates typed binary introductions among actual equation
representatives and executes the two generated component questions. Outer
coverage and conclusive component answers are checked before refutation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
open Mettapedia.GSLT.LanguageDef.WellSorted

structure BinaryShape where
  firstParam : TermParam
  secondParam : TermParam
  firstSort : TypeExpr
  secondSort : TypeExpr
  deriving Repr, DecidableEq

def binaryShape? (declaration : GrammarRule) : Option BinaryShape :=
  match declaration.params with
  | [first, second] =>
      match parameterType? first, parameterType? second with
      | some firstSort, some secondSort => some ⟨first, second, firstSort, secondSort⟩
      | _, _ => none
  | _ => none

theorem binaryShape?_sound {declaration : GrammarRule} {shape : BinaryShape}
    (checked : binaryShape? declaration = some shape) :
    declaration.params = [shape.firstParam, shape.secondParam] ∧
      parameterType? shape.firstParam = some shape.firstSort ∧
      parameterType? shape.secondParam = some shape.secondSort := by
  unfold binaryShape? at checked
  split at checked
  · rename_i first second arity
    split at checked
    · rename_i firstSort secondSort firstType secondType
      cases checked
      exact ⟨arity, firstType, secondType⟩
    · cases checked
  · cases checked

structure SplitCase where
  representative : Pattern
  first : Pattern
  second : Pattern
  deriving Repr, DecidableEq

def splitCase? (request : Request) (declaration : GrammarRule) (term : Pattern) :
    Option SplitCase :=
  match constructorArguments? request.plan.snapshot.language request.plan.snapshot.free
      request.bound declaration term with
  | some [first, second] => some ⟨term, first, second⟩
  | _ => none

def splitCases (request : Request) (state : State request) (declaration : GrammarRule) :
    List SplitCase :=
  (representedPatterns request state).filterMap (splitCase? request declaration)

theorem splitCase?_sound {request : Request} {declaration : GrammarRule}
    {term : Pattern} {candidate : SplitCase}
    (checked : splitCase? request declaration term = some candidate) :
    candidate.representative = term ∧
      ∃ value : ConstructorValue request.plan.snapshot.language request.plan.snapshot.free
          request.bound declaration,
        value.pattern = term ∧ value.arguments = [candidate.first, candidate.second] := by
  unfold splitCase? at checked
  split at checked
  · rename_i first second arguments
    cases checked
    exact ⟨rfl, constructorArguments?_sound arguments⟩
  · cases checked

theorem splitCases_member {request : Request} {state : State request}
    {declaration : GrammarRule} {candidate : SplitCase}
    (member : candidate ∈ splitCases request state declaration) :
    candidate.representative ∈ representedPatterns request state ∧
      ∃ value : ConstructorValue request.plan.snapshot.language request.plan.snapshot.free
          request.bound declaration,
        value.pattern = candidate.representative ∧
          value.arguments = [candidate.first, candidate.second] := by
  obtain ⟨term, inside, checked⟩ := List.mem_filterMap.mp member
  obtain ⟨same, value, represented, arguments⟩ := splitCase?_sound checked
  exact ⟨same ▸ inside, value, represented.trans same.symm, arguments⟩

def readSplitCase (request : Request) (shape : BinaryShape) (first second : Formula)
    (budget : Nat) (candidate : SplitCase) : Option Bool :=
  readBinary Bool.and
    (readComponentFormula request shape.firstSort candidate.first budget first)
    (readComponentFormula request shape.secondSort candidate.second budget second)

def splitAnswers (request : Request) (state : State request) (declaration : GrammarRule)
    (shape : BinaryShape) (first second : Formula) (budget : Nat) : List (Option Bool) :=
  (splitCases request state declaration).map (readSplitCase request shape first second budget)

def splitCoverage (request : Request) (state : State request) (declaration : GrammarRule)
    (shape : BinaryShape) (first second : Formula) (budget : Nat) : Bool :=
  existentialCoverage (splitAnswers request state declaration shape first second budget)
    (checkCertificate request state)

def readSplitCases (request : Request) (state : State request) (declaration : GrammarRule)
    (shape : BinaryShape) (first second : Formula) (budget : Nat) : Option Bool :=
  readExistential (splitAnswers request state declaration shape first second budget)
    (checkCertificate request state)

theorem readSplitCase_sound {request : Request} (admitted : Admitted request)
    (atom : TypeExpr → Nat → Pattern → Prop) (shape : BinaryShape)
    (first second : Formula) (budget : Nat) (candidate : SplitCase) :
    ReadoutCorrect (readSplitCase request shape first second budget candidate)
      (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom shape.firstSort first candidate.first ∧
        Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom shape.secondSort second candidate.second) :=
  readBinary_conjunction_sound
    (readComponentFormula_sound admitted atom _ _ budget first)
    (readComponentFormula_sound admitted atom _ _ budget second)

theorem splitCases_cover {request : Request} {state : State request}
    (admitted : Admitted request) (certificate : checkCertificate request state = true)
    {declaration : GrammarRule}
    (value : ConstructorValue request.plan.snapshot.language request.plan.snapshot.free
      request.bound declaration) {first second : Pattern}
    (arguments : value.arguments = [first, second])
    (related : frontierEquation request request.expected request.root value.pattern) :
    ⟨value.pattern, first, second⟩ ∈ splitCases request state declaration := by
  have object := certified_class_objects admitted certificate related
  have found := constructorArguments?_complete value object
  rw [arguments] at found
  apply List.mem_filterMap.mpr
  refine ⟨value.pattern,
    (certified_representatives_exact admitted certificate _).mpr related, ?_⟩
  simp only [splitCase?, found]

/-- The negative direction uses actual representative coverage and the
component answers inspected by the executable coverage test. -/
theorem readSplitCases_sound {request : Request} {state : State request}
    (admitted : Admitted request) {index : Nat} {declaration : GrammarRule}
    (lookup : request.plan.snapshot.language.terms[index]? = some declaration)
    (atom : TypeExpr → Nat → Pattern → Prop) (shape : BinaryShape)
    (first second : Formula) (budget : Nat) :
    ReadoutCorrect (readSplitCases request state declaration shape first second budget)
      (SplitHolds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (frontierEquation request request.expected) ⟨index, declaration⟩
        (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom shape.firstSort first)
        (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
          (frontierEquation request) atom shape.secondSort second) request.root) := by
  intro answer read
  cases answer with
  | true =>
      have found := readExistential_true read
      obtain ⟨candidate, member, observed⟩ := List.mem_map.mp found
      have components := (readSplitCase_sound admitted atom shape first second budget candidate
        true observed).mp rfl
      obtain ⟨represented, value, valueSame, arguments⟩ := splitCases_member member
      have related := representedPattern_equivalent represented
      constructor
      · intro _
        refine ⟨(mem_structuralFormers_iff _ _).mpr lookup, value, ?_,
          candidate.first, candidate.second, arguments, components⟩
        rw [valueSame]
        exact related
      · intro _; rfl
  | false =>
      obtain ⟨certificate, conclusive, noPositive⟩ := readExistential_false read
      constructor
      · intro impossible; cases impossible
      · intro holds
        obtain ⟨_, value, related, left, right, arguments, firstHolds, secondHolds⟩ := holds
        have member := splitCases_cover admitted certificate value arguments related
        have answerMember : readSplitCase request shape first second budget
            ⟨value.pattern, left, right⟩ ∈
            splitAnswers request state declaration shape first second budget :=
          List.mem_map.mpr ⟨_, member, rfl⟩
        obtain ⟨answer, observed⟩ := conclusive _ answerMember
        have positive := (readSplitCase_sound admitted atom shape first second budget
          ⟨value.pattern, left, right⟩ answer observed).mpr ⟨firstHolds, secondHolds⟩
        subst answer
        exfalso
        apply noPositive
        simpa only [observed] using answerMember

def readFrontierSplit (request : Request) (state : State request) (index : Nat)
    (first second : Formula) (budget : Nat) : Option Bool :=
  match request.plan.snapshot.language.terms[index]? with
  | none => none
  | some declaration =>
      if request.expected == .base declaration.category then
        match binaryShape? declaration with
        | none => none
        | some shape => readSplitCases request state declaration shape first second budget
      else none

theorem readFrontierSplit_sound {request : Request} {state : State request}
    (admitted : Admitted request) (atom : TypeExpr → Nat → Pattern → Prop)
    (index : Nat) (first second : Formula) (budget : Nat) :
    ReadoutCorrect (readFrontierSplit request state index first second budget)
      (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (frontierEquation request) atom request.expected (.split index first second) request.root) := by
  unfold readFrontierSplit
  cases lookup : request.plan.snapshot.language.terms[index]? with
  | none => simp [ReadoutCorrect]
  | some declaration =>
      dsimp only
      split
      · rename_i same
        have equal : request.expected = .base declaration.category := by
          simpa only [beq_iff_eq] using same
        simp only [equal]
        cases checked : binaryShape? declaration with
        | none => simp [ReadoutCorrect]
        | some shape =>
            dsimp only
            obtain ⟨arity, firstType, secondType⟩ := binaryShape?_sound checked
            have sound := readSplitCases_sound (state := state) admitted lookup atom
              shape first second budget
            simpa only [equal, holds_split_exact lookup arity firstType secondType]
              using sound
      · simp [ReadoutCorrect]

theorem checked_split_conclusive {request : Request} {state : State request}
    {declaration : GrammarRule} {shape : BinaryShape} {first second : Formula} {budget : Nat}
    (coverage : splitCoverage request state declaration shape first second budget = true) :
    ∃ answer, readSplitCases request state declaration shape first second budget = some answer :=
  existentialCoverage_conclusive coverage

end Mettapedia.OSLF.NativeTypes.Structural
