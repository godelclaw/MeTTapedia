import Mettapedia.Languages.HOLLight.MeTTa.InferenceHistory
import Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorizationControls

/-!
# Binary inference after actual source assumptions

These controls start with an empty source cache. Two ASSUME events publish
their records, then a binary inference consumes those returned records.
The source case expressions compose all three events without a trusted
initial proof cache.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.BinaryInferenceControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization Eval
open Effects (State)

def world : TheoryContext := SourceProfile.primitiveContext
def constants : Const → Atom := DeclarationTable.primitiveIdentity
def operators : Atom := CacheAuthorizationControls.operators
def declarations : Atom := CacheAuthorizationControls.declarations
def firstKey : Atom := .grounded (.string "first")
def secondKey : Atom := .grounded (.string "second")
def resultKey : Atom := .grounded (.string "result")

private theorem keys_different : (firstKey == secondKey) = false := by decide

private theorem boolean_formed : TypeFormed world.signature Ty.bool :=
  ContextControls.boolean_formed.mono (ContextControls.core_includes.trans
    (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))

private theorem function_registered : world.signature.typeOperators TypeOp.function = some 2 :=
  (ContextControls.core_includes.trans (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes)).1
    _ _ ContextControls.function_registered

private theorem equality_registered : world.signature.constants Const.equality =
    some (Ty.equality (.var ContextControls.equalityParameter)) :=
  (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes).2 _ _
    (ContextControls.baseContext.addConstant_registered _ _ ContextControls.equality_schema_formed _)

private theorem boolean_resolved : TypeFormation.Resolved world.signature Ty.bool := by
  have formed := boolean_formed
  simp only [Ty.bool, TypeFormed] at formed
  simp only [Ty.bool, TypeFormation.Resolved]
  exact ⟨⟨0, formed.1⟩, by simp⟩

private theorem function_resolved {domain codomain : Ty}
    (left : TypeFormation.Resolved world.signature domain)
    (right : TypeFormation.Resolved world.signature codomain) :
    TypeFormation.Resolved world.signature (.function domain codomain) := by
  simp only [Ty.function, TypeFormation.Resolved]
  refine ⟨⟨2, function_registered⟩, ?_⟩
  intro type member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

def termVar (name : String) (type : Ty) : CheckedSourceTerm :=
  CheckedSourceTerm.ofVariable ⟨Name.global name, type⟩

def equation (left right : String) (operand : Ty) : CheckedSourceTerm :=
  ⟨.app (.app (.const Const.equality (Ty.equality operand)) (.var (Name.global left) operand))
      (.var (Name.global right) operand), Ty.bool, by
    simp [SourceTerm.inferType, Ty.equality, Ty.destFunction?_function]⟩

private theorem variable_resolved (name : String) (type : Ty)
    (resolved : TypeFormation.Resolved world.signature type) :
    TermReading.SourceResolved world.signature (termVar name type).source := by
  simp only [termVar, CheckedSourceTerm.ofVariable, TermReading.SourceResolved]
  exact ⟨rfl, resolved⟩

private theorem variable_formed (name : String) (type : Ty)
    (formed : TypeFormed world.signature type) :
    AnnotationsFormed world.signature (termVar name type).canonical.term := by
  simpa [termVar, CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex] using
    (AnnotationsFormed.free (sourceVar := ⟨Name.global name, type⟩) formed)

private theorem equation_resolved (left right : String) (operand : Ty)
    (resolved : TypeFormation.Resolved world.signature operand) :
    TermReading.SourceResolved world.signature (equation left right operand).source := by
  simp only [equation, TermReading.SourceResolved]
  exact ⟨⟨function_resolved resolved (function_resolved resolved boolean_resolved),
    ⟨rfl, resolved⟩⟩, ⟨rfl, resolved⟩⟩

private theorem equation_formed (left right : String) (operand : Ty)
    (formed : TypeFormed world.signature operand) :
    AnnotationsFormed world.signature (equation left right operand).canonical.term := by
  have result := PrimitiveEqualityFormation.equation_annotations world.signature ContextControls.equalityParameter
    operand function_registered boolean_formed formed equality_registered
    (termVar left operand).canonical.term (termVar right operand).canonical.term
    (variable_formed left operand formed) (variable_formed right operand formed)
  simpa [equation, termVar, CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB,
    boundIndex, CanonicalTerm.equalityDB] using result

def assumeRequest (source : CheckedSourceTerm) : Atom :=
  .expression [.symbol "ASSUME", TermReading.sourceAtom source.source]

def binaryRequest (kind : String) : Atom := .expression [.symbol kind, firstKey, secondKey]

def stateValue (cache : Cache) (receipts : List ReceiptKeys.Entry) : Atom :=
  ProofLookup.sourceState operators declarations (.symbol "HOL:Nil") (ReceiptKeys.table receipts) (entries constants cache)

def bindings (left right : CheckedSourceTerm) (kind : String) : Subst :=
  [("request3", binaryRequest kind), ("request2", assumeRequest right), ("request1", assumeRequest left),
    ("resultKey", resultKey), ("secondKey", secondKey), ("firstKey", firstKey), ("state", stateValue [] [])]

def firstState (source : CheckedSourceTerm) (record : Record) : Atom :=
  stateValue [(firstKey, record)] [⟨firstKey, assumeRequest source, []⟩]

def secondState (left right : CheckedSourceTerm) (first second : Record) : Atom :=
  stateValue [(secondKey, second), (firstKey, first)]
    [⟨secondKey, assumeRequest right, []⟩, ⟨firstKey, assumeRequest left, []⟩]

def finalState (left right : CheckedSourceTerm) (kind : String) (first second result : Record) : Atom :=
  stateValue [(resultKey, result), (secondKey, second), (firstKey, first)]
    [⟨resultKey, binaryRequest kind, [firstKey, secondKey]⟩,
      ⟨secondKey, assumeRequest right, []⟩, ⟨firstKey, assumeRequest left, []⟩]

def afterFirstBindings (left right : CheckedSourceTerm) (kind : String) (first : Record) : Subst :=
  ("afterFirst", firstState left first) :: bindings left right kind

def afterSecondBindings (left right : CheckedSourceTerm) (kind : String) (first second : Record) : Subst :=
  ("afterSecond", secondState left right first second) :: afterFirstBindings left right kind first

def threeEvents : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:step", .var "state", .var "firstKey", .var "request1"],
  .expression [
    .expression [.expression [.symbol "Some", .var "afterFirst"],
      .expression [.symbol "case",
        .expression [.symbol "hol-light:step", .var "afterFirst", .var "secondKey", .var "request2"],
        .expression [
          .expression [.expression [.symbol "Some", .var "afterSecond"],
            .expression [.symbol "hol-light:step", .var "afterSecond", .var "resultKey", .var "request3"]],
          .expression [.var "secondRefused", .symbol "None"]]]],
    .expression [.var "firstRefused", .symbol "None"]]]

private theorem compose_three (left right : CheckedSourceTerm) (kind : String)
    (first second result : Record) (state : State)
    (firstEvent : PureReturns program (bindings left right kind) state
      (.expression [.symbol "hol-light:step", .var "state", .var "firstKey", .var "request1"]) state
      (.expression [.symbol "Some", firstState left first]))
    (secondEvent : PureReturns program (afterFirstBindings left right kind first) state
      (.expression [.symbol "hol-light:step", .var "afterFirst", .var "secondKey", .var "request2"]) state
      (.expression [.symbol "Some", secondState left right first second]))
    (lastEvent : PureReturns program (afterSecondBindings left right kind first second) state
      (.expression [.symbol "hol-light:step", .var "afterSecond", .var "resultKey", .var "request3"]) state
      (.expression [.symbol "Some", finalState left right kind first second result])) :
    PureReturns program (bindings left right kind) state threeEvents state
      (.expression [.symbol "Some", finalState left right kind first second result]) := by
  let innerCases : SpaceSemantics.Cases :=
    [(.expression [.symbol "Some", .var "afterSecond"],
      .expression [.symbol "hol-light:step", .var "afterSecond", .var "resultKey", .var "request3"]),
      (.var "secondRefused", .symbol "None")]
  have inner : PureReturns program (afterFirstBindings left right kind first) state
      (.expression [.symbol "case",
        .expression [.symbol "hol-light:step", .var "afterFirst", .var "secondKey", .var "request2"],
        .expression (innerCases.map (fun row => .expression [row.1, row.2]))]) state (.expression [.symbol "Some", finalState left right kind first second result]) := by
    apply case_returns program (afterFirstBindings left right kind first)
      (afterSecondBindings left right kind first second) state state state _
      (.expression [.symbol "Some", secondState left right first second])
      (.expression [.symbol "hol-light:step", .var "afterSecond", .var "resultKey", .var "request3"])
      _ _ innerCases (read_cases_encoded innerCases) secondEvent _ lastEvent
    simp [innerCases, afterFirstBindings, afterSecondBindings, bindings, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  let outerCases : SpaceSemantics.Cases :=
    [(.expression [.symbol "Some", .var "afterFirst"],
      .expression [.symbol "case",
        .expression [.symbol "hol-light:step", .var "afterFirst", .var "secondKey", .var "request2"],
        .expression (innerCases.map (fun row => .expression [row.1, row.2]))]), (.var "firstRefused", .symbol "None")]
  unfold threeEvents
  apply case_returns program (bindings left right kind) (afterFirstBindings left right kind first)
    state state state _ (.expression [.symbol "Some", firstState left first]) _ _ _ outerCases
    (read_cases_encoded outerCases) firstEvent _ inner
  simp [outerCases, afterFirstBindings, bindings, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem two_assumptions (left right : CheckedSourceTerm) (kind : String) (state : State)
    (leftResolved : TermReading.SourceResolved world.signature left.source)
    (rightResolved : TermReading.SourceResolved world.signature right.source)
    (leftFormed : AnnotationsFormed world.signature left.canonical.term)
    (rightFormed : AnnotationsFormed world.signature right.canonical.term)
    (leftBoolean : left.ty = Ty.bool) (rightBoolean : right.ty = Ty.bool) :
    ∃ first second : Record,
      first.conclusion = left.canonical ∧ second.conclusion = right.canonical ∧
      first.hypotheses = [left.canonical] ∧ second.hypotheses = [right.canonical] ∧
      first.dependencies = [] ∧ second.dependencies = [] ∧
      Valid emptyAxiomPolicy world [(secondKey, second), (firstKey, first)] ∧
      PureReturns program (bindings left right kind) state
        (.expression [.symbol "hol-light:step", .var "state", .var "firstKey", .var "request1"]) state
        (.expression [.symbol "Some", firstState left first]) ∧
      PureReturns program (afterFirstBindings left right kind first) state
        (.expression [.symbol "hol-light:step", .var "afterFirst", .var "secondKey", .var "request2"]) state
        (.expression [.symbol "Some", secondState left right first second]) := by
  obtain ⟨first, _, firstValid, firstHyps, firstDeps, _, firstSemantics, firstEvent⟩ :=
    authored_assume_preserves_valid emptyAxiomPolicy world DeclarationTable.sourcePrimitive
      (fun _ => .symbol "HOL:Primitive") constants left leftResolved leftFormed
      (leftBoolean ▸ boolean_formed) boolean_formed leftBoolean
      [] (empty_valid _ _) [] firstKey (.symbol "HOL:Nil") rfl rfl
      (bindings left right kind) state "state" "firstKey" "request1" rfl rfl rfl
  obtain ⟨second, _, secondValid, secondHyps, secondDeps, _, secondSemantics, secondEvent⟩ :=
    authored_assume_preserves_valid emptyAxiomPolicy world DeclarationTable.sourcePrimitive
      (fun _ => .symbol "HOL:Primitive") constants right rightResolved rightFormed
      (rightBoolean ▸ boolean_formed) boolean_formed rightBoolean
      [(firstKey, first)] firstValid [⟨firstKey, assumeRequest left, []⟩] secondKey (.symbol "HOL:Nil")
      (by simp [ReceiptKeys.presentB, firstKey, secondKey]) (by simp [entries, firstKey, secondKey])
      (afterFirstBindings left right kind first) state "afterFirst" "secondKey" "request2" rfl rfl rfl
  exact ⟨first, second, firstSemantics.2.2.2, secondSemantics.2.2.2, firstHyps, secondHyps,
    firstDeps, secondDeps, secondValid, firstEvent, secondEvent⟩

private theorem equation_view (left right : String) (operand : Ty) :
    CanonicalTerm.EqualityViewSemantics (equation left right operand).canonical
      (termVar left operand).canonical (termVar right operand).canonical := by
  refine ⟨rfl, ?_⟩
  simp [equation, termVar, CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical,
    SourceTerm.toDB, boundIndex, CanonicalTerm.equalityDB]

/-- Source assumptions of two distinct equations are actually published
before MK_COMB reads them. The resulting equation is not reflexivity. -/
theorem authored_assumptions_then_mk_comb (state : State) :
    let functionEquation := equation "f" "g" (.function Ty.bool Ty.bool)
    let argumentEquation := equation "x" "y" Ty.bool
    ∃ first second result : Record,
      first.conclusion = functionEquation.canonical ∧ second.conclusion = argumentEquation.canonical ∧
      first.hypotheses = [functionEquation.canonical] ∧ second.hypotheses = [argumentEquation.canonical] ∧
      result.conclusion.term = CanonicalTerm.equalityDB Ty.bool
        (.app (termVar "f" (.function Ty.bool Ty.bool)).canonical.term (termVar "x" Ty.bool).canonical.term)
        (.app (termVar "g" (.function Ty.bool Ty.bool)).canonical.term (termVar "y" Ty.bool).canonical.term) ∧
      result.dependencies = [] ∧ TheoryDerives emptyAxiomPolicy world result.fact ∧
      Valid emptyAxiomPolicy world [(resultKey, result), (secondKey, second), (firstKey, first)] ∧
      PureReturns program (bindings functionEquation argumentEquation "MK_COMB") state threeEvents state
        (.expression [.symbol "Some", finalState functionEquation argumentEquation "MK_COMB" first second result]) := by
  dsimp only
  let functionEquation := equation "f" "g" (.function Ty.bool Ty.bool)
  let argumentEquation := equation "x" "y" Ty.bool
  have functionFormed := TypeFormed.function world.signature function_registered boolean_formed boolean_formed
  obtain ⟨first, second, firstConclusion, secondConclusion, firstHyps, secondHyps, firstDeps, secondDeps,
      valid, firstEvent, secondEvent⟩ := two_assumptions functionEquation argumentEquation "MK_COMB" state
    (equation_resolved "f" "g" _ (function_resolved boolean_resolved boolean_resolved))
    (equation_resolved "x" "y" _ boolean_resolved)
    (equation_formed "f" "g" _ functionFormed) (equation_formed "x" "y" _ boolean_formed) rfl rfl
  have functionView : CanonicalTerm.EqualityViewSemantics first.conclusion
      (termVar "f" (.function Ty.bool Ty.bool)).canonical (termVar "g" (.function Ty.bool Ty.bool)).canonical := by
    rw [firstConclusion]
    exact equation_view "f" "g" _
  have argumentView : CanonicalTerm.EqualityViewSemantics second.conclusion
      (termVar "x" Ty.bool).canonical (termVar "y" Ty.bool).canonical := by
    rw [secondConclusion]
    exact equation_view "x" "y" _
  obtain ⟨result, conclusion, _, dependencies, _, _, derived, finalValid, returned⟩ :=
    InferenceHistory.authored_mk_comb_preserves_valid emptyAxiomPolicy world constants
      (DeclarationTable.primitiveIdentity_identifies _) rfl function_registered
      ContextControls.equalityParameter equality_registered [(secondKey, second), (firstKey, first)] valid
      first second firstKey secondKey (by simp only [List.lookup, keys_different, BEq.rfl]) (by simp)
      (termVar "f" (.function Ty.bool Ty.bool)).canonical (termVar "g" (.function Ty.bool Ty.bool)).canonical
      (termVar "x" Ty.bool).canonical (termVar "y" Ty.bool).canonical Ty.bool Ty.bool
      functionView argumentView rfl rfl
      [⟨secondKey, assumeRequest argumentEquation, []⟩, ⟨firstKey, assumeRequest functionEquation, []⟩]
      operators declarations (.symbol "HOL:Nil") resultKey
      (by simp [ReceiptKeys.presentB, resultKey, firstKey, secondKey])
      (by simp [entries, resultKey, firstKey, secondKey])
      (afterSecondBindings functionEquation argumentEquation "MK_COMB" first second) state
      "afterSecond" "resultKey" "request3" rfl rfl rfl
  refine ⟨first, second, result, firstConclusion, secondConclusion, firstHyps, secondHyps,
    conclusion, ?_, derived, finalValid, compose_three functionEquation argumentEquation "MK_COMB"
      first second result state firstEvent secondEvent returned⟩
  simpa [CacheUnion.dependencies, firstDeps, secondDeps, List.KeyedUnion.merge] using dependencies

/-- EQ_MP consumes the two actual assumption events, retaining both
hypotheses while changing the conclusion from p to the distinct q. -/
theorem authored_assumptions_then_eq_mp (state : State) :
    let equalitySource := equation "p" "q" Ty.bool
    let premiseSource := termVar "p" Ty.bool
    ∃ first second result : Record,
      first.conclusion = equalitySource.canonical ∧ second.conclusion = premiseSource.canonical ∧
      first.hypotheses = [equalitySource.canonical] ∧ second.hypotheses = [premiseSource.canonical] ∧
      result.conclusion = (termVar "q" Ty.bool).canonical ∧ result.dependencies = [] ∧
      TheoryDerives emptyAxiomPolicy world result.fact ∧
      Valid emptyAxiomPolicy world [(resultKey, result), (secondKey, second), (firstKey, first)] ∧
      PureReturns program (bindings equalitySource premiseSource "EQ_MP") state threeEvents state
        (.expression [.symbol "Some", finalState equalitySource premiseSource "EQ_MP" first second result]) := by
  dsimp only
  let equalitySource := equation "p" "q" Ty.bool
  let premiseSource := termVar "p" Ty.bool
  obtain ⟨first, second, firstConclusion, secondConclusion, firstHyps, secondHyps, firstDeps, secondDeps,
      valid, firstEvent, secondEvent⟩ := two_assumptions equalitySource premiseSource "EQ_MP" state
    (equation_resolved "p" "q" _ boolean_resolved) (variable_resolved "p" _ boolean_resolved)
    (equation_formed "p" "q" _ boolean_formed) (variable_formed "p" _ boolean_formed) rfl rfl
  have view : CanonicalTerm.EqualityViewSemantics first.conclusion second.conclusion
      (termVar "q" Ty.bool).canonical := by
    rw [firstConclusion, secondConclusion]
    exact equation_view "p" "q" _
  obtain ⟨result, conclusion, _, dependencies, _, _, derived, finalValid, returned⟩ :=
    InferenceHistory.authored_eq_mp_preserves_valid emptyAxiomPolicy world constants
      (DeclarationTable.primitiveIdentity_identifies _) rfl function_registered
      [(secondKey, second), (firstKey, first)] valid first second firstKey secondKey
      (by simp only [List.lookup, keys_different, BEq.rfl]) (by simp) (termVar "q" Ty.bool).canonical view
      [⟨secondKey, assumeRequest premiseSource, []⟩, ⟨firstKey, assumeRequest equalitySource, []⟩]
      operators declarations (.symbol "HOL:Nil") resultKey
      (by simp [ReceiptKeys.presentB, resultKey, firstKey, secondKey])
      (by simp [entries, resultKey, firstKey, secondKey])
      (afterSecondBindings equalitySource premiseSource "EQ_MP" first second) state
      "afterSecond" "resultKey" "request3" rfl rfl rfl
  refine ⟨first, second, result, firstConclusion, secondConclusion, firstHyps, secondHyps,
    conclusion, ?_, derived, finalValid, compose_three equalitySource premiseSource "EQ_MP"
      first second result state firstEvent secondEvent returned⟩
  simpa [CacheUnion.dependencies, firstDeps, secondDeps, List.KeyedUnion.merge] using dependencies

theorem mk_comb_operands_distinct :
    (.app (termVar "f" (.function Ty.bool Ty.bool)).canonical.term (termVar "x" Ty.bool).canonical.term : DBTerm) ≠
      .app (termVar "g" (.function Ty.bool Ty.bool)).canonical.term (termVar "y" Ty.bool).canonical.term := by
  simp [termVar, CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex, Name.global]

theorem eq_mp_changes_conclusion : (termVar "p" Ty.bool).canonical ≠ (termVar "q" Ty.bool).canonical := by
  intro same
  have terms := congrArg CanonicalTerm.term same
  simp [termVar, CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex, Name.global] at terms

/-- Two independently published assumptions of p are read at their two
source addresses. Deduction removes both hypothesis occurrences and earns
p=p without assumptions or axiom dependencies. -/
theorem authored_assumptions_then_deduct (state : State) :
    let source := termVar "p" Ty.bool
    ∃ first second result : Record,
      first.hypotheses = [source.canonical] ∧ second.hypotheses = [source.canonical] ∧
      result.conclusion.term = CanonicalTerm.equalityDB Ty.bool source.canonical.term source.canonical.term ∧
      result.hypotheses = [] ∧ result.dependencies = [] ∧
      TheoryDerives emptyAxiomPolicy world result.fact ∧
      Valid emptyAxiomPolicy world [(resultKey, result), (secondKey, second), (firstKey, first)] ∧
      PureReturns program (bindings source source "DEDUCT_ANTISYM_RULE") state threeEvents state
        (.expression [.symbol "Some", finalState source source "DEDUCT_ANTISYM_RULE" first second result]) := by
  dsimp only
  let source := termVar "p" Ty.bool
  obtain ⟨first, second, firstConclusion, secondConclusion, firstHyps, secondHyps, firstDeps, secondDeps,
      valid, firstEvent, secondEvent⟩ := two_assumptions source source "DEDUCT_ANTISYM_RULE" state
    (variable_resolved "p" _ boolean_resolved) (variable_resolved "p" _ boolean_resolved)
    (variable_formed "p" _ boolean_formed) (variable_formed "p" _ boolean_formed) rfl rfl
  obtain ⟨result, conclusion, hypotheses, dependencies, _, _, derived, finalValid, returned⟩ :=
    InferenceHistory.authored_deduct_preserves_valid emptyAxiomPolicy world constants
      (DeclarationTable.primitiveIdentity_identifies _) rfl function_registered
      ContextControls.equalityParameter equality_registered [(secondKey, second), (firstKey, first)] valid
      first second firstKey secondKey (by simp only [List.lookup, keys_different, BEq.rfl]) (by simp)
      [⟨secondKey, assumeRequest source, []⟩, ⟨firstKey, assumeRequest source, []⟩]
      operators declarations (.symbol "HOL:Nil") resultKey
      (by simp [ReceiptKeys.presentB, resultKey, firstKey, secondKey])
      (by simp [entries, resultKey, firstKey, secondKey])
      (afterSecondBindings source source "DEDUCT_ANTISYM_RULE" first second) state
      "afterSecond" "resultKey" "request3" rfl rfl rfl
  refine ⟨first, second, result, firstHyps, secondHyps, ?_, ?_, ?_, derived, finalValid,
    compose_three source source "DEDUCT_ANTISYM_RULE" first second result state firstEvent secondEvent returned⟩
  · simpa only [firstConclusion, secondConclusion] using conclusion
  · simpa [CacheDischarge.hypotheses, firstConclusion, secondConclusion, firstHyps, secondHyps,
      List.KeyedUnion.merge] using hypotheses
  · simpa [CacheUnion.dependencies, firstDeps, secondDeps, List.KeyedUnion.merge] using dependencies

/-- Discharge does not silently remove an unrelated hypothesis: the two
opposite conclusions must actually match the occurrences being removed. -/
theorem distinct_assumptions_are_retained :
    let left : Record := ⟨[(termVar "p" Ty.bool).canonical], (termVar "p" Ty.bool).canonical, [], .symbol "ASSUME"⟩
    let right : Record := ⟨[(termVar "q" Ty.bool).canonical], (termVar "q" Ty.bool).canonical, [], .symbol "ASSUME"⟩
    (CacheDischarge.hypotheses constants left right).toFinset =
      {(termVar "p" Ty.bool).canonical, (termVar "q" Ty.bool).canonical} := by
  dsimp only
  have formed (name : String) :
      TheoremFormed world.signature
        (Record.fact ⟨[(termVar name Ty.bool).canonical], (termVar name Ty.bool).canonical, [], .symbol "ASSUME"⟩) := by
    refine ⟨⟨variable_formed name _ boolean_formed, ?_⟩, ?_⟩
    · intro term member
      simp [Record.fact] at member
      exact member ▸ variable_formed name _ boolean_formed
    · simp [Record.fact]
  have support := CacheDischarge.hypotheses_support world constants (DeclarationTable.primitiveIdentity_identifies _)
    ⟨[(termVar "p" Ty.bool).canonical], (termVar "p" Ty.bool).canonical, [], .symbol "ASSUME"⟩
    ⟨[(termVar "q" Ty.bool).canonical], (termVar "q" Ty.bool).canonical, [], .symbol "ASSUME"⟩
    (formed "p") (formed "q")
  simpa [Record.fact, eq_mp_changes_conclusion, Ne.symm eq_mp_changes_conclusion] using support

end Mettapedia.Languages.HOLLight.MeTTa.BinaryInferenceControls
