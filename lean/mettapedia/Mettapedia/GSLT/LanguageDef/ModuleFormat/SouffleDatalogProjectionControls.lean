import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionOrigins
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionConstantTerm

/-! Structural projection controls: grouped declaration order, duplicate
occurrences, exact payload copying and separating refusal cases. These
controls do not grant lexical, static or native execution admission. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Reference

#guard language.validate.isEmpty

-- The first-order flow profile refuses the inherited quantified kernel rule.
#guard (language.executionFlowErrors []).map (·.message) ==
  ["forAll over `B` is unsupported by this execution-flow profile"]

def trivia : Pattern := .apply "dl-src:trivia-empty" []

def directiveSpace : Pattern := .apply "dl-src:directive-space"
  [ScalarCore.wordLeaf ⟨8, by decide +kernel⟩ ⟨32, by decide⟩, trivia]

def sourceItems (items : List Pattern) : Pattern :=
  items.foldr (fun item rest => .apply "dl-src:items-more" [item, trivia, rest])
    (.apply "dl-src:items-empty" [])

def grouped (first second : Pattern) : Pattern :=
  .apply "dl-src:item-declaration" [.apply "dl-src:declaration"
    [directiveSpace,
      .apply "dl-src:relations-more" [first,trivia,trivia,.apply "dl-src:relations-one" [second]],
      trivia,trivia,.apply "dl-src:attributes-empty" []]]

def sourceFact (name payload : Pattern) : Pattern :=
  .apply "dl-src:item-fact" [.apply "dl-src:fact"
    [.apply "dl-src:ground-atom" [name,trivia,trivia,
      .apply "dl-src:constants-one" [.apply "dl-src:constant-integer" [payload],trivia]],trivia]]

def sourceOutput (name : Pattern) : Pattern :=
  .apply "dl-src:item-output" [.apply "dl-src:output" [directiveSpace,name]]

def sourceProgram (first second name payload : Pattern) : Pattern :=
  .apply "dl-src:program" [trivia, sourceItems
    [grouped first second, sourceFact name payload, sourceFact name payload, sourceOutput name]]

def expectedFact (name payload : Pattern) : Pattern :=
  .apply "GroundFact" [relation name, groundTuple [.apply "IntegerValue" [payload]]]

def expectedStatements (first second name payload : Pattern) : List Pattern :=
  [declaration first [], declaration second [], expectedFact name payload,
    expectedFact name payload, .apply "OutputRelation" [relation name]]

theorem grouped_order_and_duplicates (first second name payload : Pattern) :
    projectProgram? (sourceProgram first second name payload) =
      some (program (expectedStatements first second name payload)) := by
  rfl

theorem origins_preserve_item_and_group_positions (first second name payload : Pattern) :
    (Origins.program? (sourceProgram first second name payload)).map (List.map (·.origin)) =
      some [⟨0,0⟩,⟨0,1⟩,⟨1,0⟩,⟨2,0⟩,⟨3,0⟩] := by
  simp [Origins.program?, Origins.items?, Origins.locate, sourceProgram, sourceItems,
    grouped, sourceFact, sourceOutput, trivia, itemInto?, attributes?, relationsInto?, fact?,
    groundAtom?, constants?, constant?, Option.bind_eq_bind]

theorem duplicate_facts_have_distinct_origins :
    (StatementOrigin.mk 1 0) ≠ StatementOrigin.mk 2 0 := by decide

theorem wrong_outer_program_refused : projectProgram? (.apply "Program" [vector []]) = none := rfl

theorem malformed_constant_refused (environment : Engine.RelationEnv) (target : Pattern) :
    ¬ReferenceStep.Step environment language
      (.apply "ProjectConstant" [.apply "dl-src:constant-integer" []]) target := by
  rw [Constants.reference_exact]
  change ¬(none = some target)
  intro impossible
  cases impossible

theorem constant_cannot_change_kind (environment : Engine.RelationEnv) (payload : Pattern) :
    ¬ReferenceStep.Step environment language (Constants.call .integer payload)
      (Constants.result .symbol payload) := by
  rw [Constants.step_exact]
  simp [Constants.result, Constants.targetHead]

theorem missing_child_refused (environment : Engine.RelationEnv) (target : Pattern) :
    ¬ReferenceStep.Step environment language
      (ConstantTerm.call (.apply "dl-src:constant-integer" [])) target := by
  rw [ConstantTerm.reference_exact]
  simp [constant?]

theorem conditional_projection (environment : Engine.RelationEnv) (payload : Pattern) :
    ReferenceStep.Step environment language
      (ConstantTerm.call (.apply "dl-src:constant-integer" [payload]))
      (ConstantTerm.result (.apply "IntegerValue" [payload])) :=
  ConstantTerm.step environment rfl

#print axioms grouped_order_and_duplicates
#print axioms origins_preserve_item_and_group_positions
#print axioms malformed_constant_refused
#print axioms constant_cannot_change_kind
#print axioms missing_child_refused
#print axioms conditional_projection

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Controls
