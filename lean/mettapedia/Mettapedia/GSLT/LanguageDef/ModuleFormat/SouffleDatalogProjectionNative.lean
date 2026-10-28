import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionNativeSlice
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! The projector's certified rule selection is an ordinary input to the
shared emitter. The authored structural operations have two-way agreement
with the independent evaluator, including whole program projection. Source
formation, literal interpretation and Datalog execution are separate joins. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Native

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

/-- The source provider is empty: projection uses only internal child steps. -/
def snapshot (freeTypes : List (String × TypeExpr)) : GeneralExecutionAdmission.Snapshot :=
  ⟨NativeSlice.language,freeTypes,{signatures := [], rows := []}⟩

def permissions : GeneralExecutionAdmission.Permissions :=
  {sites := .rootOnly, includeDerivedEquations := false}

def plan (freeTypes : List (String × TypeExpr)) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile (snapshot freeTypes) permissions

def spec (freeTypes : List (String × TypeExpr)) (expected : TypeExpr) : CompleteEmission.Spec :=
  ⟨plan freeTypes,[],expected,.standard⟩

theorem constant_lists_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (ConstantLists.call source) target ↔
      (Reference.constants? source).map Reference.groundTuple = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (ConstantLists.call source) from
      ⟨"ProjectConstants",[source],rfl,by decide +kernel⟩)]
  exact ConstantLists.reference_exact environment source target

theorem ground_atoms_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (GroundAtoms.call source) target ↔
      Reference.groundAtom? source = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (GroundAtoms.call source) from
      ⟨"ProjectGroundAtom",[source],rfl,by decide +kernel⟩)]
  exact GroundAtoms.reference_exact environment source target

theorem facts_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Facts.call source) target ↔
      Reference.fact? source = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Facts.call source) from
      ⟨"ProjectFact",[source],rfl,by decide +kernel⟩)]
  exact Facts.reference_exact environment source target

theorem terms_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Terms.call source) target ↔
      (Reference.term? source) = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Terms.call source) from
      ⟨"ProjectTerm",[source],rfl,by decide +kernel⟩)]
  exact Terms.reference_exact environment source target

theorem term_lists_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (TermLists.call source) target ↔
      (Reference.terms? source).map Reference.tuple = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (TermLists.call source) from
      ⟨"ProjectTerms",[source],rfl,by decide +kernel⟩)]
  exact TermLists.reference_exact environment source target

theorem atoms_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Atoms.call source) target ↔
      (Reference.atom? source).map Atoms.wrap = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Atoms.call source) from
      ⟨"ProjectAtom",[source],rfl,by decide +kernel⟩)]
  exact Atoms.reference_exact environment source target

theorem comparison_operators_exact (environment : Engine.RelationEnv) (source left right target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (ComparisonOperators.call source left right) target ↔
      Reference.comparisonOperator? source left right = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (ComparisonOperators.call source left right) from
      ⟨"ProjectComparisonOperator",[source,left,right],rfl,by decide +kernel⟩)]
  exact ComparisonOperators.reference_exact environment source left right target

theorem comparisons_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Comparisons.call source) target ↔
      Reference.comparison? source = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Comparisons.call source) from
      ⟨"ProjectComparison",[source],rfl,by decide +kernel⟩)]
  exact Comparisons.reference_exact environment source target

theorem positive_literals_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (PositiveLiterals.call source) target ↔
      Reference.positiveLiteral? source = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (PositiveLiterals.call source) from
      ⟨"ProjectPositiveLiteral",[source],rfl,by decide +kernel⟩)]
  exact PositiveLiterals.reference_exact environment source target

theorem bodies_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Bodies.call source) target ↔
      (Reference.body? source).map Reference.projectedBody = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Bodies.call source) from
      ⟨"ProjectBody",[source],rfl,by decide +kernel⟩)]
  exact Bodies.reference_exact environment source target

theorem attribute_types_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (AttributeTypes.call source) target ↔
      Reference.attributeType? source = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (AttributeTypes.call source) from
      ⟨"ProjectAttributeType",[source],rfl,by decide +kernel⟩)]
  exact AttributeTypes.reference_exact environment source target

theorem attributes_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Attributes.call source) target ↔
      Reference.attribute? source = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Attributes.call source) from
      ⟨"ProjectAttribute",[source],rfl,by decide +kernel⟩)]
  exact Attributes.reference_exact environment source target

theorem attribute_lists_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (AttributeLists.call source) target ↔
      (Reference.attributes? source).map Reference.projectedAttributes = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (AttributeLists.call source) from
      ⟨"ProjectAttributes",[source],rfl,by decide +kernel⟩)]
  exact AttributeLists.reference_exact environment source target

theorem relations_exact (environment : Engine.RelationEnv) (source target : Pattern) (attributes tail : List Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Relations.call source attributes tail) target ↔
      (Reference.relationsInto? source attributes tail).map Reference.program = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Relations.call source attributes tail) from
      ⟨"ProjectRelationsInto",[source,Reference.projectedAttributes attributes,Reference.program tail],rfl,by decide +kernel⟩)]
  exact Relations.reference_exact environment source target attributes tail

theorem items_exact (environment : Engine.RelationEnv) (source target : Pattern) (tail : List Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Items.call source tail) target ↔
      (Reference.itemInto? source tail).map Reference.program = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Items.call source tail) from
      ⟨"ProjectItemInto",[source,Reference.program tail],rfl,by decide +kernel⟩)]
  exact Items.reference_exact environment source target tail

theorem program_items_exact (environment : Engine.RelationEnv) (source target : Pattern) (tail : List Pattern) :
    ReferenceStep.Step environment NativeSlice.language (ProgramItems.call source tail) target ↔
      (Reference.itemsInto? source tail).map Reference.program = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (ProgramItems.call source tail) from
      ⟨"ProjectItemsInto",[source,Reference.program tail],rfl,by decide +kernel⟩)]
  exact ProgramItems.reference_exact environment source target tail

theorem program_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment NativeSlice.language (Program.call source) target ↔
      Reference.projectProgram? source = some target := by
  rw [NativeSlice.reference_exact environment
    (show NativeSlice.Calls (Program.call source) from
      ⟨"ProjectProgram",[source],rfl,by decide +kernel⟩)]
  exact Program.reference_exact environment source target

/-- A native receipt retains its declaration in the original authored module.
The two inherited inference rows precede the compiler-only selection. -/
theorem receipt_source_declaration {freeTypes : List (String × TypeExpr)}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {receipt : GeneralOccurrenceSemantics.Receipt}
    (valid : receipt.Valid (plan freeTypes) bound expected source) :
    ∃ rule index, NativeSlice.sourceLanguage.rewrites[index + 2]? = some rule ∧
      receipt.firing.job.declaration.declarationIndex = index ∧
      GeneralExecutionAdmission.rulePlan? (snapshot freeTypes) index rule =
        some receipt.firing.job.declaration := by
  obtain ⟨rule,index,member,_,compiled⟩ :=
    GeneralOccurrenceSemantics.Receipt.source_declaration valid
  have found := List.mk_mem_zipIdx_iff_getElem?.mp member
  have original : NativeSlice.sourceLanguage.rewrites[index + 2]? = some rule := by
    simpa only [snapshot,NativeSlice.language,List.getElem?_drop,Nat.add_comm] using found
  exact ⟨rule,index,original,(GeneralExecutionAdmission.rulePlan_readout compiled).1,compiled⟩

#print axioms constant_lists_exact
#print axioms ground_atoms_exact
#print axioms facts_exact
#print axioms program_exact
#print axioms receipt_source_declaration

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Native
