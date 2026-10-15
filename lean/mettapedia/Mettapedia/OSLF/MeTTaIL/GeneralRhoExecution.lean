import Mettapedia.OSLF.MeTTaIL.GeneralRhoReflection
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

/-!
# Typed original COMM receipts in the selected execution environment

This family retains the actual source body, contextual captures and selected
bag positions. The completed RHS uses the selected reflective operation. Its
source and target satisfy the actual grammar checker in arbitrary ambient
contexts. The independent firing then yields a checked executable receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open GeneralTypedSites GeneralScopedMatchMachine

private theorem open_of_type {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr} (typed : HasType language free bound pattern type)
    (represented : Represented pattern) : OpenPatternWellSorted language free bound type pattern :=
  ⟨typed, represented.1, represented.2, typed.isWellScopedAt⟩

theorem input_represented {channel body : Pattern}
    (channelRepresented : Represented channel) (bodyRepresented : Represented body) :
    Represented (input channel body) := by
  apply (represented_apply_iff _ _).mpr
  intro pattern member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact channelRepresented
  · simpa [Represented, Pattern.hasCanonicalBinderMetadata, isObjectPattern] using bodyRepresented

theorem output_represented {channel payload : Pattern}
    (channelRepresented : Represented channel) (payloadRepresented : Represented payload) :
    Represented (output channel payload) := by
  apply (represented_apply_iff _ _).mpr
  intro pattern member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact channelRepresented
  · exact payloadRepresented

theorem source_represented {channel body payload : Pattern} {rest : List Pattern}
    (channelRepresented : Represented channel) (bodyRepresented : Represented body)
    (payloadRepresented : Represented payload) (restRepresented : ∀ pattern ∈ rest, Represented pattern) :
    Represented (source channel body payload rest) := by
  apply (represented_collection_iff _ _).mpr
  intro pattern member
  simp only [List.mem_cons] at member
  rcases member with rfl | rfl | member
  · exact input_represented channelRepresented bodyRepresented
  · exact output_represented channelRepresented payloadRepresented
  · exact restRepresented pattern member

theorem captured_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : HasType language free bound channel (.base "Name"))
    (bodyTyped : HasType language free (.base "Name" :: bound) body (.base "Proc"))
    (payloadTyped : HasType language free bound payload (.base "Proc"))
    (restTyped : ElementsHaveType language free bound rest (.base "Proc")) :
    ConditionalEquationExecution.AssignmentTyped language free bound comm scopedCommBindingSpec
      (captured bound.length channel body payload rest) := by
  intro name value member
  simp only [captured, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · cases same
    exact ⟨[], .collection .hashBag (.base "Proc"), by decide +kernel, rfl, rfl, rfl,
      .collection restTyped⟩
  · cases same
    exact ⟨[], .base "Proc", by decide +kernel, rfl, rfl, rfl, payloadTyped⟩
  · cases same
    exact ⟨[.base "Name"], .base "Proc", by decide +kernel, rfl, rfl, rfl, bodyTyped⟩
  · cases same
    exact ⟨[], .base "Name", by decide +kernel, rfl, rfl, rfl, channelTyped⟩

theorem captured_objects {ambient : Nat} {channel body payload : Pattern} {rest : List Pattern}
    (channelRepresented : Represented channel) (bodyRepresented : Represented body)
    (payloadRepresented : Represented payload) (restRepresented : ∀ pattern ∈ rest, Represented pattern) :
    ConditionalEquationExecution.AssignmentObjects (captured ambient channel body payload rest) := by
  intro name value member
  simp only [captured, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · cases same
    exact ((represented_collection_iff .hashBag rest).mpr restRepresented).2
  · cases same
    exact payloadRepresented.2
  · cases same
    exact bodyRepresented.2
  · cases same
    exact channelRepresented.2

theorem root_firing {bound : List TypeExpr} {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : OpenPatternWellSorted language snapshot.free bound (.base "Name") channel)
    (bodyTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Proc") body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 1) body = true)
    (names : ReflectiveInstantiation.namesAdmitted
      rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language snapshot.free bound (.base "Proc") payload)
    (restTyped : ElementsHaveType language snapshot.free bound rest (.base "Proc"))
    (restRepresented : ∀ pattern ∈ rest, Represented pattern) :
    GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound (.base "Proc")
      (source channel body payload rest) 0 commTrace
      (captured bound.length channel body payload rest)
      (captured bound.length channel body payload rest) []
      (.collection .hashBag (reflectiveBody body payload :: rest) none) := by
  have sourceTyped := open_of_type (source_typed channelTyped.1 bodyTyped.1 payloadTyped.1 restTyped)
    (source_represented ⟨channelTyped.2.1, channelTyped.2.2.1⟩
      ⟨bodyTyped.2.1, bodyTyped.2.2.1⟩ ⟨payloadTyped.2.1, payloadTyped.2.2.1⟩ restRepresented)
  have targetBody := reflective_body_open bodyTyped sealed names payloadTyped
  have targetTyped := open_of_type (parallel_typed (.cons targetBody.1 restTyped))
    ((represented_collection_iff _ _).mpr (by
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨targetBody.2.1, targetBody.2.2.1⟩
      · exact restRepresented pattern member))
  have position : plan.rules[0]? = some declaration := by rw [compiled_rules]; rfl
  have captureTyped := captured_typed channelTyped.1 bodyTyped.1 payloadTyped.1 restTyped
  have captureObjects := captured_objects (ambient := bound.length) ⟨channelTyped.2.1, channelTyped.2.2.1⟩
    ⟨bodyTyped.2.1, bodyTyped.2.2.1⟩ ⟨payloadTyped.2.1, payloadTyped.2.2.1⟩ restRepresented
  refine .fire (GeneralPlanEnvironment.selected_rule plan position)
    (GeneralPlanEnvironment.selected_specification plan position) comm_admitted
    ((GeneralPlanEnvironment.typing_iff plan _ _ _).mpr sourceTyped)
    (source_matching channelTyped.1.isWellScopedAt (by simpa using bodyTyped.1.isWellScopedAt)
      payloadTyped.1.isWellScopedAt restTyped.isWellScopedListAt) ?_ .nil
    (reflective_reduct (by simpa using bodyTyped.1.isWellScopedAt)
      payloadTyped.1.isWellScopedAt restTyped.isWellScopedListAt)
    ((GeneralPlanEnvironment.typing_iff plan _ _ _).mpr targetTyped)
  refine ⟨?_, captureObjects⟩
  intro name value member
  obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, typed⟩ := captureTyped name value member
  exact ⟨dependencies, expected, declared, sorted, metadata, ambient,
    GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan).symm typed⟩

def rootReceipt (bound : List TypeExpr) (channel body payload : Pattern) (rest : List Pattern) :
    GeneralRuleJobs.Receipt where
  job := ⟨0, declaration, .here bound (.base "Proc") (source channel body payload rest)⟩
  matcherTrace := commTrace
  captured := captured bound.length channel body payload rest
  completed := captured bound.length channel body payload rest
  premiseHistory := []
  localTarget := .collection .hashBag (reflectiveBody body payload :: rest) none
  target := .collection .hashBag (reflectiveBody body payload :: rest) none

theorem root_receipt_valid {bound : List TypeExpr} {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : OpenPatternWellSorted language snapshot.free bound (.base "Name") channel)
    (bodyTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Proc") body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 1) body = true)
    (names : ReflectiveInstantiation.namesAdmitted
      rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language snapshot.free bound (.base "Proc") payload)
    (restTyped : ElementsHaveType language snapshot.free bound rest (.base "Proc"))
    (restRepresented : ∀ pattern ∈ rest, Represented pattern) :
    (rootReceipt bound channel body payload rest).Valid plan bound (.base "Proc")
      (source channel body payload rest) := by
  have firing := root_firing channelTyped bodyTyped sealed names payloadTyped restTyped restRepresented
  have sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language snapshot.free bound
      (.base "Proc") (source channel body payload rest) := by
    cases firing with
    | fire _ _ _ sourceTyped _ _ _ _ _ => exact sourceTyped
  have targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language snapshot.free bound
      (.base "Proc") (.collection .hashBag (reflectiveBody body payload :: rest) none) := by
    cases firing with
    | fire _ _ _ _ _ _ _ _ targetTyped => exact targetTyped
  refine ⟨⟨?_, .here rfl sourceTyped.2.2.1 sourceTyped.1⟩, firing, rfl, rfl, targetTyped⟩
  rw [compiled_rules]
  simp [rootReceipt]

theorem root_receipt_emitted {bound : List TypeExpr} {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : OpenPatternWellSorted language snapshot.free bound (.base "Name") channel)
    (bodyTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Proc") body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 1) body = true)
    (names : ReflectiveInstantiation.namesAdmitted
      rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language snapshot.free bound (.base "Proc") payload)
    (restTyped : ElementsHaveType language snapshot.free bound rest (.base "Proc"))
    (restRepresented : ∀ pattern ∈ rest, Represented pattern) :
    GeneralRuleJobs.finish? plan bound (.base "Proc")
      (rootReceipt bound channel body payload rest).job commTrace
      (captured bound.length channel body payload rest)
      (captured bound.length channel body payload rest) [] =
      some (rootReceipt bound channel body payload rest) :=
  GeneralRuleJobs.finish_complete
    (root_receipt_valid channelTyped bodyTyped sealed names payloadTyped restTyped restRepresented)

#print axioms root_firing
#print axioms root_receipt_emitted
#print axioms reflective_reduct_semantic


/-- All domain checks in this family follow from the independent original
rho presentation judgment and the quotation seal. -/
theorem derived_root_receipt_emitted {bound : List String} {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : DerivedPresentationSyntax.NameWellSorted rhoReflectivePresentation (fun _ => none) bound channel)
    (bodyTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) ("Name" :: bound) body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 1) body = true)
    (payloadTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) bound payload)
    (restTyped : DerivedPresentationSyntax.ProcListWellSorted rhoReflectivePresentation (fun _ => none) bound rest) :
    GeneralRuleJobs.finish? plan (typeBound bound) (.base "Proc")
      (rootReceipt (typeBound bound) channel body payload rest).job commTrace
      (captured bound.length channel body payload rest)
      (captured bound.length channel body payload rest) [] =
      some (rootReceipt (typeBound bound) channel body payload rest) := by
  have emitted := root_receipt_emitted (derived_name_open channelTyped) (derived_process_open bodyTyped)
    (by simpa [typeBound] using sealed) (derived_names_admitted bodyTyped (by simpa using sealed))
    (derived_process_open payloadTyped) (derived_processes_typed restTyped) (derived_processes_represented restTyped)
  simpa only [typeBound, List.length_map] using emitted

#print axioms derived_root_receipt_emitted

end Mettapedia.OSLF.MeTTaIL.GeneralRho
