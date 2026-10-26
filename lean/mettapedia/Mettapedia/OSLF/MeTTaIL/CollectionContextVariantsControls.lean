import Mettapedia.OSLF.MeTTaIL.CollectionContextVariants
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution

/-!
# Typed source controls for collection contexts

All tested holes come from the existing typed occurrence generator over the
authored module. These controls exercise the context component; the broader
execution profile remains refused until the source-coverage join is proved.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

#module_file "../../../../../metta/gslt/module/CollectionNestedControl.module"

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection.ContextControls

open Syntax GeneralTypedSites

def source : LanguageDef :=
  CollectionNestedControl.language.toOption.getD
    { «name» := "", «types» := [], «terms» := [], «equations» := [], «rewrites» := [] }

def language : LanguageDef := (source.toCore.toOption.map (·.language)).getD source

theorem source_loaded : CollectionNestedControl.language = .ok source := by rfl
example : source.toCore.isOk = true := by cbv

def permissions : OperationalPermissions :=
  { enabled := true, constructorArguments := [("Wrap", 0)],
    collectionKinds := [.hashBag, .hashSet] }

def atom (label : String) : Pattern := .apply label []
def setOf (items : List Pattern) : Pattern := .collection .hashSet items none
def bagOf (items : List Pattern) : Pattern := .collection .hashBag items none

def selectedSites (term : Pattern) : List SiteData :=
  (generate language (fun _ => none) permissions [] (.base "Proc") term).filter
    (fun site => site.focus == atom "A")

def alternatives (term : Pattern) : List SiteVariant :=
  (selectedSites term).flatMap siteVariants

def targets (term : Pattern) : List Pattern :=
  (alternatives term).map (fun variant =>
    CanonicalBags.canon (variant.site.context.fill (atom "B")))

theorem set_retains_or_consumes :
    (targets (setOf [atom "A"])).Perm
      [setOf [atom "B"], setOf [atom "A", atom "B"]] := by cbv; decide

theorem bag_consumes_only : targets (bagOf [atom "A"]) = [bagOf [atom "B"]] := by cbv

theorem nested_set_retention :
    (targets (setOf [setOf [atom "A"]])).Perm
      ([setOf [setOf [atom "B"]],
        setOf [setOf [atom "A"], setOf [atom "B"]],
        setOf [setOf [atom "A", atom "B"]],
        setOf [setOf [atom "A"], setOf [atom "A", atom "B"]]].map
          CanonicalBags.canon) := by cbv; decide

theorem replacing_into_existing_set_member :
    setOf [atom "B"] ∈ targets (setOf [atom "A", atom "B"]) := by
  cbv
  exact .head _

theorem equal_bag_occurrences_keep_origins :
    let variants := alternatives (bagOf [atom "A", atom "A"])
    variants.length = 2 ∧
      (variants.map (fun variant => variant.original.address)).Nodup ∧
      targets (bagOf [atom "A", atom "A"]) =
        [bagOf [atom "A", atom "B"], bagOf [atom "A", atom "B"]] := by cbv; decide

theorem constructor_context_kept :
    (targets (.apply "Wrap" [setOf [atom "A"]])).Perm
      [.apply "Wrap" [setOf [atom "B"]],
        .apply "Wrap" [setOf [atom "A", atom "B"]]] := by cbv; decide

def plan : GeneralExecutionAdmission.Plan := GeneralExecutionAdmission.compile
  ⟨language, [], ⟨[], [], []⟩⟩
  { sites := permissions, includeDerivedEquations := false }

theorem set_context_still_requires_qualification :
    plan.obligations = [.setDecomposition] := by cbv

theorem root_certificate_does_not_authorize_contexts :
    (CollectionExecutionAdmission.admit? plan).isNone = true := by cbv

end Mettapedia.OSLF.MeTTaIL.CollectionSelection.ContextControls

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection.ContextControls.SourceAgreement

open Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

theorem compiled_source_and_permissions :
    plan.snapshot.language = language ∧ plan.permissions.sites = permissions := by
  exact ⟨rfl, rfl⟩

theorem authored_atom_step :
    ReferenceStep.Step Engine.RelationEnv.empty source (atom "A") (atom "B") := by
  apply Exists.intro (ReferenceStep.Witness.rule 0 [] [])
  exact (ReferenceStep.checkStep_eq_some_iff _ _ _).mp (by cbv)

theorem core_atom_step :
    ReferenceStep.Step Engine.RelationEnv.empty language (atom "A") (atom "B") := by
  apply Exists.intro (ReferenceStep.Witness.rule 0 [] [])
  exact (ReferenceStep.checkStep_eq_some_iff _ _ _).mp (by cbv)

private theorem step_source_of_checked_heads {selected : LanguageDef}
    (heads : selected.rewrites.all (fun rule => rule.left == atom "A") = true)
    {first second : Pattern}
    (stepped : ReferenceStep.Step Engine.RelationEnv.empty selected first second) :
    first = atom "A" := by
  obtain ⟨witness, valid⟩ := stepped
  cases valid with
  | rule found matched _ =>
    have left := List.all_eq_true.mp heads _ (List.mem_of_getElem? found)
    simp only [beq_iff_eq] at left
    rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic, left] at matched
    cases first with
    | apply label arguments =>
      by_cases named : label = "A"
      · subst label
        cases arguments <;> simp_all [atom, Match.matchPattern]
      · have different : (("A" : String) == label) = false :=
          beq_eq_false_iff_ne.mpr (Ne.symm named)
        simp [atom, Match.matchPattern, different] at matched
    | bvar => simp [atom, Match.matchPattern] at matched
    | fvar => simp [atom, Match.matchPattern] at matched
    | lambda => simp [atom, Match.matchPattern] at matched
    | multiLambda => simp [atom, Match.matchPattern] at matched
    | «subst» => simp [atom, Match.matchPattern] at matched
    | collection => simp [atom, Match.matchPattern] at matched

private theorem no_collection_stepModulo_of_checked_heads {selected : LanguageDef}
    (heads : selected.rewrites.all (fun rule => rule.left == atom "A") = true)
    (noEquations : selected.equations = [])
    (noAlgebra : selected.hasAlgebraDeclarations = false)
    (kind : CollType) (items : List Pattern) (target : Pattern) :
    ¬ ReferenceStep.StepModulo Engine.RelationEnv.empty selected
      (.collection kind items none) target := by
  rintro ⟨redex, contractum, before, fired, _⟩
  have redex_eq := step_source_of_checked_heads heads fired
  rw [redex_eq] at before
  have same := ReferenceStep.equivalent_same noEquations noAlgebra before
  cases kind <;> simp [CanonicalBags.Same, CanonicalBags.canon, atom] at same

/-- This module has a root rule and separately permitted collection contexts.
Its authored rule inventory contains no contextual congruence rule. -/
theorem authored_collections_have_no_root_stepModulo
    (kind : CollType) (items : List Pattern) (target : Pattern) :
    ¬ ReferenceStep.StepModulo Engine.RelationEnv.empty source
      (.collection kind items none) target :=
  no_collection_stepModulo_of_checked_heads (by cbv) (by cbv) (by cbv)
    kind items target

theorem core_collections_have_no_root_stepModulo
    (kind : CollType) (items : List Pattern) (target : Pattern) :
    ¬ ReferenceStep.StepModulo Engine.RelationEnv.empty language
      (.collection kind items none) target :=
  no_collection_stepModulo_of_checked_heads (by cbv) (by cbv) (by cbv)
    kind items target

theorem requested_raw_set_witnesses_absent :
    ¬ ReferenceStep.StepModulo Engine.RelationEnv.empty source
      (setOf [atom "A"]) (setOf [atom "B"]) ∧
    ¬ ReferenceStep.StepModulo Engine.RelationEnv.empty source
      (setOf [atom "A"]) (setOf [atom "A", atom "B"]) :=
  ⟨authored_collections_have_no_root_stepModulo _ _ _,
    authored_collections_have_no_root_stepModulo _ _ _⟩

theorem set_duplicate_equivalent :
    ReferenceStep.Equivalent Engine.RelationEnv.empty language
      (setOf [atom "A"]) (setOf [atom "A", atom "A"]) := by
  have sorted : SortedAt language (setOf [atom "A", atom "A"]) "Proc" :=
    ⟨FreeTypeContext.empty, [], checkHasType_sound (by cbv)⟩
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
    (.inContext .hole (Or.inr (.setDedup_of_sorted sorted))))

theorem set_reorder_equivalent :
    ReferenceStep.Equivalent Engine.RelationEnv.empty language
      (setOf [atom "B", atom "A"]) (setOf [atom "A", atom "B"]) := by
  have sorted : SortedAt language (setOf [atom "B", atom "A"]) "Proc" :=
    ⟨FreeTypeContext.empty, [], checkHasType_sound (by cbv)⟩
  exact Relation.EqvGen.rel _ _ (.inContext .hole
    (Or.inr (.setPerm_of_sorted sorted (List.Perm.swap _ _ []))))

def consumingData : GeneralTypedSites.SiteData :=
  (selectedSites (setOf [atom "A"]))[0]'(by cbv)

theorem consuming_data_generated :
    consumingData ∈ GeneralTypedSites.generate language FreeTypeContext.empty permissions []
      (.base "Proc") (setOf [atom "A"]) := by
  cbv
  exact .tail _ (.head _)

def consumingSite := GeneralTypedSites.asExecutionSite language FreeTypeContext.empty permissions []
  (.base "Proc") (setOf [atom "A"]) consumingData consuming_data_generated

def retainingData : GeneralTypedSites.SiteData :=
  (selectedSites (setOf [atom "A", atom "A"]))[0]'(by cbv)

theorem retaining_data_generated :
    retainingData ∈ GeneralTypedSites.generate language FreeTypeContext.empty permissions []
      (.base "Proc") (setOf [atom "A", atom "A"]) := by
  cbv
  exact .tail _ (.head _)

def retainingSite := GeneralTypedSites.asExecutionSite language FreeTypeContext.empty permissions []
  (.base "Proc") (setOf [atom "A", atom "A"]) retainingData retaining_data_generated

def change : RewriteRule := language.rewrites[0]'(by cbv)

def atomicReceipt : ConditionalEquationExecution.Receipt := ⟨0, [], [], [], atom "B"⟩

theorem atomic_instance : ConditionalEquationExecution.RuleInstance Engine.RelationEnv.empty language
    FreeTypeContext.empty [] (.base "Proc") change (atom "A") atomicReceipt := by
  apply ConditionalEquationExecution.applyRuleAtOutcome_sound
  cbv
  exact .head _

def consumingReceipt : TypedContextualEquationExecution.Receipt :=
  ⟨0, consumingSite.context, [], .base "Proc", 0, atomicReceipt, setOf [atom "B"]⟩

def retainingReceipt : TypedContextualEquationExecution.Receipt :=
  ⟨0, retainingSite.context, [], .base "Proc", 0, atomicReceipt, setOf [atom "B", atom "A"]⟩

theorem set_consuming_contextual_witness :
    ContextualAuthoredEquationExecution.ContextualInstance Engine.RelationEnv.empty language
      FreeTypeContext.empty [] (.base "Proc")
      (GeneralTypedSites.generatedPermissions language FreeTypeContext.empty permissions []
        (.base "Proc") (setOf [atom "A"]))
      (setOf [atom "A"]) 0 0 change consumingSite consumingReceipt := by
  apply ContextualAuthoredEquationExecution.contextual_sound
  cbv
  exact .head _

theorem set_retaining_contextual_witness :
    ReferenceStep.Equivalent Engine.RelationEnv.empty language
      (setOf [atom "A"]) (setOf [atom "A", atom "A"]) ∧
    ContextualAuthoredEquationExecution.ContextualInstance Engine.RelationEnv.empty language
      FreeTypeContext.empty [] (.base "Proc")
      (GeneralTypedSites.generatedPermissions language FreeTypeContext.empty permissions []
        (.base "Proc") (setOf [atom "A", atom "A"]))
      (setOf [atom "A", atom "A"]) 0 0 change retainingSite retainingReceipt ∧
    ReferenceStep.Equivalent Engine.RelationEnv.empty language
      retainingReceipt.target (setOf [atom "A", atom "B"]) := by
  refine ⟨set_duplicate_equivalent, ?_, set_reorder_equivalent⟩
  apply ContextualAuthoredEquationExecution.contextual_sound
  cbv
  exact .head _

theorem change_has_original_rule_identity :
    (source.rewrites[0]?).map (fun rule => (rule.name, rule.left, rule.right, rule.premises)) =
      some (change.name, change.left, change.right, change.premises) := by
  cbv

theorem consuming_focus_has_authored_witness :
    ReferenceStep.StepValid Engine.RelationEnv.empty source consumingSite.focus
      (.rule 0 [] []) consumingReceipt.atomic.target := by
  apply (ReferenceStep.checkStep_eq_some_iff _ _ _).mp
  cbv

theorem retaining_focus_has_authored_witness :
    ReferenceStep.StepValid Engine.RelationEnv.empty source retainingSite.focus
      (.rule 0 [] []) retainingReceipt.atomic.target := by
  apply (ReferenceStep.checkStep_eq_some_iff _ _ _).mp
  cbv

theorem set_successor_classes_differ :
    ¬ CanonicalBags.Same (setOf [atom "B"]) (setOf [atom "A", atom "B"]) := by
  cbv; decide

theorem actual_contexts_are_permitted :
    permissions.permitsContext consumingSite.context = true ∧
      permissions.permitsContext retainingSite.context = true := by
  cbv

theorem bag_duplicate_not_equivalent :
    ¬ ReferenceStep.Equivalent Engine.RelationEnv.empty language
      (bagOf [atom "A"]) (bagOf [atom "A", atom "A"]) := by
  intro related
  have same := ReferenceStep.equivalent_same (by cbv) (by cbv) related
  have different : ¬ CanonicalBags.Same (bagOf [atom "A"]) (bagOf [atom "A", atom "A"]) := by
    cbv; decide
  exact different same

theorem set_singleton_does_not_collapse :
    ¬ ReferenceStep.Equivalent Engine.RelationEnv.empty language (setOf [atom "B"]) (atom "B") := by
  intro related
  have same := ReferenceStep.equivalent_same (by cbv) (by cbv) related
  have different : ¬ CanonicalBags.Same (setOf [atom "B"]) (atom "B") := by cbv; decide
  exact different same

theorem nested_set_does_not_flatten :
    ¬ ReferenceStep.Equivalent Engine.RelationEnv.empty language
      (setOf [setOf [atom "A"]]) (setOf [atom "A"]) := by
  intro related
  have same := ReferenceStep.equivalent_same (by cbv) (by cbv) related
  have different : ¬ CanonicalBags.Same (setOf [setOf [atom "A"]]) (setOf [atom "A"]) := by
    cbv; decide
  exact different same

#print axioms compiled_source_and_permissions
#print axioms authored_atom_step
#print axioms core_atom_step
#print axioms authored_collections_have_no_root_stepModulo
#print axioms core_collections_have_no_root_stepModulo
#print axioms requested_raw_set_witnesses_absent
#print axioms set_duplicate_equivalent
#print axioms set_reorder_equivalent
#print axioms consuming_data_generated
#print axioms retaining_data_generated
#print axioms atomic_instance
#print axioms set_consuming_contextual_witness
#print axioms set_retaining_contextual_witness
#print axioms change_has_original_rule_identity
#print axioms consuming_focus_has_authored_witness
#print axioms retaining_focus_has_authored_witness
#print axioms set_successor_classes_differ
#print axioms actual_contexts_are_permitted
#print axioms bag_duplicate_not_equivalent
#print axioms set_singleton_does_not_collapse
#print axioms nested_set_does_not_flatten
#print axioms set_retains_or_consumes
#print axioms bag_consumes_only
#print axioms nested_set_retention
#print axioms replacing_into_existing_set_member
#print axioms equal_bag_occurrences_keep_origins
#print axioms constructor_context_kept
#print axioms set_context_still_requires_qualification
#print axioms root_certificate_does_not_authorize_contexts
#print axioms source_loaded

end Mettapedia.OSLF.MeTTaIL.CollectionSelection.ContextControls.SourceAgreement
