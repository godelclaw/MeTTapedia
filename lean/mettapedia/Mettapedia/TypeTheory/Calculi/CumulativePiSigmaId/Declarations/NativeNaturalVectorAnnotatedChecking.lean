import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedEvidence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RootPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Elaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativePreservation

/-!
# Typed annotated instances of the selected natural/vector rows

Independent kernel proofs type each canonical endpoint and form its telescope.
The existing schema interface then gives admitted equalities under typed
simultaneous substitutions. Original row addresses and permissions are retained.

This supplies typed instances, not inversion of arbitrary raw typing proofs,
uniform raw subject preservation, normalization or native implementation trust.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.Annotated

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Annotated

abbrev Row := Fin Checking.schemas.length
abbrev arity (index : Row) := (Checking.schemas.get index).1

def context (index : Row) : CCtx Tower.Head (arity index) :=
  liftCtx (RussellTarski.substLevelsCtx levels (Checking.schemas.get index).2.context)

def resultType (index : Row) : CTm Tower.Head (arity index) :=
  liftTm (RussellTarski.substLevelsTm levels (Checking.schemas.get index).2.type)

def left (index : Row) : Tower.Tm (arity index) := (Checking.schemas.get index).2.left
def right (index : Row) : Tower.Tm (arity index) := (Checking.schemas.get index).2.right

theorem table_row (index : Row) :
    Checking.table.get index = ⟨arity index, left index, right index⟩ := by
  fin_cases index <;> rfl

theorem endpoints_typed (enabled : ComputationProfiles.Selection) (index : Row) :
    CTyped (church enabled) (context index) (liftTm (left index)) (resultType index) ∧
    CTyped (church enabled) (context index) (liftTm (right index)) (resultType index) := by
  fin_cases index
  · exact ⟨Evidence.left_0 enabled, Evidence.right_0 enabled⟩
  · exact ⟨Evidence.left_1 enabled, Evidence.right_1 enabled⟩
  · exact ⟨Evidence.left_2 enabled, Evidence.right_2 enabled⟩
  · exact ⟨Evidence.left_3 enabled, Evidence.right_3 enabled⟩

theorem context_formed (enabled : ComputationProfiles.Selection) (index : Row) :
    CCtxFormed (church enabled) (context index) := by
  fin_cases index
  · exact Evidence.context_0 enabled
  · exact Evidence.context_1 enabled
  · exact Evidence.context_2 enabled
  · exact Evidence.context_3 enabled

theorem knowledge (enabled : ComputationProfiles.Selection) (index : Row) :
    ∀ argument, patternKnowledge (church enabled).constantType none (left index) argument =
      some ((context index).lookup argument) := by
  rw [constantType_eq enabled]
  fin_cases index <;> intro argument <;> fin_cases argument <;> decide +kernel

theorem left_type (enabled : ComputationProfiles.Selection) (index : Row) :
    leftType (church enabled).constantType (left index) = some (resultType index) := by
  rw [constantType_eq enabled]
  fin_cases index <;> decide +kernel

theorem equations_empty (enabled : ComputationProfiles.Selection) (index : Row) :
    patternEquations (church enabled).constantType none (left index) = [] := by
  rw [constantType_eq enabled]
  fin_cases index <;> decide +kernel

theorem elaborated_left (enabled : ComputationProfiles.Selection) (index : Row) :
    elabLeft (church enabled).constantType (left index) = liftTm (left index) := by
  apply elab_lamFree
  fin_cases index <;> decide

theorem elaborated_right (enabled : ComputationProfiles.Selection) (index : Row) :
    elabRight (church enabled).constantType (left index) (right index) = liftTm (right index) := by
  apply elab_lamFree
  fin_cases index <;> decide

/-- The actual right sides typecheck in the contexts inferred from their left sides. -/
theorem template_typed (enabled : ComputationProfiles.Selection) (index : Row) :
    TemplateTyped (church enabled) (church enabled).constantType (left index) (right index) := by
  refine ⟨context index, resultType index, knowledge enabled index, left_type enabled index, ?_⟩
  rw [elaborated_right]
  exact (endpoints_typed enabled index).2

theorem left_firstOrder (index : Row) : firstOrder (left index) = true := by
  fin_cases index <;> decide

theorem left_not_refl (index : Row) (argument : Tower.Tm (arity index)) :
    left index ≠ .refl argument := by
  fin_cases index <;> intro impossible <;> cases impossible

/-- The root policy changes no universe ordering or universe-formation rules. -/
def levelModel (enabled : ComputationProfiles.Selection) :
    Normalization.LevelModel (ComputationProfiles.rules enabled) Nat :=
  { Normalization.TowerModel.levels (fun _ => 0) with }

/-- Disabling all row permissions leaves the declarations unchanged and no
raw declared computation. This is the actual table, not an empty replacement. -/
theorem inactive_raw_no_root {n : Nat} {left right : Tower.Tm n} :
    ¬ (ComputationProfiles.rules (fun _ => false)).computation.step left right := by
  intro root
  cases (presentation (fun _ => false)).mp root with
  | instantiate selected _ =>
      obtain ⟨_, impossible, _⟩ := selected
      cases impossible

def headReading (enabled : ComputationProfiles.Selection) :
    HeadReading (ComputationProfiles.rules enabled) :=
  { Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.towerHeadReading
      (L := Nat) with }

theorem ground_head_eq (enabled : ComputationProfiles.Selection) :
    GroundHeadEq (ComputationProfiles.rules enabled) :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.tower_groundHeadEq

/-- The opaque baseline has the richer annotated former laws, including
typed eta equality. Its eight declarations and universe policy are retained.
No enabled iota rule is admitted by this theorem. -/
theorem inactive_formerFacts : CFormerFacts (church (fun _ => false)) :=
  CFormerFacts.ofNoSteps
    (fun root => inactive_raw_no_root (erase_root (fun _ => false) root))
    (levelModel _) (headReading _) (ground_head_eq _) (u₀ := .sort Tower.zero) (.sort _)

theorem inactive_pi_not_head {n : Nat} {Γ : CCtx Tower.Head n}
    {domain : CTm Tower.Head n} {codomain : CTm Tower.Head (n + 1)} {head : Tower.Head}
    (context : CCtxFormed (church (fun _ => false)) Γ) :
    ¬ CTypeEq (church (fun _ => false)) Γ (.pi domain codomain) (.head head) := by
  intro equal
  obtain ⟨_, _, impossible, _⟩ :=
    (inactive_formerFacts.forms equal context (.pi _ _) (.head _)).pi_left
  cases impossible

/-- For a selection with enabled computation, former injectivity remains
the hypothesis of this uniform annotated root-preservation theorem. The
opaque selection is qualified independently above. -/
theorem root_preserving_of_formerFacts (enabled : ComputationProfiles.Selection)
    (facts : CFormerFacts (church enabled)) : CRootPreserving (church enabled) := by
  apply ChurchRules.ofSchemas_rootPreserving (family enabled) (presentation enabled)
  intro arity L R rule
  obtain ⟨index, _, row⟩ := rule
  rw [table_row index] at row
  cases row
  exact SchemaPreserving.of_templateTyped facts (levelModel enabled) (fun declared => declared)
    (left_firstOrder index) (left_not_refl index) (template_typed enabled index)

/-- Inversion also discharges the actual argument premises, given former facts. -/
theorem root_premised_of_formerFacts (enabled : ComputationProfiles.Selection)
    (facts : CFormerFacts (church enabled)) : CRootPremised (church enabled) := by
  have first : ∀ {arity : Nat} {L R : Tower.Tm arity}, family enabled L R → firstOrder L = true := by
    intro arity L R rule
    obtain ⟨index, _, row⟩ := rule
    rw [table_row index] at row
    cases row
    exact left_firstOrder index
  intro n Γ l r A formed step typed
  exact ChurchRules.ofSchemas_premisedIn (family enabled) (presentation enabled)
    first (fun declared => declared) (fun required => required) facts (levelModel enabled)
    formed step typed

theorem root_admitted_of_formerFacts (enabled : ComputationProfiles.Selection)
    (facts : CFormerFacts (church enabled)) : CRootAdmitted (church enabled) :=
  CRootPreserving.admitted (root_preserving_of_formerFacts enabled facts)
    (root_premised_of_formerFacts enabled facts)

theorem head_preserving (enabled : ComputationProfiles.Selection) : CHeadPreserving (church enabled) :=
  CHeadPreserving.ofLevelTower (fun known => known) (fun known => known)
    (fun known => known) (fun known => known) (church enabled)

/-- Contextual beta, projection and head computation of the actual opaque
package is an equality at its original dependent type. No termination or
admission of an enabled declared iota rule is inferred. -/
theorem inactive_reduction_equal {n : Nat} {Γ : CCtx Tower.Head n}
    {source target type : CTm Tower.Head n} (context : CCtxFormed (church (fun _ => false)) Γ)
    (steps : CReduces (church (fun _ => false)) source target)
    (typed : CTyped (church (fun _ => false)) Γ source type) :
    CEqual (church (fun _ => false)) Γ source target type :=
  CReduces.equal inactive_formerFacts (levelModel _)
    (root_admitted_of_formerFacts _ inactive_formerFacts) (head_preserving _) context steps typed

theorem inactive_reduction_typed {n : Nat} {Γ : CCtx Tower.Head n}
    {source target type : CTm Tower.Head n} (context : CCtxFormed (church (fun _ => false)) Γ)
    (steps : CReduces (church (fun _ => false)) source target)
    (typed : CTyped (church (fun _ => false)) Γ source type) :
    CTyped (church (fun _ => false)) Γ target type :=
  CReduces.typed inactive_formerFacts (levelModel _)
    (root_admitted_of_formerFacts _ inactive_formerFacts) (head_preserving _) context steps typed

/-- A permitted original row is an annotated step; each argument keeps its annotation. -/
theorem instantiated_step (enabled : ComputationProfiles.Selection) (index : Row)
    (permitted : enabled index = true) {n : Nat} (substitution : CSub Tower.Head (arity index) n) :
    (church enabled).computation.step
      ((liftTm (left index)).subst substitution) ((liftTm (right index)).subst substitution) := by
  have rule : family enabled (left index) (right index) := ⟨index, permitted, table_row index⟩
  have step : (church enabled).computation.step
      ((elabLeft (church enabled).constantType (left index)).subst substitution)
      ((elabRight (church enabled).constantType (left index) (right index)).subst substitution) :=
    CSchemaStep.instantiate ⟨left index, right index, rule, rfl, rfl⟩ substitution
  simpa only [elaborated_left, elaborated_right] using step

/-- Typed assignments discharge the actual premises; permission alone is insufficient. -/
theorem instantiated_admits (enabled : ComputationProfiles.Selection) (index : Row)
    (permitted : enabled index = true) {n : Nat} {Γ : CCtx Tower.Head n}
    {substitution : CSub Tower.Head (arity index) n}
    (typed : CSubstMor (church enabled) (context index) Γ substitution) :
    (church enabled).Admits Γ
      ((liftTm (left index)).subst substitution) ((liftTm (right index)).subst substitution) := by
  have rule : family enabled (left index) (right index) := ⟨index, permitted, table_row index⟩
  have admitted := CSchemaRequires.admits (Q := church enabled)
    (decls := (church enabled).constantType) (S := family enabled)
    (fun required => required) rule substitution
    (CSubstMor.patternTypings (knowledge enabled index) typed)
    (fun equation member => by simp only [equations_empty, List.not_mem_nil] at member)
  simpa only [elaborated_left, elaborated_right] using admitted

/-- These equalities use independent canonical typing, actual premises and actual roots. -/
theorem instantiated_equal (enabled : ComputationProfiles.Selection) (index : Row)
    (permitted : enabled index = true) {n : Nat} {Γ : CCtx Tower.Head n}
    {substitution : CSub Tower.Head (arity index) n}
    (typed : CSubstMor (church enabled) (context index) Γ substitution) :
    CEqual (church enabled) Γ
      ((liftTm (left index)).subst substitution) ((liftTm (right index)).subst substitution)
      ((resultType index).subst substitution) :=
  .rootAdmitted (instantiated_step enabled index permitted substitution)
    (instantiated_admits enabled index permitted typed)
    ((endpoints_typed enabled index).1.substitute typed)
    ((endpoints_typed enabled index).2.substitute typed)

/-- Erasure keeps the selected typed-equality judgment and its actual assignment. -/
theorem erased_instantiated_equal (enabled : ComputationProfiles.Selection) (index : Row)
    (permitted : enabled index = true) {n : Nat} {Γ : CCtx Tower.Head n}
    {substitution : CSub Tower.Head (arity index) n}
    (typed : CSubstMor (church enabled) (context index) Γ substitution) :
    Equal (ComputationProfiles.rules enabled) Γ.erase
      (subst (CTm.eraseSub substitution) (left index))
      (subst (CTm.eraseSub substitution) (right index))
      (subst (CTm.eraseSub substitution) (resultType index).erase) := by
  simpa only [CStatement.erase, CTm.erase_subst, erase_liftTm] using
    (instantiated_equal enabled index permitted typed).erase

/-- Every original row has a formed, canonical, nonempty proof witness. -/
theorem canonical_equal (index : Row) :
    CEqual (church (fun _ => true)) (context index)
      (liftTm (left index)) (liftTm (right index)) (resultType index) := by
  have typed : CSubstMor (church (fun _ => true)) (context index) (context index) CTm.ids := by
    intro argument
    change CTyped (church (fun _ => true)) (context index) (.var argument)
      (CTm.subst CTm.ids ((context index).lookup argument))
    rw [CTm.subst_ids]
    exact .var argument
  simpa only [CTm.subst_ids] using instantiated_equal (fun _ => true) index rfl typed

def metadataVerdicts : List (String × Bool) :=
  let declared := (church (fun _ => false)).constantType
  (List.finRange Checking.schemas.length).flatMap fun index => [
    ("canonical row variable types " ++ toString index.val,
      (List.finRange (arity index)).all fun argument =>
        decide (patternKnowledge declared none (left index) argument =
          some ((context index).lookup argument))),
    ("canonical row result type " ++ toString index.val,
      leftType declared (left index) == some (resultType index)),
    ("canonical row refuses changed result type " ++ toString index.val,
      !(leftType declared (left index) == some (.const `UndeclaredResult))),
    ("canonical row has no reflexivity equations " ++ toString index.val,
      (patternEquations declared none (left index)).isEmpty)]

theorem all_metadataVerdicts : metadataVerdicts.all Prod.snd = true := by decide +kernel

end Programs.Annotated
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
