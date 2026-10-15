import Mettapedia.OSLF.NativeTypes.Modal.Counterexamples

open Mettapedia.OSLF.Framework

/-!
# Conditional authored introductions require actual premise evidence

The unconditional base-rule context is empty. Extending that presentation to a
conditional authored rule requires its ordered premise witnesses. Here the
specified RHS is sorted and has its continuation certificate, but its provider
has no enabling row. Neither an authored introduction nor any operational
step can be obtained from RHS typing alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.ConditionalControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.Counterexamples (carrier beta done equation binding permissions)

def guarded : RewriteRule :=
  {Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.firstRule with premises := [.relationQuery "Enabled" []]}

def language : LanguageDef :=
  {Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.language with rewrites := [guarded]}

def signature : GeneralPremise.Signature := ⟨"Enabled", [], []⟩

def snapshot : Snapshot := ⟨language, [], ⟨[signature], []⟩⟩
def declaration : RulePlan := ⟨0, guarded, binding⟩
def runtimePlan : Plan :=
  ⟨snapshot, permissions, [declaration],
    [⟨0, equation, .forward, binding, true⟩, ⟨0, equation, .reverse, binding, true⟩], []⟩

theorem actual_plan : compile snapshot permissions = runtimePlan := by cbv

def schema : Schema runtimePlan where
  ordinal := 0
  declaration := declaration
  declared := List.mem_cons_self
  position := (RedexPosition.positions guarded.left).head!
  bound := []
  programCarrier := carrier
  focusBound := []
  focusCarrier := carrier

theorem no_provider_rows : (GeneralPlanEnvironment.environment runtimePlan).provider.rows = [] := rfl

/-- The premise reads actual row availability, not target typing. -/
theorem query_premise_requires_row {environment : GeneralPremise.Environment}
    {context : GeneralPremise.Context} {relation : String} {arguments : List Pattern}
    {tail : List Premise} {initial completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (held : GeneralPremise.PremisesHold environment context
      (.relationQuery relation arguments :: tail) initial completed history) :
    ∃ (index : Nat) (row : GeneralPremise.ProviderRow), environment.provider.rows[index]? = some row := by
  cases held with
  | cons head _ =>
      cases head with
      | query queried =>
          cases queried with
          | row selected _ _ _ _ => exact ⟨_, _, selected⟩

theorem no_primitive {bound : List TypeExpr} {expected : TypeExpr} {source target : Pattern}
    {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} :
    ¬ GeneralPremise.RootFiring (GeneralPlanEnvironment.environment runtimePlan)
      bound expected source index trace captured completed history target := by
  intro firing
  cases firing with
  | @fire _ _ _ _ _ rule _ _ _ _ _ selected _ _ _ _ _ premises _ _ =>
      have declared : rule ∈ (GeneralPlanEnvironment.environment runtimePlan).language.rewrites :=
        List.mem_of_getElem? selected
      have same : rule = declaration.rule := by
        simpa only [GeneralPlanEnvironment.environment, runtimePlan, List.map_cons,
          List.map_nil, List.mem_singleton] using declared
      have starts : rule.premises = [.relationQuery "Enabled" []] := by rw [same]; rfl
      rw [starts] at premises
      obtain ⟨rowIndex, row, found⟩ := query_premise_requires_row premises
      rw [no_provider_rows] at found
      simp at found

theorem no_semantic_step (source target : Pattern) :
    ¬ (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step source target := by
  rintro ⟨_, receipt, _, primitive, _⟩
  exact no_primitive primitive.2.1

def continuation : Continuation := fun _ target => PLift (target = done)

theorem rhs_target_typed : HasType language snapshot.free [] done carrier := by
  apply checkHasType_sound
  cbv

theorem rhs_available : schema.rhs? [] = some done := by cbv

theorem rhs_continuation : Nonempty (continuation [] done) := ⟨⟨rfl⟩⟩

theorem guarded_introduction_impossible :
    ¬ Nonempty (IntroductionCase schema beta [] continuation) := by
  rintro ⟨introduced⟩
  have guardedPremise : schema.declaration.rule.premises = [.relationQuery "Enabled" []] := rfl
  have premises := introduced.premises
  rw [guardedPremise] at premises
  obtain ⟨rowIndex, row, found⟩ := query_premise_requires_row premises
  rw [no_provider_rows] at found
  simp at found

theorem schema_fill (assignment : ScopedRuleMatching.Assignment) (term : Pattern) :
    schema.fill? assignment term = some term := by
  have root : schema.position = [] := by cbv
  unfold Schema.fill?
  rw [root]
  simp only [Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill?]

theorem guarded_modality_impossible :
    ¬ Inhabits schema (fun _ _ => False) continuation beta := by
  rintro ⟨implementation⟩
  have request : TypedRequest schema (fun _ _ => False) implementation.anchor [] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have names : schema.relyNames = [] := by cbv
      intro name present
      rw [names] at present
      exact False.elim (List.not_mem_nil present)
    · exact ⟨fun _ _ impossible => False.elim (List.not_mem_nil impossible),
        fun _ _ impossible => False.elim (List.not_mem_nil impossible)⟩
    · have names : schema.matchedNames = [] := by cbv
      intro name present
      rw [names] at present
      exact False.elim (List.not_mem_nil present)
    · have names : RedexPosition.fvarNames schema.declaration.rule.left ++
          RedexPosition.fvarNames schema.declaration.rule.right = [] := by cbv
      intro name present
      rw [names] at present
      exact False.elim (List.not_mem_nil present)
  obtain ⟨source, target, _, _, fired⟩ := m_step implementation [] request
  exact no_semantic_step source target fired

/-- A concrete separator for the conditional extension of M-INTRO. This does
not refute the unconditional base-rule introduction. -/
theorem rhs_typing_without_enabled_premise_insufficient :
    schema.rhs? [] = some done ∧ HasType language snapshot.free [] done carrier ∧
      Nonempty (continuation [] done) ∧
      ¬ Inhabits schema (fun _ _ => False) continuation beta :=
  ⟨rhs_available, rhs_target_typed, rhs_continuation, guarded_modality_impossible⟩

end Mettapedia.OSLF.NativeTypes.Modal.ConditionalControls
