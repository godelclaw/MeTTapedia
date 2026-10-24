import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultEvidence

/-!
# Checked registered List method adaptation with a dependent motive

Four independent submissions supply input/output formation, the primitive
projection and the result family. The generic constructor-code theorem then
derives the adapter from the source method and its original child List.
The carrier, motive, constructor, source method and children are open variables.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultAdapter.Registered
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Presentation Declaration RussellTarski NativeIndexedFamilies FormationSensitive
open FunctionArgumentAdapters
open IndexedPositiveContainerGuestTypes IndexedPositiveContainerGuestPlans
open IndexedPositiveContainerGuestResultArguments IndexedPositiveContainerGuestMethodSpecialization
open IndexedPositiveContainerGuestControls.Lists

abbrev rules := NativeListResultView.rules
abbrev decoder := NativeListResultView.decoder

local instance : DecidableRel rules.headTyping :=
  fun a b => inferInstanceAs (Decidable (Tower.rules.headTyping a b))
local instance : DecidablePred rules.isUniverse :=
  fun a => inferInstanceAs (Decidable (Tower.rules.isUniverse a))
local instance : ∀ a b c, Decidable (rules.join a b c) :=
  fun a b c => inferInstanceAs (Decidable (Tower.rules.join a b c))
local instance : DecidableRel rules.cumulative :=
  fun a b => inferInstanceAs (Decidable (Tower.rules.cumulative a b))
local instance : DecidableRel rules.headEq := LevelTower.instDecidableHeadEq

set_option maxRecDepth 8192 in
theorem input_replayed : FormationSensitiveElaboration.replay rules decoder context
    inputType (sortTm NativeListResultView.level) Evidence.inputSubmission = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem output_replayed : FormationSensitiveElaboration.replay rules decoder context
    outputType (sortTm NativeListResultView.level) Evidence.outputSubmission = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem projection_replayed : FormationSensitiveElaboration.replay rules decoder context
    projection (arrow inputType outputType) Evidence.projectionSubmission = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem result_replayed : FormationSensitiveElaboration.replay rules decoder context
    resultType (sortTm NativeListResultView.level) Evidence.resultSubmission = true := by decide +kernel

theorem context_formed : ContextFormation rules context :=
  (FormationSensitiveElaboration.replay_sound rules decoder input_replayed).context

theorem primitive_evidence : SlotsTyped rules context (.sort NativeListResultView.level) argumentSlots := by
  intro slot present
  rw [slots_exact] at present
  obtain rfl := List.mem_singleton.mp present
  exact ⟨(FormationSensitiveElaboration.replay_sound rules decoder input_replayed).typing,
    (FormationSensitiveElaboration.replay_sound rules decoder output_replayed).typing,
    (FormationSensitiveElaboration.replay_sound rules decoder projection_replayed).typing⟩

theorem source_typed : Judgment rules context (.var 1) methodType := by
  refine ⟨context_formed, ?_⟩
  have same : Ctx.lookup context 1 = methodType := by decide +kernel
  rw [← same]
  exact .var 1

theorem field_evidence : SuppliedFields rules context code fields methodType remainingType := by
  rw [method_spine_exact]
  unfold methodSpine
  refine SuppliedFields.nested _ _ _ _ _ _ fields
    (Typing.var (R := rules) (Γ := context) 0) ?_
  let body : Tower.Tm 6 :=
    .pi (Intrinsic.listApp (NativeListResultView.packedType (.var 5) (.var 4)))
      (.app (.var 5) (.app (.var 4) (.var 1)))
  have readback : inst0 (.var 0 : Tower.Tm 5) body = remainingType := by decide +kernel
  change SuppliedFields rules context _ _ (inst0 (.var 0) body) remainingType
  rw [readback]
  exact .result _ _ _

theorem product_closure : ∃ result,
    rules.join (.sort NativeListResultView.level) (.sort NativeListResultView.level) result ∧
      (result = .sort NativeListResultView.level ∨ rules.cumulative result (.sort NativeListResultView.level)) :=
  ⟨.sort (.max NativeListResultView.level NativeListResultView.level), .sorts _ _,
    Or.inr (fun _ => max_le le_rfl le_rfl)⟩

theorem method_universe : rules.isUniverse (.sort NativeListResultView.level) := .sort _

theorem adapter_typed : Judgment rules context adapter adapterType := by
  have derived := adaptedMethod_typed indexing containers results code types PUnit.unit
    (.var 3) (.var 2) fields method_universe product_closure primitive_evidence
    (FormationSensitiveElaboration.replay_sound rules decoder result_replayed).typing source_typed field_evidence
  change Judgment rules context adapter (hypotheses (argumentSlots.map Slot.input) resultType) at derived
  rw [slots_exact] at derived
  exact derived

theorem programme_typed : Judgment rules .nil programme programmeType := by
  refine ⟨.nil, FormationCheckedTelescopePrograms.close_typed
    (FormationSensitive.towerUniverseRegularity.includeSignature NativeListResultView.instantiation.signature)
    ?_ adapter_typed.context adapter_typed.typing⟩
  intro first second firstUniverse secondUniverse
  cases firstUniverse with
  | sort first =>
    cases secondUniverse with
    | sort second => exact ⟨.sort (.max first second), .sort _, .sorts _ _⟩

theorem caller_typed {n : Nat} {target : Tower.Ctx n}
    (targetFormation : ContextFormation rules target) {sigma : Sub Tower.Head 5 n}
    (typed : FormationSensitive.CtxMor rules context target sigma) :
    Judgment rules target (subst sigma adapter) (subst sigma adapterType) :=
  ⟨targetFormation, adapter_typed.typing.substitute typed⟩

theorem programme_application {n : Nat} (sigma : Sub Tower.Head 5 n) :
    TelescopeAbstraction.BetaSteps
      (TelescopeAbstraction.applyClosed context sigma (liftClosed programme)) (subst sigma adapter) :=
  TelescopeAbstraction.applyClosed_beta context sigma adapter

theorem adapter_levels (theta : Nat → Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat) :
    Judgment (NativeListResultView.levelInstance theta).rules
      (substLevelsCtx theta context) (substLevelsTm theta adapter) (substLevelsTm theta adapterType) :=
  (NativeListResultView.levelInstance theta).refinedJudgment adapter_typed

theorem target_caller_typed (theta : Nat → Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat)
    {n : Nat} {target : Tower.Ctx n}
    (targetFormation : ContextFormation (NativeListResultView.levelInstance theta).rules target)
    {sigma : Sub Tower.Head 5 n}
    (typed : FormationSensitive.CtxMor (NativeListResultView.levelInstance theta).rules
      (substLevelsCtx theta context) target sigma) :
    Judgment (NativeListResultView.levelInstance theta).rules target
      (subst sigma (substLevelsTm theta adapter)) (subst sigma (substLevelsTm theta adapterType)) :=
  ⟨targetFormation, (adapter_levels theta).typing.substitute typed⟩

theorem substitution_square (theta : Nat → Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat)
    {n : Nat} (sigma : Sub Tower.Head 5 n) :
    substLevelsTm theta (subst sigma adapter) =
      subst (fun index => substLevelsTm theta (sigma index)) (substLevelsTm theta adapter) :=
  Tm.mapHead_subst (substLevelsHead theta) sigma adapter

namespace Controls

theorem slot_contract :
    Typing rules context inputType (sortTm NativeListResultView.level) ∧
    Typing rules context outputType (sortTm NativeListResultView.level) ∧
    Typing rules context projection (arrow inputType outputType) :=
  primitive_evidence ⟨inputType, outputType, projection⟩ (by rw [slots_exact]; exact List.mem_singleton_self _)

def extendedContext : Tower.Ctx 6 := .snoc context (sortTm NativeListResultView.level)

theorem extended_context_formed : ContextFormation rules extendedContext :=
  .snoc context_formed (.headType (.sort _)) (.sort _)

theorem extended_assignment : FormationSensitive.CtxMor rules context extendedContext (renSub wk) := by
  intro index
  simpa only [subst_renSub, extendedContext, Ctx.lookup_snoc_succ, renSub, wk] using
    (Typing.var (R := rules) (Γ := extendedContext) index.succ)

theorem weakened_caller : Judgment rules extendedContext
    (subst (renSub wk) adapter) (subst (renSub wk) adapterType) :=
  caller_typed extended_context_formed extended_assignment

def raisedLevels (parameter : Nat) : Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat :=
  if parameter = 0 then .succ Tower.zero else .param parameter

def raisedContext : Tower.Ctx 6 :=
  .snoc (substLevelsCtx raisedLevels context) (sortTm (.succ Tower.zero))

theorem raised_context_formed :
    ContextFormation (NativeListResultView.levelInstance raisedLevels).rules raisedContext :=
  .snoc ((NativeListResultView.levelInstance raisedLevels).refinedContext context_formed)
    (.headType (.sort _)) (.sort _)

theorem raised_assignment : FormationSensitive.CtxMor (NativeListResultView.levelInstance raisedLevels).rules
    (substLevelsCtx raisedLevels context) raisedContext (renSub wk) := by
  intro index
  simpa only [subst_renSub, raisedContext, Ctx.lookup_snoc_succ, renSub, wk] using
    (Typing.var (R := (NativeListResultView.levelInstance raisedLevels).rules) (Γ := raisedContext) index.succ)

theorem raised_caller : Judgment (NativeListResultView.levelInstance raisedLevels).rules raisedContext
    (subst (renSub wk) (substLevelsTm raisedLevels adapter))
    (subst (renSub wk) (substLevelsTm raisedLevels adapterType)) :=
  target_caller_typed raisedLevels raised_context_formed raised_assignment

set_option maxRecDepth 8192 in
theorem second_projection_refused : FormationSensitiveElaboration.replay rules decoder context
    (.lam (.snd (.var 0))) (arrow inputType outputType) Evidence.projectionSubmission = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("registered List bundle forms at the selected method universe",
    FormationSensitiveElaboration.replay rules decoder context inputType (sortTm NativeListResultView.level) Evidence.inputSubmission),
   ("registered dependent List result view forms",
    FormationSensitiveElaboration.replay rules decoder context outputType (sortTm NativeListResultView.level) Evidence.outputSubmission),
   ("registered List projection replays independently",
    FormationSensitiveElaboration.replay rules decoder context projection (arrow inputType outputType) Evidence.projectionSubmission),
   ("registered List method result family forms",
    FormationSensitiveElaboration.replay rules decoder context resultType (sortTm NativeListResultView.level) Evidence.resultSubmission),
   ("registered List projection certificate refuses second projection",
    !(FormationSensitiveElaboration.replay rules decoder context (.lam (.snd (.var 0)))
      (arrow inputType outputType) Evidence.projectionSubmission))]

end Controls

#print axioms primitive_evidence
#print axioms field_evidence
#print axioms adapter_typed
#print axioms programme_typed
#print axioms caller_typed
#print axioms adapter_levels
#print axioms target_caller_typed
#print axioms Controls.raised_caller
#print axioms Controls.second_projection_refused
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerListResultAdapter.Registered
