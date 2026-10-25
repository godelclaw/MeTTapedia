import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FunctionArgumentAdapters
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeFormationReadback
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeJoins
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllOriginalInputUniversesChecking

/-!
# Vector result adapters at symbolic universe bounds and neutral inputs

The original lower-input/higher-result programme supplies the projection.
Its dependent prefix retains an arbitrary element type, result type, length
and source Vector. The complete closed product type earns that prefix's
formation; the existing typed telescope application supplies the projection
without decoding the neutral Vector or assuming a generated adapter typing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllSymbolicResultAdapter

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration FormationSensitive FunctionArgumentAdapters
open NativeNaturalVectorFamilies RussellTarski TypedEquality.Normalization
open NativeVectorAll.ResultView

abbrev rules := OriginalInputUniverses.rules
abbrev decoder := OriginalInputUniverses.decoder
abbrev choices := OriginalInputUniverses.choices
abbrev dataLevel := NativeVectorAll.Universes.dataLevel
abbrev resultLevel := NativeVectorAll.Universes.predicateLevel
abbrev methodLevel := NativeVectorAll.Universes.resultLevel

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def parameterContext : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (sortTm dataLevel)) (sortTm resultLevel)) natTm)
    (vecApp (.var 2) (.var 0))

def inputType : Tower.Tm 4 :=
  NativeVectorAll.Universes.allType (.var 3) (predicate (.var 2)) (.var 1) (.var 0)
def outputType : Tower.Tm 4 := OriginalInputUniverses.upperVec (.var 2) (.var 1)
def projectionType : Tower.Tm 4 := arrow inputType outputType
def resultType : Tower.Tm 4 := .var 2

theorem closed_type_readback : TelescopeAbstraction.closeType parameterContext projectionType =
    OriginalInputUniverses.programType := by decide +kernel

def fullTypeAccepted : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 256 .nil
    OriginalInputUniverses.programType (sortTm (.succ methodLevel))).isSome

set_option maxRecDepth 8192 in
theorem full_type_checked : fullTypeAccepted = true := by decide +kernel

theorem full_type_formed : Judgment rules .nil OriginalInputUniverses.programType (sortTm (.succ methodLevel)) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp full_type_checked
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 256 .nil _ _ submission produced

theorem parameter_context_formation : ContextFormation rules parameterContext ∧
    ∃ level, rules.isUniverse level ∧ Typing rules parameterContext projectionType (.head level) := by
  apply TelescopeAbstraction.formation_of_closeType (R := rules) parameterContext
    (level := .sort (.succ methodLevel)) (.sort _)
  rw [closed_type_readback]
  exact full_type_formed.typing

theorem parameter_context_formed : ContextFormation rules parameterContext := parameter_context_formation.1

theorem parameter_identity : FormationSensitive.CtxMor rules parameterContext parameterContext ids := by
  intro index
  simpa only [subst_ids, ids] using (Typing.var (R := rules) (Γ := parameterContext) index)

def projection : Tower.Tm 4 :=
  TelescopeAbstraction.applyClosed parameterContext ids (liftClosed OriginalInputUniverses.program)

theorem projection_source_typed : Typing rules parameterContext (liftClosed OriginalInputUniverses.program)
    (liftClosed (TelescopeAbstraction.closeType parameterContext projectionType)) := by
  rw [closed_type_readback]
  exact FormationCheckedTelescopePrograms.liftClosed_typing
    OriginalInputUniverses.program_formed.typing parameterContext

theorem projection_typed : Judgment rules parameterContext projection projectionType := by
  have applied := FormationCheckedTelescopePrograms.apply_typed parameter_identity projection_source_typed
  exact ⟨parameter_context_formed, by simpa only [projection, subst_ids] using applied⟩

def checked (term type : Tower.Tm 4) : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 256 parameterContext term type).isSome

theorem checked_sound {term type : Tower.Tm 4} (accepted : checked term type = true) :
    Judgment rules parameterContext term type := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 256 parameterContext
    term type submission produced

set_option maxRecDepth 8192 in
theorem input_formed : checked inputType (sortTm methodLevel) = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem output_formed : checked outputType (sortTm methodLevel) = true := by decide +kernel

theorem result_lookup : Ctx.lookup parameterContext (2 : Fin 4) = sortTm resultLevel := by decide +kernel

theorem result_at_caller_level : Typing rules parameterContext resultType (sortTm resultLevel) := by
  simpa only [resultType, result_lookup] using (Typing.var (R := rules) (Γ := parameterContext) 2)

theorem result_formed : Typing rules parameterContext resultType (sortTm methodLevel) :=
  .cumul result_at_caller_level (fun _ => Nat.le_max_right _ _)

theorem method_universe : rules.isUniverse (.sort methodLevel) := .sort _

theorem product_closure : ∃ result, rules.join (.sort methodLevel) (.sort methodLevel) result ∧
    (result = .sort methodLevel ∨ rules.cumulative result (.sort methodLevel)) :=
  ⟨.sort (.max methodLevel methodLevel), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩

def slot : Slot Tower.Head 4 := ⟨inputType, outputType, projection⟩
def slots : List (Slot Tower.Head 4) := [slot]

theorem slots_typed : SlotsTyped rules parameterContext (.sort methodLevel) slots := by
  intro selected member
  have same : selected = slot := by simpa only [slots, List.mem_singleton] using member
  subst selected
  exact ⟨(checked_sound input_formed).typing, (checked_sound output_formed).typing, projection_typed.typing⟩

def sourceType : Tower.Tm 4 := curriedType (slots.map Slot.output) resultType
def targetType : Tower.Tm 4 := curriedType (slots.map Slot.input) resultType
def context : Tower.Ctx 5 := .snoc parameterContext sourceType

theorem context_formed : ContextFormation rules context := by
  refine .snoc parameter_context_formed ?_ method_universe
  exact curriedType_formed method_universe product_closure (slots.map Slot.output) resultType
    (by
      intro type member
      obtain ⟨selected, present, rfl⟩ := List.mem_map.mp member
      exact (slots_typed selected present).2.1) result_formed

theorem source_typed : Judgment rules context (.var 0)
    (curriedType ((slots.map Slot.weaken).map Slot.output) (rename wk resultType)) := by
  refine ⟨context_formed, ?_⟩
  simpa only [context, sourceType, Ctx.lookup_snoc_zero, curriedType_rename, List.map_map,
    Slot.weaken, Slot.map, Function.comp_def] using (Typing.var (R := rules) (Γ := context) 0)

def programme : Tower.Tm 5 := adapt (slots.map Slot.weaken) (.var 0)

theorem programme_typed : Judgment rules context programme (rename wk targetType) := by
  have generated := adapt_judgment method_universe product_closure (slots.map Slot.weaken)
    (slots_typed.weaken sourceType) result_formed.weaken source_typed
  simpa only [context, programme, targetType, curriedType_rename, List.map_map,
    Slot.weaken, Slot.map, Function.comp_def] using generated

theorem universe_regularity : UniverseRegularity rules :=
  towerUniverseRegularity.includeSignature OriginalInputUniverses.signature

theorem joins {first second : Tower.Head} (firstUniverse : rules.isUniverse first)
    (secondUniverse : rules.isUniverse second) :
    ∃ result, rules.isUniverse result ∧ rules.join first second result :=
  FormationCheckedTelescopePrograms.tower_joins firstUniverse secondUniverse

def closedProgramme : Tower.Tm 0 := TelescopeAbstraction.closeTerm context programme
def closedProgrammeType : Tower.Tm 0 := TelescopeAbstraction.closeType context (rename wk targetType)

theorem closed_programme_typed : Judgment rules .nil closedProgramme closedProgrammeType :=
  ⟨.nil, FormationCheckedTelescopePrograms.close_typed universe_regularity
    (fun first second => joins first second) context_formed programme_typed.typing⟩

def expectedProgramme : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam (.lam (.app (.var 1)
    (appSpine (liftClosed OriginalInputUniverses.program) [.var 5, .var 4, .var 3, .var 2, .var 0])))))))

theorem closed_programme_readback : closedProgramme = expectedProgramme := by decide +kernel

def slotsAtLevels (theta : Nat → LevelExpr Nat) : List (Slot Tower.Head 5) :=
  (slots.map Slot.weaken).map (Slot.map (substLevelsTm theta))
def programmeAtLevels (theta : Nat → LevelExpr Nat) : Tower.Tm 5 :=
  adapt (slotsAtLevels theta) (.var 0)
def typeAtLevels (theta : Nat → LevelExpr Nat) : Tower.Tm 5 :=
  curriedType ((slotsAtLevels theta).map Slot.input) (substLevelsTm theta (rename wk resultType))

theorem programme_levels_readback (theta : Nat → LevelExpr Nat) :
    substLevelsTm theta programme = programmeAtLevels theta := by
  have same : (substLevelsTm theta : Tower.Tm 5 → Tower.Tm 5) = Tm.mapHead (substLevelsHead theta) := rfl
  simp only [programme, programmeAtLevels, slotsAtLevels, same, substLevelsTm, adapt_mapHead, Tm.mapHead]

theorem programme_type_levels_readback (theta : Nat → LevelExpr Nat) :
    substLevelsTm theta (rename wk targetType) = typeAtLevels theta := by
  simp only [targetType, typeAtLevels, slotsAtLevels, substLevelsTm, curriedType_rename,
    curriedType_mapHead, List.map_map, Slot.weaken, Slot.map, Function.comp_def, Tm.mapHead_rename]

theorem programme_levels_typed (theta : Nat → LevelExpr Nat) :
    Judgment (OriginalInputUniverses.resultLevelInstance theta).rules (substLevelsCtx theta context)
      (programmeAtLevels theta) (typeAtLevels theta) := by
  have transported := (OriginalInputUniverses.resultLevelInstance theta).refinedJudgment programme_typed
  rw [programme_levels_readback, programme_type_levels_readback] at transported
  exact transported

theorem closed_programme_levels_readback (theta : Nat → LevelExpr Nat) :
    substLevelsTm theta closedProgramme =
      TelescopeAbstraction.closeTerm (substLevelsCtx theta context) (programmeAtLevels theta) := by
  change (TelescopeAbstraction.closeTerm context programme).mapHead (substLevelsHead theta) = _
  rw [TelescopeAbstraction.closeTerm_mapHead]
  exact congrArg (TelescopeAbstraction.closeTerm (substLevelsCtx theta context))
    (programme_levels_readback theta)

theorem closed_type_levels_readback (theta : Nat → LevelExpr Nat) :
    substLevelsTm theta closedProgrammeType =
      TelescopeAbstraction.closeType (substLevelsCtx theta context) (typeAtLevels theta) := by
  change (TelescopeAbstraction.closeType context (rename wk targetType)).mapHead (substLevelsHead theta) = _
  rw [TelescopeAbstraction.closeType_mapHead]
  exact congrArg (TelescopeAbstraction.closeType (substLevelsCtx theta context))
    (programme_type_levels_readback theta)

theorem closed_programme_levels_typed (theta : Nat → LevelExpr Nat) :
    Judgment (OriginalInputUniverses.resultLevelInstance theta).rules .nil
      (TelescopeAbstraction.closeTerm (substLevelsCtx theta context) (programmeAtLevels theta))
      (TelescopeAbstraction.closeType (substLevelsCtx theta context) (typeAtLevels theta)) := by
  have transported := (OriginalInputUniverses.resultLevelInstance theta).refinedJudgment closed_programme_typed
  rw [closed_programme_levels_readback, closed_type_levels_readback] at transported
  exact transported

theorem programme_substitution_levels (theta : Nat → LevelExpr Nat) {n : Nat}
    (sigma : Sub Tower.Head 5 n) :
    substLevelsTm theta (subst sigma programme) =
      subst (fun index => substLevelsTm theta (sigma index)) (programmeAtLevels theta) := by
  change (subst sigma programme).mapHead (substLevelsHead theta) = _
  rw [Tm.mapHead_subst]
  exact congrArg (subst (fun index => substLevelsTm theta (sigma index)))
    (programme_levels_readback theta)

theorem type_substitution_levels (theta : Nat → LevelExpr Nat) {n : Nat}
    (sigma : Sub Tower.Head 5 n) :
    substLevelsTm theta (subst sigma (rename wk targetType)) =
      subst (fun index => substLevelsTm theta (sigma index)) (typeAtLevels theta) := by
  change (subst sigma (rename wk targetType)).mapHead (substLevelsHead theta) = _
  rw [Tm.mapHead_subst]
  exact congrArg (subst (fun index => substLevelsTm theta (sigma index)))
    (programme_type_levels_readback theta)

theorem programme_substitution_levels_typed (theta : Nat → LevelExpr Nat) {n : Nat}
    {replacement : Tower.Ctx n} {sigma : Sub Tower.Head 5 n}
    (formed : ContextFormation rules replacement)
    (assigned : FormationSensitive.CtxMor rules context replacement sigma) :
    Judgment (OriginalInputUniverses.resultLevelInstance theta).rules (substLevelsCtx theta replacement)
      (subst (fun index => substLevelsTm theta (sigma index)) (programmeAtLevels theta))
      (subst (fun index => substLevelsTm theta (sigma index)) (typeAtLevels theta)) := by
  have transported := (OriginalInputUniverses.resultLevelInstance theta).refinedJudgment
    (programme_typed.substitute formed assigned)
  rw [programme_substitution_levels, type_substitution_levels] at transported
  exact transported

/-- Callers may supply inputs that become available in the instantiated
profile. Their actual context morphism is checked in that target profile. -/
theorem programme_at_levels_inputs_typed (theta : Nat → LevelExpr Nat) {n : Nat}
    {replacement : Tower.Ctx n} {sigma : Sub Tower.Head 5 n}
    (formed : ContextFormation (OriginalInputUniverses.resultLevelInstance theta).rules replacement)
    (assigned : FormationSensitive.CtxMor (OriginalInputUniverses.resultLevelInstance theta).rules
      (substLevelsCtx theta context) replacement sigma) :
    Judgment (OriginalInputUniverses.resultLevelInstance theta).rules replacement
      (subst sigma (programmeAtLevels theta)) (subst sigma (typeAtLevels theta)) :=
  (programme_levels_typed theta).substitute formed assigned

def appliedClosedProgramme (theta : Nat → LevelExpr Nat) {n : Nat}
    (sigma : Sub Tower.Head 5 n) : Tower.Tm n :=
  TelescopeAbstraction.applyClosed (substLevelsCtx theta context) sigma
    (liftClosed (TelescopeAbstraction.closeTerm (substLevelsCtx theta context) (programmeAtLevels theta)))

theorem applied_closed_programme_typed (theta : Nat → LevelExpr Nat) {n : Nat}
    {replacement : Tower.Ctx n} {sigma : Sub Tower.Head 5 n}
    (formed : ContextFormation (OriginalInputUniverses.resultLevelInstance theta).rules replacement)
    (assigned : FormationSensitive.CtxMor (OriginalInputUniverses.resultLevelInstance theta).rules
      (substLevelsCtx theta context) replacement sigma) :
    Judgment (OriginalInputUniverses.resultLevelInstance theta).rules replacement
      (appliedClosedProgramme theta sigma) (subst sigma (typeAtLevels theta)) := by
  exact ⟨formed, FormationCheckedTelescopePrograms.apply_typed assigned
    (FormationCheckedTelescopePrograms.liftClosed_typing (closed_programme_levels_typed theta).typing replacement)⟩

theorem applied_closed_programme_beta (theta : Nat → LevelExpr Nat) {n : Nat}
    (sigma : Sub Tower.Head 5 n) :
    TelescopeAbstraction.BetaSteps (appliedClosedProgramme theta sigma)
      (subst sigma (programmeAtLevels theta)) :=
  TelescopeAbstraction.applyClosed_beta (substLevelsCtx theta context) sigma (programmeAtLevels theta)

namespace Controls

theorem mixed_levels_programme :
    Judgment (OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).rules
      (substLevelsCtx OriginalInputUniverses.closedLevels context)
      (programmeAtLevels OriginalInputUniverses.closedLevels) (typeAtLevels OriginalInputUniverses.closedLevels) :=
  programme_levels_typed OriginalInputUniverses.closedLevels

theorem mixed_levels_closed_programme :
    Judgment (OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).rules .nil
      (TelescopeAbstraction.closeTerm (substLevelsCtx OriginalInputUniverses.closedLevels context)
        (programmeAtLevels OriginalInputUniverses.closedLevels))
      (TelescopeAbstraction.closeType (substLevelsCtx OriginalInputUniverses.closedLevels context)
        (typeAtLevels OriginalInputUniverses.closedLevels)) :=
  closed_programme_levels_typed OriginalInputUniverses.closedLevels

set_option maxRecDepth 8192 in
theorem child_vector_refused : checked (.var 0) inputType = false := by decide +kernel

def collapseLevels : Nat → LevelExpr Nat := fun _ => Tower.zero

theorem source_bounds_distinct : (.sort dataLevel : Tower.Head) ≠ .sort resultLevel := by decide +kernel

theorem collapsed_bounds_equal :
    substLevelsHead collapseLevels (.sort dataLevel) = substLevelsHead collapseLevels (.sort resultLevel) := rfl

theorem level_substitution_not_injective : ¬ Function.Injective (substLevelsHead collapseLevels) := by
  intro injective
  exact source_bounds_distinct (injective collapsed_bounds_equal)

theorem collapsed_levels_programme :
    Judgment (OriginalInputUniverses.resultLevelInstance collapseLevels).rules
      (substLevelsCtx collapseLevels context) (programmeAtLevels collapseLevels) (typeAtLevels collapseLevels) :=
  programme_levels_typed collapseLevels

/-- The existing within-signature evidence maps use a larger recursor
capacity. Their Nat eliminator cannot be merged with the old output profile
through literal declaration agreement. This does not refute a checked
translation or a new common-capacity profile. -/
theorem raised_recursors_not_literal_compatible :
    ¬ Signature.Compatible NativeVectorAll.Universes.CumulativeElimination.signature
      OriginalInputUniverses.upper := by
  intro compatible
  have first : NativeVectorAll.Universes.CumulativeElimination.signature.entries natEliminateName =
      some ({ type := substLevelsTm NativeVectorAll.Universes.CumulativeElimination.levels natEliminateType } : Entry Tower.Head) := by
    rfl
  have second : OriginalInputUniverses.upper.entries natEliminateName =
      some ({ type := substLevelsTm Universes.levels natEliminateType } : Entry Tower.Head) := by
    rfl
  have same := congrArg Entry.type (compatible natEliminateName _ _ first second)
  have different : substLevelsTm NativeVectorAll.Universes.CumulativeElimination.levels natEliminateType ≠
      substLevelsTm Universes.levels natEliminateType := by decide +kernel
  exact different same

def missingName : DeclName := `SymbolicResultAdapter.missingType
def missingType {n : Nat} : Tower.Tm n := .const missingName
def malformedContext : Tower.Ctx 1 := .snoc .nil missingType

theorem missing_lookup : rules.constantType missingName = none := by decide +kernel

theorem raw_variable_typed : Typing rules malformedContext (.var 0) missingType := by
  simpa only [malformedContext, Ctx.lookup_snoc_zero, missingType, rename] using
    (Typing.var (R := rules) (Γ := malformedContext) 0)

theorem malformed_context_unformed : ¬ ContextFormation rules malformedContext := by
  intro formed
  cases formed with
  | snoc prior domain universeWitness =>
      obtain ⟨type, level, known, _, _⟩ := domain.constFormation
      rw [missing_lookup] at known
      cases known

theorem malformed_variable_judgment_refused : ¬ Judgment rules malformedContext (.var 0) missingType :=
  fun judgment => malformed_context_unformed judgment.context

theorem malformed_closed_type_unformed :
    ¬ ∃ level, rules.isUniverse level ∧
      Typing rules .nil (TelescopeAbstraction.closeType malformedContext missingType) (.head level) := by
  rintro ⟨level, universeWitness, formed⟩
  exact malformed_context_unformed
    (TelescopeAbstraction.formation_of_closeType malformedContext universeWitness formed).1

theorem natural_type_formed : Typing rules context natTm (sortTm Tower.zero) := by
  have known : rules.constantType natName = some (sortTm Tower.zero) := by decide +kernel
  have typed := Typing.const (R := rules) (Γ := context) (u := .sort (.succ Tower.zero))
    known (.headType (.sort Tower.zero)) (.sort _)
  simpa only [natTm, liftClosed, sortTm, rename] using typed

def extendedContext : Tower.Ctx 6 := .snoc context natTm

theorem extended_context_formed : ContextFormation rules extendedContext :=
  .snoc context_formed natural_type_formed (.sort _)

theorem weakening_typed : FormationSensitive.CtxMor rules context extendedContext (renSub wk) := by
  intro index
  simpa only [extendedContext, renSub, subst_renSub, rename] using
    (Typing.var (R := rules) (Γ := context) index).weaken (extension := natTm)

def assignment : Sub Tower.Head 5 6 :=
  fun index => substLevelsTm OriginalInputUniverses.closedLevels ((renSub wk : Sub Tower.Head 5 6) index)

theorem assignment_typed :
    FormationSensitive.CtxMor
      (OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).rules
      (substLevelsCtx OriginalInputUniverses.closedLevels context)
      (substLevelsCtx OriginalInputUniverses.closedLevels extendedContext) assignment :=
  (OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).refinedSubstitution weakening_typed

theorem weakening_square_typed :
    Judgment (OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).rules
      (substLevelsCtx OriginalInputUniverses.closedLevels extendedContext)
      (subst assignment (programmeAtLevels OriginalInputUniverses.closedLevels))
      (subst assignment (typeAtLevels OriginalInputUniverses.closedLevels)) :=
  programme_substitution_levels_typed OriginalInputUniverses.closedLevels extended_context_formed weakening_typed

theorem target_inputs_typed :
    Judgment (OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).rules
      (substLevelsCtx OriginalInputUniverses.closedLevels extendedContext)
      (subst assignment (programmeAtLevels OriginalInputUniverses.closedLevels))
      (subst assignment (typeAtLevels OriginalInputUniverses.closedLevels)) :=
  programme_at_levels_inputs_typed OriginalInputUniverses.closedLevels
    ((OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).refinedContext extended_context_formed)
    assignment_typed

theorem closed_application_typed :
    Judgment (OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).rules
      (substLevelsCtx OriginalInputUniverses.closedLevels extendedContext)
      (appliedClosedProgramme OriginalInputUniverses.closedLevels assignment)
      (subst assignment (typeAtLevels OriginalInputUniverses.closedLevels)) :=
  applied_closed_programme_typed OriginalInputUniverses.closedLevels
    ((OriginalInputUniverses.resultLevelInstance OriginalInputUniverses.closedLevels).refinedContext extended_context_formed)
    assignment_typed

theorem closed_application_beta :
    TelescopeAbstraction.BetaSteps (appliedClosedProgramme OriginalInputUniverses.closedLevels assignment)
      (subst assignment (programmeAtLevels OriginalInputUniverses.closedLevels)) :=
  applied_closed_programme_beta OriginalInputUniverses.closedLevels assignment

end Controls

#print axioms closed_type_readback
#print axioms parameter_context_formation
#print axioms projection_typed
#print axioms slots_typed
#print axioms programme_typed
#print axioms full_type_formed
#print axioms closed_programme_typed
#print axioms programme_levels_typed
#print axioms closed_programme_levels_typed
#print axioms programme_substitution_levels_typed
#print axioms applied_closed_programme_typed
#print axioms applied_closed_programme_beta
#print axioms Controls.mixed_levels_closed_programme
#print axioms Controls.child_vector_refused
#print axioms Controls.level_substitution_not_injective
#print axioms Controls.malformed_closed_type_unformed
#print axioms Controls.weakening_square_typed
#print axioms Controls.closed_application_typed
#print axioms Controls.closed_application_beta
#print axioms Controls.raised_recursors_not_literal_compatible

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllSymbolicResultAdapter
