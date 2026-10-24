import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestResultArguments

/-!
# Specializing registered constructor methods at their original fields

Original fields form a dependent telescope. Supplying them leaves precisely
the curried induction-hypothesis interface, in source order, and the motive
at the fully applied constructor. This connects result-argument adapters to
the existing declaration-type generator without assuming that a generated
adapter already has its required type.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestMethodSpecialization

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation FormationSensitive FunctionArgumentAdapters
open IndexedInductive.Guest (TermEnv mapEnv)
open IndexedInductive.Guest.Types (weakenEnvironment)
open IndexedPositiveContainerGuestTypes IndexedPositiveContainerGuestPlans
open IndexedPositiveContainerGuestResultArguments

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

def hypothesisTypes (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} : {context : List I.SortCode} → (code : Code I registry parameters context) →
    {n : Nat} → TypeSyntax I Head n → TermEnv I Head n context → Tm Head n →
    (Fin (fieldCount code) → Tm Head n) → List (Tm Head n)
  | _, .result _, _, _, _, _, _ => []
  | _, .data _ rest, _, types, environment, motive, fields =>
      hypothesisTypes indexing containers rest types
        (fields ⟨0, by simp [fieldCount]⟩, environment) motive (fun i => fields i.succ)
  | _, .recursive index rest, _, types, environment, motive, fields =>
      .app (indexing.predicateAt motive index environment) (fields ⟨0, by simp [fieldCount]⟩) ::
        hypothesisTypes indexing containers rest types environment motive (fun i => fields i.succ)
  | _, .nested name entry registered output index rest, _, types, environment, motive, fields =>
      containers.bundleType name entry registered output environment
        (indexing.familyAt types.family index environment) (indexing.predicateAt motive index environment)
        (fields ⟨0, by simp [fieldCount]⟩) ::
        hypothesisTypes indexing containers rest types environment motive (fun i => fields i.succ)

def conclusion (indexing : Indexing I Head) {parameters : Nat} :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    {n : Nat} → TermEnv I Head n context → Tm Head n → Tm Head n →
    (Fin (fieldCount code) → Tm Head n) → Tm Head n
  | _, .result index, _, environment, motive, constructor, _ =>
      .app (indexing.predicateAt motive index environment) constructor
  | _, .data _ rest, _, environment, motive, constructor, fields =>
      conclusion indexing rest (fields ⟨0, by simp [fieldCount]⟩, environment) motive
        (.app constructor (fields ⟨0, by simp [fieldCount]⟩)) (fun i => fields i.succ)
  | _, .recursive _ rest, _, environment, motive, constructor, fields =>
      conclusion indexing rest environment motive
        (.app constructor (fields ⟨0, by simp [fieldCount]⟩)) (fun i => fields i.succ)
  | _, .nested _ _ _ _ _ rest, _, environment, motive, constructor, fields =>
      conclusion indexing rest environment motive
        (.app constructor (fields ⟨0, by simp [fieldCount]⟩)) (fun i => fields i.succ)

def instantiateFields {parameters : Nat} : {context : List I.SortCode} →
    (code : Code I registry parameters context) → {n : Nat} →
    (Fin (fieldCount code) → Tm Head n) → Tm Head n → Option (Tm Head n)
  | _, .result _, _, _, type => some type
  | _, .data _ rest, _, fields, .pi _ body =>
      instantiateFields rest (fun i => fields i.succ) (inst0 (fields ⟨0, by simp [fieldCount]⟩) body)
  | _, .recursive _ rest, _, fields, .pi _ body =>
      instantiateFields rest (fun i => fields i.succ) (inst0 (fields ⟨0, by simp [fieldCount]⟩) body)
  | _, .nested _ _ _ _ _ rest, _, fields, .pi _ body =>
      instantiateFields rest (fun i => fields i.succ) (inst0 (fields ⟨0, by simp [fieldCount]⟩) body)
  | _, _, _, _, _ => none

theorem TypeSyntax.open_weaken {n : Nat} (types : TypeSyntax I Head n) (argument : Tm Head n) :
    types.weaken.map (subst (subst0 argument)) = types := by
  cases types
  simp only [TypeSyntax.weaken, TypeSyntax.map]
  congr 1
  · funext sort
    exact inst0_rename_wk argument _
  · exact inst0_rename_wk argument _
  · funext name
    exact inst0_rename_wk argument _

theorem environment_open_weaken {context : List I.SortCode} {n : Nat}
    (environment : TermEnv I Head n context) (argument : Tm Head n) :
    mapEnv (subst (subst0 argument)) (weakenEnvironment environment) = environment := by
  induction context with
  | nil => rfl
  | cons sort rest ih =>
      exact Prod.ext (inst0_rename_wk argument environment.1) (ih environment.2)

theorem pending_open_weaken {n : Nat} (pending : List (Tm Head n)) (argument : Tm Head n) :
    (pending.map (rename wk)).map (subst (subst0 argument)) = pending := by
  rw [List.map_map]
  have identity : (subst (subst0 argument) ∘ rename wk : Tm Head n → Tm Head n) = id :=
    funext (inst0_rename_wk argument)
  rw [identity, List.map_id]

theorem slots_inputs (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) :
    (slots indexing containers results code types environment motive fields).map Slot.input =
      hypothesisTypes indexing containers code types environment motive fields := by
  induction code with
  | result _ => rfl
  | data _ _ ih => exact ih _ _
  | recursive _ _ ih => simp only [slots, hypothesisTypes, List.map_cons, directSlot, ih]
  | nested _ _ _ _ _ _ ih => simp only [slots, hypothesisTypes, List.map_cons, nestedSlot, ih]

theorem slots_outputs (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) :
    (slots indexing containers results code types environment motive fields).map Slot.output =
      hypothesisTypes indexing (results.viewRegistry containers) code types environment motive fields := by
  induction code with
  | result _ => rfl
  | data _ _ ih => exact ih _ _
  | recursive _ _ ih => simp only [slots, hypothesisTypes, List.map_cons, directSlot, ih]
  | nested _ _ _ _ _ _ ih =>
      simp only [slots, hypothesisTypes, List.map_cons, nestedSlot, ResultSyntax.viewRegistry, ih]

theorem methodBody_specialize (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (types : TypeSyntax I Head n) (environment : TermEnv I Head n context)
    (motive constructor : Tm Head n) (pending : List (Tm Head n))
    (fields : Fin (fieldCount code) → Tm Head n) :
    instantiateFields code fields (methodBody indexing containers code types environment motive constructor pending) =
      some (hypotheses (pending ++ hypothesisTypes indexing containers code types environment motive fields)
        (conclusion indexing code environment motive constructor fields)) := by
  induction code generalizing n with
  | result index => simp only [instantiateFields, methodBody, hypothesisTypes, conclusion, List.append_nil]
  | data sort rest ih =>
      simp only [instantiateFields, methodBody]
      rw [inst0, methodBody_substitute indexing containers rest types.weaken
        (.var 0, weakenEnvironment environment) (rename wk motive)
        (.app (rename wk constructor) (.var 0)) (pending.map (rename wk))]
      simp only [TypeSyntax.open_weaken, mapEnv, subst, subst0, Fin.cases_zero,
        environment_open_weaken, pending_open_weaken, show ∀ term : Tm Head n,
          subst (subst0 (fields ⟨0, by simp [fieldCount]⟩)) (rename wk term) = term from
          inst0_rename_wk _]
      simpa only [hypothesisTypes, conclusion, List.map_id] using
        ih types (fields ⟨0, by simp [fieldCount]⟩, environment) motive
          (.app constructor (fields ⟨0, by simp [fieldCount]⟩)) pending (fun i => fields i.succ)
  | recursive index rest ih =>
      simp only [instantiateFields, methodBody]
      rw [inst0, methodBody_substitute]
      simp only [TypeSyntax.open_weaken, List.map_append, List.map_cons, List.map_nil, pending_open_weaken,
        subst, indexing.predicateAt_substitute, environment_open_weaken,
        show ∀ term : Tm Head n,
          subst (subst0 (fields ⟨0, by simp [fieldCount]⟩)) (rename wk term) = term from
          inst0_rename_wk _, subst0, Fin.cases_zero]
      have checked := ih types environment motive (.app constructor (fields ⟨0, by simp [fieldCount]⟩))
          (pending ++ [.app (indexing.predicateAt motive index environment)
            (fields ⟨0, by simp [fieldCount]⟩)]) (fun i => fields i.succ)
      convert checked using 1
      exact congrArg (fun arguments => some (hypotheses arguments
          (conclusion indexing rest environment motive
            (.app constructor (fields ⟨0, by simp [fieldCount]⟩)) (fun i => fields i.succ))))
        (List.append_assoc pending [_] _).symm
  | nested name entry registered output index rest ih =>
      simp only [instantiateFields, methodBody]
      rw [inst0, methodBody_substitute]
      simp only [TypeSyntax.open_weaken, List.map_append, List.map_cons, List.map_nil, pending_open_weaken,
        subst, containers.bundleType_substitute, indexing.familyAt_substitute,
        indexing.predicateAt_substitute, environment_open_weaken,
        show ∀ term : Tm Head n,
          subst (subst0 (fields ⟨0, by simp [fieldCount]⟩)) (rename wk term) = term from
          inst0_rename_wk _, subst0, Fin.cases_zero]
      simpa only [hypothesisTypes, conclusion, List.append_assoc, List.cons_append, List.nil_append] using
        ih types environment motive (.app constructor (fields ⟨0, by simp [fieldCount]⟩))
          (pending ++ [containers.bundleType name entry registered output environment
            (indexing.familyAt types.family index environment) (indexing.predicateAt motive index environment)
            (fields ⟨0, by simp [fieldCount]⟩)]) (fun i => fields i.succ)

def applyFields {parameters : Nat} : {context : List I.SortCode} →
    (code : Code I registry parameters context) → {n : Nat} →
    (Fin (fieldCount code) → Tm Head n) → Tm Head n → Tm Head n
  | _, .result _, _, _, function => function
  | _, .data _ rest, _, fields, function =>
      applyFields rest (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))
  | _, .recursive _ rest, _, fields, function =>
      applyFields rest (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))
  | _, .nested _ _ _ _ _ rest, _, fields, function =>
      applyFields rest (fun i => fields i.succ) (.app function (fields ⟨0, by simp [fieldCount]⟩))

/-- The evidence at each original field is its dependent domain typing.
The remaining interface is determined by ordinary substitution into the
codomain. This relation does not mention an adapter programme. -/
inductive SuppliedFields (R : Rules Head) {n : Nat} (ambient : Ctx Head n) {parameters : Nat} :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    (Fin (fieldCount code) → Tm Head n) → Tm Head n → Tm Head n → Prop where
  | result {context : List I.SortCode} (index : I.IndexExpr context)
      (fields : Fin (fieldCount (.result index : Code I registry parameters context)) → Tm Head n)
      (type : Tm Head n) : SuppliedFields R ambient (.result index) fields type type
  | data {context : List I.SortCode} (sort : I.SortCode) (rest : Code I registry parameters (sort :: context))
      (fields : Fin (fieldCount (.data sort rest)) → Tm Head n)
      {domain : Tm Head n} {body : Tm Head (n + 1)} {target : Tm Head n}
      (argument : Typing R ambient (fields ⟨0, by simp [fieldCount]⟩) domain)
      (remaining : SuppliedFields R ambient rest (fun i => fields i.succ)
        (inst0 (fields ⟨0, by simp [fieldCount]⟩) body) target) :
      SuppliedFields R ambient (.data sort rest) fields (.pi domain body) target
  | recursive {context : List I.SortCode} (index : I.IndexExpr context)
      (rest : Code I registry parameters context)
      (fields : Fin (fieldCount (.recursive index rest)) → Tm Head n)
      {domain : Tm Head n} {body : Tm Head (n + 1)} {target : Tm Head n}
      (argument : Typing R ambient (fields ⟨0, by simp [fieldCount]⟩) domain)
      (remaining : SuppliedFields R ambient rest (fun i => fields i.succ)
        (inst0 (fields ⟨0, by simp [fieldCount]⟩) body) target) :
      SuppliedFields R ambient (.recursive index rest) fields (.pi domain body) target
  | nested {context : List I.SortCode} (name : String) (entry : Entry I)
      (registered : registry.lookup name = some entry) (output : entry.OutputExpr context)
      (index : I.IndexExpr context) (rest : Code I registry parameters context)
      (fields : Fin (fieldCount (.nested name entry registered output index rest)) → Tm Head n)
      {domain : Tm Head n} {body : Tm Head (n + 1)} {target : Tm Head n}
      (argument : Typing R ambient (fields ⟨0, by simp [fieldCount]⟩) domain)
      (remaining : SuppliedFields R ambient rest (fun i => fields i.succ)
        (inst0 (fields ⟨0, by simp [fieldCount]⟩) body) target) :
      SuppliedFields R ambient (.nested name entry registered output index rest) fields (.pi domain body) target

theorem SuppliedFields.instantiate {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {parameters : Nat} {context : List I.SortCode} {code : Code I registry parameters context}
    {fields : Fin (fieldCount code) → Tm Head n} {source target : Tm Head n}
    (typed : SuppliedFields R ambient code fields source target) :
    instantiateFields code fields source = some target := by
  induction typed with
  | result => rfl
  | data _ _ _ _ _ ih => exact ih
  | recursive _ _ _ _ _ ih => exact ih
  | nested _ _ _ _ _ _ _ _ _ ih => exact ih

theorem SuppliedFields.apply_typed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {parameters : Nat} {context : List I.SortCode} {code : Code I registry parameters context}
    {fields : Fin (fieldCount code) → Tm Head n} {source target : Tm Head n}
    (typed : SuppliedFields R ambient code fields source target) {function : Tm Head n}
    (functionTyped : Typing R ambient function source) :
    Typing R ambient (applyFields code fields function) target := by
  induction typed generalizing function with
  | result => exact functionTyped
  | data _ _ _ argument _ ih => exact ih (Typing.appElim functionTyped argument)
  | recursive _ _ _ argument _ ih => exact ih (Typing.appElim functionTyped argument)
  | nested _ _ _ _ _ _ _ argument _ ih => exact ih (Typing.appElim functionTyped argument)

/-- The actual declaration-generated view method is applied to its typed
original fields before the induction-hypothesis adapter is generated. -/
theorem adaptedMethod_typed (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive constructor : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) {R : Rules Head} {ambient : Ctx Head n}
    {level : Head} (isUniverse : R.isUniverse level)
    (closure : ∃ result, R.join level level result ∧ (result = level ∨ R.cumulative result level))
    (primitiveEvidence : SlotsTyped R ambient level
      (slots indexing containers results code types environment motive fields))
    (resultFormed : Typing R ambient (conclusion indexing code environment motive constructor fields) (.head level))
    {function finalType : Tm Head n}
    (source : Judgment R ambient function
      (methodBody indexing (results.viewRegistry containers) code types environment motive constructor []))
    (fieldEvidence : SuppliedFields R ambient code fields
      (methodBody indexing (results.viewRegistry containers) code types environment motive constructor []) finalType) :
    Judgment R ambient
      (adapter indexing containers results code types environment motive fields (applyFields code fields function))
      (hypotheses ((slots indexing containers results code types environment motive fields).map Slot.input)
        (conclusion indexing code environment motive constructor fields)) := by
  have specialized := methodBody_specialize indexing (results.viewRegistry containers)
    code types environment motive constructor [] fields
  have exactType := Option.some.inj (fieldEvidence.instantiate.symm.trans specialized)
  simp only [List.nil_append, ← slots_outputs indexing containers results] at exactType
  have applied := fieldEvidence.apply_typed source.typing
  rw [exactType] at applied
  exact IndexedPositiveContainerGuestResultArguments.adapter_typed indexing containers results
    code types environment motive fields isUniverse closure primitiveEvidence resultFormed
    ⟨source.context, applied⟩

#print axioms methodBody_specialize
#print axioms SuppliedFields.apply_typed
#print axioms adaptedMethod_typed

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestMethodSpecialization
