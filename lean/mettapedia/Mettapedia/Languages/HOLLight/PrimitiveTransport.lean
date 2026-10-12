import Mettapedia.Languages.HOLLight.Rules
import Mettapedia.Languages.HOLLight.GraphExpansion
import Mettapedia.Languages.OpenTheory.ReverseTranslation

/-!
# Primitive OpenTheory proofs in the HOL Light inference kernel

The common equality operations retain their complete theorem objects. Joint
type and term substitutions are split into the source's `INST_TYPE` and `INST`
operations. General beta conversion is expanded into the source's trivial
`BETA` followed by `INST`, with a fresh named representative.

HOL Light's axiom operation admits hypothesis-free sequents. The transport
therefore records this source admission requirement on the selected policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight

open Mettapedia.Languages.OpenTheory Mettapedia.Logic SourceSubstitution

namespace PrimitiveTransport

def typeEntries (types : TypeSubst) : List (Ty × Ty) :=
  types.entries.map fun entry => (entry.2, .var entry.1)

private theorem variableType_typeEntries (entries : List (Name × Ty)) (name : Name) :
    variableType (entries.map fun entry => (entry.2, Ty.var entry.1)) name =
      (List.lookup name entries).getD (.var name) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, type⟩
      by_cases same : name = key
      · subst key
        simp [variableType, List.lookup]
      · simp only [List.map_cons, variableType, if_neg same]
        have missed : (name == key) = false := by simp [same]
        rw [List.lookup_cons, missed]
        exact ih

theorem typeEntries_apply (types : TypeSubst) : ∀ type : Ty,
    (typeSubstitution (typeEntries types)).apply type = types.apply type
  | .var name => by
      rw [apply_variable]
      simpa only [typeEntries, TypeSubst.apply, TypeSubst.lookup] using
        variableType_typeEntries types.entries name
  | .op operator arguments => by
      simp only [TypeSubst.apply_op]
      congr 1
      exact List.map_congr_left fun type _ => typeEntries_apply types type
termination_by type => sizeOf type

def termEntries (substitution : TypeCorrectTermSubstitution) : List TermMaplet :=
  substitution.raw.entries.map fun entry =>
    (entry.2, .var entry.1.name entry.1.ty)

theorem termEntries_admissible (substitution : TypeCorrectTermSubstitution) :
    TermMapletsAdmissible (termEntries substitution) := by
  intro entry member
  change entry ∈ substitution.raw.entries.map _ at member
  obtain ⟨stored, storedMember, storedEq⟩ := List.mem_map.mp member
  rw [← storedEq]
  exact substitution.typeCorrect stored storedMember

theorem termEntries_raw (substitution : TypeCorrectTermSubstitution) :
    SourceSubstitution.termEntries (termEntries substitution) = substitution.raw.entries := by
  simp [termEntries, SourceSubstitution.termEntries, List.filterMap_map]

def termOnly (substitution : TypeCorrectTermSubstitution) : TypeCorrectTermSubstitution :=
  ⟨⟨TypeSubst.empty, substitution.raw.entries⟩, substitution.typeCorrect⟩

theorem termEntries_admitted (substitution : TypeCorrectTermSubstitution) :
    admitTermSubstitution (termEntries substitution) = some (termOnly substitution) := by
  have valid := (all_termMapletB_eq_true_iff _).mpr (termEntries_admissible substitution)
  simp only [admitTermSubstitution, valid, ↓reduceDIte]
  congr 1
  simp [termSubstitution, termEntries_raw, termOnly]

theorem applyDB_split (substitution : TypeCorrectTermSubstitution) : ∀ term : DBTerm,
    (termOnly substitution).raw.applyDB
      ((typeOnlySubstitution (typeEntries substitution.raw.types)).raw.applyDB term) =
        substitution.raw.applyDB term
  | .const constant type => by
      simp [termOnly, typeOnlySubstitution,
        TypeCorrectTermSubstitution.ofTypes, typeEntries_apply]
  | .free sourceVar => by
      simp [TermSubst.applyDB, termOnly, typeOnlySubstitution,
        TypeCorrectTermSubstitution.ofTypes, TypeSubst.applyVar, TermSubst.lookup,
        typeEntries_apply]
  | .bound index => by simp
  | .app function argument => by
      simp only [TermSubst.applyDB_app]
      rw [applyDB_split substitution function, applyDB_split substitution argument]
  | .abs domain body => by
      simp only [TermSubst.applyDB_abs]
      rw [applyDB_split substitution body]
      simp [termOnly, typeOnlySubstitution, TypeCorrectTermSubstitution.ofTypes,
        typeEntries_apply]

theorem apply_split (substitution : TypeCorrectTermSubstitution) (term : CanonicalTerm) :
    (termOnly substitution).apply
      ((typeOnlySubstitution (typeEntries substitution.raw.types)).apply term) =
        substitution.apply term := by
  apply CanonicalTerm.ext_term
  exact applyDB_split substitution term.term

theorem substituteTheorem_split (substitution : TypeCorrectTermSubstitution)
    (input : Theorem) :
    substituteTheorem (termOnly substitution)
      (substituteTheorem (typeOnlySubstitution (typeEntries substitution.raw.types)) input) =
        substituteTheorem substitution input := by
  apply Theorem.ext
  · rfl
  · apply Sequent.ext
    · simp only [substituteTheorem, Theorem.preserveAxiomsResult,
        TypeCorrectTermSubstitution.applyHypotheses, Finset.image_image]
      apply Finset.image_congr
      intro term _
      exact apply_split substitution term
    · exact apply_split substitution input.sequent.concl

private theorem infer (policy : AxiomPolicy) (request : InferenceRequest)
    {out : Theorem} (step : request.Semantics out)
    (children : ∀ premise ∈ request.premises, Derives (Rule policy) premise) :
    Derives (Rule policy) out :=
  .node request.premises out (.inl ⟨request, rfl, step⟩) children

theorem substitution_derives (policy : AxiomPolicy)
    (substitution : TypeCorrectTermSubstitution) {input out : Theorem}
    (step : TheoremSubstitutionSemantics substitution input out)
    (proof : Derives (Rule policy) input) : Derives (Rule policy) out := by
  have output := (substituteTheorem_semantics substitution input).unique step
  rw [← output, ← substituteTheorem_split substitution input]
  apply infer policy (.inst (termEntries substitution)
      (substituteTheorem (typeOnlySubstitution (typeEntries substitution.raw.types)) input))
  · exact ⟨termOnly substitution, termEntries_admitted substitution,
      substituteTheorem_semantics _ _⟩
  · intro premise member
    simp only [InferenceRequest.premises, List.mem_singleton] at member
    subst premise
    apply infer policy (.instType (typeEntries substitution.raw.types) input)
    · exact substituteTheorem_semantics _ _
    · intro premise member
      simp only [InferenceRequest.premises, List.mem_singleton] at member
      subst premise
      exact proof

/-! ## Fresh named representatives -/

def freeNames : DBTerm → List Name
  | .const _ _ | .bound _ => []
  | .free sourceVar => [sourceVar.name]
  | .app function argument => freeNames function ++ freeNames argument
  | .abs _ body => freeNames body

private theorem boundIndex_none_of_name_absent (sourceVar : SourceVar)
    (binders : List SourceVar) (absent : sourceVar.name ∉ binders.map Var.name) :
    boundIndex sourceVar binders = none := by
  induction binders with
  | nil => rfl
  | cons binder binders ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      have different : sourceVar ≠ binder := by
        intro same
        exact absent.1 (congrArg Var.name same)
      simp only [boundIndex, sourceVarSame_eq_true_iff, different, ↓reduceIte]
      rw [ih absent.2]
      rfl

private theorem boundIndex_of_getElem (binders : List SourceVar)
    (unique : (binders.map Var.name).Nodup) (index : Nat) {sourceVar : SourceVar}
    (found : binders[index]? = some sourceVar) : boundIndex sourceVar binders = some index := by
  induction binders generalizing index with
  | nil => simp at found
  | cons binder binders ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst sourceVar
          simp [boundIndex]
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have nodup := List.nodup_cons.mp unique
          have member := List.mem_of_getElem? found
          have different : sourceVar ≠ binder := by
            intro same
            exact nodup.1 (List.mem_map.mpr ⟨sourceVar, member,
              congrArg Var.name same⟩)
          simp only [boundIndex, sourceVarSame_eq_true_iff, different, ↓reduceIte]
          rw [ih nodup.2 index found]
          rfl

/-- Construct named syntax by selecting fresh binder names and resolving each
bound index against the current binder vector. Escaping indices are refused. -/
def named? : DBTerm → List SourceVar → Option SourceTerm
  | .const constant type, _ => some (.const constant type)
  | .free sourceVar, _ => some (.var sourceVar.name sourceVar.ty)
  | .bound index, binders => do
      let sourceVar ← binders[index]?
      pure (.var sourceVar.name sourceVar.ty)
  | .app function argument, binders => do
      let functionSource ← named? function binders
      let argumentSource ← named? argument binders
      pure (.app functionSource argumentSource)
  | .abs domain body, binders => do
      let name := ReverseTranslation.freshName (binders.map Var.name ++ freeNames body)
      let bodySource ← named? body (⟨name, domain⟩ :: binders)
      pure (.abs name domain bodySource)

/-- The executable representative construction is complete and erases to the
original nameless term under the exact fresh, distinct binder context. -/
theorem named?_complete (term : DBTerm) (binders : List SourceVar)
    (scope : DBTerm.LooseBelow binders.length term)
    (unique : (binders.map Var.name).Nodup)
    (fresh : ∀ name ∈ freeNames term, name ∉ binders.map Var.name) :
    ∃ source : SourceTerm, named? term binders = some source ∧ source.toDB binders = term := by
  induction term generalizing binders with
  | const constant type => exact ⟨.const constant type, rfl, by simp⟩
  | free sourceVar =>
      refine ⟨.var sourceVar.name sourceVar.ty, rfl, ?_⟩
      have absent := fresh sourceVar.name (by simp [freeNames])
      simp only [SourceTerm.toDB, boundIndex_none_of_name_absent sourceVar binders absent]
  | bound index =>
      have inRange : index < binders.length := scope
      let sourceVar := binders[index]
      have found : binders[index]? = some sourceVar := List.getElem?_eq_getElem inRange
      refine ⟨.var sourceVar.name sourceVar.ty, by simp [named?, found], ?_⟩
      simp only [SourceTerm.toDB, boundIndex_of_getElem binders unique index found]
  | app function argument functionIH argumentIH =>
      obtain ⟨functionSource, functionNamed, functionEq⟩ := functionIH binders scope.1 unique
        (fun name member => fresh name (by simp [freeNames, member]))
      obtain ⟨argumentSource, argumentNamed, argumentEq⟩ := argumentIH binders scope.2 unique
        (fun name member => fresh name (by simp [freeNames, member]))
      exact ⟨.app functionSource argumentSource,
        by simp [named?, functionNamed, argumentNamed],
        by simp only [SourceTerm.toDB, functionEq, argumentEq]⟩
  | abs domain body ih =>
      let name := ReverseTranslation.freshName (binders.map Var.name ++ freeNames body)
      have absent := ReverseTranslation.freshName_not_mem (binders.map Var.name ++ freeNames body)
      have absentBinders : name ∉ binders.map Var.name := fun member =>
        absent (List.mem_append_left _ member)
      have absentBody : name ∉ freeNames body := fun member =>
        absent (List.mem_append_right _ member)
      have newUnique : (((⟨name, domain⟩ : SourceVar) :: binders).map Var.name).Nodup :=
        List.nodup_cons.mpr ⟨absentBinders, unique⟩
      obtain ⟨source, computed, equation⟩ := ih (⟨name, domain⟩ :: binders)
        (by simpa only [List.length_cons, DBTerm.LooseBelow] using scope) newUnique (by
          intro other member
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨fun same => absentBody (same ▸ member), fresh other member⟩)
      exact ⟨.abs name domain source, by
        simp only [named?]
        change (named? body (⟨name, domain⟩ :: binders)).bind _ = _
        rw [computed]
        rfl, by simp only [SourceTerm.toDB, equation]⟩

/-- Total executable representative construction for a scoped term. The
successful-result proof is erased; the computation is the preceding scanner. -/
def named (term : DBTerm) (binders : List SourceVar)
    (scope : DBTerm.LooseBelow binders.length term)
    (unique : (binders.map Var.name).Nodup)
    (fresh : ∀ name ∈ freeNames term, name ∉ binders.map Var.name) : SourceTerm :=
  (named? term binders).get (by
    obtain ⟨source, computed, _⟩ := named?_complete term binders scope unique fresh
    rw [computed]
    rfl)

theorem named_exact (term : DBTerm) (binders : List SourceVar)
    (scope : DBTerm.LooseBelow binders.length term)
    (unique : (binders.map Var.name).Nodup)
    (fresh : ∀ name ∈ freeNames term, name ∉ binders.map Var.name) :
    (named term binders scope unique fresh).toDB binders = term := by
  obtain ⟨source, computed, exactImage⟩ := named?_complete term binders scope unique fresh
  have same : named term binders scope unique fresh = source := by
    unfold named
    simp only [computed, Option.get_some]
  exact same ▸ exactImage

theorem exists_named (term : DBTerm) (binders : List SourceVar)
    (scope : DBTerm.LooseBelow binders.length term)
    (unique : (binders.map Var.name).Nodup)
    (fresh : ∀ name ∈ freeNames term, name ∉ binders.map Var.name) :
    ∃ source : SourceTerm, source.toDB binders = term := by
  obtain ⟨source, _, exactImage⟩ := named?_complete term binders scope unique fresh
  exact ⟨source, exactImage⟩

/-- Retain the source type check of the computed named representative. -/
def checkedSource? (term : CanonicalTerm) : Option CheckedSourceTerm := do
  let source ← named? term.term []
  match checked : source.inferType with
  | some type => pure ⟨source, type, checked⟩
  | none => none

/-- Every canonical term has the exact computed checked source representative. -/
theorem checkedSource?_complete (term : CanonicalTerm) :
    ∃ source : CheckedSourceTerm,
      checkedSource? term = some source ∧ source.canonical = term := by
  obtain ⟨source, computed, equation⟩ := named?_complete term.term []
    (DBTerm.looseBelow_of_inferType term.checked) (by simp) (by simp)
  have checked : source.inferType = some term.ty := by
    rw [← DBTerm.inferType_toDB [], equation]
    exact term.checked
  refine ⟨⟨source, term.ty, checked⟩, ?_, ?_⟩
  · unfold checkedSource?
    rw [computed]
    change (match checked : source.inferType with
      | some type => some (⟨source, type, checked⟩ : CheckedSourceTerm)
      | none => none) = _
    split
    · rename_i type actual
      have same := Option.some.inj (actual.symm.trans checked)
      subst type
      rfl
    · rename_i rejected
      rw [checked] at rejected
      contradiction
  · apply CanonicalTerm.ext_term
    exact equation

theorem checkedSource?_exact (term : CanonicalTerm) {source : CheckedSourceTerm}
    (computed : checkedSource? term = some source) : source.canonical = term := by
  obtain ⟨actual, same, exactImage⟩ := checkedSource?_complete term
  have equal := Option.some.inj (same.symm.trans computed)
  exact equal ▸ exactImage

/-- A canonical term's checked named representative, computed without proof
search or choice. -/
def checkedSource (term : CanonicalTerm) : CheckedSourceTerm :=
  (checkedSource? term).get (by
    obtain ⟨source, computed, _⟩ := checkedSource?_complete term
    rw [computed]
    rfl)

theorem checkedSource_exact (term : CanonicalTerm) :
    (checkedSource term).canonical = term := by
  obtain ⟨source, computed, exactImage⟩ := checkedSource?_complete term
  have same : checkedSource term = source := by
    unfold checkedSource
    simp only [computed, Option.get_some]
  exact same ▸ exactImage

theorem exists_checked_source (term : CanonicalTerm) :
    ∃ source : CheckedSourceTerm, source.canonical = term := by
  obtain ⟨source, _, exactImage⟩ := checkedSource?_complete term
  exact ⟨source, exactImage⟩

private theorem applyDB_fresh_singleton (needle : SourceVar)
    (replacement : CheckedSourceTerm) : ∀ term : DBTerm,
    needle.name ∉ freeNames term →
    (TermSubst.mk TypeSubst.empty [(needle, replacement)]).applyDB term = term
  | .const constant type, _ => by simp
  | .free sourceVar, absent => by
      have different : needle ≠ sourceVar := by
        intro same
        exact absent (by simp [freeNames, same])
      simp [TermSubst.applyDB, TypeSubst.applyVar, TermSubst.lookup,
        TermSubst.keySame, different]
  | .bound index, _ => by simp
  | .app function argument, absent => by
      simp only [freeNames, List.mem_append, not_or] at absent
      simp only [TermSubst.applyDB_app]
      rw [applyDB_fresh_singleton needle replacement function absent.1,
        applyDB_fresh_singleton needle replacement argument absent.2]
  | .abs domain body, absent => by
      simp only [TermSubst.applyDB_abs, TypeSubst.apply_empty]
      rw [applyDB_fresh_singleton needle replacement body absent]

private theorem applyDB_instantiate_singleton (needle : SourceVar)
    (replacement : CheckedSourceTerm) : ∀ term : DBTerm, ∀ depth : Nat,
    needle.name ∉ freeNames term →
    (TermSubst.mk TypeSubst.empty [(needle, replacement)]).applyDB
      (DBTerm.instantiateAt (.free needle) depth term) =
        DBTerm.instantiateAt replacement.canonical.term depth term
  | .const constant type, depth, _ => by simp [DBTerm.instantiateAt]
  | .free sourceVar, depth, absent => by
      simp only [DBTerm.instantiateAt]
      exact applyDB_fresh_singleton needle replacement (.free sourceVar) absent
  | .bound index, depth, _ => by
      by_cases same : index = depth
      · simp [same, TermSubst.applyDB, TypeSubst.applyVar,
          TermSubst.lookup, TermSubst.keySame]
      · simp [DBTerm.instantiateAt, same]
  | .app function argument, depth, absent => by
      simp only [freeNames, List.mem_append, not_or] at absent
      simp only [DBTerm.instantiateAt, TermSubst.applyDB_app]
      rw [applyDB_instantiate_singleton needle replacement function depth absent.1,
        applyDB_instantiate_singleton needle replacement argument depth absent.2]
  | .abs domain body, depth, absent => by
      simp only [DBTerm.instantiateAt, TermSubst.applyDB_abs, TypeSubst.apply_empty]
      rw [applyDB_instantiate_singleton needle replacement body (depth + 1) absent]

/-- The fresh variable used by a general beta expansion. -/
def betaNeedle (domain : Ty) (body : DBTerm) : SourceVar :=
  ⟨ReverseTranslation.freshName (freeNames body), domain⟩

theorem betaNeedle_fresh (domain : Ty) (body : DBTerm) :
    (betaNeedle domain body).name ∉ freeNames body :=
  ReverseTranslation.freshName_not_mem _

/-- Source HOL Light permits BETA at the named binder itself. The body is
computed under that exact binder, rather than selected from an existence proof. -/
def betaSource (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain) : CheckedSourceTerm :=
  let needle := betaNeedle domain body
  let bodySource := named body [needle]
    (by simpa only [List.length_singleton] using DBTerm.looseBelow_of_inferType checkedBody)
    (by simp) (by
      intro other member
      change other ∉ [needle.name]
      simp only [List.mem_singleton]
      exact fun same => betaNeedle_fresh domain body (same ▸ member))
  let source := SourceTerm.app (.abs needle.name domain bodySource) (.var needle.name domain)
  ⟨source, codomain, by
    rw [← DBTerm.inferType_toDB []]
    have image := named_exact body [needle]
      (by simpa only [List.length_singleton] using DBTerm.looseBelow_of_inferType checkedBody)
      (by simp) (by
        intro other member
        change other ∉ [needle.name]
        simp only [List.mem_singleton]
        exact fun same => betaNeedle_fresh domain body (same ▸ member))
    simp only [source, SourceTerm.toDB, boundIndex, List.map_nil]
    change (DBTerm.app (.abs domain (bodySource.toDB [needle])) (.free needle)).inferType [] = _
    rw [image]
    simp [DBTerm.inferType, checkedBody, needle, betaNeedle]⟩

theorem betaSource_term (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain) :
    (betaSource domain body codomain checkedBody).canonical.term =
      .app (.abs domain body) (.free (betaNeedle domain body)) := by
  unfold betaSource CheckedSourceTerm.canonical
  simp only [SourceTerm.toDB, boundIndex]
  change (DBTerm.app (.abs domain ((named body [betaNeedle domain body] _ _ _).toDB
    [betaNeedle domain body])) (.free (betaNeedle domain body))) = _
  rw [named_exact]

/-- A checked beta application, including the source argument type check. -/
def betaRedex (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) : CanonicalTerm :=
  ⟨.app (.abs domain body) argument.term, codomain, by
    simp [DBTerm.inferType, checkedBody, argument.checked, argumentType]⟩

def betaReduced (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) : CanonicalTerm :=
  ⟨DBTerm.instantiateAt argument.term 0 body, codomain,
    DBTerm.inferType_instantiateAt argument.term body domain
      (by simpa [argumentType] using argument.checked) [] checkedBody⟩

/-- A general beta conversion expands to two chronological primitive requests.
The stored outputs are computed theorem objects, and the fields retain their
successful checks against the actual source operations. -/
structure BetaExpansion where
  source : CheckedSourceTerm
  entries : List TermMaplet
  intermediate : Theorem
  conclusion : Theorem
  betaChecked : (InferenceRequest.beta source).check = some intermediate
  instChecked : (InferenceRequest.inst entries intermediate).check = some conclusion

/-- Compute a BETA/INST expansion using fresh named syntax and a single
capture-avoiding maplet. Its computation does not inspect a derivation proof. -/
def betaExpansion (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) : BetaExpansion := by
  let needle := betaNeedle domain body
  let source := betaSource domain body codomain checkedBody
  let freeArgument := (CheckedSourceTerm.ofVariable needle).canonical
  let reduced := betaReduced domain body codomain checkedBody freeArgument rfl
  let equality := CanonicalTerm.equalityOfSameType source.canonical reduced rfl
  let intermediate := Theorem.emptyResult ∅ equality
  let argumentSource := checkedSource argument
  have argumentSourceType : argumentSource.ty = domain := by
    exact (congrArg CanonicalTerm.ty (checkedSource_exact argument)).trans argumentType
  let substitution : TypeCorrectTermSubstitution :=
    ⟨⟨TypeSubst.empty, [(needle, argumentSource)]⟩, by
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      exact argumentSourceType⟩
  refine ⟨source, termEntries substitution, intermediate,
    substituteTheorem substitution intermediate, ?_, ?_⟩
  · apply (InferenceRequest.check_eq_some_iff _ _).mpr
    refine ⟨⟨rfl, rfl⟩, reduced, equality, ?_,
      CanonicalTerm.equalityOfSameType_semantics source.canonical reduced rfl,
      rfl, rfl, rfl⟩
    refine ⟨domain, body, freeArgument, ?_, rfl⟩
    simpa only [freeArgument, CheckedSourceTerm.canonical, CheckedSourceTerm.ofVariable,
      SourceTerm.toDB, boundIndex] using betaSource_term domain body codomain checkedBody
  · apply (InferenceRequest.check_eq_some_iff _ _).mpr
    refine ⟨termOnly substitution, termEntries_admitted substitution, ?_⟩
    change TheoremSubstitutionSemantics substitution intermediate _
    exact substituteTheorem_semantics substitution intermediate

/-- The algorithmic expansion returns the exact ordinary beta equation, with
no hypotheses or axiom dependencies introduced. -/
theorem betaExpansion_conclusion (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    (betaExpansion domain body codomain checkedBody argument argumentType).conclusion =
      Theorem.emptyResult ∅ (CanonicalTerm.equalityOfSameType
        (betaRedex domain body codomain checkedBody argument argumentType)
        (betaReduced domain body codomain checkedBody argument argumentType) rfl) := by
  apply Theorem.ext
  · rfl
  · apply Sequent.ext
    · simp [betaExpansion, substituteTheorem, TypeCorrectTermSubstitution.applyHypotheses,
        Theorem.preserveAxiomsResult, Theorem.emptyResult]
    · apply CanonicalTerm.ext_term
      dsimp only [betaExpansion, betaReduced, substituteTheorem, Theorem.preserveAxiomsResult,
        Theorem.emptyResult, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked,
        CanonicalTerm.equalityOfSameType]
      have sourceType : (betaSource domain body codomain checkedBody).canonical.ty = codomain := rfl
      rw [sourceType]
      have freeImage : (CheckedSourceTerm.ofVariable (betaNeedle domain body)).canonical.term =
          .free (betaNeedle domain body) := by
        simp [CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex]
      rw [freeImage]
      change (TermSubst.mk TypeSubst.empty
        [(betaNeedle domain body, checkedSource argument)]).applyDB
        (CanonicalTerm.equalityDB codomain
          (betaSource domain body codomain checkedBody).canonical.term
          (DBTerm.instantiateAt (.free (betaNeedle domain body)) 0 body)) = _
      rw [betaSource_term]
      simp only [CanonicalTerm.equalityDB, TermSubst.applyDB_app, TermSubst.applyDB_const,
        TermSubst.applyDB_abs, TypeSubst.apply_empty]
      rw [applyDB_fresh_singleton _ _ body (betaNeedle_fresh domain body)]
      have needleLookup :
          (TermSubst.mk TypeSubst.empty
            [(betaNeedle domain body, checkedSource argument)]).applyDB
            (.free (betaNeedle domain body)) = (checkedSource argument).canonical.term := by
        simp [TermSubst.applyDB, TypeSubst.applyVar, TermSubst.lookup, TermSubst.keySame]
      rw [needleLookup]
      rw [applyDB_instantiate_singleton _ _ body 0 (betaNeedle_fresh domain body),
        checkedSource_exact]
      rfl

/-- The computed two-request plan has the independent shared beta semantics. -/
theorem betaExpansion_semantics (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    BetaConvSemantics (betaRedex domain body codomain checkedBody argument argumentType)
      (betaExpansion domain body codomain checkedBody argument argumentType).conclusion := by
  rw [betaExpansion_conclusion]
  refine ⟨betaReduced domain body codomain checkedBody argument argumentType, _,
    ⟨domain, body, argument, rfl, rfl⟩,
    CanonicalTerm.equalityOfSameType_semantics
      (betaRedex domain body codomain checkedBody argument argumentType)
      (betaReduced domain body codomain checkedBody argument argumentType) rfl, rfl, rfl, rfl⟩

/-- Recognize a checked beta redex and compute its two actual source requests.
Non-redexes and malformed source typing data are refused. -/
def betaExpansion? (redex : CanonicalTerm) : Option BetaExpansion :=
  match redex.term with
  | .app (.abs domain body) rawArgument => do
      let argument ← CanonicalTerm.ofDB? rawArgument
      if sameType : Ty.same domain argument.ty = true then
        match bodyChecked : body.inferType [domain] with
        | some codomain => pure (betaExpansion domain body codomain bodyChecked argument
          ((Ty.same_eq_true_iff _ _).mp sameType).symm)
        | none => none
      else none
  | _ => none

/-- Any admitted shared beta conversion has a computed two-primitive expansion
with exactly the specified theorem. -/
theorem betaExpansion?_complete {redex : CanonicalTerm} {out : Theorem}
    (step : BetaConvSemantics redex out) :
    ∃ expansion, betaExpansion? redex = some expansion ∧ expansion.conclusion = out := by
  obtain ⟨reduced, equality, reduction, construction, parts⟩ := step
  obtain ⟨domain, body, argument, redexShape, reducedShape⟩ := reduction
  have wholeChecked := redex.checked
  rw [redexShape] at wholeChecked
  simp only [DBTerm.inferType, argument.checked] at wholeChecked
  cases bodyResult : body.inferType [domain] with
  | none => simp [bodyResult] at wholeChecked
  | some codomain =>
      have matchDomain : argument.ty = domain := by
        by_cases same : Ty.same domain argument.ty = true
        · exact ((Ty.same_eq_true_iff _ _).mp same).symm
        · simp [bodyResult, Ty.destFunction?_function, same] at wholeChecked
      let expansion := betaExpansion domain body codomain bodyResult argument matchDomain
      have computed : betaExpansion? redex = some expansion := by
        unfold betaExpansion?
        rw [redexShape]
        simp only [CanonicalTerm.ofDB?_term]
        have matchB : Ty.same domain argument.ty = true :=
          (Ty.same_eq_true_iff _ _).mpr matchDomain.symm
        change (if sameType : Ty.same domain argument.ty = true then
          (match bodyChecked : body.inferType [domain] with
          | some type => some (betaExpansion domain body type bodyChecked argument
              ((Ty.same_eq_true_iff _ _).mp sameType).symm)
          | none => none) else none) = _
        rw [dif_pos matchB]
        split
        · rename_i type actual
          have same := Option.some.inj (actual.symm.trans bodyResult)
          subst type
          rfl
        · rename_i rejected
          rw [bodyResult] at rejected
          contradiction
      have redexEq : betaRedex domain body codomain bodyResult argument matchDomain = redex := by
        apply CanonicalTerm.ext_term
        exact redexShape.symm
      have semantics := betaExpansion_semantics domain body codomain bodyResult argument matchDomain
      rw [redexEq] at semantics
      have original : BetaConvSemantics redex out :=
        ⟨reduced, equality, ⟨domain, body, argument, redexShape, reducedShape⟩, construction, parts⟩
      have exactOutput := Option.some.inj
        (((checkBetaConv_eq_some_iff _ _).mpr semantics).symm.trans
          ((checkBetaConv_eq_some_iff _ _).mpr original))
      exact ⟨expansion, computed, exactOutput⟩

/-- A general beta plan retains two source operation occurrences and no
external theorem premise. The INST node refers back to the single BETA node. -/
def betaBlock (expansion : BetaExpansion) (origin : ProofExecution.Origin) : ProofSystem.Certificate :=
  ([⟨expansion.intermediate, .inference (.beta expansion.source), [], origin⟩,
    ⟨expansion.conclusion, .inference (.inst expansion.entries expansion.intermediate), [0], origin⟩], 1)

theorem betaBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (expansion : BetaExpansion) (origin : ProofExecution.Origin) :
    GraphExpansion.BlockChecked policy [] expansion.conclusion (betaBlock expansion origin) := by
  let first : ProofExecution.Receipt :=
    ⟨expansion.intermediate, .inference (.beta expansion.source), [], origin⟩
  let second : ProofExecution.Receipt :=
    ⟨expansion.conclusion, .inference (.inst expansion.entries expansion.intermediate), [0], origin⟩
  have firstReplay : first.replay (ruleWitness policy) #[] = some (#[expansion.intermediate]) := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, expansion.betaChecked, rfl⟩
  have secondReplay : second.replay (ruleWitness policy) #[expansion.intermediate] =
      some (#[expansion.intermediate, expansion.conclusion]) := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, expansion.instChecked, rfl⟩
  refine ⟨#[expansion.intermediate, expansion.conclusion], ?_, rfl⟩
  change DerivationGraph.replayFrom (ruleWitness policy) #[] [first, second] = _
  simp only [DerivationGraph.replayFrom, firstReplay]
  change DerivationGraph.replayFrom (ruleWitness policy) #[expansion.intermediate] [second] = _
  simp only [DerivationGraph.replayFrom, secondReplay]
  rfl

theorem beta_derives (policy : AxiomPolicy) {redex : CanonicalTerm} {out : Theorem}
    (step : BetaConvSemantics redex out) : Derives (Rule policy) out := by
  obtain ⟨expansion, _, exactOutput⟩ := betaExpansion?_complete step
  rw [← exactOutput]
  apply infer policy (.inst expansion.entries expansion.intermediate)
  · exact (InferenceRequest.check_eq_some_iff _ _).mp expansion.instChecked
  · intro premise member
    simp only [InferenceRequest.premises, List.mem_singleton] at member
    subst premise
    apply infer policy (.beta expansion.source)
    · exact (InferenceRequest.check_eq_some_iff _ _).mp expansion.betaChecked
    · simp [InferenceRequest.premises]

/-- Every shared primitive step expands to the actual source operations.
The restriction is the source axiom admission rule, not a new proof premise
for substitution, beta conversion, or any inference operation. -/
theorem primitive_derives (policy : AxiomPolicy)
    (hypothesisFree : ∀ sequent, policy sequent → sequent.hyp = ∅)
    (request : PrimitiveRequest) {out : Theorem}
    (allowed : request.InputAxiomsAllowed policy) (step : PrimitiveStep request out)
    (children : ∀ premise ∈ request.premises, Derives (Rule policy) premise) :
    Derives (Rule policy) out := by
  cases request with
  | core request =>
      have coreStep : CoreStep request out := by
        obtain ⟨evidence⟩ := step
        cases evidence with
        | core evidence => exact ⟨evidence⟩
      cases request with
      | «axiom» sequent =>
          exact .node [] out
            (.inr ⟨sequent, rfl, hypothesisFree sequent allowed, allowed,
              (axiomSemantics_iff_coreStep _ _).mpr coreStep⟩)
            (by simp)
      | assume term =>
          exact infer policy (.assume term) ((assumeSemantics_iff_coreStep _ _).mpr coreStep)
            children
      | refl term =>
          exact infer policy (.refl term) ((reflSemantics_iff_coreStep _ _).mpr coreStep)
            children
      | app left right =>
          exact infer policy (.mkComb left right) ((appSemantics_iff_coreStep _ _ _).mpr coreStep)
            children
      | deductAntisym left right =>
          exact infer policy (.deductAntisym left right)
            ((deductAntisymSemantics_iff_coreStep _ _ _).mpr coreStep) children
      | eqMp equality premise =>
          exact infer policy (.eqMp equality premise) ((eqMpSemantics_iff_coreStep _ _ _).mpr coreStep)
            children
  | binding request =>
      have bindingStep : BindingStep request out := by
        obtain ⟨evidence⟩ := step
        cases evidence with
        | binding evidence => exact ⟨evidence⟩
      cases request with
      | abs binder input =>
          exact infer policy (.abs binder input) ((absSemantics_iff_bindingStep _ _ _).mpr bindingStep)
            children
      | betaConv term =>
          exact beta_derives policy ((betaConvSemantics_iff_bindingStep _ _).mpr bindingStep)
  | subst substitution input =>
      obtain ⟨evidence⟩ := step
      cases evidence with
      | subst semantics =>
          exact substitution_derives policy substitution semantics
            (children input (by simp [PrimitiveRequest.premises]))

theorem derives_source (policy : AxiomPolicy)
    (hypothesisFree : ∀ sequent, policy sequent → sequent.hyp = ∅) {out : Theorem}
    (derivation : Derives (PolicyPrimitiveRule policy) out) : Derives (Rule policy) out := by
  apply Derives.least (Derives (Rule policy)) _ derivation
  intro premises out step children
  obtain ⟨request, rfl, allowed, semantics⟩ := step
  exact primitive_derives policy hypothesisFree request allowed semantics children

/-- Agreement is on the complete theorem object: hypotheses, conclusion and
the unchanged axiom-provenance set. -/
theorem derives_iff_shared (policy : AxiomPolicy)
    (hypothesisFree : ∀ sequent, policy sequent → sequent.hyp = ∅) (out : Theorem) :
    Derives (Rule policy) out ↔ Derives (PolicyPrimitiveRule policy) out :=
  ⟨derives_shared policy, derives_source policy hypothesisFree⟩

/-- The source's existing certificate checker accepts exactly the shared
primitive closure, at the same complete theorem observation. -/
theorem checked_iff_shared (policy : AxiomPolicy) [DecidablePred policy]
    (hypothesisFree : ∀ sequent, policy sequent → sequent.hyp = ∅) (out : Theorem) :
    (∃ certificate : Derivation Theorem RuleRequest,
      certificate.valid (ruleWitness policy) = true ∧ certificate.concl = out) ↔
        Derives (PolicyPrimitiveRule policy) out := by
  constructor
  · rintro ⟨certificate, valid, rfl⟩
    exact derives_shared policy (certificate.valid_sound (ruleWitness policy) valid)
  · intro proof
    exact (derives_source policy hypothesisFree proof).exists_derivation (ruleWitness policy)

namespace Controls

open BindingExamples BindingRuleExamples

/-- The broader beta rule is replayed even when source `BETA` alone refuses
the differently named argument. -/
theorem general_beta_replayed (policy : AxiomPolicy) :
    Derives (Rule policy) betaTheorem := by
  apply beta_derives policy
  exact ⟨freeY, betaEquality,
    ⟨Examples.individual, .bound 0, freeY,
      by simp [identityAppliedToY, freeY], by simp [freeY]⟩,
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp betaEqualityResult,
    rfl, rfl, rfl⟩

theorem different_beta_argument_still_not_primitive :
    ¬ TrivialBetaRedex HOLLight.Controls.differentArgument :=
  HOLLight.Controls.different_argument_refused

theorem malformed_beta_still_refused : checkBetaConv freeY = none := by
  simp [checkBetaConv, CanonicalTerm.betaReduce?, freeY]

theorem nontrivial_term_substitution_replayed (policy : AxiomPolicy)
    {input : Theorem} (proof : Derives (Rule policy) input) :
    Derives (Rule policy)
      (substituteTheorem TheoremSubstitutionExamples.renameXToY input) :=
  substitution_derives policy _ (substituteTheorem_semantics _ _) proof

end Controls

end PrimitiveTransport
end Mettapedia.Languages.HOLLight
