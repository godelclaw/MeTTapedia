import Mettapedia.Languages.HOLLight.MeTTa.ProofEvents

/-!
# Derivation evidence for the actual authored proof cache

Ordered theorem metadata is interpreted in the existing registered HOL
calculus. Cache retrieval earns a premise derivation through the actual
encoded lookup and the registered declaration identities. The metadata is
retained; logical support does not reconstruct origins or occurrence lists.
This module does not authorize an arbitrary supplied initial cache.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Eval
open Effects (State)

/-- A retained dependency names a hypothesis-free Boolean commitment. -/
structure Dependency where
  label : Atom
  statement : CanonicalTerm
  boolean : statement.IsBool

def Dependency.sequent (dependency : Dependency) : Sequent :=
  ⟨∅, dependency.statement⟩

def Dependency.atom (constants : Const → Atom) (dependency : Dependency) : Atom :=
  .expression [.symbol "HOL:AxiomDependency", dependency.label,
    TheoremMetadata.hypothesisAtom constants dependency.statement]

/-- The source keeps these lists and origin, independently of their support. -/
structure Record where
  hypotheses : List CanonicalTerm
  conclusion : CanonicalTerm
  dependencies : List Dependency
  origin : Atom

def Record.fact (record : Record) : Theorem :=
  { axioms := (record.dependencies.map Dependency.sequent).toFinset
    axiomsBoolean := by
      intro sequent member
      obtain ⟨dependency, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      exact ⟨dependency.boolean, by simp [Dependency.sequent]⟩
    sequent := ⟨record.hypotheses.toFinset, record.conclusion⟩ }

def Record.atom (constants : Const → Atom) (record : Record) : Atom :=
  Representation.theoremAtom constants [] record.conclusion.term
    (record.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
    (record.dependencies.map (Dependency.atom constants)) record.origin

abbrev Cache := List (Atom × Record)

def entries (constants : Const → Atom) (cache : Cache) : List (Atom × Atom) :=
  cache.map (fun entry => (entry.1, entry.2.atom constants))

/-- This is the registered calculus's derivation invariant over the actual
source cache representation, not a new proof-checking calculus. -/
def Valid (policy : AxiomPolicy) (world : TheoryContext) (cache : Cache) : Prop :=
  ∀ entry ∈ cache, TheoryDerives policy world entry.2.fact

theorem empty_valid (policy : AxiomPolicy) (world : TheoryContext) :
    Valid policy world [] := by simp [Valid]

theorem insert_valid {policy : AxiomPolicy} {world : TheoryContext} {cache : Cache}
    (before : Valid policy world cache) (key : Atom) (record : Record)
    (derived : TheoryDerives policy world record.fact) :
    Valid policy world ((key, record) :: cache) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · exact derived
  · exact before entry member

/-- Context extension transports derivations by the existing registered
weakening rule. It grants no additional axiom commitment. -/
theorem weaken_valid {policy : AxiomPolicy} {before after : TheoryContext}
    (included : before.signature.Includes after.signature) {cache : Cache}
    (valid : Valid policy before cache) : Valid policy after cache :=
  fun entry member => .weaken included (valid entry member)

private theorem keys_injective (left right : List Atom)
    (same : Premises.keys left = Premises.keys right) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [Premises.keys] at same ⊢
  | cons first rest ih =>
      cases right with
      | nil => simp [Premises.keys] at same
      | cons value values =>
          simp only [Premises.keys, Atom.expression.injEq, List.cons.injEq, true_and] at same
          exact congrArg₂ List.cons same.1 (ih values same.2.1)

private theorem dependency_formed (world : TheoryContext) (record : Record)
    (formed : TheoremFormed world.signature record.fact) (dependency : Dependency)
    (member : dependency ∈ record.dependencies) :
    AnnotationsFormed world.signature dependency.statement.term := by
  apply (formed.2 dependency.sequent ?_).1
  simp only [Record.fact, List.mem_toFinset, List.mem_map]
  exact ⟨dependency, member, rfl⟩

private theorem dependencies_support (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact)
    (same : left.dependencies.map (Dependency.atom constants) =
      right.dependencies.map (Dependency.atom constants)) : left.fact.axioms = right.fact.axioms := by
  have inclusion (first second : Record)
      (firstFormed : TheoremFormed world.signature first.fact)
      (secondFormed : TheoremFormed world.signature second.fact)
      (sameAtoms : first.dependencies.map (Dependency.atom constants) =
        second.dependencies.map (Dependency.atom constants)) :
      first.fact.axioms ⊆ second.fact.axioms := by
    intro sequent member
    obtain ⟨dependency, present, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have encoded : dependency.atom constants ∈ second.dependencies.map (Dependency.atom constants) := by
      rw [← sameAtoms]
      exact List.mem_map.mpr ⟨dependency, present, rfl⟩
    obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp encoded
    have parts : other.label = dependency.label ∧
        TheoremMetadata.hypothesisAtom constants other.statement =
          TheoremMetadata.hypothesisAtom constants dependency.statement := by
      simpa only [Dependency.atom, Atom.expression.injEq, List.cons.injEq, true_and, and_true] using equal
    have termsSame : TheoremMetadata.hypothesisAtom constants other.statement =
        TheoremMetadata.hypothesisAtom constants dependency.statement := by
      exact parts.2
    have statementsSame : other.statement = dependency.statement := CanonicalTerm.ext_term
      (TermReflection.registered_termAtom_injective world constants identified [] other.statement.term
        dependency.statement.term (dependency_formed world second secondFormed other otherMember)
        (dependency_formed world first firstFormed dependency present) termsSame)
    simp only [Record.fact, List.mem_toFinset, List.mem_map]
    exact ⟨other, otherMember, by simp [Dependency.sequent, statementsSame]⟩
  exact Finset.Subset.antisymm (inclusion left right leftFormed rightFormed same)
    (inclusion right left rightFormed leftFormed same.symm)

/-- Matching a retained record reflects its logical theorem only within the
registered declaration context. Origins and list representations stay intact. -/
theorem record_faithful (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact)
    (same : left.atom constants = right.atom constants) : left.fact = right.fact := by
  have fields : Premises.keys (left.hypotheses.map (TheoremMetadata.hypothesisAtom constants)) =
        Premises.keys (right.hypotheses.map (TheoremMetadata.hypothesisAtom constants)) ∧
      Representation.termAtom Representation.registeredOperatorAtom constants [] left.conclusion.term =
        Representation.termAtom Representation.registeredOperatorAtom constants [] right.conclusion.term ∧
      Premises.keys (left.dependencies.map (Dependency.atom constants)) =
        Premises.keys (right.dependencies.map (Dependency.atom constants)) ∧ left.origin = right.origin := by
    simpa only [Record.atom, Representation.theoremAtom, Atom.expression.injEq, List.cons.injEq,
      true_and, and_true] using same
  apply Theorem.ext
  · exact dependencies_support world constants identified left right leftFormed rightFormed
      (keys_injective _ _ fields.2.2.1)
  · apply Sequent.ext
    · apply (TheoremMetadata.hypothesis_support_faithful world constants identified left.hypotheses right.hypotheses
        (fun term member => leftFormed.1.2 term (List.mem_toFinset.mpr member))
        (fun term member => rightFormed.1.2 term (List.mem_toFinset.mpr member))).mp
      exact congrArg List.toFinset (keys_injective _ _ fields.1)
    · exact CanonicalTerm.ext_term (TermReflection.registered_termAtom_injective world constants identified []
        left.conclusion.term right.conclusion.term leftFormed.1.1 rightFormed.1.1 fields.2.1)

theorem lookup_entries (constants : Const → Atom) (cache : Cache) (key : Atom) :
    (entries constants cache).lookup key = (cache.lookup key).map (Record.atom constants) := by
  induction cache with
  | nil => rfl
  | cons first rest ih =>
      simp only [entries, List.map_cons, List.lookup]
      split
      · rfl
      · exact ih

private theorem lookup_member (cache : Cache) (key : Atom) (record : Record)
    (found : cache.lookup key = some record) : (key, record) ∈ cache := by
  induction cache with
  | nil => simp [List.lookup] at found
  | cons first rest ih =>
      simp only [List.lookup] at found
      split at found
      · rename_i equal
        have keySame : key = first.1 := by simpa using equal
        have valueSame : first.2 = record := Option.some.inj found
        have entrySame : first = (key, record) := Prod.ext keySame.symm valueSame
        exact List.mem_cons.mpr (Or.inl entrySame.symm)
      · exact List.mem_cons_of_mem first (ih found)

/-- A retrieved logical record inherits its derivation from the actual
insertion history; no separately assumed formation of the record is needed. -/
theorem stored_lookup_derived (policy : AxiomPolicy) (world : TheoryContext)
    (cache : Cache) (valid : Valid policy world cache) (key : Atom) (record : Record)
    (found : cache.lookup key = some record) : TheoryDerives policy world record.fact :=
  valid (key, record) (lookup_member cache key record found)

/-- An actual encoded cache lookup discharges the rule's premise derivation
obligation. Matching theorem names or raw payloads is not used as authority. -/
theorem lookup_derived (policy : AxiomPolicy) (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (cache : Cache)
    (valid : Valid policy world cache) (key : Atom) (expected : Record)
    (expectedFormed : TheoremFormed world.signature expected.fact)
    (found : (entries constants cache).lookup key = some (expected.atom constants)) :
    TheoryDerives policy world expected.fact := by
  rw [lookup_entries] at found
  cases selected : cache.lookup key with
  | none => simp [selected] at found
  | some retrieved =>
      have equal : retrieved.atom constants = expected.atom constants := by simpa [selected] using found
      have derived := valid (key, retrieved) (lookup_member cache key retrieved selected)
      have same := record_faithful world constants identified retrieved expected derived.wellFormed expectedFormed equal
      exact same ▸ derived

/-- Within a registered context, an occupied slot cannot be read as a
different logical theorem, even when the requested key and origin agree. -/
theorem mismatched_fact_not_found (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (key : Atom) (stored expected : Record)
    (storedFormed : TheoremFormed world.signature stored.fact)
    (expectedFormed : TheoremFormed world.signature expected.fact)
    (different : stored.fact ≠ expected.fact) :
    (entries constants [(key, stored)]).lookup key ≠ some (expected.atom constants) := by
  intro found
  have same : stored.atom constants = expected.atom constants := by simpa [entries] using found
  exact different (record_faithful world constants identified stored expected storedFormed expectedFormed same)

/-- The authored known operation returns a record together with its earned
registered derivation; it does not require a separate assumed premise proof. -/
theorem authored_known_derivation (policy : AxiomPolicy) (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (cache : Cache)
    (valid : Valid policy world cache) (key : Atom) (expected : Record)
    (expectedFormed : TheoremFormed world.signature expected.fact)
    (found : (entries constants cache).lookup key = some (expected.atom constants))
    (operators declarations axioms receipts : Atom) (bindings : Subst) (state : State)
    (stateKey proofKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) =
      ProofLookup.sourceState operators declarations axioms receipts (entries constants cache))
    (keyCaptured : applySubst bindings (.var proofKey) = key) :
    TheoryDerives policy world expected.fact ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:known", .var stateKey, .var proofKey])
        state (.expression [.symbol "Some", expected.atom constants]) := by
  refine ⟨lookup_derived policy world constants identified cache valid key expected expectedFormed found, ?_⟩
  simpa only [found, Lookup.answer] using ProofLookup.authored_known_return bindings state
    operators declarations axioms receipts key (entries constants cache) stateKey proofKey stateCaptured keyCaptured

/-- A successful actual REFL event extends an authorized cache in the same
registered context. Both the derivation and exact new source state are built. -/
theorem authored_refl_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : AnnotationsFormed world.signature source.canonical.term)
    (equalityType : TypeFormed world.signature (Ty.equality source.ty))
    (equalityInstance : ConstantInstance world.signature Const.equality (Ty.equality source.ty))
    (cache : Cache) (valid : Valid policy world cache) (receipts : List ReceiptKeys.Entry)
    (key axioms : Atom) (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "REFL", TermReading.sourceAtom source.source]) :
    ∃ record : Record, TheoryDerives policy world record.fact ∧
      Valid policy world ((key, record) :: cache) ∧ record.hypotheses = [] ∧ record.dependencies = [] ∧
      record.origin = .expression [.symbol "HOL:Origin", key,
        .expression [.symbol "REFL", TermReading.sourceAtom source.source]] ∧
      InferenceRequest.Semantics (.refl source.canonical) record.fact ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName])
        state (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "REFL", TermReading.sourceAtom source.source], []⟩ :: receipts))
          (entries constants ((key, record) :: cache))]) := by
  obtain ⟨out, semantics, _, dependencies, hypotheses, returned⟩ :=
    ProofEvents.authored_refl_step_derivation world table origins constants equalityIdentity source resolved annotations
      key axioms (entries constants cache) receipts bindings state stateKey keyName requestName
      stateCaptured keyCaptured requestCaptured policy
  have formed : TheoremFormed world.signature out := by
    obtain ⟨equality, construction, parts⟩ := semantics
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have termSame : out.sequent.concl.term =
          CanonicalTerm.equalityDB source.ty source.canonical.term source.canonical.term :=
        (congrArg CanonicalTerm.term parts.2.2).trans construction.2
      rw [termSame]
      exact .app (.app (.constant equalityType equalityInstance) annotations) annotations
    · intro term member
      rw [hypotheses] at member
      simp at member
    · intro commitment member
      rw [dependencies] at member
      simp at member
  have derived : TheoryDerives policy world out := .inference semantics
    (by simp [InferenceFormation.Formed, InferenceFormation.types, InferenceFormation.terms, annotations])
    (by simp [InferenceRequest.premises]) formed
  let record : Record := ⟨[], out.sequent.concl, [], .expression [.symbol "HOL:Origin", key,
    .expression [.symbol "REFL", TermReading.sourceAtom source.source]]⟩
  have factSame : record.fact = out := by
    apply Theorem.ext
    · simpa [record, Record.fact] using dependencies.symm
    · exact Sequent.ext (by simpa [record, Record.fact] using hypotheses.symm) rfl
  have recordDerived : TheoryDerives policy world record.fact := factSame ▸ derived
  refine ⟨record, recordDerived, insert_valid valid key record recordDerived, rfl, rfl, rfl,
    factSame ▸ semantics, ?_⟩
  simp only [Publication.result, receiptFresh, Bool.false_eq_true, ↓reduceIte, cacheFresh] at returned
  simpa [Publication.afterState, ProofLookup.sourceState,
    entries, record, Record.atom, Publication.publishedValue, Publication.value, Representation.theoremAtom,
    Premises.keys] using returned

/-- A successful actual ASSUME event constructs its registered derivation,
retains the one hypothesis and preserves authorization of the old cache. -/
theorem authored_assume_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : AnnotationsFormed world.signature source.canonical.term)
    (formed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (isBool : source.canonical.IsBool)
    (cache : Cache) (valid : Valid policy world cache) (receipts : List ReceiptKeys.Entry)
    (key axioms : Atom) (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "ASSUME", TermReading.sourceAtom source.source]) :
    ∃ record : Record, TheoryDerives policy world record.fact ∧
      Valid policy world ((key, record) :: cache) ∧ record.hypotheses = [source.canonical] ∧ record.dependencies = [] ∧
      record.origin = .expression [.symbol "HOL:Origin", key,
        .expression [.symbol "ASSUME", TermReading.sourceAtom source.source]] ∧
      InferenceRequest.Semantics (.assume source.canonical) record.fact ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName])
        state (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "ASSUME", TermReading.sourceAtom source.source], []⟩ :: receipts))
          (entries constants ((key, record) :: cache))]) := by
  let operators := OperatorTable.tableAtom table.operators origins
  let declarations := DeclarationTable.tableAtom table constants
  let bound := ProofEvents.inferenceEnvironment operators declarations axioms key .assume
    (TermReading.sourceAtom source.source) (.symbol "None") (.symbol "None") (entries constants cache) receipts
  obtain ⟨out, semantics, _, dependencies, hypotheses, inferred⟩ :=
    InferenceExecution.authored_assume_derivation world table origins constants source resolved annotations formed booleanFormed isBool
      bound state axioms (ReceiptKeys.table receipts) (entries constants cache) "state" "request"
      (by rfl) (by rfl) policy
  have outFormed : TheoremFormed world.signature out := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [semantics.2.2.2] using annotations
    · intro term member
      rw [hypotheses, Finset.mem_singleton] at member
      exact member ▸ annotations
    · intro commitment member
      rw [dependencies] at member
      simp at member
  have derived : TheoryDerives policy world out := .inference semantics
    (by simp [InferenceFormation.Formed, InferenceFormation.types, InferenceFormation.terms, annotations])
    (by simp [InferenceRequest.premises]) outFormed
  let record : Record := ⟨[source.canonical], out.sequent.concl, [], .expression [.symbol "HOL:Origin", key,
    .expression [.symbol "ASSUME", TermReading.sourceAtom source.source]]⟩
  have factSame : record.fact = out := by
    apply Theorem.ext
    · simpa [record, Record.fact] using dependencies.symm
    · exact Sequent.ext (by simpa [record, Record.fact] using hypotheses.symm) rfl
  have recordDerived : TheoryDerives policy world record.fact := factSame ▸ derived
  have returned := ProofEvents.authored_step_inference_return operators declarations axioms key
    (Premises.keys [TheoremMetadata.hypothesisAtom constants source.canonical])
    (Representation.termAtom Representation.registeredOperatorAtom constants [] out.sequent.concl.term)
    (.symbol "HOL:Nil") (.symbol "ASSUME") .assume (TermReading.sourceAtom source.source)
    (.symbol "None") (.symbol "None") (entries constants cache) receipts bindings state stateKey keyName requestName
    stateCaptured keyCaptured requestCaptured inferred
  refine ⟨record, recordDerived, insert_valid valid key record recordDerived, rfl, rfl, rfl,
    factSame ▸ semantics, ?_⟩
  simp only [Publication.result, receiptFresh, Bool.false_eq_true, ↓reduceIte, cacheFresh] at returned
  simpa [Publication.afterState, ProofLookup.sourceState, operators, declarations, Premises.request, Premises.occurrences,
    entries, record, Record.atom, Publication.publishedValue, Publication.value, Representation.theoremAtom,
    Premises.keys, TheoremMetadata.hypothesisAtom] using returned

/-- A complete actual TRANS event reuses an authorized reflexivity premise
twice. Both lookups are executed, the derivation is constructed from the
stored premise, and its receipt retains the two address occurrences. -/
theorem authored_trans_reflexivity_preserves_valid (policy : AxiomPolicy) (world : TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (term : CanonicalTerm) (annotations : AnnotationsFormed world.signature term.term)
    (cache : Cache) (valid : Valid policy world cache) (record : Record) (premise : Atom)
    (selected : cache.lookup premise = some record)
    (reflexivity : InferenceRequest.Semantics (.refl term) record.fact)
    (hypothesesEmpty : record.hypotheses = []) (dependenciesEmpty : record.dependencies = [])
    (receipts : List ReceiptKeys.Entry) (operators declarations axioms key : Atom)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries constants cache).lookup key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators declarations axioms (ReceiptKeys.table receipts) (entries constants cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = .expression [.symbol "TRANS", premise, premise]) :
    ∃ next : Record, next.fact = record.fact ∧ TheoryDerives policy world next.fact ∧
      Valid policy world ((key, next) :: cache) ∧
      InferenceRequest.Semantics (.trans record.fact record.fact) next.fact ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName])
        state (.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table (⟨key, .expression [.symbol "TRANS", premise, premise], [premise, premise]⟩ :: receipts))
          (entries constants ((key, next) :: cache))]) := by
  have prior := valid (premise, record) (lookup_member cache premise record selected)
  have found : (entries constants cache).lookup premise = some (record.atom constants) := by
    rw [lookup_entries, selected]
    rfl
  have earned := lookup_derived policy world constants identified cache valid premise record prior.wellFormed found
  have termSame : record.conclusion.term = CanonicalTerm.equalityDB term.ty term.term term.term := by
    obtain ⟨equality, construction, parts⟩ := reflexivity
    exact (congrArg CanonicalTerm.term parts.2.2).trans construction.2
  have sourceFound : (entries constants cache).lookup premise = some
      (Transitivity.theoremValue constants [] term.ty term.term term.term [] [] record.origin) := by
    simpa only [Record.atom, hypothesesEmpty, dependenciesEmpty, List.map_nil, Transitivity.theoremValue, termSame] using found
  let bound := ProofEvents.inferenceEnvironment operators declarations axioms key .trans (.symbol "None")
    premise premise (entries constants cache) receipts
  have inferred := InferenceExecution.authored_infer_trans_return world constants identified equalityIdentity
    bound state [] term.ty term.term term.term term.term term.term term.checked term.checked annotations annotations
    [] [] [] [] record.origin record.origin operators declarations axioms (ReceiptKeys.table receipts)
    (entries constants cache) premise premise sourceFound sourceFound "state" "request" rfl rfl
  have inferredResult : PureReturns program bound state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value (.symbol "HOL:Nil")
        (Representation.termAtom Representation.registeredOperatorAtom constants [] record.conclusion.term)
        (.symbol "HOL:Nil") (.symbol "TRANS")]) := by
    simpa [DBTerm.same_eq_true_iff, Transitivity.union, Transitivity.theoremValue, Representation.theoremAtom,
      Premises.keys, Publication.value, termSame] using inferred
  let next : Record := { record with origin := .expression [.symbol "HOL:Origin", key,
    .expression [.symbol "TRANS", premise, premise]] }
  have factSame : next.fact = record.fact := rfl
  have semantics : InferenceRequest.Semantics (.trans record.fact record.fact) record.fact := by
    refine ⟨term, term, term, term, record.conclusion, ⟨rfl, termSame⟩, ⟨rfl, termSame⟩, rfl,
      ⟨rfl, termSame⟩, ?_⟩
    exact ⟨by simp, by simp, rfl⟩
  have derived : TheoryDerives policy world next.fact := .inference semantics
    (by simp [InferenceFormation.Formed, InferenceFormation.types, InferenceFormation.terms])
    (by
      intro parent member
      have same : parent = record.fact := by simpa [InferenceRequest.premises] using member
      exact same ▸ earned) prior.wellFormed
  have returned := ProofEvents.authored_step_inference_return operators declarations axioms key
    (.symbol "HOL:Nil") (Representation.termAtom Representation.registeredOperatorAtom constants [] record.conclusion.term)
    (.symbol "HOL:Nil") (.symbol "TRANS") .trans (.symbol "None") premise premise (entries constants cache) receipts
    bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured inferredResult
  refine ⟨next, factSame, derived, insert_valid valid key next derived, semantics, ?_⟩
  simp only [Publication.result, receiptFresh, Bool.false_eq_true, ↓reduceIte, cacheFresh] at returned
  simpa [Publication.afterState, ProofLookup.sourceState, entries, next, Record.atom, hypothesesEmpty, dependenciesEmpty,
    Publication.publishedValue, Publication.value, Representation.theoremAtom, Premises.keys, Premises.request,
    Premises.occurrences] using returned

/-- A fresh declaration's identity cannot alter the encoding of an admitted
old term. The argument retains positional annotations in any bound context. -/
theorem term_atom_fresh_identity (world : TheoryContext) (constant : Const)
    (fresh : world.signature.constants constant = none) (before : Const → Atom) (identity : Atom)
    (term : DBTerm) (formed : AnnotationsFormed world.signature term) (positions : List Ty) :
    Representation.termAtom Representation.registeredOperatorAtom
        (DeclarationTable.extendIdentity before constant identity) positions term =
      Representation.termAtom Representation.registeredOperatorAtom before positions term := by
  induction formed generalizing positions with
  | @constant old annotation _ instanceProof =>
      obtain ⟨schema, _, registered, _⟩ := instanceProof
      have different : old ≠ constant := by
        intro same
        rw [same, fresh] at registered
        cases registered
      simp [Representation.termAtom, DeclarationTable.extendIdentity, Const.same_eq_true_iff, different]
  | free _ => simp only [Representation.termAtom]
  | bound _ => simp only [Representation.termAtom]
  | app _ _ functionIH argumentIH => simp only [Representation.termAtom, functionIH, argumentIH]
  | abs _ _ bodyIH => simp only [Representation.termAtom, bodyIH]

/-- Ordered dependency payloads survive a fresh identity extension. Their
formation is obtained from the retained record's actual theorem judgment. -/
theorem dependencies_fresh_identity (world : TheoryContext) (constant : Const)
    (fresh : world.signature.constants constant = none) (before : Const → Atom) (identity : Atom)
    (record : Record) (formed : TheoremFormed world.signature record.fact) :
    record.dependencies.map (Dependency.atom (DeclarationTable.extendIdentity before constant identity)) =
      record.dependencies.map (Dependency.atom before) := by
  apply List.map_congr_left
  intro dependency member
  unfold Dependency.atom TheoremMetadata.hypothesisAtom
  rw [term_atom_fresh_identity world constant fresh before identity dependency.statement.term
    (dependency_formed world record formed dependency member) []]

/-- Every retained logical field, dependency label and origin is unchanged
when the identity assignment is extended at an unregistered constant. -/
theorem record_atom_fresh_identity (world : TheoryContext) (constant : Const)
    (fresh : world.signature.constants constant = none) (before : Const → Atom) (identity : Atom)
    (record : Record) (formed : TheoremFormed world.signature record.fact) :
    record.atom (DeclarationTable.extendIdentity before constant identity) = record.atom before := by
  have hypotheses : record.hypotheses.map
        (TheoremMetadata.hypothesisAtom (DeclarationTable.extendIdentity before constant identity)) =
      record.hypotheses.map (TheoremMetadata.hypothesisAtom before) := by
    apply List.map_congr_left
    intro hypothesis member
    exact term_atom_fresh_identity world constant fresh before identity hypothesis.term
      (formed.1.2 hypothesis (List.mem_toFinset.mpr member)) []
  have dependencies := dependencies_fresh_identity world constant fresh before identity record formed
  simp only [Record.atom, Representation.theoremAtom, hypotheses, dependencies,
    term_atom_fresh_identity world constant fresh before identity record.conclusion.term formed.1.1 []]

/-- Cache representation commutes with a real fresh identity extension.
Authorization provides the formation evidence needed for every old record. -/
theorem entries_fresh_identity (policy : AxiomPolicy) (world : TheoryContext) (constant : Const)
    (fresh : world.signature.constants constant = none) (before : Const → Atom) (identity : Atom)
    (cache : Cache) (valid : Valid policy world cache) :
    entries (DeclarationTable.extendIdentity before constant identity) cache = entries before cache := by
  apply List.map_congr_left
  intro entry member
  exact congrArg (fun value => (entry.1, value))
    (record_atom_fresh_identity world constant fresh before identity entry.2 (valid entry member).wellFormed)

/-- A registered fresh declaration transports the derivation invariant and
preserves the complete actual cache representation, including old origins.
This does not supply a model extension or a full context fibration. -/
theorem add_constant_transports_cache (policy : AxiomPolicy) (world : TheoryContext)
    (constant : Const) (schema : Ty) (formed : TypeFormed world.signature schema)
    (fresh : .constant (constantName constant) ∉ world.names)
    (before : Const → Atom) (identity : Atom) (cache : Cache) (valid : Valid policy world cache) :
    Valid policy (world.addConstant constant schema formed fresh) cache ∧
      entries (DeclarationTable.extendIdentity before constant identity) cache = entries before cache :=
  ⟨weaken_valid (world.addConstant_includes constant schema formed fresh) valid,
    entries_fresh_identity policy world constant (world.constant_unregistered constant fresh) before identity cache valid⟩

end Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorization
