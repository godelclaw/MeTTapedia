import Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorization

/-!
# Constructed authored-cache evidence and refusal controls

A source event constructs an authorized theorem in the actual primitive
declaration context. Its next authored lookup consumes the returned cache.
Different logical records cannot be substituted under the same address.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorizationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization
open Eval
open Effects (State)

def world : TheoryContext := SourceProfile.primitiveContext
def constants : Const → Atom := DeclarationTable.primitiveIdentity
def operators : Atom := OperatorTable.tableAtom DeclarationTable.sourcePrimitive.operators
  (fun _ => .symbol "HOL:Primitive")
def declarations : Atom := DeclarationTable.tableAtom DeclarationTable.sourcePrimitive constants
def key : Atom := .grounded (.string "seed")
def source : CheckedSourceTerm := ⟨.var (Name.global "p") Ty.bool, Ty.bool, by simp [SourceTerm.inferType]⟩
def request : Atom := .expression [.symbol "REFL", TermReading.sourceAtom source.source]
def initial : Atom := ProofLookup.sourceState operators declarations (.symbol "HOL:Nil") (.symbol "HOL:Nil") []
def bindings : Subst := [("request", request), ("key", key), ("state", initial)]

private theorem boolean_formed : TypeFormed world.signature Ty.bool :=
  ContextControls.boolean_formed.mono (ContextControls.core_includes.trans
    (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))
private theorem function_registered : world.signature.typeOperators TypeOp.function = some 2 :=
  (ContextControls.core_includes.trans (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes)).1
    _ _ ContextControls.function_registered
private theorem boolean_registered : world.signature.typeOperators TypeOp.bool = some 0 := by
  have formed := boolean_formed
  simp only [Ty.bool, TypeFormed] at formed
  exact formed.1
private theorem source_resolved : TermReading.SourceResolved world.signature source.source := by
  simp only [source, TermReading.SourceResolved]
  refine ⟨rfl, ?_⟩
  simp only [Ty.bool, TypeFormation.Resolved]
  exact ⟨⟨0, boolean_registered⟩, by simp⟩
private theorem source_formed : AnnotationsFormed world.signature source.canonical.term := by
  simp only [source, CheckedSourceTerm.canonical, SourceTerm.toDB]
  exact .free boolean_formed
private theorem equality_formed : TypeFormed world.signature (Ty.equality source.ty) :=
  TypeFormed.function _ function_registered boolean_formed
    (TypeFormed.function _ function_registered boolean_formed boolean_formed)
private theorem equality_registered : ConstantInstance world.signature Const.equality (Ty.equality source.ty) := by
  refine ⟨Ty.equality (.var ContextControls.equalityParameter),
    ⟨[(ContextControls.equalityParameter, Ty.bool)]⟩, ?_, ?_⟩
  · exact (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes).2 _ _
      (ContextControls.baseContext.addConstant_registered _ _ ContextControls.equality_schema_formed _)
  · simp [source, TypeSubst.lookup, Ty.equality, Ty.function, Ty.bool]

def stateWith (record : Record) : Atom := ProofLookup.sourceState operators declarations (.symbol "HOL:Nil")
  (ReceiptKeys.table [⟨key, request, []⟩]) (entries constants [(key, record)])

def readBack : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"],
  .expression [
    .expression [.expression [.symbol "Some", .var "next"],
      .expression [.symbol "hol-light:known", .var "next", .var "key"]],
    .expression [.var "refused", .symbol "None"]]]

/-- The actual source event starts from an empty proof cache, constructs its
registered derivation and then executes lookup from the returned state value.
The cache invariant and both computations are instantiated, not assumed. -/
theorem authored_event_and_readback (state : State) :
    ∃ record : Record, TheoryDerives emptyAxiomPolicy world record.fact ∧
      Valid emptyAxiomPolicy world [(key, record)] ∧
      PureReturns program bindings state readBack state
        (.expression [.symbol "Some", record.atom constants]) := by
  obtain ⟨record, derived, valid, _, _, _, _, event⟩ := authored_refl_preserves_valid
    emptyAxiomPolicy world DeclarationTable.sourcePrimitive (fun _ => .symbol "HOL:Primitive") constants rfl
    source source_resolved source_formed equality_formed equality_registered [] (empty_valid _ _) []
    key (.symbol "HOL:Nil") rfl rfl bindings state "state" "key" "request" rfl rfl rfl
  let after := stateWith record
  let next : Subst := ("next", after) :: bindings
  have actual : PureReturns program bindings state
      (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"])
      state (.expression [.symbol "Some", after]) := event
  have found : (entries constants [(key, record)]).lookup key = some (record.atom constants) := by simp [entries]
  obtain ⟨_, lookedUp⟩ := authored_known_derivation emptyAxiomPolicy world constants
    (DeclarationTable.primitiveIdentity_identifies _) [(key, record)] valid key record derived.wellFormed found
    operators declarations (.symbol "HOL:Nil") (ReceiptKeys.table [⟨key, request, []⟩]) next state
    "next" "key" rfl rfl
  refine ⟨record, derived, valid, ?_⟩
  unfold readBack
  let alternatives : SpaceSemantics.Cases :=
    [(.expression [.symbol "Some", .var "next"], .expression [.symbol "hol-light:known", .var "next", .var "key"]),
      (.var "refused", .symbol "None")]
  apply case_returns program bindings next state state state _ (.expression [.symbol "Some", after])
    (.expression [.symbol "hol-light:known", .var "next", .var "key"]) _ _ alternatives
    (read_cases_encoded alternatives) actual _ lookedUp
  simp [alternatives, next, bindings, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

def sharedKey : Atom := .grounded (.string "shared")
def sharedRequest : Atom := .expression [.symbol "TRANS", key, key]
def reuseBindings : Subst := ("sharedKey", sharedKey) :: ("sharedRequest", sharedRequest) :: bindings
def reuse : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"],
  .expression [
    .expression [.expression [.symbol "Some", .var "next"],
      .expression [.symbol "hol-light:step", .var "next", .var "sharedKey", .var "sharedRequest"]],
    .expression [.var "refused", .symbol "None"]]]
def stateWithReuse (record next : Record) : Atom := ProofLookup.sourceState operators declarations (.symbol "HOL:Nil")
  (ReceiptKeys.table [⟨sharedKey, sharedRequest, [key, key]⟩, ⟨key, request, []⟩])
  (entries constants [(sharedKey, next), (key, record)])

/-- Two actual source events construct the final authorized cache from an
empty cache. TRANS reads the same earned premise twice, and its two address
occurrences remain in the concrete returned receipt. -/
theorem authored_event_and_shared_reuse (state : State) :
    ∃ record next : Record, next.fact = record.fact ∧
      TheoryDerives emptyAxiomPolicy world next.fact ∧
      Valid emptyAxiomPolicy world [(sharedKey, next), (key, record)] ∧
      PureReturns program reuseBindings state reuse state
        (.expression [.symbol "Some", stateWithReuse record next]) := by
  obtain ⟨record, _, valid, hypotheses, dependencies, _, reflexivity, event⟩ := authored_refl_preserves_valid
    emptyAxiomPolicy world DeclarationTable.sourcePrimitive (fun _ => .symbol "HOL:Primitive") constants rfl
    source source_resolved source_formed equality_formed equality_registered [] (empty_valid _ _) []
    key (.symbol "HOL:Nil") rfl rfl reuseBindings state "state" "key" "request" rfl rfl rfl
  let after := stateWith record
  let nextBindings : Subst := ("next", after) :: reuseBindings
  obtain ⟨next, same, derived, finalValid, _, second⟩ := authored_trans_reflexivity_preserves_valid
    emptyAxiomPolicy world constants (DeclarationTable.primitiveIdentity_identifies _) rfl
    source.canonical source_formed [(key, record)] valid record key (by simp) reflexivity hypotheses dependencies
    [⟨key, request, []⟩] operators declarations (.symbol "HOL:Nil") sharedKey
    (by decide) (by simp [entries, key, sharedKey]) nextBindings state "next" "sharedKey" "sharedRequest" rfl rfl rfl
  have first : PureReturns program reuseBindings state
      (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"])
      state (.expression [.symbol "Some", after]) := event
  refine ⟨record, next, same, derived, finalValid, ?_⟩
  unfold reuse
  let alternatives : SpaceSemantics.Cases :=
    [(.expression [.symbol "Some", .var "next"],
      .expression [.symbol "hol-light:step", .var "next", .var "sharedKey", .var "sharedRequest"]),
     (.var "refused", .symbol "None")]
  apply case_returns program reuseBindings nextBindings state state state _ (.expression [.symbol "Some", after])
    (.expression [.symbol "hol-light:step", .var "next", .var "sharedKey", .var "sharedRequest"]) _ _ alternatives
    (read_cases_encoded alternatives) first _ second
  simp [alternatives, nextBindings, reuseBindings, bindings, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

def equality : CanonicalTerm := CanonicalTerm.equalityOfSameType source.canonical source.canonical rfl
def retained : Record := ⟨[], equality, [], .symbol "same-origin"⟩
def forged : Record := ⟨[], source.canonical, [], .symbol "same-origin"⟩
private theorem retained_formed : TheoremFormed world.signature retained.fact := by
  refine ⟨⟨?_, by simp [retained, Record.fact]⟩, by simp [retained, Record.fact]⟩
  change AnnotationsFormed world.signature (CanonicalTerm.equalityDB source.ty source.canonical.term source.canonical.term)
  exact .app (.app (.constant equality_formed equality_registered) source_formed) source_formed
private theorem forged_formed : TheoremFormed world.signature forged.fact := by
  exact ⟨⟨source_formed, by simp [forged, Record.fact]⟩, by simp [forged, Record.fact]⟩

/-- A formed Boolean claim at the same key and origin is still not the stored
equality theorem. This refusal concerns its payload, not its printed label. -/
theorem forged_conclusion_not_found :
    (entries constants [(key, retained)]).lookup key ≠ some (forged.atom constants) := by
  apply mismatched_fact_not_found world constants (DeclarationTable.primitiveIdentity_identifies _)
    key retained forged retained_formed forged_formed
  intro same
  have terms := congrArg (fun fact : Theorem => fact.sequent.concl.term) same
  simp [retained, forged, Record.fact, equality, source, CheckedSourceTerm.canonical,
    CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, SourceTerm.toDB, boundIndex] at terms

/-- Changing a registered identity is outside fresh-declaration transport. -/
theorem existing_equality_is_not_fresh : world.signature.constants Const.equality ≠ none := by
  obtain ⟨schema, _, found, _⟩ := equality_registered
  rw [found]
  exact Option.some_ne_none schema

end Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorizationControls
