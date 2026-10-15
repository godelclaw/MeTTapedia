import Mettapedia.Languages.HOLLight.MeTTa.InferenceHistory
import Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorizationControls

/-!
# General TRANS over constructed authorized records

The input cache is constructed from an assumption and an explicit object
axiom. The actual source TRANS event retains the resulting hypothesis and
dependency, with distinct equality endpoints. This is an inference-event
control; it does not assert source replay of an arbitrary initial history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.InferenceHistoryControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization Eval
open Effects (State)

def world : TheoryContext := SourceProfile.primitiveContext
def constants : Const → Atom := DeclarationTable.primitiveIdentity

private theorem boolean_formed : TypeFormed world.signature Ty.bool :=
  ContextControls.boolean_formed.mono (ContextControls.core_includes.trans
    (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))

private theorem function_registered : world.signature.typeOperators TypeOp.function = some 2 :=
  (ContextControls.core_includes.trans (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes)).1
    _ _ ContextControls.function_registered

private theorem equality_instance : ConstantInstance world.signature Const.equality (Ty.equality Ty.bool) := by
  refine ⟨Ty.equality (.var ContextControls.equalityParameter),
    ⟨[(ContextControls.equalityParameter, Ty.bool)]⟩, ?_, ?_⟩
  · exact (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes).2 _ _
      (ContextControls.baseContext.addConstant_registered _ _ ContextControls.equality_schema_formed _)
  · simp [TypeSubst.lookup, Ty.equality, Ty.function, Ty.bool]

def boolVar (name : String) : CanonicalTerm :=
  ⟨.free ⟨Name.global name, Ty.bool⟩, Ty.bool, by simp [DBTerm.inferType]⟩

def equation (left right : String) : CanonicalTerm :=
  CanonicalTerm.equalityOfSameType (boolVar left) (boolVar right) rfl

private theorem equation_formed (left right : String) : AnnotationsFormed world.signature (equation left right).term := by
  have equalityFormed := TypeFormed.function _ function_registered boolean_formed
    (TypeFormed.function _ function_registered boolean_formed boolean_formed)
  exact .app (.app (.constant equalityFormed equality_instance) (.free boolean_formed)) (.free boolean_formed)

def commitment : Dependency := ⟨.grounded (.string "q=r"), equation "q" "r", rfl⟩
def policy : AxiomPolicy := fun sequent => sequent = commitment.sequent
def left : Record := ⟨[equation "p" "q"], equation "p" "q", [], .symbol "ASSUME"⟩
def right : Record := ⟨[], equation "q" "r", [commitment], .symbol "AXIOM"⟩
def first : Atom := .grounded (.string "first")
def second : Atom := .grounded (.string "second")
def key : Atom := .grounded (.string "trans")
def cache : Cache := [(first, left), (second, right)]

private theorem left_derived : TheoryDerives policy world left.fact := by
  apply TheoryDerives.inference (request := .assume (equation "p" "q"))
  · exact ⟨rfl, by simp [HasParts, left, Record.fact]⟩
  · refine ⟨by simp [InferenceFormation.types], ?_⟩
    intro term member
    simp only [InferenceFormation.terms, List.mem_singleton] at member
    exact member ▸ equation_formed "p" "q"
  · simp [InferenceRequest.premises]
  · refine ⟨⟨equation_formed "p" "q", ?_⟩, ?_⟩
    · intro term member
      have same : term = equation "p" "q" := by simpa [left, Record.fact] using member
      exact same ▸ equation_formed "p" "q"
    · simp [left, Record.fact]

private theorem right_derived : TheoryDerives policy world right.fact := by
  apply TheoryDerives.axiom (sequent := commitment.sequent)
  · rfl
  · rfl
  · exact ⟨⟨rfl, by simp [Dependency.sequent]⟩, by simp [HasParts, right, Record.fact, Dependency.sequent, commitment]⟩
  · refine ⟨⟨equation_formed "q" "r", by simp [right, Record.fact]⟩, ?_⟩
    intro sequent member
    have same : sequent = commitment.sequent := by simpa [right, Record.fact] using member
    rw [same]
    exact ⟨equation_formed "q" "r", by simp [Dependency.sequent]⟩

theorem cache_valid : Valid policy world cache := by
  intro entry member
  simp only [cache, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact left_derived
  · exact right_derived

/-- The general source event handles both nonempty hypothesis and dependency
metadata, rather than the special empty-support reflexivity case. -/
theorem mixed_support_event (state : State) (operators declarations axioms : Atom) :
    let initial := ProofLookup.sourceState operators declarations axioms (.symbol "HOL:Nil") (entries constants cache)
    let request := Atom.expression [.symbol "TRANS", first, second]
    let bindings := [("request", request), ("key", key), ("state", initial)]
    ∃ next : Record, next.hypotheses = [equation "p" "q"] ∧ next.dependencies = [commitment] ∧
      next.conclusion.term = CanonicalTerm.equalityDB Ty.bool (boolVar "p").term (boolVar "r").term ∧
      TheoryDerives policy world next.fact ∧ Valid policy world ((key, next) :: cache) ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"]) state
        (.expression [.symbol "Some", ProofLookup.sourceState operators declarations axioms
          (ReceiptKeys.table [⟨key, request, [first, second]⟩]) (entries constants ((key, next) :: cache))]) := by
  dsimp only
  obtain ⟨next, conclusion, hypotheses, dependencies, _, _, derived, valid, returned⟩ :=
    InferenceHistory.authored_trans_preserves_valid policy world constants
      (DeclarationTable.primitiveIdentity_identifies _) rfl cache cache_valid left right first second
      rfl rfl (boolVar "p") (boolVar "q") (boolVar "r") ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      [] operators declarations axioms key rfl (by decide)
      [("request", .expression [.symbol "TRANS", first, second]), ("key", key),
        ("state", ProofLookup.sourceState operators declarations axioms (.symbol "HOL:Nil") (entries constants cache))]
      state "state" "key" "request" rfl rfl rfl
  refine ⟨next, ?_, ?_, conclusion, derived, valid, returned⟩
  · simpa [CacheUnion.hypotheses, left, right, List.KeyedUnion.merge] using hypotheses
  · simpa [CacheUnion.dependencies, left, right, List.KeyedUnion.merge] using dependencies

theorem mixed_support_is_nonreflexive : (boolVar "p").term ≠ (boolVar "r").term := by
  simp [boolVar, Name.global]

end Mettapedia.Languages.HOLLight.MeTTa.InferenceHistoryControls
