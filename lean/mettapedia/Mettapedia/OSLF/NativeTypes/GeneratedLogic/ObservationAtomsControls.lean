import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ObservationAtoms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaDriverReading
import Mettapedia.OSLF.NativeTypes.Runtime.Controls
import Mettapedia.OSLF.MeTTaIL.PatternTreeSize

/-!
# Controls: observations of the λ-calculus as declared relations

The λ driver observes the size of a term: "at most three nodes" and "at most five nodes", counted on the term as
written. Declared with the language as the unary relations `small3` and `small5`, they are the atoms `inRelation
"small3"` and `inRelation "small5"` of its native types, and the λ driver's reading by steps extends to them.

- `λx. x` has three nodes, and `(λx. x) (λx. x)` seven: the first is small and the second is not, while its step reaches
  a small term. The generated front door decides each closed formula, evaluated by the kernel with the declared
  relations, and the runtime agrees at every budget (`agrees`).
- A relation the language does not declare holds of nothing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Observations.Controls

open Mettapedia.OSLF.Binding LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver Meaning)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Test)
open Mettapedia.OSLF.NativeTypes.Decision.Admission (LeafAdmission)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.ReferenceAgreement (selectedLanguage)
open Mettapedia.OSLF.MeTTaIL.PatternTreeSize (nodes)

/-! ## The declared observations -/

/-- **At most this many nodes**, counted on the term as written. -/
def small (bound : ℕ) : Observation := ⟨"small" ++ toString bound, fun term => decide (nodes term ≤ bound)⟩

/-- The observations the language declares. -/
def observations : List Observation := [small 3, small 5]

/-- The relation environment with the declared observations. -/
abbrev env : RelationEnv := observationEnv RelationEnv.empty observations

def declaredAs : Fin 2 → Observation := fun atom => if atom.val = 0 then small 3 else small 5

theorem declared : ∀ atom, Declared observations (declaredAs atom) := by
  intro atom
  fin_cases atom <;> rfl

/-! ## The λ driver with its observations -/

abbrev base : Driver := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.driver {} []

/-- The runtime's test of an observation: the encoding of the term is observed. -/
def sizeTest (atom : Fin 2) : Test base.system base.admitted :=
  Test.ofBoolean
    ⟨fun source => (declaredAs atom).observe (encodeTerm source) = true, by
      intro first second related
      change first = second at related
      subst second
      rfl⟩
    (fun source => (declaredAs atom).observe (encodeTerm source)) (fun _ => Iff.rfl)

def atomicAdmission : LeafAdmission (Fin 2) where
  admitted _ := True
  probe _ := .ok ()
  exact _ := ⟨fun _ => trivial, fun _ => rfl⟩

/-- **The λ driver, observing sizes.** -/
abbrev observed : Driver := Mettapedia.OSLF.NativeTypes.Runtime.Atoms.extend base sizeTest atomicAdmission

/-- **Its reading by steps, with the observations as declared relations.** -/
def reading :=
  (LambdaReading.reading {} env).observe sizeTest atomicAdmission declaredAs declared (by decide)
    fun _ source _ => ⟨fun observedHolds =>
      ⟨Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.encode_object source, observedHolds⟩,
      fun both => both.2⟩

/-- The variables of the λ driver's tests. -/
abbrev positive (leaf : base.Leaf) := LocalReading.testVariable (LambdaReading.configured {}) leaf.index true
abbrev negative (leaf : base.Leaf) := LocalReading.testVariable (LambdaReading.configured {}) leaf.index false

/-- The closed formula of a formula about the observed driver. -/
def closed (formula : observed.Formula) : Formula 0 :=
  (Embeddings.ofCore (observedPositive (k := 2) positive) (observedNegative (k := 2) negative) (fun _ => .hashBag) true
    formula).subst reading.closing

/-- **The generated front door's answer** about a formula of the observed driver, with the declared relations. -/
def frontDoor (formula : observed.Formula) (raw : Pattern) (rounds : ℕ) : Option Bool :=
  match ask env [] (selectedLanguage {}) 3 (closed formula) raw none rounds with
  | .proved _ => some true
  | .refuted _ => some false
  | .unknown _ => none

/-- **The runtime agrees with the generated front door** about a formula without separating conjunctions whose
constructor tests accept everything, at a closed λ-term, at every budget. -/
theorem agrees (formula : observed.Formula) (atoms : Embeddings.AtomsCovered reading.covers formula)
    (spatial : Embeddings.spatialFree formula = true) (term : Term sig [] .term) {rounds : ℕ} {answer : Bool}
    (answered : frontDoor formula (encodeTerm term) rounds = some answer) (budget : ℕ) {runtimeAnswer : Bool}
    (read : (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed formula (encodeTerm term) budget).readout =
      .judgment (.decided runtimeAnswer)) :
    runtimeAnswer = answer := by
  have meaning := Embeddings.meaning_iff_sat_steps (kindOf := fun _ => .hashBag) reading formula atoms spatial
    (⟨term, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted term, rfl⟩ :
      observed.Decoded (encodeTerm term)) trivial
  unfold frontDoor at answered
  split at answered
  · rename_i evidence proved
    cases answered
    cases runtimeAnswer with
    | true => rfl
    | false =>
      exact absurd (meaning.mpr (ask_proved proved))
        (Mettapedia.OSLF.NativeTypes.Runtime.Description.negative observed formula _ _ read)
  · rename_i evidence refuted
    cases answered
    cases runtimeAnswer with
    | false => rfl
    | true =>
      exact absurd (meaning.mp (Mettapedia.OSLF.NativeTypes.Runtime.Description.positive observed formula _ _ read))
        (ask_refuted refuted)
  · cases answered

/-! ## The controls -/

open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls (identity redex)

/-- The test "built by `Lam`". -/
def lamLeaf : base.Leaf := ⟨⟨1, by decide⟩, fun _ _ => true⟩

theorem lam_label : (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration (LambdaReading.configured {})
    lamLeaf.index).label = "Lam" := by decide

def smallThree : observed.Formula := .atom (.inr 0)
def smallFive : observed.Formula := .atom (.inr 1)

theorem identity_small : frontDoor smallThree (encodeTerm identity) 4 = some true := by decide +kernel

theorem redex_not_small : frontDoor smallFive (encodeTerm redex) 6 = some false := by decide +kernel

theorem redex_steps_to_small : frontDoor (.possibility smallThree) (encodeTerm redex) 6 = some true := by
  decide +kernel

theorem identity_lam_and_small :
    frontDoor (.conj (.atom (.inl lamLeaf)) smallThree) (encodeTerm identity) 4 = some true := by decide +kernel

theorem identity_small_agrees (budget : ℕ) {answer : Bool}
    (read : (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed smallThree (encodeTerm identity)
      budget).readout = .judgment (.decided answer)) : answer = true :=
  agrees smallThree trivial rfl identity identity_small budget read

theorem redex_not_small_agrees (budget : ℕ) {answer : Bool}
    (read : (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed smallFive (encodeTerm redex)
      budget).readout = .judgment (.decided answer)) : answer = false :=
  agrees smallFive trivial rfl redex redex_not_small budget read

theorem redex_steps_to_small_agrees (budget : ℕ) {answer : Bool}
    (read : (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed (.possibility smallThree)
      (encodeTerm redex) budget).readout = .judgment (.decided answer)) : answer = true :=
  agrees (.possibility smallThree) trivial rfl redex redex_steps_to_small budget read

theorem identity_lam_and_small_agrees (budget : ℕ) {answer : Bool}
    (read : (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed (.conj (.atom (.inl lamLeaf)) smallThree)
      (encodeTerm identity) budget).readout = .judgment (.decided answer)) : answer = true :=
  agrees (.conj (.atom (.inl lamLeaf)) smallThree) ⟨fun _ _ => rfl, trivial⟩ rfl identity identity_lam_and_small
    budget read

-- The runtime itself, compiled, gives the same answers.
#guard (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed smallThree (encodeTerm identity) 20).readout ==
  .judgment (.decided true)
#guard (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed smallFive (encodeTerm redex) 20).readout ==
  .judgment (.decided false)
#guard (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed (.possibility smallThree) (encodeTerm redex)
  20).readout == .judgment (.decided true)

/-- **A relation the language does not declare holds of nothing.** -/
theorem undeclared_holds_nothing (term : Pattern) :
    ¬ (referenceStructure env (selectedLanguage {})).sat Env.closed (.inRelation "large") term := by
  rintro ⟨-, representative, -, member⟩
  have notFound : observations.find? (fun observation => observation.name == "large") = none := rfl
  simp [builtinRelationTuples_single, env, observationEnv, notFound, RelationEnv.empty] at member

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Observations.Controls
