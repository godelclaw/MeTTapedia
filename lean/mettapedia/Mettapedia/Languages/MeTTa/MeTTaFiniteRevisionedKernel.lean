import Mettapedia.GSLT.LanguageDef.SemanticEvidence
import Mettapedia.GSLT.LanguageDef.ProofSystems
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProvider
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
import Mettapedia.Languages.MeTTa.MeTTaZeroNativeKernel
import Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
import Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire
import Mettapedia.Languages.MeTTa.PeTTa.CellHistory

/-!
# Finite native realization of revisioned named-space operations

Finite rows use the existing `CellHistory.History` and `values` operations.
Their interpretation is the existing functional `RevisionedSpaces` world.
Different row enumerations may denote the same world: the raw checker compares
revision and all supported named-space occurrence bags, not row order.

Publication and matching below implement the original `PersistentEmitReceipt`
and `MatchArticle` relations. Computed result bags and replayed explicit
matching choices earn the same independent source articles. Checked-ground continuations and support-aware contextual continuations are
distinct admitted operations. The latter check actual source capture depths,
scoped fillings and binder transport. They retain explicit substitution and
collection-rest syntax rather than identifying this fragment with a whole
Prime, HE or PeTTa operational profile.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy (QueryProof)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

abbrev History := PeTTa.CellHistory.History Pattern
abbrev WorldCode := Nat × History

def rowsAt (code : WorldCode) (space : String) : List Pattern :=
  PeTTa.CellHistory.values code.2 space

def interpret (code : WorldCode) : RevisionedSpaces String where
  revision := code.1
  contents := fun space => (rowsAt code space : Multiset Pattern)

/-- Publication constructs a new occurrence and advances the actual revision.
The front position is this representation's strategy, not a language order. -/
def publish (code : WorldCode) (space : String) (atom : Pattern) : WorldCode :=
  (code.1 + 1, (space, atom) :: code.2)

@[simp] theorem rowsAt_publish (code : WorldCode) (written read : String)
    (atom : Pattern) :
    rowsAt (publish code written atom) read =
      if read = written then atom :: rowsAt code read else rowsAt code read := by
  by_cases same : read = written
  · subst read
    simp [rowsAt, publish, PeTTa.CellHistory.values]
  · simp [rowsAt, publish, PeTTa.CellHistory.values, same, Ne.symm same]

/-- The finite update realizes the actual source update, for every named
space including names absent from the finite code. -/
theorem interpret_publish (code : WorldCode) (space : String) (atom : Pattern) :
    interpret (publish code space atom) = addAtomWorld (interpret code) space atom := by
  apply RevisionedSpaces.ext
  · rfl
  · intro read
    by_cases same : read = space
    · subst read
      simp [interpret, addAtomWorld, rowsAt_publish]
    · simp [interpret, addAtomWorld, rowsAt_publish, same]

private theorem rowsAt_nil_of_absent (code : WorldCode) (space : String)
    (absent : space ∉ code.2.map Prod.fst) : rowsAt code space = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro row member
  have different : row.1 ≠ space := by
    intro same
    exact absent (List.mem_map.mpr ⟨row, member, same⟩)
  simp [different]

/-- Finite comparison observes all names present in either code. Unsupported
names are empty by construction, so they need not be searched separately. -/
def Equivalent (first second : WorldCode) : Prop :=
  first.1 = second.1 ∧
    ∀ space ∈ (first.2 ++ second.2).map Prod.fst,
      (rowsAt first space : Multiset Pattern) = rowsAt second space

instance (first second : WorldCode) : Decidable (Equivalent first second) := by
  unfold Equivalent
  infer_instance

def sameWorld (first second : WorldCode) : Bool := decide (Equivalent first second)

/-- Code equivalence is exactly functional-world equality, proved from finite
support rather than assuming a decider for arbitrary function equality. -/
theorem equivalent_iff_interpret (first second : WorldCode) :
    Equivalent first second ↔ interpret first = interpret second := by
  constructor
  · rintro ⟨revision, spaces⟩
    apply RevisionedSpaces.ext
    · exact revision
    · intro space
      by_cases present : space ∈ (first.2 ++ second.2).map Prod.fst
      · exact spaces space present
      · have absentFirst : space ∉ first.2.map Prod.fst := by
          intro member
          exact present (by simp only [List.map_append, List.mem_append]; exact Or.inl member)
        have absentSecond : space ∉ second.2.map Prod.fst := by
          intro member
          exact present (by simp only [List.map_append, List.mem_append]; exact Or.inr member)
        simp [interpret, rowsAt_nil_of_absent first space absentFirst,
          rowsAt_nil_of_absent second space absentSecond]
  · intro same
    refine ⟨congrArg RevisionedSpaces.revision same, ?_⟩
    intro space _
    exact congrArg (fun world : RevisionedSpaces String => world.contents space) same

@[simp] theorem sameWorld_exact (first second : WorldCode) :
    sameWorld first second = true ↔ interpret first = interpret second := by
  simp [sameWorld, equivalent_iff_interpret]

/-- Intrinsic raw matching evidence reuses the already specified occurrence
coordinates. Checked-ground instantiation is the source's own gate. -/
def MatchValid (before after : WorldCode) (space : String)
    (pattern template result : Pattern) (proof : QueryProof) : Prop :=
  interpret after = interpret before ∧
  proof.atomOccurrence < Multiset.count proof.candidate
    ((interpret before).contents space) ∧
  proof.matchOccurrence < Multiset.count proof.bindings
    ((structuralModel).matchAtoms pattern proof.candidate) ∧
  applyBindingsGround? proof.bindings template = some result

def checkMatch (before after : WorldCode) (space : String)
    (pattern template result : Pattern) (proof : QueryProof) : Bool :=
  sameWorld after before &&
  decide (proof.atomOccurrence < Multiset.count proof.candidate
    (rowsAt before space : Multiset Pattern)) &&
  decide (proof.matchOccurrence < Multiset.count proof.bindings
    (matchPattern pattern proof.candidate : Multiset Bindings)) &&
  decide (applyBindingsGround? proof.bindings template = some result)

@[simp] theorem checkMatch_exact (before after : WorldCode) (space : String)
    (pattern template result : Pattern) (proof : QueryProof) :
    checkMatch before after space pattern template result proof = true ↔
      MatchValid before after space pattern template result proof := by
  simp [checkMatch, MatchValid, interpret, structuralModel, and_assoc]

def matchArticleOfValid {before after : WorldCode} {space : String}
    {pattern template result : Pattern} {proof : QueryProof}
    (valid : MatchValid before after space pattern template result proof) :
    MatchArticle structuralModel space pattern template
      (interpret before) (interpret after) result where
  readOnly := valid.1
  event := {
    candidate := proof.candidate
    atomOccurrence := proof.atomOccurrence
    atomOccurrence_exists := valid.2.1
    bindings := proof.bindings
    matchOccurrence := proof.matchOccurrence
    matchOccurrence_exists := valid.2.2.1
    instantiates := valid.2.2.2 }

/-- Exactness with the existing independent source article, for every finite
represented before/after world. Alternate representations remain admissible. -/
theorem matchArticle_iff_exists_checked (before after : WorldCode) (space : String)
    (pattern template result : Pattern) :
    Nonempty (MatchArticle structuralModel space pattern template
      (interpret before) (interpret after) result) ↔
      ∃ proof : QueryProof,
        checkMatch before after space pattern template result proof = true := by
  constructor
  · rintro ⟨article⟩
    refine ⟨⟨article.event.candidate, article.event.atomOccurrence,
      article.event.bindings, article.event.matchOccurrence⟩,
      (checkMatch_exact before after space pattern template result _).mpr ?_⟩
    exact ⟨article.readOnly, article.event.atomOccurrence_exists,
      article.event.matchOccurrence_exists, article.event.instantiates⟩
  · rintro ⟨proof, accepted⟩
    exact ⟨matchArticleOfValid ((checkMatch_exact before after space pattern template result proof).mp accepted)⟩

/-- Native execution actually enumerates candidates, matches them, checks
continuation instantiation and emits the successful results. -/
def matchResults (before : WorldCode) (space : String)
    (pattern template : Pattern) : List Pattern :=
  (rowsAt before space).flatMap fun candidate =>
    (matchPattern pattern candidate).filterMap fun bindings =>
      applyBindingsGround? bindings template

/-- Native matching is sound and existence-complete for the existing source
`MatchArticle`. Its result list is a physical enumeration of occurrences. -/
theorem mem_matchResults_iff_article (before : WorldCode) (space : String)
    (pattern template result : Pattern) :
    result ∈ matchResults before space pattern template ↔
      Nonempty (MatchArticle structuralModel space pattern template
        (interpret before) (interpret before) result) := by
  simp only [matchResults, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨candidate, candidateMember, bindings, bindingMember, instantiates⟩
    exact ⟨{
      readOnly := rfl
      event := {
        candidate := candidate
        atomOccurrence := 0
        atomOccurrence_exists := by
          have member : candidate ∈ (rowsAt before space : Multiset Pattern) := by
            simpa using candidateMember
          exact Multiset.count_pos.mpr member
        bindings := bindings
        matchOccurrence := 0
        matchOccurrence_exists := by
          have member : bindings ∈ (matchPattern pattern candidate : Multiset Bindings) := by
            simpa using bindingMember
          exact Multiset.count_pos.mpr member
        instantiates := instantiates } }⟩
  · rintro ⟨article⟩
    exact ⟨article.event.candidate,
      Multiset.count_pos.mp (Nat.zero_lt_of_lt article.event.atomOccurrence_exists),
      article.event.bindings,
      Multiset.count_pos.mp (Nat.zero_lt_of_lt article.event.matchOccurrence_exists),
      article.event.instantiates⟩

/-- Publication evidence checks the actual interpreted update, with no
function-equality oracle and no trusted after-state. -/
def checkEmit (before after : WorldCode) (space : String) (atom : Pattern) : Bool :=
  sameWorld after (publish before space atom)

@[simp] theorem checkEmit_exact (before after : WorldCode) (space : String)
    (atom : Pattern) :
    checkEmit before after space atom = true ↔
      Nonempty (PersistentEmitReceipt (interpret before) (interpret after) space atom) := by
  rw [checkEmit, sameWorld_exact, interpret_publish]
  constructor
  · intro same
    exact ⟨⟨same⟩⟩
  · rintro ⟨receipt⟩
    exact receipt.after_eq

/-- The native update constructs the source receipt, rather than requesting a
soundness callback from the caller. -/
def publishReceipt (before : WorldCode) (space : String) (atom : Pattern) :
    PersistentEmitReceipt (interpret before) (interpret (publish before space atom)) space atom :=
  ⟨interpret_publish before space atom⟩


/-! ## Occurrence bags and causal composition -/

/-- Every physical native match occurrence is retained, including duplicate
space rows and duplicate matcher solutions. -/
theorem matchResults_bag (before : WorldCode) (space : String)
    (pattern template : Pattern) :
    (matchResults before space pattern template : Multiset Pattern) =
      MeTTaRevisionedQueryBindEval.matchBag (interpret before) space pattern template := by
  unfold matchResults MeTTaRevisionedQueryBindEval.matchBag interpret
  simp only [structuralModel, Multiset.filterMap_coe]
  exact (Multiset.coe_bind _ _).symm

/-- The larger operation is the existing source bind of persistent emission
and read-only matching. There is no second source transition relation. -/
def publicationThenMatch (written : String) (atom : Pattern) (queried : String)
    (pattern template : Pattern) : Computation (RevisionedSpaces String) Pattern :=
  Bind (AddAtom written atom) fun _ => Match structuralModel queried pattern template

/-- Native execution performs the publication before looking up matching
occurrences in the resulting world. -/
def publishAndMatch (before : WorldCode) (written : String) (atom : Pattern)
    (queried : String) (pattern template : Pattern) : WorldCode × List Pattern :=
  let after := publish before written atom
  (after, matchResults after queried pattern template)

theorem publicationThenMatch_iff_article (before after : WorldCode)
    (written : String) (atom : Pattern) (queried : String)
    (pattern template result : Pattern) :
    Nonempty (publicationThenMatch written atom queried pattern template
      (interpret before) (interpret after) result) ↔
      Nonempty (MatchArticle structuralModel queried pattern template
        (interpret (publish before written atom)) (interpret after) result) := by
  constructor
  · rintro ⟨middle, value, published, matched⟩
    have middleEq : middle = interpret (publish before written atom) :=
      published.1.after_eq.trans (interpret_publish before written atom).symm
    change MatchArticle structuralModel queried pattern template middle (interpret after) result at matched
    exact ⟨by simpa only [middleEq] using matched⟩
  · rintro ⟨article⟩
    exact ⟨⟨interpret (publish before written atom), (),
      ⟨publishReceipt before written atom, ⟨rfl⟩⟩, article⟩⟩

/-- Exact checking of the composed source operation, including the complete
after-state. The publication receipt is constructed by the operation. -/
theorem publicationThenMatch_iff_checked (before after : WorldCode)
    (written : String) (atom : Pattern) (queried : String)
    (pattern template result : Pattern) :
    Nonempty (publicationThenMatch written atom queried pattern template
      (interpret before) (interpret after) result) ↔
      ∃ proof : QueryProof,
        checkMatch (publish before written atom) after queried pattern template result proof = true := by
  rw [publicationThenMatch_iff_article, matchArticle_iff_exists_checked]

/-- Every source execution of this composition from a represented world has
a represented output. No completeness for arbitrary input function worlds is
assumed. -/
theorem publicationThenMatch_represented_output (before : WorldCode)
    (after : RevisionedSpaces String) (written : String) (atom : Pattern)
    (queried : String) (pattern template result : Pattern)
    (running : Nonempty (publicationThenMatch written atom queried pattern template
      (interpret before) after result)) :
    after = interpret (publish before written atom) := by
  rcases running with ⟨middle, value, published, matched⟩
  exact matched.readOnly.trans
    (published.1.after_eq.trans (interpret_publish before written atom).symm)

/-- Native execution covers exactly the successful source results while
constructing their correct after-state. -/
theorem publishAndMatch_source_exact (before : WorldCode)
    (written : String) (atom : Pattern) (queried : String)
    (pattern template result : Pattern) :
    result ∈ (publishAndMatch before written atom queried pattern template).2 ↔
      Nonempty (publicationThenMatch written atom queried pattern template
        (interpret before)
        (interpret (publishAndMatch before written atom queried pattern template).1) result) := by
  change result ∈ matchResults (publish before written atom) queried pattern template ↔ _
  rw [mem_matchResults_iff_article]
  exact (publicationThenMatch_iff_article before (publish before written atom)
    written atom queried pattern template result).symm

/-- The composed operation earns its revision advance and its new occurrence
from the actual source emitter's laws. -/
theorem publicationThenMatch_effects (before : WorldCode)
    (after : RevisionedSpaces String) (written : String) (atom : Pattern)
    (queried : String) (pattern template result : Pattern)
    (running : Nonempty (publicationThenMatch written atom queried pattern template
      (interpret before) after result)) :
    after.revision = before.1 + 1 ∧
      Multiset.count atom (after.contents written) =
        Multiset.count atom ((interpret before).contents written) + 1 := by
  rw [publicationThenMatch_represented_output before after written atom queried pattern template result running,
    interpret_publish]
  exact ⟨rfl, addAtomWorld_count_same (interpret before) written atom⟩


/-! ## Checked patterned continuation and original source `Let` -/

/-- The fixed activation for this fragment is the original query-derived
one-step Zero semantics, read in the selected current named space. -/
def zeroActivation (space : String) (subject : Pattern) :
    Computation (RevisionedSpaces String) Pattern :=
  fun before after result => PLift (after = before) ×
    PLift (result ∈ evaluateOne structuralModel (before.contents space) subject)

/-- This composition uses the existing patterned source `Let`, including its
original checked-ground continuation gate. -/
def queryThenLet (queried : String) (queryPattern queryTemplate : Pattern)
    (bindingPattern body : Pattern) (evaluationSpace : String) :
    Computation (RevisionedSpaces String) Pattern :=
  Let structuralModel (zeroActivation evaluationSpace) bindingPattern
    (Match structuralModel queried queryPattern queryTemplate) body

/-- Native execution of the same composition. It computes the initial query,
all pattern-binding occurrences, the checked instantiated continuation and
its actual one-step results. -/
def letResults (before : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) : Multiset Pattern :=
  (matchResults before queried queryPattern queryTemplate : Multiset Pattern).bind
    fun value => (matchPattern bindingPattern value : Multiset Bindings).bind
      fun bindings =>
        match applyBindingsGround? bindings body with
        | none => 0
        | some instantiated =>
            evaluateOne structuralModel ((interpret before).contents evaluationSpace) instantiated

private theorem mem_letResults (before : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) :
    result ∈ letResults before queried queryPattern queryTemplate bindingPattern body evaluationSpace ↔
      ∃ value ∈ matchResults before queried queryPattern queryTemplate,
        ∃ bindings ∈ matchPattern bindingPattern value,
          ∃ instantiated, applyBindingsGround? bindings body = some instantiated ∧
            result ∈ evaluateOne structuralModel
              ((interpret before).contents evaluationSpace) instantiated := by
  simp only [letResults, Multiset.mem_bind, Multiset.mem_coe]
  constructor
  · rintro ⟨value, member, bindings, bindingMember, resultMember⟩
    cases instantiated : applyBindingsGround? bindings body with
    | none => simp [instantiated] at resultMember
    | some value' => exact ⟨value, member, bindings, bindingMember, value', instantiated,
        by simpa only [instantiated] using resultMember⟩
  · rintro ⟨value, member, bindings, bindingMember, instantiated, application, resultMember⟩
    exact ⟨value, member, bindings, bindingMember, by simpa only [application] using resultMember⟩

/-- Native result existence agrees with the original source bind/continuation
judgment at the same world. -/
theorem letResults_source_exact (before : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) :
    result ∈ letResults before queried queryPattern queryTemplate bindingPattern body evaluationSpace ↔
      Nonempty (queryThenLet queried queryPattern queryTemplate bindingPattern body evaluationSpace
        (interpret before) (interpret before) result) := by
  rw [mem_letResults]
  constructor
  · rintro ⟨value, member, bindings, bindingMember, instantiated, application, resultMember⟩
    obtain ⟨queryArticle⟩ := (mem_matchResults_iff_article before queried queryPattern queryTemplate value).mp member
    refine ⟨⟨interpret before, value, queryArticle,
      instantiated, ?_, ⟨rfl⟩, ⟨resultMember⟩⟩⟩
    exact {
      bindings := bindings
      occurrence := 0
      occurrence_exists := by
        have member : bindings ∈ (matchPattern bindingPattern value : Multiset Bindings) := by
          simpa using bindingMember
        exact Multiset.count_pos.mpr member
      instantiates := application }
  · rintro ⟨middle, value, queryArticle, instantiated, binding, activation⟩
    change MatchArticle structuralModel queried queryPattern queryTemplate (interpret before) middle value at queryArticle
    have middleEq := queryArticle.readOnly
    have queryArticle' : MatchArticle structuralModel queried queryPattern queryTemplate
        (interpret before) (interpret before) value := by simpa only [middleEq] using queryArticle
    refine ⟨value, (mem_matchResults_iff_article before queried queryPattern queryTemplate value).mpr
      ⟨queryArticle'⟩, binding.bindings, ?_, instantiated, binding.instantiates, ?_⟩
    · exact Multiset.count_pos.mp (Nat.zero_lt_of_lt binding.occurrence_exists)
    · simpa only [zeroActivation, middleEq] using activation.2.down

/-- Every source result after the query/ground-let fragment remains in the
represented input world. This is earned from both source read-only laws. -/
theorem queryThenLet_represented_output (before : WorldCode)
    (after : RevisionedSpaces String) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern)
    (running : Nonempty (queryThenLet queried queryPattern queryTemplate bindingPattern body evaluationSpace
      (interpret before) after result)) :
    after = interpret before := by
  rcases running with ⟨middle, value, queryArticle, instantiated, binding, activation⟩
  exact activation.1.down.trans queryArticle.readOnly

/-- Raw intrinsic proof of the query and continuation occurrences. No
matching result, instantiation or completed evaluation is trusted. -/
structure LetProof where
  value : Pattern
  queryProof : QueryProof
  bindings : Bindings
  matchOccurrence : Nat
  instantiated : Pattern
  evaluation : MeTTaZeroStagedAdequacy.ObservationProof
  deriving Repr, DecidableEq

def LetProof.Valid (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) (proof : LetProof) : Prop :=
  interpret after = interpret before ∧
  MatchValid before before queried queryPattern queryTemplate proof.value proof.queryProof ∧
  proof.matchOccurrence < Multiset.count proof.bindings
    (structuralModel.matchAtoms bindingPattern proof.value) ∧
  applyBindingsGround? proof.bindings body = some proof.instantiated ∧
  proof.evaluation.Valid structuralModel
    (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result

def checkLet (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) (proof : LetProof) : Bool :=
  sameWorld after before &&
  checkMatch before before queried queryPattern queryTemplate proof.value proof.queryProof &&
  decide (proof.matchOccurrence < Multiset.count proof.bindings
    (matchPattern bindingPattern proof.value : Multiset Bindings)) &&
  decide (applyBindingsGround? proof.bindings body = some proof.instantiated) &&
  MeTTaZeroStagedAdequacy.checkObservationProof structuralModel
    (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result proof.evaluation

@[simp] theorem checkLet_exact (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) (proof : LetProof) :
    checkLet before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result proof = true ↔
      proof.Valid before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result := by
  simp [checkLet, LetProof.Valid, structuralModel, and_assoc]

/-- Exact native proof checking and evidence-existence completeness for the
existing source `Let`, on every pair of represented worlds in this fragment. -/
theorem queryThenLet_iff_checked (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) :
    Nonempty (queryThenLet queried queryPattern queryTemplate bindingPattern body evaluationSpace
      (interpret before) (interpret after) result) ↔
      ∃ proof : LetProof,
        checkLet before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result proof = true := by
  constructor
  · intro running
    have afterEq := queryThenLet_represented_output before (interpret after) queried
      queryPattern queryTemplate bindingPattern body evaluationSpace result running
    have sameRunning : Nonempty (queryThenLet queried queryPattern queryTemplate bindingPattern body evaluationSpace
        (interpret before) (interpret before) result) := by simpa only [afterEq] using running
    have member := (letResults_source_exact before queried queryPattern queryTemplate bindingPattern body evaluationSpace result).mpr sameRunning
    obtain ⟨value, queryMember, bindings, bindingMember, instantiated, application, resultMember⟩ :=
      (mem_letResults before queried queryPattern queryTemplate bindingPattern body evaluationSpace result).mp member
    obtain ⟨queryProof, queryAccepted⟩ :=
      (matchArticle_iff_exists_checked before before queried queryPattern queryTemplate value).mp
        ((mem_matchResults_iff_article before queried queryPattern queryTemplate value).mp queryMember)
    obtain ⟨evaluation, evaluationValid⟩ :=
      (MeTTaZeroStagedAdequacy.observation_mem_iff_exists_valid structuralModel
        (.evaluate ((interpret before).contents evaluationSpace) instantiated) result).mp
        (Eq.mpr (congrArg (fun answers : Multiset Pattern => result ∈ answers)
          (MeTTaZeroStagedAdequacy.run_evaluate structuralModel
            ((interpret before).contents evaluationSpace) instantiated)) resultMember)
    refine ⟨⟨value, queryProof, bindings, 0, instantiated, evaluation⟩,
      (checkLet_exact before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result _).mpr ?_⟩
    refine ⟨afterEq, (checkMatch_exact before before queried queryPattern queryTemplate value queryProof).mp queryAccepted,
      ?_, application, evaluationValid⟩
    have member : bindings ∈ (matchPattern bindingPattern value : Multiset Bindings) := by
      simpa using bindingMember
    exact Multiset.count_pos.mpr member
  · rintro ⟨proof, accepted⟩
    obtain ⟨afterEq, queryValid, matchCopy, application, evaluationValid⟩ :=
      (checkLet_exact before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result proof).mp accepted
    have queryArticle := matchArticleOfValid queryValid
    have resultMember := (MeTTaZeroStagedAdequacy.observation_mem_iff_exists_valid structuralModel
      (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result).mpr
        ⟨proof.evaluation, evaluationValid⟩
    have source : Nonempty (queryThenLet queried queryPattern queryTemplate bindingPattern body evaluationSpace
        (interpret before) (interpret before) result) := by
      refine ⟨⟨interpret before, proof.value, queryArticle, proof.instantiated,
        ?_, ⟨rfl⟩, ?_⟩⟩
      · exact ⟨proof.bindings, proof.matchOccurrence, matchCopy, application⟩
      · exact ⟨Eq.mp (congrArg (fun answers : Multiset Pattern => result ∈ answers)
          (MeTTaZeroStagedAdequacy.run_evaluate structuralModel
            ((interpret before).contents evaluationSpace) proof.instantiated)) resultMember⟩
    simpa only [afterEq] using source


/-! ## Versioned finite-state and article wire boundary -/

open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire

def encodeRows (rows : History) : List WireTerm :=
  encodeAssignmentEntries (rows.map fun row => ⟨row.1, row.2⟩)

def decodeRows (rows : List WireTerm) : Option History :=
  (decodeAssignmentEntries rows).map fun entries =>
    entries.map fun entry => (entry.name, entry.value)

@[simp] theorem decodeRows_encodeRows (rows : History) :
    decodeRows (encodeRows rows) = some rows := by
  simp [decodeRows, encodeRows, List.map_map, Function.comp_def]

def encodeWorld (code : WorldCode) : WireTerm :=
  .list [.symbol "WFiniteRevisionedWorld", .natural 1,
    .natural code.1, .list (encodeRows code.2)]

def decodeWorld : WireTerm → Option WorldCode
  | .list [.symbol "WFiniteRevisionedWorld", .natural 1,
      .natural revision, .list rows] => do
      let decoded ← decodeRows rows
      some (revision, decoded)
  | _ => none

/-- Exact code round trip retains the whole finite history, not just its
functional-world interpretation. -/
@[simp] theorem decodeWorld_encodeWorld (code : WorldCode) :
    decodeWorld (encodeWorld code) = some code := by
  rcases code with ⟨revision, rows⟩
  simp [decodeWorld, encodeWorld]

def encodeQueryProof (proof : QueryProof) : WireTerm :=
  .list [.symbol "WNativeQueryProof", .natural 1,
    encodePattern proof.candidate, .natural proof.atomOccurrence,
    .list (encodeRows proof.bindings), .natural proof.matchOccurrence]

def decodeQueryProof : WireTerm → Option QueryProof
  | .list [.symbol "WNativeQueryProof", .natural 1,
      candidate, .natural atomOccurrence, .list bindings, .natural matchOccurrence] => do
      let candidate' ← decodePattern candidate
      let bindings' ← decodeRows bindings
      some ⟨candidate', atomOccurrence, bindings', matchOccurrence⟩
  | _ => none

@[simp] theorem decodeQueryProof_encodeQueryProof (proof : QueryProof) :
    decodeQueryProof (encodeQueryProof proof) = some proof := by
  cases proof
  simp [decodeQueryProof, encodeQueryProof]

/-- Parsing supplies raw data only. Original native checking still earns
world equality, each occurrence, matching and checked instantiation. -/
def checkMatchWire (beforeWire afterWire proofWire : WireTerm) (space : String)
    (pattern template result : Pattern) : Bool :=
  match decodeWorld beforeWire, decodeWorld afterWire, decodeQueryProof proofWire with
  | some before, some after, some proof =>
      checkMatch before after space pattern template result proof
  | _, _, _ => false

/-- The actual wire boundary refines exactly the independently stated native
source article judgment. Malformed decodings never reach that judgment. -/
theorem checkMatchWire_encoded_exact (before after : WorldCode) (proof : QueryProof)
    (space : String) (pattern template result : Pattern) :
    checkMatchWire (encodeWorld before) (encodeWorld after)
        (encodeQueryProof proof) space pattern template result = true ↔
      MatchValid before after space pattern template result proof := by
  simp [checkMatchWire]


/-! ## Support-aware contextual queries and continuations -/

/-- Replay the selected source and matcher occurrences, followed by the
actual contextual substitution provider. -/
def checkSupportedMatch (before after : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern template result : Pattern) (proof : QueryProof) : Bool :=
  sameWorld after before &&
    decide (proof.atomOccurrence <
      Multiset.count proof.candidate ((interpret before).contents space)) &&
    checkSupportedBinding structuralModel support depth pattern template proof.candidate result
      proof.bindings proof.matchOccurrence

theorem supportedMatch_iff_checked (before after : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat) (pattern template result : Pattern) :
    Nonempty (SupportedMatchArticle structuralModel space pattern template support depth
      (interpret before) (interpret after) result) ↔
      ∃ proof, checkSupportedMatch before after space support depth pattern template result proof = true := by
  simp only [checkSupportedMatch, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨article⟩
    obtain ⟨bindings, occurrence, checked⟩ :=
      (supportedBinding_iff_checked structuralModel support depth pattern template
        article.candidate.candidate result).mp ⟨article.binding⟩
    refine ⟨⟨article.candidate.candidate, article.candidate.atomOccurrence, bindings, occurrence⟩,
      ⟨?_, article.candidate.atomOccurrence_exists⟩, checked⟩
    exact (sameWorld_exact after before).mpr article.readOnly
  · rintro ⟨proof, ⟨same, occurs⟩, checked⟩
    exact ⟨{
      readOnly := (sameWorld_exact after before).mp same
      candidate := ⟨proof.candidate, proof.atomOccurrence, occurs⟩
      binding := supportedBindingOfChecked structuralModel checked }⟩

/-- Actual contextual query execution.  The multiset bind retains both
physical source multiplicity and matcher multiplicity. -/
def supportedMatchResults (before : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern template : Pattern) : Multiset Pattern :=
  ((interpret before).contents space).bind fun candidate =>
    supportedBindingResults structuralModel support depth pattern template candidate

theorem mem_supportedMatchResults (before : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat) (pattern template result : Pattern) :
    result ∈ supportedMatchResults before space support depth pattern template ↔
      Nonempty (SupportedMatchArticle structuralModel space pattern template support depth
        (interpret before) (interpret before) result) := by
  simp only [supportedMatchResults, Multiset.mem_bind, mem_supportedBindingResults]
  constructor
  · rintro ⟨candidate, occurs, ⟨binding⟩⟩
    exact ⟨{
      readOnly := rfl
      candidate := ⟨candidate, 0, Multiset.count_pos.mpr occurs⟩
      binding := binding }⟩
  · rintro ⟨article⟩
    exact ⟨article.candidate.candidate,
      Multiset.count_pos.mp (Nat.zero_lt_of_lt article.candidate.atomOccurrence_exists),
      ⟨article.binding⟩⟩

/-- Query-derived producer with a contextual continuation and the existing
one-step Zero activation.  The query uses the separately qualified checked-
ground projection; the continuation may carry ambient de Bruijn references. -/
def queryThenSupportedLet (queried : String) (queryPattern queryTemplate : Pattern)
    (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) :
    Computation (RevisionedSpaces String) Pattern :=
  SupportedLet structuralModel (zeroActivation evaluationSpace) support depth bindingPattern
    (Match structuralModel queried queryPattern queryTemplate) body

def supportedLetResults (before : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) : Multiset Pattern :=
  (matchResults before queried queryPattern queryTemplate : Multiset Pattern).bind fun value =>
    (supportedBindingResults structuralModel support depth bindingPattern body value).bind
      fun instantiated => evaluateOne structuralModel
        ((interpret before).contents evaluationSpace) instantiated

theorem supportedLetResults_source_exact (before : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern) :
    result ∈ supportedLetResults before queried queryPattern queryTemplate support depth
      bindingPattern body evaluationSpace ↔
      Nonempty (queryThenSupportedLet queried queryPattern queryTemplate support depth
        bindingPattern body evaluationSpace (interpret before) (interpret before) result) := by
  simp only [supportedLetResults, Multiset.mem_bind, Multiset.mem_coe, mem_supportedBindingResults]
  constructor
  · rintro ⟨value, member, instantiated, ⟨binding⟩, produced⟩
    obtain ⟨queryArticle⟩ := (mem_matchResults_iff_article before queried queryPattern queryTemplate value).mp member
    exact ⟨⟨interpret before, value, queryArticle, instantiated, binding, ⟨rfl⟩, ⟨produced⟩⟩⟩
  · rintro ⟨middle, value, queryArticle, instantiated, binding, activation⟩
    change MatchArticle structuralModel queried queryPattern queryTemplate (interpret before) middle value at queryArticle
    have middleEq := queryArticle.readOnly
    have queryArticle' : MatchArticle structuralModel queried queryPattern queryTemplate
        (interpret before) (interpret before) value := by simpa only [middleEq] using queryArticle
    refine ⟨value, (mem_matchResults_iff_article before queried queryPattern queryTemplate value).mpr
      ⟨queryArticle'⟩, instantiated, ⟨binding⟩, ?_⟩
    simpa only [zeroActivation, middleEq] using activation.2.down

theorem queryThenSupportedLet_represented_output (before : WorldCode)
    (after : RevisionedSpaces String) (queried : String) (queryPattern queryTemplate : Pattern)
    (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern)
    (running : Nonempty (queryThenSupportedLet queried queryPattern queryTemplate support depth
      bindingPattern body evaluationSpace (interpret before) after result)) :
    after = interpret before := by
  rcases running with ⟨middle, value, queryArticle, instantiated, binding, activation⟩
  exact activation.1.down.trans queryArticle.readOnly

/-- The same raw let receipt is reused.  Only the independently authored
continuation discipline changes. -/
def checkSupportedLet (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern)
    (proof : LetProof) : Bool :=
  sameWorld after before &&
    checkMatch before before queried queryPattern queryTemplate proof.value proof.queryProof &&
    checkSupportedBinding structuralModel support depth bindingPattern body proof.value
      proof.instantiated proof.bindings proof.matchOccurrence &&
    MeTTaZeroStagedAdequacy.checkObservationProof structuralModel
      (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated)
      result proof.evaluation

theorem queryThenSupportedLet_iff_checked (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern) :
    Nonempty (queryThenSupportedLet queried queryPattern queryTemplate support depth
      bindingPattern body evaluationSpace (interpret before) (interpret after) result) ↔
      ∃ proof, checkSupportedLet before after queried queryPattern queryTemplate support depth
        bindingPattern body evaluationSpace result proof = true := by
  simp only [checkSupportedLet, Bool.and_eq_true]
  constructor
  · rintro ⟨middle, value, queryArticle, instantiated, binding, activation⟩
    change MatchArticle structuralModel queried queryPattern queryTemplate (interpret before) middle value at queryArticle
    have middleEq := queryArticle.readOnly
    have afterEq : interpret after = interpret before := activation.1.down.trans middleEq
    have queryArticle' : MatchArticle structuralModel queried queryPattern queryTemplate
        (interpret before) (interpret before) value := by simpa only [middleEq] using queryArticle
    obtain ⟨queryProof, queryChecked⟩ :=
      (matchArticle_iff_exists_checked before before queried queryPattern queryTemplate value).mp ⟨queryArticle'⟩
    obtain ⟨bindings, occurrence, bindingChecked⟩ :=
      (supportedBinding_iff_checked structuralModel support depth bindingPattern body value instantiated).mp ⟨binding⟩
    have resultMember : result ∈ evaluateOne structuralModel
        ((interpret before).contents evaluationSpace) instantiated := by
      simpa only [zeroActivation, middleEq] using activation.2.down
    obtain ⟨evaluationProof, evaluationChecked⟩ :=
      (MeTTaZeroStagedAdequacy.observation_mem_iff_exists_accepted structuralModel
        (.evaluate ((interpret before).contents evaluationSpace) instantiated) result).mp
          (Eq.mpr (congrArg (fun answers : Multiset Pattern => result ∈ answers)
            (MeTTaZeroStagedAdequacy.run_evaluate structuralModel
              ((interpret before).contents evaluationSpace) instantiated)) resultMember)
    exact ⟨⟨value, queryProof, bindings, occurrence, instantiated, evaluationProof⟩,
      ⟨⟨(sameWorld_exact after before).mpr afterEq, queryChecked⟩, bindingChecked⟩,
      evaluationChecked⟩
  · rintro ⟨proof, ⟨⟨same, queryChecked⟩, bindingChecked⟩, evaluationChecked⟩
    obtain ⟨queryArticle⟩ := (matchArticle_iff_exists_checked before before queried
      queryPattern queryTemplate proof.value).mpr ⟨proof.queryProof, queryChecked⟩
    have binding := supportedBindingOfChecked structuralModel bindingChecked
    have resultMember :=
      (MeTTaZeroStagedAdequacy.observation_mem_iff_exists_accepted structuralModel
        (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result).mpr
          ⟨proof.evaluation, evaluationChecked⟩
    exact ⟨⟨interpret before, proof.value, queryArticle, proof.instantiated, binding,
      ⟨(sameWorld_exact after before).mp same⟩,
      ⟨Eq.mp (congrArg (fun answers : Multiset Pattern => result ∈ answers)
        (MeTTaZeroStagedAdequacy.run_evaluate structuralModel
          ((interpret before).contents evaluationSpace) proof.instantiated)) resultMember⟩⟩⟩


/-- Source-field validity for one raw contextual query proof. -/
def SupportedMatchValid (before after : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern template result : Pattern) (proof : QueryProof) : Prop :=
  interpret after = interpret before ∧
    proof.atomOccurrence < Multiset.count proof.candidate ((interpret before).contents space) ∧
    proof.matchOccurrence < Multiset.count proof.bindings
      (structuralModel.matchAtoms pattern proof.candidate) ∧
    BindingAdmitted support depth pattern template proof.bindings ∧
    ContextSupport.substituteAt support (bindingAssignment proof.bindings) depth template = result

@[simp] theorem checkSupportedMatch_exact (before after : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern template result : Pattern) (proof : QueryProof) :
    checkSupportedMatch before after space support depth pattern template result proof = true ↔
      SupportedMatchValid before after space support depth pattern template result proof := by
  simp [checkSupportedMatch, SupportedMatchValid, checkSupportedBinding_exact, and_assoc]

/-- Source-field validity for the raw contextual continuation receipt. -/
def LetProof.SupportedValid (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern)
    (proof : LetProof) : Prop :=
  interpret after = interpret before ∧
    MatchValid before before queried queryPattern queryTemplate proof.value proof.queryProof ∧
    proof.matchOccurrence < Multiset.count proof.bindings
      (structuralModel.matchAtoms bindingPattern proof.value) ∧
    BindingAdmitted support depth bindingPattern body proof.bindings ∧
    ContextSupport.substituteAt support (bindingAssignment proof.bindings) depth body = proof.instantiated ∧
    proof.evaluation.Valid structuralModel
      (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result

@[simp] theorem checkSupportedLet_exact (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern)
    (proof : LetProof) :
    checkSupportedLet before after queried queryPattern queryTemplate support depth
      bindingPattern body evaluationSpace result proof = true ↔
      proof.SupportedValid before after queried queryPattern queryTemplate support depth
        bindingPattern body evaluationSpace result := by
  simp [checkSupportedLet, LetProof.SupportedValid, checkSupportedBinding_exact, and_assoc]

/-! ## Guided structural matching in the same source operations -/

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroNativeKernel
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
open Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchEvidence

/-- Ground-query evidence with source-space identity and an explicit matcher
path. The source's checked-ground continuation gate is unchanged. -/
def GuidedMatchValid (before after : WorldCode) (space : String)
    (pattern template result : Pattern) (proof : GuidedQuery.Proof) : Prop :=
  interpret after = interpret before ∧
    proof.atomOccurrence < Multiset.count proof.candidate ((interpret before).contents space) ∧
    GuidedMatchRel pattern proof.candidate proof.bindings proof.choices [] ∧
    applyBindingsGround? proof.bindings template = some result

def checkGuidedMatchArticle (before after : WorldCode) (space : String)
    (pattern template result : Pattern) (proof : GuidedQuery.Proof) : Bool :=
  sameWorld after before &&
    decide (proof.atomOccurrence < Multiset.count proof.candidate (rowsAt before space : Multiset Pattern)) &&
    checkGuidedMatch pattern proof.candidate proof.bindings proof.choices &&
    decide (applyBindingsGround? proof.bindings template = some result)

@[simp] theorem checkGuidedMatchArticle_exact (before after : WorldCode) (space : String)
    (pattern template result : Pattern) (proof : GuidedQuery.Proof) :
    checkGuidedMatchArticle before after space pattern template result proof = true ↔
      GuidedMatchValid before after space pattern template result proof := by
  simp [checkGuidedMatchArticle, GuidedMatchValid, interpret, checkGuidedMatch_exact, and_assoc]

/-- Guided evidence constructs the original independently specified source
article. The source matcher-occurrence coordinate is recovered by the proved
finite bijection rather than supplied as an authority premise. -/
def guidedMatchArticleOfValid {before after : WorldCode} {space : String}
    {pattern template result : Pattern} {proof : GuidedQuery.Proof}
    (valid : GuidedMatchValid before after space pattern template result proof) :
    MatchArticle structuralModel space pattern template (interpret before) (interpret after) result := by
  let matching : StructuralMatching.Claim := ⟨pattern, proof.candidate, proof.bindings⟩
  let ordinal := (StructuralMatching.occurrenceEquiv matching).symm
    ⟨proof.choices, (checkGuidedMatch_exact _ _ _ _).mpr valid.2.2.1⟩
  refine { readOnly := valid.1, event := {
    candidate := proof.candidate
    atomOccurrence := proof.atomOccurrence
    atomOccurrence_exists := valid.2.1
    bindings := proof.bindings
    matchOccurrence := ordinal.1
    matchOccurrence_exists := ?_
    instantiates := valid.2.2.2 } }
  simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP,
    Bool.beq_eq_decide_eq] using ordinal.2

theorem matchArticle_iff_exists_guided (before after : WorldCode) (space : String)
    (pattern template result : Pattern) :
    Nonempty (MatchArticle structuralModel space pattern template
      (interpret before) (interpret after) result) ↔
      ∃ proof : GuidedQuery.Proof,
        checkGuidedMatchArticle before after space pattern template result proof = true := by
  constructor
  · rintro ⟨article⟩
    let matching : StructuralMatching.Claim :=
      ⟨pattern, article.event.candidate, article.event.bindings⟩
    have bound : article.event.matchOccurrence <
        (matchPattern pattern article.event.candidate).count article.event.bindings := by
      simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP,
        Bool.beq_eq_decide_eq] using article.event.matchOccurrence_exists
    let selected := StructuralMatching.occurrenceEquiv matching ⟨article.event.matchOccurrence, bound⟩
    refine ⟨⟨article.event.candidate, article.event.atomOccurrence, article.event.bindings, selected.1⟩,
      (checkGuidedMatchArticle_exact _ _ _ _ _ _ _).mpr ?_⟩
    exact ⟨article.readOnly, article.event.atomOccurrence_exists,
      (checkGuidedMatch_exact _ _ _ _).mp selected.2, article.event.instantiates⟩
  · rintro ⟨proof, accepted⟩
    exact ⟨guidedMatchArticleOfValid ((checkGuidedMatchArticle_exact _ _ _ _ _ _ _).mp accepted)⟩

/-- Contextual queries follow an explicit matcher path, then execute the
existing independently refined support-aware continuation provider. -/
def GuidedSupportedMatchValid (before after : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern template result : Pattern) (proof : GuidedQuery.Proof) : Prop :=
  interpret after = interpret before ∧
    proof.atomOccurrence < Multiset.count proof.candidate ((interpret before).contents space) ∧
    GuidedMatchRel pattern proof.candidate proof.bindings proof.choices [] ∧
    BindingAdmitted support depth pattern template proof.bindings ∧
    ContextSupport.substituteAt support (bindingAssignment proof.bindings) depth template = result

def checkGuidedSupportedMatch (before after : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern template result : Pattern) (proof : GuidedQuery.Proof) : Bool :=
  sameWorld after before &&
    decide (proof.atomOccurrence < Multiset.count proof.candidate ((interpret before).contents space)) &&
    checkGuidedMatch pattern proof.candidate proof.bindings proof.choices &&
    decide (instantiateBinding? support depth pattern template proof.bindings = some result)

@[simp] theorem checkGuidedSupportedMatch_exact (before after : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern template result : Pattern) (proof : GuidedQuery.Proof) :
    checkGuidedSupportedMatch before after space support depth pattern template result proof = true ↔
      GuidedSupportedMatchValid before after space support depth pattern template result proof := by
  simp [checkGuidedSupportedMatch, GuidedSupportedMatchValid, instantiateBinding?_exact,
    checkGuidedMatch_exact, and_assoc]

def guidedSupportedMatchArticleOfValid {before after : WorldCode} {space : String}
    {support : ContextSupport.Support} {depth : Nat} {pattern template result : Pattern}
    {proof : GuidedQuery.Proof}
    (valid : GuidedSupportedMatchValid before after space support depth pattern template result proof) :
    SupportedMatchArticle structuralModel space pattern template support depth
      (interpret before) (interpret after) result := by
  let matching : StructuralMatching.Claim := ⟨pattern, proof.candidate, proof.bindings⟩
  let ordinal := (StructuralMatching.occurrenceEquiv matching).symm
    ⟨proof.choices, (checkGuidedMatch_exact _ _ _ _).mpr valid.2.2.1⟩
  refine {
    readOnly := valid.1
    candidate := ⟨proof.candidate, proof.atomOccurrence, valid.2.1⟩
    binding := {
      bindings := proof.bindings
      occurrence := ordinal.1
      occurrence_exists := ?_
      unique := valid.2.2.2.1.1
      capturesAligned := valid.2.2.2.1.2.1
      captured := valid.2.2.2.1.2.2.1
      available := valid.2.2.2.1.2.2.2
      instantiates := valid.2.2.2.2 } }
  simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP,
    Bool.beq_eq_decide_eq] using ordinal.2

theorem supportedMatch_iff_exists_guided (before after : WorldCode) (space : String)
    (support : ContextSupport.Support) (depth : Nat) (pattern template result : Pattern) :
    Nonempty (SupportedMatchArticle structuralModel space pattern template support depth
      (interpret before) (interpret after) result) ↔
      ∃ proof : GuidedQuery.Proof,
        checkGuidedSupportedMatch before after space support depth pattern template result proof = true := by
  constructor
  · rintro ⟨article⟩
    let matching : StructuralMatching.Claim :=
      ⟨pattern, article.candidate.candidate, article.binding.bindings⟩
    have bound : article.binding.occurrence <
        (matchPattern pattern article.candidate.candidate).count article.binding.bindings := by
      simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP,
        Bool.beq_eq_decide_eq] using article.binding.occurrence_exists
    let selected := StructuralMatching.occurrenceEquiv matching ⟨article.binding.occurrence, bound⟩
    refine ⟨⟨article.candidate.candidate, article.candidate.atomOccurrence,
      article.binding.bindings, selected.1⟩,
      (checkGuidedSupportedMatch_exact _ _ _ _ _ _ _ _ _).mpr ?_⟩
    exact ⟨article.readOnly, article.candidate.atomOccurrence_exists,
      (checkGuidedMatch_exact _ _ _ _).mp selected.2,
      ⟨article.binding.unique, article.binding.capturesAligned, article.binding.captured, article.binding.available⟩,
      article.binding.instantiates⟩
  · rintro ⟨proof, accepted⟩
    exact ⟨guidedSupportedMatchArticleOfValid
      ((checkGuidedSupportedMatch_exact _ _ _ _ _ _ _ _ _).mp accepted)⟩


/-! ### The existing query article format with explicit guidance (version 2) -/

def decodeGuidance : List WireTerm → Option (List Nat) :=
  List.mapM fun item => match item with
    | .natural index => some index
    | _ => none

@[simp] theorem decodeGuidance_map (choices : List Nat) :
    decodeGuidance (choices.map WireTerm.natural) = some choices := by
  simp only [decodeGuidance, List.mapM_map, Function.comp_def]
  simpa using (List.mapM_pure (m := Option) (l := choices) (f := id))

def encodeGuidedQueryProof (proof : GuidedQuery.Proof) : WireTerm :=
  .list [.symbol "WNativeQueryProof", .natural 2,
    encodePattern proof.candidate, .natural proof.atomOccurrence,
    .list (encodeRows proof.bindings), .list (proof.choices.map WireTerm.natural)]

def decodeGuidedQueryProof : WireTerm → Option GuidedQuery.Proof
  | .list [.symbol "WNativeQueryProof", .natural 2,
      candidate, .natural atomOccurrence, .list bindings, .list choices] => do
      let candidate' ← decodePattern candidate
      let bindings' ← decodeRows bindings
      let choices' ← decodeGuidance choices
      some ⟨candidate', atomOccurrence, bindings', choices'⟩
  | _ => none

@[simp] theorem decodeGuidedQueryProof_encodeGuidedQueryProof (proof : GuidedQuery.Proof) :
    decodeGuidedQueryProof (encodeGuidedQueryProof proof) = some proof := by
  cases proof
  simp [encodeGuidedQueryProof, decodeGuidedQueryProof]

def checkGuidedMatchWire (beforeWire afterWire proofWire : WireTerm) (space : String)
    (pattern template result : Pattern) : Bool :=
  match decodeWorld beforeWire, decodeWorld afterWire, decodeGuidedQueryProof proofWire with
  | some before, some after, some proof =>
      checkGuidedMatchArticle before after space pattern template result proof
  | _, _, _ => false

theorem checkGuidedMatchWire_encoded_exact (before after : WorldCode) (proof : GuidedQuery.Proof)
    (space : String) (pattern template result : Pattern) :
    checkGuidedMatchWire (encodeWorld before) (encodeWorld after)
        (encodeGuidedQueryProof proof) space pattern template result = true ↔
      GuidedMatchValid before after space pattern template result proof := by
  simp [checkGuidedMatchWire]


/-! ## Guided continuations with original evaluation evidence -/

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy
open Mettapedia.Languages.MeTTa.MeTTaZeroNativeKernel
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
open Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchEvidence

/-- Query and continuation matching carry separate explicit paths.
Evaluation retains the existing independently checked Zero article. -/
structure GuidedLetProof where
  value : Pattern
  queryProof : GuidedQuery.Proof
  bindings : Bindings
  bindingChoices : List Nat
  instantiated : Pattern
  evaluation : ObservationProof
  deriving Repr, DecidableEq

def GuidedLetProof.Valid (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) (proof : GuidedLetProof) : Prop :=
  interpret after = interpret before ∧
    GuidedMatchValid before before queried queryPattern queryTemplate proof.value proof.queryProof ∧
    GuidedMatchRel bindingPattern proof.value proof.bindings proof.bindingChoices [] ∧
    applyBindingsGround? proof.bindings body = some proof.instantiated ∧
    proof.evaluation.Valid structuralModel
      (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result

def checkGuidedLet (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) (proof : GuidedLetProof) : Bool :=
  sameWorld after before &&
    checkGuidedMatchArticle before before queried queryPattern queryTemplate proof.value proof.queryProof &&
    checkGuidedMatch bindingPattern proof.value proof.bindings proof.bindingChoices &&
    decide (applyBindingsGround? proof.bindings body = some proof.instantiated) &&
    checkObservationProof structuralModel
      (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result proof.evaluation

@[simp] theorem checkGuidedLet_exact (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) (proof : GuidedLetProof) :
    checkGuidedLet before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result proof = true ↔
      proof.Valid before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result := by
  simp [checkGuidedLet, GuidedLetProof.Valid, checkGuidedMatch_exact, and_assoc]

theorem queryThenLet_iff_exists_guided (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate bindingPattern body : Pattern)
    (evaluationSpace : String) (result : Pattern) :
    Nonempty (queryThenLet queried queryPattern queryTemplate bindingPattern body evaluationSpace
      (interpret before) (interpret after) result) ↔
      ∃ proof, checkGuidedLet before after queried queryPattern queryTemplate bindingPattern body
        evaluationSpace result proof = true := by
  rw [queryThenLet_iff_checked]
  constructor
  · rintro ⟨proof, accepted⟩
    obtain ⟨sameWorld, queryValid, matching, instantiated, evaluation⟩ :=
      (checkLet_exact _ _ _ _ _ _ _ _ _ _).mp accepted
    obtain ⟨queryProof, queryChecked⟩ := (matchArticle_iff_exists_guided _ _ _ _ _ _).mp
      ⟨matchArticleOfValid queryValid⟩
    let claim : StructuralMatching.Claim := ⟨bindingPattern, proof.value, proof.bindings⟩
    have bound : proof.matchOccurrence < (matchPattern bindingPattern proof.value).count proof.bindings := by
      simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP,
        Bool.beq_eq_decide_eq] using matching
    let selected := StructuralMatching.occurrenceEquiv claim ⟨proof.matchOccurrence, bound⟩
    refine ⟨⟨proof.value, queryProof, proof.bindings, selected.1, proof.instantiated, proof.evaluation⟩,
      (checkGuidedLet_exact _ _ _ _ _ _ _ _ _ _).mpr ?_⟩
    exact ⟨sameWorld, (checkGuidedMatchArticle_exact _ _ _ _ _ _ _).mp queryChecked,
      (checkGuidedMatch_exact _ _ _ _).mp selected.2, instantiated, evaluation⟩
  · rintro ⟨proof, accepted⟩
    obtain ⟨sameWorld, queryValid, matching, instantiated, evaluation⟩ :=
      (checkGuidedLet_exact _ _ _ _ _ _ _ _ _ _).mp accepted
    let article := guidedMatchArticleOfValid queryValid
    let queryProof : QueryProof := ⟨article.event.candidate, article.event.atomOccurrence,
      article.event.bindings, article.event.matchOccurrence⟩
    let claim : StructuralMatching.Claim := ⟨bindingPattern, proof.value, proof.bindings⟩
    let ordinal := (StructuralMatching.occurrenceEquiv claim).symm
      ⟨proof.bindingChoices, (checkGuidedMatch_exact _ _ _ _).mpr matching⟩
    refine ⟨⟨proof.value, queryProof, proof.bindings, ordinal.1, proof.instantiated, proof.evaluation⟩,
      (checkLet_exact _ _ _ _ _ _ _ _ _ _).mpr ?_⟩
    refine ⟨sameWorld, ?_, ?_, instantiated, evaluation⟩
    · exact ⟨article.readOnly, article.event.atomOccurrence_exists,
        article.event.matchOccurrence_exists, article.event.instantiates⟩
    · simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP,
        Bool.beq_eq_decide_eq] using ordinal.2

def GuidedLetProof.SupportedValid (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern)
    (proof : GuidedLetProof) : Prop :=
  interpret after = interpret before ∧
    GuidedMatchValid before before queried queryPattern queryTemplate proof.value proof.queryProof ∧
    GuidedMatchRel bindingPattern proof.value proof.bindings proof.bindingChoices [] ∧
    BindingAdmitted support depth bindingPattern body proof.bindings ∧
    ContextSupport.substituteAt support (bindingAssignment proof.bindings) depth body = proof.instantiated ∧
    proof.evaluation.Valid structuralModel
      (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result

def checkGuidedSupportedLet (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern)
    (proof : GuidedLetProof) : Bool :=
  sameWorld after before &&
    checkGuidedMatchArticle before before queried queryPattern queryTemplate proof.value proof.queryProof &&
    checkGuidedMatch bindingPattern proof.value proof.bindings proof.bindingChoices &&
    decide (instantiateBinding? support depth bindingPattern body proof.bindings = some proof.instantiated) &&
    checkObservationProof structuralModel
      (.evaluate ((interpret before).contents evaluationSpace) proof.instantiated) result proof.evaluation

@[simp] theorem checkGuidedSupportedLet_exact (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern)
    (proof : GuidedLetProof) :
    checkGuidedSupportedLet before after queried queryPattern queryTemplate support depth bindingPattern body
        evaluationSpace result proof = true ↔
      proof.SupportedValid before after queried queryPattern queryTemplate support depth bindingPattern body
        evaluationSpace result := by
  simp [checkGuidedSupportedLet, GuidedLetProof.SupportedValid, checkGuidedMatch_exact,
    instantiateBinding?_exact, and_assoc]

theorem queryThenSupportedLet_iff_exists_guided (before after : WorldCode) (queried : String)
    (queryPattern queryTemplate : Pattern) (support : ContextSupport.Support) (depth : Nat)
    (bindingPattern body : Pattern) (evaluationSpace : String) (result : Pattern) :
    Nonempty (queryThenSupportedLet queried queryPattern queryTemplate support depth bindingPattern body evaluationSpace
      (interpret before) (interpret after) result) ↔
      ∃ proof, checkGuidedSupportedLet before after queried queryPattern queryTemplate support depth
        bindingPattern body evaluationSpace result proof = true := by
  rw [queryThenSupportedLet_iff_checked]
  constructor
  · rintro ⟨proof, accepted⟩
    obtain ⟨sameWorld, queryValid, matching, admitted, instantiated, evaluation⟩ :=
      (checkSupportedLet_exact _ _ _ _ _ _ _ _ _ _ _ _).mp accepted
    obtain ⟨queryProof, queryChecked⟩ := (matchArticle_iff_exists_guided _ _ _ _ _ _).mp
      ⟨matchArticleOfValid queryValid⟩
    let claim : StructuralMatching.Claim := ⟨bindingPattern, proof.value, proof.bindings⟩
    have bound : proof.matchOccurrence < (matchPattern bindingPattern proof.value).count proof.bindings := by
      simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP,
        Bool.beq_eq_decide_eq] using matching
    let selected := StructuralMatching.occurrenceEquiv claim ⟨proof.matchOccurrence, bound⟩
    refine ⟨⟨proof.value, queryProof, proof.bindings, selected.1, proof.instantiated, proof.evaluation⟩,
      (checkGuidedSupportedLet_exact _ _ _ _ _ _ _ _ _ _ _ _).mpr ?_⟩
    exact ⟨sameWorld, (checkGuidedMatchArticle_exact _ _ _ _ _ _ _).mp queryChecked,
      (checkGuidedMatch_exact _ _ _ _).mp selected.2, admitted, instantiated, evaluation⟩
  · rintro ⟨proof, accepted⟩
    obtain ⟨sameWorld, queryValid, matching, admitted, instantiated, evaluation⟩ :=
      (checkGuidedSupportedLet_exact _ _ _ _ _ _ _ _ _ _ _ _).mp accepted
    let article := guidedMatchArticleOfValid queryValid
    let queryProof : QueryProof := ⟨article.event.candidate, article.event.atomOccurrence,
      article.event.bindings, article.event.matchOccurrence⟩
    let claim : StructuralMatching.Claim := ⟨bindingPattern, proof.value, proof.bindings⟩
    let ordinal := (StructuralMatching.occurrenceEquiv claim).symm
      ⟨proof.bindingChoices, (checkGuidedMatch_exact _ _ _ _).mpr matching⟩
    refine ⟨⟨proof.value, queryProof, proof.bindings, ordinal.1, proof.instantiated, proof.evaluation⟩,
      (checkSupportedLet_exact _ _ _ _ _ _ _ _ _ _ _ _).mpr ?_⟩
    refine ⟨sameWorld, ?_, ?_, admitted, instantiated, evaluation⟩
    · exact ⟨article.readOnly, article.event.atomOccurrence_exists,
        article.event.matchOccurrence_exists, article.event.instantiates⟩
    · simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP,
        Bool.beq_eq_decide_eq] using ordinal.2

/-! ## Native service for the combined finite profile -/

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.SemanticService

/-- Claims retain complete finite before/after worlds and all source inputs.
The constructors request distinct source operations and binding disciplines. -/
inductive Claim where
  | matchSpace (before after : WorldCode) (space : String)
      (pattern template result : Pattern)
  | emit (before after : WorldCode) (space : String) (atom : Pattern)
  | letQuery (before after : WorldCode) (queried : String)
      (queryPattern queryTemplate bindingPattern body : Pattern)
      (evaluationSpace : String) (result : Pattern)
  | supportedMatchSpace (before after : WorldCode) (space : String)
      (support : List SupportEntry) (depth : Nat) (pattern template result : Pattern)
  | supportedLetQuery (before after : WorldCode) (queried : String)
      (support : List SupportEntry) (depth : Nat)
      (queryPattern queryTemplate bindingPattern body : Pattern)
      (evaluationSpace : String) (result : Pattern)
  | livePath (before after : PeTTa.ProgramReplay.Snapshot)
  | liveBag (before : PeTTa.ProgramReplay.Snapshot) (answers : List OSLFCore.Atom)

/-- Meaning is the previously defined source computation/receipt, not a
checker tag or an externally supplied soundness premise. -/
def Claim.Meaning : Claim → Prop
  | .livePath before after => PeTTa.ProgramReplay.LiveRegistry.theory.MultiStep before.decode after.decode
  | .liveBag before answers => PeTTa.ProgramReplay.LiveRegistry.Completed before.decode answers
  | .matchSpace before after space pattern template result =>
      Nonempty (MatchArticle structuralModel space pattern template
        (interpret before) (interpret after) result)
  | .emit before after space atom =>
      Nonempty (PersistentEmitReceipt (interpret before) (interpret after) space atom)
  | .letQuery before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result =>
      Nonempty (queryThenLet queried queryPattern queryTemplate bindingPattern body evaluationSpace
        (interpret before) (interpret after) result)
  | .supportedMatchSpace before after space support depth pattern template result =>
      Nonempty (SupportedMatchArticle structuralModel space pattern template (supportContext support) depth
        (interpret before) (interpret after) result)
  | .supportedLetQuery before after queried support depth queryPattern queryTemplate bindingPattern body
      evaluationSpace result =>
      Nonempty (queryThenSupportedLet queried queryPattern queryTemplate (supportContext support) depth
        bindingPattern body evaluationSpace (interpret before) (interpret after) result)

inductive Proof where
  | matchSpace (article : QueryProof)
  | guidedMatchSpace (article : GuidedQuery.Proof)
  | guidedSupportedMatchSpace (article : GuidedQuery.Proof)
  | emit
  | letQuery (article : LetProof)
  | guidedLetQuery (article : GuidedLetProof)
  | guidedSupportedLetQuery (article : GuidedLetProof)
  | supportedMatchSpace (article : QueryProof)
  | supportedLetQuery (article : LetProof)
  | liveExecution (trace : List PeTTa.ProgramReplay.Snapshot)
  deriving Repr, DecidableEq

/-- The intrinsic raw-proof judgment records the independent source field
conditions. Cross-operation proof objects are rejected. -/
def Proof.Valid : Claim → Proof → Prop
  | .livePath before after, .liveExecution trace =>
      List.IsChain PeTTa.ProgramReplay.LiveRegistry.Transition
        (before.decode :: trace.map PeTTa.ProgramReplay.Snapshot.decode) ∧
      (PeTTa.ProgramReplay.traceEnd before trace).decode = after.decode
  | .liveBag before claimed, .liveExecution trace =>
      List.IsChain PeTTa.ProgramReplay.LiveRegistry.Transition
        (before.decode :: trace.map PeTTa.ProgramReplay.Snapshot.decode) ∧
      ∃ answers, (PeTTa.ProgramReplay.traceEnd before trace).decode.control = .returned answers ∧
        (PeTTa.ProgramReplay.traceEnd before trace).decode.frames = [] ∧
        (answers : Multiset OSLFCore.Atom) = (claimed : Multiset OSLFCore.Atom)
  | .matchSpace before after space pattern template result, .matchSpace article =>
      MatchValid before after space pattern template result article
  | .matchSpace before after space pattern template result, .guidedMatchSpace article =>
      GuidedMatchValid before after space pattern template result article
  | .supportedMatchSpace before after space support depth pattern template result,
      .guidedSupportedMatchSpace article =>
      GuidedSupportedMatchValid before after space (supportContext support) depth pattern template result article
  | .emit before after space atom, .emit =>
      interpret after = addAtomWorld (interpret before) space atom
  | .letQuery before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result,
      .letQuery article =>
      article.Valid before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result
  | .letQuery before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result,
      .guidedLetQuery article =>
      article.Valid before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result
  | .supportedLetQuery before after queried support depth queryPattern queryTemplate bindingPattern body
      evaluationSpace result, .guidedSupportedLetQuery article =>
      article.SupportedValid before after queried queryPattern queryTemplate (supportContext support) depth
        bindingPattern body evaluationSpace result
  | .supportedMatchSpace before after space support depth pattern template result,
      .supportedMatchSpace article =>
      SupportedMatchValid before after space (supportContext support) depth pattern template result article
  | .supportedLetQuery before after queried support depth queryPattern queryTemplate bindingPattern body
      evaluationSpace result, .supportedLetQuery article =>
      article.SupportedValid before after queried queryPattern queryTemplate (supportContext support) depth
        bindingPattern body evaluationSpace result
  | _, _ => False

def check : Claim → Proof → Bool
  | .livePath before after, .liveExecution trace =>
      PeTTa.ProgramReplay.LiveRegistry.checkPath before after trace
  | .liveBag before answers, .liveExecution trace =>
      PeTTa.ProgramReplay.LiveRegistry.checkCompletedBag before trace answers
  | .matchSpace before after space pattern template result, .matchSpace article =>
      checkMatch before after space pattern template result article
  | .matchSpace before after space pattern template result, .guidedMatchSpace article =>
      checkGuidedMatchArticle before after space pattern template result article
  | .supportedMatchSpace before after space support depth pattern template result,
      .guidedSupportedMatchSpace article =>
      checkGuidedSupportedMatch before after space (supportContext support) depth pattern template result article
  | .emit before after space atom, .emit => checkEmit before after space atom
  | .letQuery before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result,
      .letQuery article =>
      checkLet before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result article
  | .letQuery before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result,
      .guidedLetQuery article =>
      checkGuidedLet before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result article
  | .supportedLetQuery before after queried support depth queryPattern queryTemplate bindingPattern body
      evaluationSpace result, .guidedSupportedLetQuery article =>
      checkGuidedSupportedLet before after queried queryPattern queryTemplate (supportContext support) depth
        bindingPattern body evaluationSpace result article
  | .supportedMatchSpace before after space support depth pattern template result,
      .supportedMatchSpace article =>
      checkSupportedMatch before after space (supportContext support) depth pattern template result article
  | .supportedLetQuery before after queried support depth queryPattern queryTemplate bindingPattern body
      evaluationSpace result, .supportedLetQuery article =>
      checkSupportedLet before after queried queryPattern queryTemplate (supportContext support) depth
        bindingPattern body evaluationSpace result article
  | _, _ => false

@[simp] theorem check_exact (claim : Claim) (proof : Proof) :
    check claim proof = true ↔ Proof.Valid claim proof := by
  cases claim <;> cases proof <;>
    simp [check, Proof.Valid, checkEmit, interpret_publish,
      PeTTa.ProgramReplay.LiveRegistry.checkPath_exact,
      PeTTa.ProgramReplay.LiveRegistry.checkCompletedBag_sourceExact]

def proofSystem : NativeProofSystem Claim where
  ProofObject := Proof
  Judges proof claim := Proof.Valid claim proof

def proofKernel : NativeProofKernel proofSystem where
  decide := check
  correct := check_exact

theorem meaning_iff_checked (claim : Claim) :
    claim.Meaning ↔ ∃ proof, check claim proof = true := by
  cases claim with
  | livePath before after =>
      constructor
      · intro path
        obtain ⟨trace, accepted⟩ :=
          (PeTTa.ProgramReplay.LiveRegistry.accepted_path_iff_source_reachable before after).mpr path
        exact ⟨.liveExecution trace, accepted⟩
      · rintro ⟨proof, accepted⟩
        cases proof with
        | liveExecution trace =>
          exact (PeTTa.ProgramReplay.LiveRegistry.accepted_path_iff_source_reachable before after).mp
            ⟨trace, accepted⟩
        | _ => simp [check] at accepted
  | liveBag before answers =>
      constructor
      · intro completed
        obtain ⟨trace, accepted⟩ :=
          (PeTTa.ProgramReplay.LiveRegistry.accepted_bag_iff_source_completed before answers).mpr completed
        exact ⟨.liveExecution trace, accepted⟩
      · rintro ⟨proof, accepted⟩
        cases proof with
        | liveExecution trace =>
          exact (PeTTa.ProgramReplay.LiveRegistry.accepted_bag_iff_source_completed before answers).mp
            ⟨trace, accepted⟩
        | _ => simp [check] at accepted
  | matchSpace before after space pattern template result =>
      rw [Claim.Meaning, matchArticle_iff_exists_checked]
      constructor
      · rintro ⟨article, accepted⟩
        exact ⟨.matchSpace article, accepted⟩
      · rintro ⟨proof, accepted⟩
        cases proof with
        | matchSpace article => exact ⟨article, accepted⟩
        | guidedMatchSpace article =>
            exact (matchArticle_iff_exists_checked _ _ _ _ _ _).mp
              ((matchArticle_iff_exists_guided _ _ _ _ _ _).mpr ⟨article, accepted⟩)
        | _ => simp [check] at accepted
  | emit before after space atom =>
      rw [Claim.Meaning, ← checkEmit_exact]
      constructor
      · intro accepted
        exact ⟨.emit, accepted⟩
      · rintro ⟨proof, accepted⟩
        cases proof with
        | emit => exact accepted
        | _ => simp [check] at accepted
  | letQuery before after queried queryPattern queryTemplate bindingPattern body evaluationSpace result =>
      rw [Claim.Meaning, queryThenLet_iff_checked]
      constructor
      · rintro ⟨article, accepted⟩
        exact ⟨.letQuery article, accepted⟩
      · rintro ⟨proof, accepted⟩
        cases proof with
        | letQuery article => exact ⟨article, accepted⟩
        | guidedLetQuery article =>
            exact (queryThenLet_iff_checked _ _ _ _ _ _ _ _ _).mp
              ((queryThenLet_iff_exists_guided _ _ _ _ _ _ _ _ _).mpr ⟨article, accepted⟩)
        | _ => simp [check] at accepted
  | supportedMatchSpace before after space support depth pattern template result =>
      rw [Claim.Meaning, supportedMatch_iff_checked]
      constructor
      · rintro ⟨article, accepted⟩
        exact ⟨.supportedMatchSpace article, accepted⟩
      · rintro ⟨proof, accepted⟩
        cases proof with
        | supportedMatchSpace article => exact ⟨article, accepted⟩
        | guidedSupportedMatchSpace article =>
            exact (supportedMatch_iff_checked _ _ _ _ _ _ _ _).mp
              ((supportedMatch_iff_exists_guided _ _ _ _ _ _ _ _).mpr ⟨article, accepted⟩)
        | _ => simp [check] at accepted
  | supportedLetQuery before after queried support depth queryPattern queryTemplate bindingPattern body
      evaluationSpace result =>
      rw [Claim.Meaning, queryThenSupportedLet_iff_checked]
      constructor
      · rintro ⟨article, accepted⟩
        exact ⟨.supportedLetQuery article, accepted⟩
      · rintro ⟨proof, accepted⟩
        cases proof with
        | supportedLetQuery article => exact ⟨article, accepted⟩
        | guidedSupportedLetQuery article =>
            exact (queryThenSupportedLet_iff_checked _ _ _ _ _ _ _ _ _ _ _).mp
              ((queryThenSupportedLet_iff_exists_guided _ _ _ _ _ _ _ _ _ _ _).mpr ⟨article, accepted⟩)
        | _ => simp [check] at accepted

def target : AdmissionObject where
  Carrier := Claim
  Meaning := Claim.Meaning

theorem meaning_iff_native_proof (claim : Claim) :
    claim.Meaning ↔ Nonempty (proofSystem.ProofFibre claim) := by
  rw [meaning_iff_checked]
  constructor
  · rintro ⟨proof, accepted⟩
    exact ⟨⟨proof, (check_exact claim proof).mp accepted⟩⟩
  · rintro ⟨⟨proof, valid⟩⟩
    exact ⟨proof, (check_exact claim proof).mpr valid⟩

/-- The finite stateful profile supplies an actual intrinsic native kernel
for persistent publication, two query disciplines and two continuation
disciplines. It is not a whole Prime/HE/PeTTa profile. -/
def nativeProofService : Service target :=
  .nativeProof proofSystem proofKernel meaning_iff_native_proof

/-! ## Contextual operation controls -/

namespace ContextualControls

open MeTTaSupportIndexedABTWire.SupportedBindingControls

def supportEntries : List SupportEntry := [⟨"x", [.base "Value"]⟩]

def world : WorldCode :=
  ⟨17, [("&self", valueX), ("&self", valueX)]⟩

def queryProof : QueryProof :=
  ⟨valueX, 1, [("v", valueX)], 0⟩

def matchProof : QueryProof :=
  ⟨valueX, 1, [("x", .bvar 0)], 0⟩

def letProof : LetProof :=
  ⟨valueX, queryProof, [("x", .bvar 0)], 0, resultX, .inert⟩

def matchClaim : Claim :=
  .supportedMatchSpace world world "&self" supportEntries 0 patternX bodyX resultX

def letClaim : Claim :=
  .supportedLetQuery world world "&self" supportEntries 0
    (.fvar "v") (.fvar "v") patternX bodyX "&eval" resultX

theorem contextual_query_retains_duplicate_occurrences :
    supportedMatchResults world "&self" (supportContext supportEntries) 0 patternX bodyX =
      {resultX, resultX} := by decide +kernel

theorem contextual_let_retains_duplicate_occurrences :
    supportedLetResults world "&self" (.fvar "v") (.fvar "v") (supportContext supportEntries) 0
      patternX bodyX "&eval" = {resultX, resultX} := by decide +kernel

theorem contextual_query_accepted :
    check matchClaim (.supportedMatchSpace matchProof) = true := by decide +kernel

theorem contextual_let_accepted :
    check letClaim (.supportedLetQuery letProof) = true := by decide +kernel

theorem contextual_let_has_source_meaning : letClaim.Meaning :=
  (meaning_iff_checked letClaim).mpr ⟨.supportedLetQuery letProof, contextual_let_accepted⟩

theorem nonexistent_source_occurrence_rejected :
    check matchClaim (.supportedMatchSpace { matchProof with atomOccurrence := 2 }) = false := by
  decide +kernel

theorem nonexistent_matcher_occurrence_rejected :
    check matchClaim (.supportedMatchSpace { matchProof with matchOccurrence := 1 }) = false := by
  decide +kernel

theorem continuation_capture_rejected :
    checkSupportedLet world world "&self" (.fvar "v") (.fvar "v") (supportContext supportEntries) 0
      patternX (.fvar "x") "&eval" (.bvar 0)
      { letProof with instantiated := .bvar 0 } = false := by decide +kernel

theorem forged_capture_support_rejected :
    checkSupportedMatch world world "&self" (fun _ => []) 0 patternX bodyX resultX matchProof = false := by
  decide +kernel

theorem ground_continuation_does_not_admit_open_filling :
    letResults world "&self" (.fvar "v") (.fvar "v") patternX bodyX "&eval" = 0 := by
  decide +kernel

theorem cross_discipline_receipt_rejected :
    check letClaim (.letQuery letProof) = false := by rfl


/-- The same source occurrence and supported filling, with its explicit
structural matching path. -/
def guidedMatchProof : GuidedQuery.Proof :=
  ⟨matchProof.candidate, matchProof.atomOccurrence, matchProof.bindings, []⟩

def guidedLetProof : GuidedLetProof where
  value := letProof.value
  queryProof := ⟨letProof.queryProof.candidate, letProof.queryProof.atomOccurrence,
    letProof.queryProof.bindings, []⟩
  bindings := letProof.bindings
  bindingChoices := []
  instantiated := letProof.instantiated
  evaluation := letProof.evaluation

theorem guided_match_admitted :
    check matchClaim (.guidedSupportedMatchSpace guidedMatchProof) = true := by decide +kernel

theorem guided_match_refuses_unconsumed_choice :
    check matchClaim (.guidedSupportedMatchSpace {guidedMatchProof with choices := [0]}) = false := by
  decide +kernel

theorem guided_let_admitted :
    check letClaim (.guidedSupportedLetQuery guidedLetProof) = true := by decide +kernel

theorem guided_let_refuses_wrong_shift :
    check letClaim (.guidedSupportedLetQuery
      {guidedLetProof with instantiated := .lambda none (.lambda none (.bvar 0))}) = false := by
  decide +kernel

theorem guided_let_refuses_other_discipline :
    check letClaim (.guidedLetQuery guidedLetProof) = false := by decide +kernel

end ContextualControls



open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation (ProgramCommand Program)
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

/-- Native type-schema lookup uses the actual finite declaration rows. -/
def typeResults (before : WorldCode) (current : String) (subject : Pattern) : List Pattern :=
  (rowsAt before current).flatMap fun candidate =>
    match candidate with
    | .apply ":" [term, type] =>
        (matchPattern term subject).map fun bindings => applyBindings bindings type
    | _ => []

@[simp] theorem typeResults_source (before : WorldCode) (current : String) (subject : Pattern) :
    (typeResults before current subject : Multiset Pattern) =
      sourceDeclaredTypes (interpret before) current subject := by
  unfold typeResults sourceDeclaredTypes interpret
  rw [← Multiset.coe_bind]
  apply Multiset.bind_congr
  intro candidate _
  split <;> simp [structuralModel]

/-- Physical equation replay reads the same public reflective rows used by
queries.  Every source and matcher occurrence contributes a list occurrence. -/
def equationAnswerList (before : WorldCode) (current : String) (subject : Pattern) : List Pattern :=
  (rowsAt before current).flatMap fun candidate =>
    match viewEquation? candidate with
    | none => []
    | some (left, right) =>
        (matchPattern left subject).map fun bindings => applyBindings bindings right

theorem equationAnswerList_source (before : WorldCode) (current : String) (subject : Pattern) :
    (equationAnswerList before current subject : Multiset Pattern) =
      equationResults structuralModel ((interpret before).contents current) subject := by
  unfold equationResults
  have contents : queryAll structuralModel ((interpret before).contents current) =
      (interpret before).contents current :=
    queryAll_eq_contents (structuralModel (fun _ => 0)) (structuralModel_lawful _) _
  rw [contents]
  unfold equationAnswerList
  rw [← Multiset.coe_bind]
  apply Multiset.bind_congr
  intro candidate _
  split <;> simp_all [structuralModel]

/-- Closed finite emptiness controls the original inert fallback. -/
def zeroAnswerList (before : WorldCode) (current : String) (subject : Pattern) : List Pattern :=
  let answers := equationAnswerList before current subject
  if answers = [] then [subject] else answers

@[simp] theorem zeroAnswerList_source (before : WorldCode) (current : String) (subject : Pattern) :
    (zeroAnswerList before current subject : Multiset Pattern) =
      evaluateOne structuralModel ((interpret before).contents current) subject := by
  unfold zeroAnswerList evaluateOne interpretedResults
  have ground : structuralModel.groundApply subject = 0 := rfl
  rw [ground, add_zero, ← equationAnswerList_source]
  by_cases empty : equationAnswerList before current subject = []
  · simp [empty]
  · simp [empty]

/-- Native activation has a physical enumeration; its source observation is
the answer bag, and no public result-order law is asserted. -/
def readAnswerList (before : WorldCode) (current : String) : Pattern → List Pattern
  | .apply "quote" [subject] => [subject]
  | .apply "match" [.apply space [], pattern, template] => matchResults before space pattern template
  | .apply "get-atoms" [.apply space []] => rowsAt before space
  | .apply "get-type" [subject] => typeResults before current subject
  | subject => zeroAnswerList before current subject

@[simp] theorem readAnswerList_source (before : WorldCode) (current : String) (subject : Pattern) :
    (readAnswerList before current subject : Multiset Pattern) =
      sourceReadAnswers (interpret before) current subject := by
  unfold readAnswerList sourceReadAnswers
  split <;> simp [matchResults_bag, interpret, typeResults_source]

def readAnswers (before : WorldCode) (current : String) (subject : Pattern) : Multiset Pattern :=
  readAnswerList before current subject

@[simp] theorem readAnswers_source (before : WorldCode) (current : String) (subject : Pattern) :
    readAnswers before current subject = sourceReadAnswers (interpret before) current subject :=
  readAnswerList_source before current subject

def evalAnswerList (before : WorldCode) (current : String) : Pattern → List Pattern
  | .apply "let" [pattern, value, body] =>
      (readAnswerList before current value).flatMap fun result =>
        (matchPattern pattern result).flatMap fun bindings =>
          match applyBindingsGround? bindings body with
          | none => []
          | some instantiated => readAnswerList before current instantiated
  | subject => readAnswerList before current subject

@[simp] theorem evalAnswerList_source (before : WorldCode) (current : String) (subject : Pattern) :
    (evalAnswerList before current subject : Multiset Pattern) =
      sourceEvalAnswers (interpret before) current subject := by
  unfold evalAnswerList sourceEvalAnswers
  split
  · rw [← Multiset.coe_bind, readAnswerList_source]
    apply Multiset.bind_congr
    intro value _
    rw [← Multiset.coe_bind]
    simp only [structuralModel]
    apply Multiset.bind_congr
    intro bindings _
    split <;> simp_all
  · first
    | exact readAnswerList_source _ _ _
    | split
      · simp_all
      · exact readAnswerList_source _ _ _

def evalAnswers (before : WorldCode) (current : String) (subject : Pattern) : Multiset Pattern :=
  evalAnswerList before current subject

@[simp] theorem evalAnswers_source (before : WorldCode) (current : String) (subject : Pattern) :
    evalAnswers before current subject = sourceEvalAnswers (interpret before) current subject :=
  evalAnswerList_source before current subject

/-- Physical command output retains its chosen enumeration.  Its public
source meaning below observes answer bags, not this machine's list order. -/
inductive CommandOutput where
  | answers (values : List Pattern)
  | retained (command : ProgramCommand Pattern)
deriving Repr, DecidableEq

@[simp] def CommandOutput.observation : CommandOutput → CommandObservation
  | .answers values => .answers (values : Multiset Pattern)
  | .retained command => .retained command

/-- Permuting one physical answer enumeration preserves its source meaning. -/
theorem CommandOutput.observation_perm {first second : List Pattern}
    (permutation : first.Perm second) :
    (CommandOutput.answers first).observation = (CommandOutput.answers second).observation :=
  congrArg CommandObservation.answers (Multiset.coe_eq_coe.mpr permutation)

/-- Raw finite output carries actual answer lists; the checker replays finite
operations and compares their bag observations.  Guided matcher articles remain
an independently qualified explicit-evidence service. -/
structure CommandReceipt where
  after : WorldCode
  output : CommandOutput
deriving Repr, DecidableEq

@[simp] def CommandReceipt.observation (receipt : CommandReceipt) : CommandObservation :=
  receipt.output.observation

def runCommand (before : WorldCode) (current : String) :
    ProgramCommand Pattern → CommandReceipt
  | .empty => ⟨before, .answers []⟩
  | .eval (.apply "add-atom" [.apply space [], atom]) =>
      ⟨publish before space atom, .answers [.apply "True" []]⟩
  | .eval subject => ⟨before, .answers (evalAnswerList before current subject)⟩
  | .fact atom => ⟨publish before current atom, .answers []⟩
  | .defineEq left right => ⟨publish before current (.apply "=" [left, right]), .answers []⟩
  | .defineType term type => ⟨publish before current (.apply ":" [term, type]), .answers []⟩
  | .relationFact name arguments =>
      ⟨publish before current (.apply "relation!" (.apply name [] :: arguments)), .answers []⟩
  | .builtinFact name arguments =>
      ⟨publish before current (.apply "builtin!" (.apply name [] :: arguments)), .answers []⟩
  | .addAtom (.apply space []) atom => ⟨publish before space atom, .answers []⟩
  | command => ⟨before, .retained command⟩

/-- Native execution constructs the independently stated source article. -/
def runCommand_article (before : WorldCode) (current : String)
    (command : ProgramCommand Pattern) :
    CommandDerivation current command (interpret before)
      (interpret (runCommand before current command).after)
      (runCommand before current command).observation := by
  unfold runCommand
  split
  · exact .empty _
  · simpa only [interpret_publish, CommandReceipt.observation, CommandOutput.observation, Multiset.coe_nil, Multiset.coe_singleton] using CommandDerivation.evalPublish (current := current) (interpret before) _ _
  · simp only [CommandReceipt.observation, CommandOutput.observation, evalAnswerList_source]
    exact .eval _ _ (by unfold ReadOnlySubject; split <;> simp_all)
  · simpa only [interpret_publish, CommandReceipt.observation, CommandOutput.observation, Multiset.coe_nil, Multiset.coe_singleton] using CommandDerivation.declaration (interpret before) _ _ (.fact _)
  · simpa only [interpret_publish, CommandReceipt.observation, CommandOutput.observation, Multiset.coe_nil, Multiset.coe_singleton] using CommandDerivation.declaration (interpret before) _ _ (.equation _ _)
  · simpa only [interpret_publish, CommandReceipt.observation, CommandOutput.observation, Multiset.coe_nil, Multiset.coe_singleton] using CommandDerivation.declaration (interpret before) _ _ (.type _ _)
  · simpa only [interpret_publish, CommandReceipt.observation, CommandOutput.observation, Multiset.coe_nil, Multiset.coe_singleton] using CommandDerivation.declaration (interpret before) _ _ (.relation _ _)
  · simpa only [interpret_publish, CommandReceipt.observation, CommandOutput.observation, Multiset.coe_nil, Multiset.coe_singleton] using CommandDerivation.declaration (interpret before) _ _ (.builtin _ _)
  · simpa only [interpret_publish, CommandReceipt.observation, CommandOutput.observation, Multiset.coe_nil, Multiset.coe_singleton] using CommandDerivation.publish (current := current) (interpret before) _ _
  · exact .retained _ _ (by
      intro handled
      unfold CommandHandled at handled
      split at handled <;> simp_all)

/-- The fallback preserves the literal parsed command and the entire world. -/
theorem runCommand_retained (before : WorldCode) (current : String)
    (command : ProgramCommand Pattern) (unhandled : ¬ CommandHandled command) :
    runCommand before current command = ⟨before, .retained command⟩ := by
  unfold runCommand
  split <;> simp_all [CommandHandled]

theorem runCommand_eval (before : WorldCode) (current : String) (subject : Pattern)
    (readOnly : ReadOnlySubject subject) :
    runCommand before current (.eval subject) =
      ⟨before, .answers (evalAnswerList before current subject)⟩ := by
  unfold runCommand
  split <;> simp_all [ReadOnlySubject]

/-- Every independent source transition has exactly the native state/answer
readout, even if its endpoint was specified as a functional world. -/
theorem command_native_readback {current : String} {command : ProgramCommand Pattern}
    {before : WorldCode} {after : RevisionedSpaces String} {observation : CommandObservation}
    (derivation : CommandDerivation current command (interpret before) after observation) :
    interpret (runCommand before current command).after = after ∧
      (runCommand before current command).observation = observation := by
  cases derivation with
  | empty => exact ⟨rfl, rfl⟩
  | declaration world command atom declared =>
      cases declared <;> exact ⟨interpret_publish _ _ _, rfl⟩
  | eval world subject readOnly =>
      simp [runCommand_eval _ _ _ readOnly]
  | evalPublish => exact ⟨interpret_publish _ _ _, rfl⟩
  | publish => exact ⟨interpret_publish _ _ _, rfl⟩
  | retained world command unhandled => simp [runCommand_retained _ _ _ unhandled]

def checkCommand (before : WorldCode) (current : String)
    (command : ProgramCommand Pattern) (receipt : CommandReceipt) : Bool :=
  let actual := runCommand before current command
  sameWorld receipt.after actual.after && decide (receipt.observation = actual.observation)

/-- Raw command summaries are checked against independent source judgments.
The checker recomputes finite operations; this is not a machine-time theorem. -/
@[simp] theorem checkCommand_exact (before : WorldCode) (current : String)
    (command : ProgramCommand Pattern) (receipt : CommandReceipt) :
    checkCommand before current command receipt = true ↔
      Nonempty (CommandDerivation current command (interpret before)
        (interpret receipt.after) receipt.observation) := by
  simp only [checkCommand, Bool.and_eq_true, sameWorld_exact, decide_eq_true_eq]
  constructor
  · rintro ⟨world, observation⟩
    rw [world, observation]
    exact ⟨runCommand_article before current command⟩
  · rintro ⟨article⟩
    obtain ⟨world, observation⟩ := command_native_readback article
    exact ⟨world.symm, observation.symm⟩

/-- A finite row trace retains causal source positions, including empty rows
and uninterpreted commands.  Per-row result bags retain duplicate answers. -/
structure ProgramReceipt where
  after : WorldCode
  outputs : List (Nat × CommandOutput)
  deriving Repr, DecidableEq

@[simp] def ProgramReceipt.observations (receipt : ProgramReceipt) : List (Nat × CommandObservation) :=
  receipt.outputs.map fun row => (row.1, row.2.observation)

def runProgram (before : WorldCode) (current : String) : Program Pattern → ProgramReceipt
  | [] => ⟨before, []⟩
  | (line, command) :: rest =>
      let first := runCommand before current command
      let remaining := runProgram first.after current rest
      ⟨remaining.after, (line, first.output) :: remaining.outputs⟩

/-- Native finite execution constructs a source derivation for every row. -/
def runProgram_article (before : WorldCode) (current : String)
    (program : Program Pattern) :
    ProgramDerivation current program (interpret before)
      (interpret (runProgram before current program).after)
      (runProgram before current program).observations := by
  induction program generalizing before with
  | nil => exact .nil _
  | cons row rest inductionHypothesis =>
      exact .cons row.1 row.2 rest _ _ _ _ _
        (runCommand_article before current row.2)
        (inductionHypothesis (runCommand before current row.2).after)

/-- Source execution is covered at every represented input, with no extra
hypothesis that arbitrary function worlds admit finite representations. -/
theorem program_native_readback (current : String) (program : Program Pattern)
    (before : WorldCode) (after : RevisionedSpaces String)
    (observations : List (Nat × CommandObservation))
    (derivation : ProgramDerivation current program (interpret before) after observations) :
    interpret (runProgram before current program).after = after ∧
      (runProgram before current program).observations = observations := by
  induction program generalizing before after observations with
  | nil => cases derivation; exact ⟨rfl, rfl⟩
  | cons row rest inductionHypothesis =>
      cases derivation with
      | cons line command rest beforeWorld middle after observation observations first remaining =>
          obtain ⟨world, answer⟩ := command_native_readback first
          have remaining' : ProgramDerivation current rest
              (interpret (runCommand before current command).after) after observations := by
            rw [world]
            exact remaining
          obtain ⟨afterWorld, afterAnswers⟩ :=
            inductionHypothesis _ after observations remaining'
          refine ⟨afterWorld, ?_⟩
          change (line, (runCommand before current command).observation) ::
              (runProgram (runCommand before current command).after current rest).observations =
            (line, observation) :: observations
          rw [answer, afterAnswers]

def checkProgram (before : WorldCode) (current : String)
    (program : Program Pattern) (receipt : ProgramReceipt) : Bool :=
  let actual := runProgram before current program
  sameWorld receipt.after actual.after && decide (receipt.observations = actual.observations)

@[simp] theorem checkProgram_exact (before : WorldCode) (current : String)
    (program : Program Pattern) (receipt : ProgramReceipt) :
    checkProgram before current program receipt = true ↔
      Nonempty (ProgramDerivation current program (interpret before)
        (interpret receipt.after) receipt.observations) := by
  simp only [checkProgram, Bool.and_eq_true, sameWorld_exact, decide_eq_true_eq]
  constructor
  · rintro ⟨world, observations⟩
    rw [world, observations]
    exact ⟨runProgram_article before current program⟩
  · rintro ⟨article⟩
    obtain ⟨world, observations⟩ := program_native_readback current program before _ _ article
    exact ⟨world.symm, observations.symm⟩

/-- The actual parser feeds the actual command runner. Parse errors remain
parser errors; successfully parsed unknown commands remain literal observations. -/
def runSource (spec : MeTTailCore.MeTTaSyntax.SyntaxSpec) (before : WorldCode)
    (current source : String) : Except String ProgramReceipt :=
  (Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation.parseProgramWith spec source).map (runProgram before current)

/-- A parser-success theorem connects the source text to the independently
specified causal execution of its original command constructors. -/
theorem runSource_source (spec : MeTTailCore.MeTTaSyntax.SyntaxSpec) (before : WorldCode)
    (current source : String) (program : Program Pattern)
    (parsed : Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation.parseProgramWith spec source = .ok program) :
    runSource spec before current source = .ok (runProgram before current program) ∧
      Nonempty (ProgramDerivation current program (interpret before)
        (interpret (runProgram before current program).after)
        (runProgram before current program).observations) := by
  constructor
  · unfold runSource
    rw [parsed]
    rfl
  · exact ⟨runProgram_article before current program⟩

/-- A native receipt and a source derivation are different proof faces.
This indexed source face permits functional worlds; it does not assert a
finite representation for arbitrary input worlds. -/
abbrev ProgramSourceArticle (before : RevisionedSpaces String) (current : String)
    (program : Program Pattern) :=
  Σ after : RevisionedSpaces String,
    Σ observations : List (Nat × CommandObservation),
      ProgramDerivation current program before after observations

abbrev AcceptedProgramReceipt (before : WorldCode) (current : String)
    (program : Program Pattern) :=
  { receipt : ProgramReceipt // checkProgram before current program receipt = true }

/-- Operational-to-logical map constructs the actual independent source article. -/
def acceptedProgramToSource (before : WorldCode) (current : String) (program : Program Pattern)
    (receipt : AcceptedProgramReceipt before current program) :
    ProgramSourceArticle (interpret before) current program := by
  refine ⟨interpret receipt.1.after, receipt.1.observations, ?_⟩
  have checked : interpret receipt.1.after = interpret (runProgram before current program).after ∧
      receipt.1.observations = (runProgram before current program).observations := by
    simpa only [checkProgram, Bool.and_eq_true, sameWorld_exact, decide_eq_true_eq] using receipt.2
  rw [checked.1, checked.2]
  exact runProgram_article before current program

/-- Logical readout retains the world and all per-row answer bags. -/
def sourceProgramObservation {before : RevisionedSpaces String} {current : String}
    {program : Program Pattern} (article : ProgramSourceArticle before current program) :
    RevisionedSpaces String × List (Nat × CommandObservation) :=
  (article.1, article.2.1)

/-- The direct operational readout interprets finite rows and retains bags.
It is not defined by first constructing a source derivation. -/
def acceptedProgramObservation {before : WorldCode} {current : String}
    {program : Program Pattern} (receipt : AcceptedProgramReceipt before current program) :
    RevisionedSpaces String × List (Nat × CommandObservation) :=
  (interpret receipt.1.after, receipt.1.observations)

/-- The pointwise triangle commutes.  General contextual substitution
naturality is a separate obligation and is not inferred from this equation. -/
theorem program_observation_triangle (before : WorldCode) (current : String)
    (program : Program Pattern) (receipt : AcceptedProgramReceipt before current program) :
    sourceProgramObservation (acceptedProgramToSource before current program receipt) =
      acceptedProgramObservation receipt := rfl

/-- Every source execution from a represented input is realized by the native
runner with its exact world/answer observation. -/
theorem source_program_observation_covered (before : WorldCode) (current : String)
    (program : Program Pattern)
    (article : ProgramSourceArticle (interpret before) current program) :
    (interpret (runProgram before current program).after,
      (runProgram before current program).observations) = sourceProgramObservation article := by
  obtain ⟨world, observations⟩ := program_native_readback current program before _ _ article.2.2
  exact Prod.ext world observations

open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.SemanticService

/-- Source input preserves both text and the actual parser result.  The
admission condition checks their correspondence rather than assuming it. -/
structure ParsedProgramInput where
  spec : MeTTailCore.MeTTaSyntax.SyntaxSpec
  before : WorldCode
  current : String
  source : String
  program : Program Pattern

def parsedProgramInput : AdmissionObject where
  Carrier := ParsedProgramInput
  Meaning input :=
    Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation.parseProgramWith input.spec input.source =
      .ok input.program

/-- Executable source admission reruns the actual parser and compares its
complete command/line result with the supplied prepared program. -/
def checkParsedProgramInput (input : ParsedProgramInput) : Bool :=
  decide (Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation.parseProgramWith input.spec input.source =
    .ok input.program)

@[simp] theorem checkParsedProgramInput_exact (input : ParsedProgramInput) :
    checkParsedProgramInput input = true ↔ parsedProgramInput.Meaning input := by
  simp [checkParsedProgramInput, parsedProgramInput]

def parsedProgramOutput : AdmissionObject where
  Carrier := ParsedProgramInput × ProgramReceipt
  Meaning output :=
    parsedProgramInput.Meaning output.1 ∧
      Nonempty (ProgramDerivation output.1.current output.1.program (interpret output.1.before)
        (interpret output.2.after) output.2.observations)

/-- The admitted operation runs the original command executor.  It receives
no proof/trace and invokes no certificate checker at execution time. -/
def parsedProgramOperation : AdmissionHom parsedProgramInput parsedProgramOutput where
  run input := (input, runProgram input.before input.current input.program)
  preserves input parsed := ⟨parsed, ⟨runProgram_article input.before input.current input.program⟩⟩

def parsedProgramNativeService : Service parsedProgramOutput :=
  .nativeOperation parsedProgramInput parsedProgramOperation

/-- The operation's output agrees with the actual source parser path. -/
theorem parsedProgramOperation_parser (input : ParsedProgramInput)
    (parsed : parsedProgramInput.Meaning input) :
    runSource input.spec input.before input.current input.source =
      .ok (parsedProgramOperation.run input).2 := by
  unfold runSource
  rw [parsed]
  rfl

/-! ## Parsed recursive/effectful live computation through the common service -/

namespace LiveNative
open PeTTa.ProgramReplay

/-- The expression has its original Atom reader and a literal source string.
The complete finite initial store, input and output are retained. -/
structure Request where
  before : Snapshot
  source : String
  expression : OSLFCore.Atom
  budget : Nat

def Request.Meaning (request : Request) : Prop :=
  PeTTa.SpaceSemantics.readSource request.source = .ok [request.expression] ∧
    request.before.control = .evaluate [] request.expression ∧ request.before.frames = []

def input : AdmissionObject where
  Carrier := Request
  Meaning := Request.Meaning

instance (request : Request) : Decidable request.Meaning := by
  unfold Request.Meaning
  infer_instance

def checkInput (request : Request) : Bool := decide request.Meaning

@[simp] theorem checkInput_exact (request : Request) :
    checkInput request = true ↔ request.Meaning := by simp [checkInput]

structure Result where
  request : Request
  after : Snapshot

def Result.Meaning (result : Result) : Prop :=
  result.request.Meaning ∧
    result.after.decode = LiveRegistry.advance result.request.budget result.request.before.decode ∧
    LiveRegistry.theory.MultiStep result.request.before.decode result.after.decode

def output : AdmissionObject where
  Carrier := Result
  Meaning := Result.Meaning

/-- This operation runs the actual source-indexing and dispatcher code. It
receives no submitted proof, and retains faults and unfinished configurations. -/
def operation : AdmissionHom input output where
  run request := ⟨request, LiveRegistry.nativeAdvance request.budget request.before⟩
  preserves request meaningful := by
    refine ⟨meaningful, LiveRegistry.nativeAdvance_decode _ _, ?_⟩
    rw [LiveRegistry.nativeAdvance_traceEnd]
    exact LiveRegistry.checkedTrace_path _ _ (LiveRegistry.emitTrace_checked _ _)

def nativeService : Service.{0, 0} output := .nativeOperation input operation

/-- The same actual result is admitted as an intrinsic source-reachability
claim by the combined proof guest. Proof checking remains a separate route. -/
def resultClaim : AdmissionHom output target where
  run result := .livePath result.request.before result.after
  preserves _ meaningful := meaningful.2.2

theorem operation_source (request : Request) (meaningful : request.Meaning) :
    PeTTa.SpaceSemantics.readSource request.source = .ok [request.expression] ∧
      Claim.Meaning (.livePath request.before (operation.run request).after) :=
  ⟨meaningful.1, (operation.preserves request meaningful).2.2⟩

theorem operation_budget_endpoint (request : Request) :
    (operation.run request).after.decode =
      LiveRegistry.advance request.budget request.before.decode :=
  LiveRegistry.nativeAdvance_decode _ _

end LiveNative

namespace ProgramControls

def initial : WorldCode :=
  (4, [("&self", .apply "a" []), ("&self", .apply "b" [])])

def first : ProgramReceipt := ⟨initial, []⟩
def second : ProgramReceipt := ⟨(initial.1, initial.2.reverse), []⟩

theorem first_checked : checkProgram initial "&self" [] first = true := by decide
theorem second_checked : checkProgram initial "&self" [] second = true := by decide

theorem distinct_rows : first ≠ second := by decide

/-- Distinct physical history orders denote the same source observation.
This supplies a concrete information-loss boundary, not an exact trinity. -/
theorem same_observation :
    acceptedProgramObservation ⟨first, first_checked⟩ =
      acceptedProgramObservation ⟨second, second_checked⟩ := by
  apply Prod.ext
  · have same := (sameWorld_exact second.after first.after).mp (by decide)
    exact same.symm
  · rfl

namespace SubstitutionBoundary

def a : Pattern := .apply "a" []
def b : Pattern := .apply "b" []
def world : WorldCode := (0, [("&self", a), ("&self", b)])
def request : Pattern := .apply "match" [.apply "&self" [], .fvar "x", .fvar "x"]

def support : ContextSupport.Support := fun _ => []
def assignment : ContextSupport.Assignment := fun name => if name = "x" then a else .fvar name
def instantiate : Pattern → Pattern := ContextSupport.substituteAt support assignment 0

def mappedWorld : WorldCode := (world.1, world.2.map fun row => (row.1, instantiate row.2))

/-- This substitution is well scoped, and it fixes every stored ground atom. -/
theorem represented_world_unchanged : mappedWorld = world := by
  simp [mappedWorld, world, a, b, instantiate, ContextSupport.substituteAt]

/-- Uniform syntax mapping also substitutes the variables locally bound by
matching. It therefore restricts the query and changes its answer bag. -/
theorem uniform_command_map_changes_query :
    (ProgramCommand.eval request).map instantiate =
      .eval (.apply "match" [.apply "&self" [], a, a]) := by
  simp [ProgramCommand.map, instantiate, request, ContextSupport.substituteAt, support, assignment,
    a, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem original_answers : sourceReadAnswers (interpret world) "&self" request = {a, b} := by
  decide +kernel

theorem substituted_answers : sourceReadAnswers (interpret mappedWorld) "&self"
    (instantiate request) = {a} := by
  have changed : instantiate request = .apply "match" [.apply "&self" [], a, a] := by
    have same := uniform_command_map_changes_query
    simpa only [ProgramCommand.map, ProgramCommand.eval.injEq] using same
  rw [represented_world_unchanged, changed]
  decide +kernel

/-- Plain `ProgramCommand.map` is not a substitution action for the binding
roles of this query syntax. A scoped contextual comparison needs an operation
that distinguishes pattern-bound metavariables from ambient object variables. -/
theorem uniform_substitution_not_query_natural :
    (sourceReadAnswers (interpret world) "&self" request).map instantiate ≠
      sourceReadAnswers (interpret mappedWorld) "&self" (instantiate request) := by
  rw [original_answers, substituted_answers]
  simpa [instantiate, ContextSupport.substituteAt, a, b] using
    (by decide : ({a, b} : Multiset Pattern) ≠ {a})

end SubstitutionBoundary

end ProgramControls



open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

/-- Physical payload transformation preserves every history occurrence. -/
def mapPayloads (transform : Pattern → Pattern) (code : WorldCode) : WorldCode :=
  (code.1, code.2.map fun row => (row.1, transform row.2))

@[simp] theorem rowsAt_mapPayloads (transform : Pattern → Pattern)
    (code : WorldCode) (space : String) :
    rowsAt (mapPayloads transform code) space = (rowsAt code space).map transform := by
  unfold rowsAt mapPayloads PeTTa.CellHistory.values
  rw [List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro row
  by_cases same : row.1 = space <;> simp [same]

theorem interpret_mapPayloads (transform : Pattern → Pattern) (code : WorldCode) :
    interpret (mapPayloads transform code) = (interpret code).mapPayloads transform := by
  apply RevisionedSpaces.ext
  · rfl
  · intro space
    simp [interpret, RevisionedSpaces.mapPayloads]

@[simp] theorem mapPayloads_revision (transform : Pattern → Pattern) (code : WorldCode) :
    (mapPayloads transform code).1 = code.1 := rfl

/-- Global history positions retain their original names and mapped payloads. -/
@[simp] theorem mapPayloads_historyOccurrence (transform : Pattern → Pattern)
    (code : WorldCode) (index : Nat) :
    (mapPayloads transform code).2[index]? =
      (code.2[index]?).map (fun row => (row.1, transform row.2)) := by
  simp [mapPayloads]

/-- An atom-occurrence coordinate in the existing query evidence is retained
under injective payload maps. Matcher evidence needs its own role-aware law. -/
theorem mapPayloads_atomOccurrence (transform : Pattern → Pattern)
    (injective : Function.Injective transform) (code : WorldCode) (space : String)
    (atom : Pattern) (occurrence : Nat)
    (present : occurrence < Multiset.count atom ((interpret code).contents space)) :
    occurrence < Multiset.count (transform atom)
      ((interpret (mapPayloads transform code)).contents space) := by
  rw [interpret_mapPayloads, RevisionedSpaces.mapPayloads_count _ injective]
  exact present

/-- Mapping occurrences and publishing one new occurrence commute physically. -/
theorem mapPayloads_publish (transform : Pattern → Pattern) (before : WorldCode)
    (space : String) (atom : Pattern) :
    mapPayloads transform (publish before space atom) =
      publish (mapPayloads transform before) space (transform atom) := by
  rfl

/-- Existing world equivalence remains respected; noninjective payload maps
need not reflect it. -/
theorem mapPayloads_respects_equivalence (transform : Pattern → Pattern)
    {first second : WorldCode} (same : interpret first = interpret second) :
    interpret (mapPayloads transform first) = interpret (mapPayloads transform second) := by
  rw [interpret_mapPayloads, interpret_mapPayloads, same]

namespace PayloadTransportControls

def world : WorldCode := (7, [("&self", .apply "a" []), ("&self", .apply "b" [])])
def collapse : Pattern → Pattern := fun _ => .apply "a" []

/-- A noninjective map preserves the two source occurrences while merging
value classes; it cannot preserve each original value-class count. -/
theorem collision_retains_multiplicity :
    Multiset.count (.apply "a" []) ((interpret (mapPayloads collapse world)).contents "&self") = 2 ∧
      Multiset.count (.apply "a" []) ((interpret world).contents "&self") = 1 := by
  decide +kernel

end PayloadTransportControls



end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel


/-! ## Original binding before native evaluation dispatch -/

namespace Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire.AmbientBinding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
/-- Preparation is followed by the original native request, so its finite
source derivation is inherited through the proved binding-action agreement. -/
theorem native_eval_agrees
    (before : MeTTaFiniteRevisionedKernel.WorldCode) (current : String)
    (incoming : Bindings) (subject : Pattern)
    (wellScoped : subject.isWellScopedAt 0 = true)
    (plain : isMatchCorrectAux subject = true) :
    MeTTaFiniteRevisionedKernel.runCommand before current
        (.eval (reopen incoming 0 (prepare incoming 0 subject))) =
      MeTTaFiniteRevisionedKernel.runCommand before current
        (.eval (applyBindings incoming subject)) := by
  rw [reopen_prepare_applyBindings incoming subject wellScoped plain]

/-- The returned source article describes binding before native dispatch,
not a uniform substitution of a query's already completed answer bag. -/
def native_eval_source
    (before : MeTTaFiniteRevisionedKernel.WorldCode) (current : String)
    (incoming : Bindings) (subject : Pattern)
    (wellScoped : subject.isWellScopedAt 0 = true)
    (plain : isMatchCorrectAux subject = true) :
    CommandDerivation current (.eval (applyBindings incoming subject))
      (MeTTaFiniteRevisionedKernel.interpret before)
      (MeTTaFiniteRevisionedKernel.interpret
        (MeTTaFiniteRevisionedKernel.runCommand before current
          (.eval (reopen incoming 0 (prepare incoming 0 subject)))).after)
      (MeTTaFiniteRevisionedKernel.runCommand before current
        (.eval (reopen incoming 0 (prepare incoming 0 subject)))).observation := by
  rw [native_eval_agrees before current incoming subject wellScoped plain]
  exact MeTTaFiniteRevisionedKernel.runCommand_article before current
    (.eval (applyBindings incoming subject))

end Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire.AmbientBinding



/-!
Native installation and conditional computation reuse the original command
converter, finite world representation, plan compiler and retained job machine.
Installation, execution admission and firing authority are separate judgments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation

open Mettapedia.OSLF.MeTTaIL
open Syntax GeneralExecutionAdmission
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
open Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge

structure InstallRequest where
  before : Snapshot
  world : WorldCode
  current : String
  name : String
  command : MeTTailCore.MeTTaSyntax.SyntaxCommand

structure InstallResult where
  request : InstallRequest
  after : Snapshot
  world : WorldCode
  observation : CommandObservation

/-- This operation installs original structured source rules; unknown command
families retain their original literal command without a public error. -/
def install (request : InstallRequest) : InstallResult :=
  match MeTTailCore.MeTTaSyntax.syntaxRule? request.name request.command,
      MeTTaRevisionedQueryBindEval.AuthoredActivation.ruleAtom request.command with
  | some authored, some literal =>
      ⟨request, MeTTaRevisionedQueryBindEval.AuthoredActivation.installSnapshot request.before (coreToSpecRewriteRule authored),
        publish request.world request.current literal, .answers 0⟩
  | _, _ =>
      ⟨request, request.before, request.world,
        .retained (MeTTaSyntaxQuotation.coreProgramCommandToProgramCommand request.command)⟩

@[simp] theorem install_request (request : InstallRequest) : (install request).request = request := by
  unfold install
  split <;> rfl

/-- A completed installation has source authority; an uninterpreted request
retains its literal command and state and installs no executable rule. -/
def InstallResult.Meaning (result : InstallResult) : Prop :=
  match result.observation with
  | .answers values => values = 0 ∧ Nonempty (MeTTaRevisionedQueryBindEval.AuthoredActivation.Installed
      result.request.current result.request.name result.request.command
      (result.request.before, interpret result.request.world)
      (result.after, interpret result.world))
  | .retained command =>
      command = MeTTaSyntaxQuotation.coreProgramCommandToProgramCommand result.request.command ∧
      result.after = result.request.before ∧ result.world = result.request.world ∧
      MeTTailCore.MeTTaSyntax.syntaxRule? result.request.name result.request.command = none

theorem install_source (request : InstallRequest) : (install request).Meaning := by
  unfold install
  cases parsed : MeTTailCore.MeTTaSyntax.syntaxRule? request.name request.command with
  | none =>
      cases literal : MeTTaRevisionedQueryBindEval.AuthoredActivation.ruleAtom request.command <;>
        exact ⟨rfl, rfl, rfl, parsed⟩
  | some authored =>
      obtain ⟨literal, quoted⟩ := MeTTaRevisionedQueryBindEval.AuthoredActivation.parsed_has_literal request.name request.command authored parsed
      rw [quoted]
      change (0 : Multiset Pattern) = 0 ∧ _
      refine ⟨rfl, ?_⟩
      rw [interpret_publish]
      exact ⟨.declaration (request.before, interpret request.world) authored literal parsed quoted⟩

/-- This dependent package carries the independently proved license of the
actual generated occurrence; it does not receive a caller-supplied proof. -/
structure Prepared where
  request : GeneralRuleJobExecution.Request
  licensed : request.job.Valid request.plan request.bound request.expected request.source

def prepare (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (occurrence : Nat) : Option Prepared :=
  let plan := GeneralExecutionAdmission.compile snapshot permissions
  match selected : (GeneralRuleJobs.jobs plan bound expected source)[occurrence]? with
  | none => none
  | some job =>
      some ⟨⟨plan, bound, expected, source, job⟩,
        (GeneralRuleJobs.jobs_spec _ _ _ _ _).mp (List.mem_of_getElem? selected)⟩

/-- The semantic receipt is connected to the actual newly parsed source
clause, rather than a similarly named rule or an unguarded reconstruction. -/
theorem answer_new_guarded_fields (before : Snapshot) (permissions : Permissions)
    (name : String) (left right : MeTTailCore.MeTTaIL.Syntax.Pattern)
    (terms : List MeTTailCore.MeTTaIL.Syntax.Pattern) (rule : RewriteRule)
    (parsed : MeTTaRevisionedQueryBindEval.AuthoredActivation.parsedRule? name (.defineRule left right terms) = some rule)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid (GeneralExecutionAdmission.compile
      (MeTTaRevisionedQueryBindEval.AuthoredActivation.installSnapshot before rule) permissions) bound expected source)
    (newDeclaration : receipt.job.declaration.declarationIndex = before.language.rewrites.length) :
    ∃ premises : List MeTTailCore.MeTTaIL.Syntax.Premise,
      terms.mapM MeTTailCore.MeTTaSyntax.syntaxPremise? = some premises ∧
      receipt.job.declaration.rule.name = name ∧
      receipt.job.declaration.rule.left = coreToSpecPattern left ∧
      receipt.job.declaration.rule.right = coreToSpecPattern right ∧
      receipt.job.declaration.rule.premises = premises.map coreToSpecPremise := by
  have selected := (List.mk_mem_zipIdx_iff_getElem?.mp valid.1.1)
  have member := List.mem_of_getElem? selected
  exact MeTTaRevisionedQueryBindEval.AuthoredActivation.compiled_new_guarded_fields before permissions name left right terms rule
    parsed receipt.job.declaration member newDeclaration

theorem prepare_fields (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (occurrence : Nat) (prepared : Prepared)
    (selected : prepare snapshot permissions bound expected source occurrence = some prepared) :
    prepared.request.plan = GeneralExecutionAdmission.compile snapshot permissions ∧
      prepared.request.bound = bound ∧ prepared.request.expected = expected ∧
      prepared.request.source = source ∧
      (GeneralRuleJobs.jobs prepared.request.plan bound expected source)[occurrence]? =
        some prepared.request.job := by
  unfold prepare at selected
  dsimp only at selected
  split at selected
  next => contradiction
  next job position =>
    cases Option.some.inj selected
    exact ⟨rfl, rfl, rfl, rfl, position⟩

structure NativeWork where
  prepared : Prepared
  state : GeneralRuleJobExecution.State prepared.request

/-- The entry point accepts source data, an occurrence coordinate and fuel,
then prepares and runs the original typed conditional machine itself. -/
def execute (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (occurrence budget : Nat) : Option NativeWork := do
  let prepared ← prepare snapshot permissions bound expected source occurrence
  return ⟨prepared, GeneralRuleJobExecution.run prepared.request budget
    (GeneralRuleJobExecution.start prepared.request prepared.licensed)⟩

/-- Resumption retains this exact prepared request and suspended state;
it never restarts the matcher or replays already completed query effects. -/
def NativeWork.resume (work : NativeWork) (budget : Nat) : NativeWork :=
  ⟨work.prepared, GeneralRuleJobExecution.run work.prepared.request budget work.state⟩

theorem NativeWork.resume_add (work : NativeWork) (first second : Nat) :
    (work.resume first).resume second = work.resume (first + second) := by
  cases work
  simp only [resume, GeneralRuleJobExecution.run_add]

/-- Readouts retain whole receipts; their target projection is a bag, not a
promise of a result order in the source language. -/
def NativeWork.receipts (work : NativeWork) : List GeneralRuleJobs.Receipt :=
  work.state.answers.map Subtype.val

def NativeWork.answers (work : NativeWork) : Multiset Pattern :=
  (work.receipts.map GeneralRuleJobs.Receipt.target : Multiset Pattern)

theorem execute_source (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (occurrence budget : Nat) (work : NativeWork)
    (computed : execute snapshot permissions bound expected source occurrence budget = some work)
    (receipt : GeneralRuleJobs.Receipt) (emitted : receipt ∈ work.receipts) :
    receipt.Valid (GeneralExecutionAdmission.compile snapshot permissions) bound expected source := by
  unfold execute at computed
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
  obtain ⟨prepared, selected, returned⟩ := computed
  cases Option.some.inj returned
  obtain ⟨answer, _, same⟩ := List.mem_map.mp emitted
  cases same
  have fields := prepare_fields snapshot permissions bound expected source occurrence prepared selected
  simpa only [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1] using answer.property

/-- Source parsing and installation feed the actual original conditional
computation; an unknown installation still retains its separate observation. -/
def installAndExecute (request : InstallRequest) (permissions : Permissions)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (occurrence budget : Nat) : InstallResult × Option NativeWork :=
  let installed := install request
  (installed, execute installed.after permissions bound expected source occurrence budget)

theorem install_after_parsed (request : InstallRequest) (rule : RewriteRule)
    (parsed : MeTTaRevisionedQueryBindEval.AuthoredActivation.parsedRule?
      request.name request.command = some rule) :
    (install request).after = MeTTaRevisionedQueryBindEval.AuthoredActivation.installSnapshot request.before rule := by
  obtain ⟨authored, decoded, same⟩ :=
    (MeTTaRevisionedQueryBindEval.AuthoredActivation.parsedRule?_source _ _ _).mp parsed
  obtain ⟨literal, quoted⟩ :=
    MeTTaRevisionedQueryBindEval.AuthoredActivation.parsed_has_literal _ _ _ decoded
  simp only [install, decoded, quoted]
  rw [same]

theorem execute_fields (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (occurrence budget : Nat) (work : NativeWork)
    (computed : execute snapshot permissions bound expected source occurrence budget = some work) :
    work.prepared.request.plan = GeneralExecutionAdmission.compile snapshot permissions ∧
      work.prepared.request.bound = bound ∧ work.prepared.request.expected = expected ∧
      work.prepared.request.source = source ∧
      (GeneralRuleJobs.jobs work.prepared.request.plan bound expected source)[occurrence]? =
        some work.prepared.request.job ∧
      work.state = GeneralRuleJobExecution.run work.prepared.request budget
        (GeneralRuleJobExecution.start work.prepared.request work.prepared.licensed) := by
  unfold execute at computed
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
  obtain ⟨prepared, selected, returned⟩ := computed
  cases Option.some.inj returned
  have fields := prepare_fields snapshot permissions bound expected source occurrence prepared selected
  exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2, rfl⟩

@[simp] theorem execute_none_iff (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (occurrence budget : Nat) :
    execute snapshot permissions bound expected source occurrence budget = none ↔
      (GeneralRuleJobs.jobs (GeneralExecutionAdmission.compile snapshot permissions)
        bound expected source)[occurrence]? = none := by
  unfold execute prepare
  dsimp only
  split <;> simp_all

/-- This is the constructed pipeline theorem: actual native execution, not a
separately supplied receipt-validity premise, retains the source guards. -/
theorem execute_new_guarded_fields (before : Snapshot) (permissions : Permissions)
    (name : String) (left right : MeTTailCore.MeTTaIL.Syntax.Pattern)
    (terms : List MeTTailCore.MeTTaIL.Syntax.Pattern) (rule : RewriteRule)
    (parsed : MeTTaRevisionedQueryBindEval.AuthoredActivation.parsedRule?
      name (.defineRule left right terms) = some rule)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (occurrence budget : Nat) (work : NativeWork)
    (computed : execute (MeTTaRevisionedQueryBindEval.AuthoredActivation.installSnapshot before rule)
      permissions bound expected source occurrence budget = some work)
    (receipt : GeneralRuleJobs.Receipt) (emitted : receipt ∈ work.receipts)
    (newDeclaration : receipt.job.declaration.declarationIndex = before.language.rewrites.length) :
    ∃ premises : List MeTTailCore.MeTTaIL.Syntax.Premise,
      terms.mapM MeTTailCore.MeTTaSyntax.syntaxPremise? = some premises ∧
      receipt.job.declaration.rule.name = name ∧
      receipt.job.declaration.rule.left = coreToSpecPattern left ∧
      receipt.job.declaration.rule.right = coreToSpecPattern right ∧
      receipt.job.declaration.rule.premises = premises.map coreToSpecPremise := by
  exact answer_new_guarded_fields before permissions name left right terms rule parsed bound expected source
    receipt (execute_source _ _ _ _ _ _ _ _ computed receipt emitted) newDeclaration

open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.SemanticService

/-- Parser syntax remains explicit. The submitted data carries source text,
its prepared command, the finite world and the actual typed source request. -/
structure ServiceRequest where
  spec : MeTTailCore.MeTTaSyntax.SyntaxSpec
  text : String
  installation : InstallRequest
  permissions : Permissions
  bound : List TypeExpr
  expected : TypeExpr
  source : Pattern
  occurrence : Nat
  budget : Nat

def ServiceRequest.Meaning (request : ServiceRequest) : Prop :=
  Algorithms.MeTTa.Simple.Parser.parseStmtWith request.spec request.text =
    .ok request.installation.command

instance (request : ServiceRequest) : Decidable request.Meaning := by
  unfold ServiceRequest.Meaning
  infer_instance

def checkServiceInput (request : ServiceRequest) : Bool := decide request.Meaning

@[simp] theorem checkServiceInput_exact (request : ServiceRequest) :
    checkServiceInput request = true ↔ request.Meaning := by simp [checkServiceInput]

structure ServiceResult where
  request : ServiceRequest
  installation : InstallResult
  work : Option NativeWork

/-- Source interpretation, physical occurrence selection, exact original
machine endpoint and independent semantic receipts are separate coordinates. -/
def ServiceResult.Meaning (result : ServiceResult) : Prop :=
  result.request.Meaning ∧ result.installation.Meaning ∧
    result.installation.request = result.request.installation ∧
    match result.work with
    | none =>
        (GeneralRuleJobs.jobs
          (GeneralExecutionAdmission.compile result.installation.after result.request.permissions)
          result.request.bound result.request.expected result.request.source)[result.request.occurrence]? = none
    | some work =>
        work.prepared.request.plan = GeneralExecutionAdmission.compile
          result.installation.after result.request.permissions ∧
        work.prepared.request.bound = result.request.bound ∧
        work.prepared.request.expected = result.request.expected ∧
        work.prepared.request.source = result.request.source ∧
        (GeneralRuleJobs.jobs work.prepared.request.plan result.request.bound
          result.request.expected result.request.source)[result.request.occurrence]? =
          some work.prepared.request.job ∧
        work.state = GeneralRuleJobExecution.run work.prepared.request result.request.budget
          (GeneralRuleJobExecution.start work.prepared.request work.prepared.licensed) ∧
        ∀ receipt ∈ work.receipts,
          receipt.Valid (GeneralExecutionAdmission.compile result.installation.after
            result.request.permissions) result.request.bound result.request.expected result.request.source

def serviceInput : AdmissionObject where
  Carrier := ServiceRequest
  Meaning := ServiceRequest.Meaning

def serviceOutput : AdmissionObject where
  Carrier := ServiceResult
  Meaning := ServiceResult.Meaning

/-- This admitted native service installs the original parsed source declaration and
executes the existing retained conditional machine without a proof input. -/
def operation : AdmissionHom serviceInput serviceOutput where
  run request :=
    let result := installAndExecute request.installation request.permissions request.bound
      request.expected request.source request.occurrence request.budget
    ⟨request, result.1, result.2⟩
  preserves request parsed := by
    change ServiceResult.Meaning _
    refine ⟨parsed, install_source request.installation, install_request request.installation, ?_⟩
    dsimp only [installAndExecute]
    cases computed : execute (install request.installation).after request.permissions request.bound
        request.expected request.source request.occurrence request.budget with
    | none => exact (execute_none_iff _ _ _ _ _ _ _).mp computed
    | some work =>
        have fields := execute_fields _ _ _ _ _ _ _ work computed
        exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1,
          fields.2.2.2.2.2, fun receipt emitted => execute_source _ _ _ _ _ _ _ work computed receipt emitted⟩

def nativeService : Service.{0, 0} serviceOutput := .nativeOperation serviceInput operation

/-- Untrusted text/prepared-command pairs pass the actual source reader
before the native operation runs. Failed admission is not a language error. -/
def admitAndRun (request : ServiceRequest) : Option ServiceResult :=
  if checkServiceInput request then some (operation.run request) else none

theorem admitAndRun_source (request : ServiceRequest) (result : ServiceResult)
    (computed : admitAndRun request = some result) : result.Meaning := by
  unfold admitAndRun at computed
  split at computed
  next admitted =>
    cases Option.some.inj computed
    exact operation.preserves request ((checkServiceInput_exact request).mp admitted)
  next => contradiction

@[simp] theorem operation_request (request : ServiceRequest) :
    (operation.run request).request = request := rfl

/-- Actual parser admission, installation and native execution retain the
original guarded declaration, including every repeated source premise. -/
theorem admitted_new_guarded_fields
    (request : ServiceRequest) (result : ServiceResult) (work : NativeWork)
    (computed : admitAndRun request = some result) (executed : result.work = some work)
    (left right : MeTTailCore.MeTTaIL.Syntax.Pattern)
    (terms : List MeTTailCore.MeTTaIL.Syntax.Pattern) (rule : RewriteRule)
    (command : request.installation.command = .defineRule left right terms)
    (parsed : MeTTaRevisionedQueryBindEval.AuthoredActivation.parsedRule?
      request.installation.name request.installation.command = some rule)
    (receipt : GeneralRuleJobs.Receipt) (emitted : receipt ∈ work.receipts)
    (newDeclaration : receipt.job.declaration.declarationIndex =
      request.installation.before.language.rewrites.length) :
    ∃ premises : List MeTTailCore.MeTTaIL.Syntax.Premise,
      terms.mapM MeTTailCore.MeTTaSyntax.syntaxPremise? = some premises ∧
      receipt.job.declaration.rule.name = request.installation.name ∧
      receipt.job.declaration.rule.left = coreToSpecPattern left ∧
      receipt.job.declaration.rule.right = coreToSpecPattern right ∧
      receipt.job.declaration.rule.premises = premises.map coreToSpecPremise := by
  unfold admitAndRun at computed
  split at computed
  next =>
    cases Option.some.inj computed
    change execute (install request.installation).after request.permissions request.bound
      request.expected request.source request.occurrence request.budget = some work at executed
    rw [install_after_parsed request.installation rule parsed] at executed
    rw [command] at parsed
    exact execute_new_guarded_fields request.installation.before request.permissions
      request.installation.name left right terms rule parsed request.bound request.expected request.source
      request.occurrence request.budget work executed receipt emitted newDeclaration
  next => contradiction

end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomFreshness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.ProcessCalculi.MORK (Subst SourceGuardHolds)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation
open Mettapedia.GSLT.LanguageDef.SemanticService
open Mettapedia.GSLT.LanguageDef.SemanticEvidence

/-- The original source guard is evaluated on decoded Atom data. -/
def onAtom (substitution : Subst) (atom : Atom) : AtomFreshnessObservation :=
  match lowerAtomFreshness? atom with
  | none => .retained atom
  | some guard =>
      if Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard substitution guard
      then .held else .failed

theorem onAtom_source (substitution : Subst) (atom : Atom) :
    AtomFreshnessOutcome substitution atom (onAtom substitution atom) := by
  cases lowered : lowerAtomFreshness? atom with
  | none =>
      have unknown : ∀ guard, ¬ AtomFreshnessForm atom guard := by
        intro guard formed
        have selected := (lowerAtomFreshness?_exact atom guard).mpr formed
        rw [lowered] at selected
        contradiction
      simpa only [onAtom, lowered] using AtomFreshnessOutcome.retained unknown
  | some guard =>
      have formed := (lowerAtomFreshness?_exact atom guard).mp lowered
      cases checked : Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard substitution guard with
      | false =>
          have failed := (Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard_refused_exact
            substitution guard).mp checked
          simpa only [onAtom, lowered, checked, Bool.false_eq_true, if_false] using
            AtomFreshnessOutcome.failed formed failed
      | true =>
          have held := (Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard_exact
            substitution guard).mp checked
          simpa only [onAtom, lowered, checked, if_true] using
            AtomFreshnessOutcome.held formed held

theorem onAtom_complete {substitution : Subst} {atom : Atom}
    {observation : AtomFreshnessObservation}
    (source : AtomFreshnessOutcome substitution atom observation) :
    onAtom substitution atom = observation := by
  cases source with
  | held formed holds =>
      simp only [onAtom, (lowerAtomFreshness?_exact _ _).mpr formed,
        (Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard_exact _ _).mpr holds, if_true]
  | failed formed fails =>
      simp only [onAtom, (lowerAtomFreshness?_exact _ _).mpr formed,
        (Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard_refused_exact _ _).mpr fails,
        Bool.false_eq_true, if_false]
  | retained unknown =>
      cases lowered : lowerAtomFreshness? atom with
      | none => simp only [onAtom, lowered]
      | some guard => exact (unknown guard ((lowerAtomFreshness?_exact _ _).mp lowered)).elim

@[simp] theorem onAtom_exact (substitution : Subst) (atom : Atom)
    (observation : AtomFreshnessObservation) :
    onAtom substitution atom = observation ↔
      AtomFreshnessOutcome substitution atom observation := by
  constructor
  · intro computed
    rw [← computed]
    exact onAtom_source _ _
  · exact onAtom_complete

structure Request where
  substitution : Subst
  premise : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  deriving Repr

def Request.Meaning (request : Request) : Prop :=
  ∃ atom, GroundData.decode request.premise = some atom

/-- Malformed wire data is an internal admission refusal. Successfully
read unknown source syntax remains its literal original Atom. -/
def run (request : Request) : Option AtomFreshnessObservation :=
  (GroundData.decode request.premise).map (onAtom request.substitution)

@[simp] theorem run_exact (request : Request) (observation : AtomFreshnessObservation) :
    run request = some observation ↔
      ∃ atom, GroundData.decode request.premise = some atom ∧
        AtomFreshnessOutcome request.substitution atom observation := by
  simp only [run, Option.map_eq_some_iff, onAtom_exact]

structure Result where
  request : Request
  observation : Option AtomFreshnessObservation
  deriving Repr

def Result.Meaning (result : Result) : Prop :=
  ∃ atom observation, GroundData.decode result.request.premise = some atom ∧
    result.observation = some observation ∧
    AtomFreshnessOutcome result.request.substitution atom observation

def operation : AdmissionHom
    (⟨Request, Request.Meaning⟩ : AdmissionObject)
    (⟨Result, Result.Meaning⟩ : AdmissionObject) where
  run request := ⟨request, run request⟩
  preserves request admitted := by
    obtain ⟨atom, decoded⟩ := admitted
    refine ⟨atom, onAtom request.substitution atom, decoded, ?_, onAtom_source _ _⟩
    simp only [run, decoded, Option.map_some]

def nativeService : Service.{0, 0} (⟨Result, Result.Meaning⟩ : AdmissionObject) :=
  .nativeOperation (⟨Request, Request.Meaning⟩ : AdmissionObject) operation

/-- Exact check of a proposed source observation, including negative and
uninterpreted outcomes. This computes the guard, never an arbitrary callback. -/
def check (request : Request) (observation : AtomFreshnessObservation) : Bool :=
  decide (run request = some observation)

@[simp] theorem check_exact (request : Request) (observation : AtomFreshnessObservation) :
    check request observation = true ↔
      ∃ atom, GroundData.decode request.premise = some atom ∧
        AtomFreshnessOutcome request.substitution atom observation := by
  simp only [check, decide_eq_true_eq, run_exact]

theorem run_encoded (substitution : Subst) (atom : Atom) :
    run ⟨substitution, GroundData.encode atom⟩ = some (onAtom substitution atom) := by
  simp only [run, GroundData.decode_encode, Option.map_some]

/-- Concrete decision on resolved source arguments. A non-name value fails
its source guard; it is not a successful freshness witness. -/
def resolvedDecision (nameValue subject : Atom) : Bool :=
  match nameValue with
  | .var name => Mettapedia.Languages.ProcessCalculi.MORK.isAtomFresh name subject
  | _ => false

@[simp] theorem resolvedDecision_exact (nameValue subject : Atom) :
    resolvedDecision nameValue subject = true ↔ ResolvedAtomFreshness nameValue subject := by
  constructor
  · intro held
    cases nameValue with
    | var name =>
        exact .variableName name subject
          (by simpa [resolvedDecision, Mettapedia.Languages.ProcessCalculi.MORK.isAtomFresh] using held)
    | symbol _ | grounded _ | expression _ => simp [resolvedDecision] at held
  · intro held
    cases held with
    | variableName name subject fresh =>
        simp [resolvedDecision, Mettapedia.Languages.ProcessCalculi.MORK.isAtomFresh, fresh]

/-- A two-input source-native predicate for the common query adapter. `none`
means bad arity or data outside the lossless source image, never guard failure. -/
def query : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Option Bool
  | [name, subject] => do
      let nameValue ← GroundData.decode name
      let subjectValue ← GroundData.decode subject
      some (resolvedDecision nameValue subjectValue)
  | _ => none

@[simp] theorem query_encoded (nameValue subject : Atom) :
    query [GroundData.encode nameValue, GroundData.encode subject] =
      some (resolvedDecision nameValue subject) := by
  simp only [query, GroundData.decode_encode, bind, Option.bind]

/-- This lowering equation uses the original first-match source lookup and
original non-recursive substitution. No freshness of encoded data is assumed. -/
theorem query_source_guard (substitution : Subst) (name : String) (subject : Atom) :
    query [GroundData.encode ((substitution.lookup name).getD (.var name)),
        GroundData.encode (Mettapedia.Languages.ProcessCalculi.MORK.applySubst substitution subject)] =
      some (Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard substitution
        (.freshness name subject)) := by
  rw [query_encoded]
  cases found : substitution.lookup name with
  | none => simp only [Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard, found,
      Option.getD_none, resolvedDecision]
  | some value =>
      cases value <;> simp only [Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard,
        found, Option.getD_some, resolvedDecision]

/-- The concrete query exposes exactly two losslessly decoded source inputs. -/
theorem query_readout (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (output : Bool) :
    query arguments = some output ↔
      ∃ nameValue subject, arguments = [GroundData.encode nameValue, GroundData.encode subject] ∧
        resolvedDecision nameValue subject = output := by
  constructor
  · intro checked
    unfold query at checked
    split at checked
    next nameWire subjectWire =>
      cases named : GroundData.decode nameWire with
      | none => simp only [named, bind, Option.bind] at checked; contradiction
      | some nameValue =>
        cases read : GroundData.decode subjectWire with
        | none => simp only [named, read, bind, Option.bind] at checked; contradiction
        | some subject =>
          have held : resolvedDecision nameValue subject = output := by
            simpa only [named, read, bind, Option.bind, Option.some.injEq] using checked
          exact ⟨nameValue, subject, by
            rw [(GroundData.decode_eq_some_iff _ _).mp named,
              (GroundData.decode_eq_some_iff _ _).mp read],
            held⟩
    next => contradiction
  · rintro ⟨nameValue, subject, rfl, held⟩
    rw [query_encoded, held]


@[simp] theorem resolvedDecision_refused_exact (nameValue subject : Atom) :
    resolvedDecision nameValue subject = false ↔ ¬ ResolvedAtomFreshness nameValue subject := by
  rw [← resolvedDecision_exact]
  exact Bool.eq_false_iff

/-- A successful query is authorized by original guest free-name absence. -/
theorem query_accepted_exact (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    query arguments = some true ↔
      ∃ nameValue subject, arguments = [GroundData.encode nameValue, GroundData.encode subject] ∧
        ResolvedAtomFreshness nameValue subject := by
  rw [query_readout]
  simp only [resolvedDecision_exact]

/-- A completed empty answer is a negative source guard, not missing input
admission or an inability to decode a submitted argument. -/
theorem query_failed_exact (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    query arguments = some false ↔
      ∃ nameValue subject, arguments = [GroundData.encode nameValue, GroundData.encode subject] ∧
        ¬ ResolvedAtomFreshness nameValue subject := by
  rw [query_readout]
  simp only [resolvedDecision_refused_exact]

theorem query_unknown_exact (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    query arguments = none ↔
      ¬ ∃ nameValue subject, arguments = [GroundData.encode nameValue, GroundData.encode subject] := by
  constructor
  · intro unknown ⟨nameValue, subject, same⟩
    subst arguments
    rw [query_encoded] at unknown
    contradiction
  · intro outside
    cases computed : query arguments with
    | none => rfl
    | some output =>
        obtain ⟨nameValue, subject, same, _⟩ := (query_readout arguments output).mp computed
        exact (outside ⟨nameValue, subject, same⟩).elim

/-- All-input query rows preserve their arguments and add no binding. -/
def queryRows (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Option (List (List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)) :=
  (query arguments).map fun held => if held then [arguments] else []

theorem queryRows_held_exact (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    queryRows arguments = some [arguments] ↔
      ∃ nameValue subject, arguments = [GroundData.encode nameValue, GroundData.encode subject] ∧
        ResolvedAtomFreshness nameValue subject := by
  rw [← query_accepted_exact]
  cases computed : query arguments with
  | none => simp only [queryRows, computed, Option.map_none, reduceCtorEq]
  | some output => cases output <;> simp [queryRows, computed]

theorem queryRows_failed_exact (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    queryRows arguments = some [] ↔
      ∃ nameValue subject, arguments = [GroundData.encode nameValue, GroundData.encode subject] ∧
        ¬ ResolvedAtomFreshness nameValue subject := by
  rw [← query_failed_exact]
  cases computed : query arguments with
  | none => simp only [queryRows, computed, Option.map_none, reduceCtorEq]
  | some output => cases output <;> simp [queryRows, computed]


/-- Complete table semantics retains failure separately from missing admission. -/
inductive RowsMeaning (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    List (List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) → Prop where
  | held {nameValue subject : Atom}
      (image : arguments = [GroundData.encode nameValue, GroundData.encode subject])
      (fresh : ResolvedAtomFreshness nameValue subject) : RowsMeaning arguments [arguments]
  | failed {nameValue subject : Atom}
      (image : arguments = [GroundData.encode nameValue, GroundData.encode subject])
      (notFresh : ¬ ResolvedAtomFreshness nameValue subject) : RowsMeaning arguments []

@[simp] theorem queryRows_exact (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (rows : List (List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)) :
    queryRows arguments = some rows ↔ RowsMeaning arguments rows := by
  constructor
  · intro computed
    cases checked : query arguments with
    | none => simp only [queryRows, checked, Option.map_none] at computed; contradiction
    | some truth =>
        cases truth with
        | false =>
            have result : rows = [] := by
              simpa only [queryRows, checked, Option.map_some, Bool.false_eq_true, if_false,
                Option.some.injEq] using computed.symm
            subst rows
            obtain ⟨nameValue, subject, image, source⟩ := (query_failed_exact arguments).mp checked
            exact .failed image source
        | true =>
            have result : rows = [arguments] := by
              simpa only [queryRows, checked, Option.map_some, if_true,
                Option.some.injEq] using computed.symm
            subst rows
            obtain ⟨nameValue, subject, image, source⟩ := (query_accepted_exact arguments).mp checked
            exact .held image source
  · intro source
    cases source with
    | held image fresh => exact (queryRows_held_exact arguments).mpr ⟨_, _, image, fresh⟩
    | failed image notFresh => exact (queryRows_failed_exact arguments).mpr ⟨_, _, image, notFresh⟩

theorem queryRows_unknown_exact (arguments : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    queryRows arguments = none ↔
      ¬ ∃ nameValue subject, arguments = [GroundData.encode nameValue, GroundData.encode subject] := by
  rw [← query_unknown_exact]
  cases computed : query arguments <;> simp [queryRows, computed]

end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomFreshness



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomMatching

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.GSLT.LanguageDef.SemanticService
open Mettapedia.GSLT.LanguageDef.SemanticEvidence

/-- Compute the selected original operation without a replacement evaluator. -/
def onAtoms (mode : AtomMatchMode) (initial : Subst) (pattern value : Atom) : Option Subst :=
  match mode with
  | .value => SpaceSemantics.matchValue initial pattern value
  | .binding => SpaceSemantics.matchBinding initial pattern value

@[simp] theorem onAtoms_matched_exact (mode : AtomMatchMode) (initial : Subst)
    (pattern value : Atom) (final : Subst) :
    onAtoms mode initial pattern value = some final ↔ AtomMatched mode initial pattern value final := by
  cases mode
  · exact SpaceSemantics.matchValue_exact initial pattern value final
  · exact SpaceSemantics.matchBinding_exact initial pattern value final

@[simp] theorem onAtoms_refused_exact (mode : AtomMatchMode) (initial : Subst)
    (pattern value : Atom) :
    onAtoms mode initial pattern value = none ↔
      ∀ final, ¬ AtomMatched mode initial pattern value final := by
  constructor
  · intro refused final matched
    have computed := (onAtoms_matched_exact _ _ _ _ _).mpr matched
    rw [refused] at computed
    contradiction
  · intro absent
    cases computed : onAtoms mode initial pattern value with
    | none => rfl
    | some final => exact (absent final ((onAtoms_matched_exact _ _ _ _ _).mp computed)).elim

@[simp] theorem onAtoms_exact (mode : AtomMatchMode) (initial : Subst)
    (pattern value : Atom) (result : Option Subst) :
    onAtoms mode initial pattern value = result ↔ AtomMatchOutcome mode initial pattern value result := by
  cases result with
  | none =>
      constructor
      · intro failed
        exact .refused ((onAtoms_refused_exact _ _ _ _).mp failed)
      · intro source
        cases source with
        | refused absent => exact (onAtoms_refused_exact _ _ _ _).mpr absent
  | some final =>
      constructor
      · intro checked
        exact .matched ((onAtoms_matched_exact _ _ _ _ _).mp checked)
      · intro source
        cases source with
        | matched matched => exact (onAtoms_matched_exact _ _ _ _ _).mpr matched

/-- The existing configuration codec reads substitution rows, including
original duplicate names and first-match lookup behavior. -/
def readInputs (bindings pattern value : Pattern) : Option (Subst × Atom × Atom) := do
  let bindingAtom ← GroundData.decode bindings
  let initial ← readBindings bindingAtom
  let patternAtom ← GroundData.decode pattern
  let valueAtom ← GroundData.decode value
  return (initial, patternAtom, valueAtom)

@[simp] theorem readInputs_encoded (initial : Subst) (pattern value : Atom) :
    readInputs (GroundData.encode (bindingsData initial))
      (GroundData.encode pattern) (GroundData.encode value) = some (initial, pattern, value) := by
  simp only [readInputs, GroundData.decode_encode, readBindings_bindingsData, bind, Option.bind,
    pure]

/-- Successful input admission is exactly the original canonical codec image. -/
theorem readInputs_exact (bindings pattern value : Pattern)
    (initial : Subst) (patternAtom valueAtom : Atom) :
    readInputs bindings pattern value = some (initial, patternAtom, valueAtom) ↔
      bindings = GroundData.encode (bindingsData initial) ∧
      pattern = GroundData.encode patternAtom ∧ value = GroundData.encode valueAtom := by
  constructor
  · intro read
    simp only [readInputs, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨bindingAtom, bindingsRead, initial, substRead, p, patternRead, v, valueRead, equal⟩ := read
    cases Option.some.inj equal
    exact ⟨(GroundData.encode_of_decode bindingsRead).symm.trans
        (congrArg GroundData.encode (bindingsData_of_readBindings substRead).symm),
      (GroundData.encode_of_decode patternRead).symm,
      (GroundData.encode_of_decode valueRead).symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact readInputs_encoded initial patternAtom valueAtom

structure Request where
  mode : AtomMatchMode
  bindings : Pattern
  pattern : Pattern
  value : Pattern
  deriving Repr

def Request.Meaning (request : Request) : Prop :=
  ∃ initial pattern value, request.bindings = GroundData.encode (bindingsData initial) ∧
    request.pattern = GroundData.encode pattern ∧ request.value = GroundData.encode value

/-- The outer option is codec admission; the inner option is source matching. -/
def run (request : Request) : Option (Option Subst) := do
  let (initial, pattern, value) ← readInputs request.bindings request.pattern request.value
  return onAtoms request.mode initial pattern value

@[simp] theorem run_exact (request : Request) (outcome : Option Subst) :
    run request = some outcome ↔
      ∃ initial pattern value,
        request.bindings = GroundData.encode (bindingsData initial) ∧
        request.pattern = GroundData.encode pattern ∧ request.value = GroundData.encode value ∧
        AtomMatchOutcome request.mode initial pattern value outcome := by
  simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨initial, pattern, value⟩, decoded, equal⟩
    have source := (readInputs_exact _ _ _ _ _ _).mp decoded
    exact ⟨initial, pattern, value, source.1, source.2.1, source.2.2,
      (onAtoms_exact _ _ _ _ _).mp (Option.some.inj equal)⟩
  · rintro ⟨initial, pattern, value, bindingsRead, patternRead, valueRead, source⟩
    exact ⟨(initial, pattern, value), (readInputs_exact _ _ _ _ _ _).mpr
      ⟨bindingsRead, patternRead, valueRead⟩,
      congrArg some ((onAtoms_exact _ _ _ _ _).mpr source)⟩

structure Result where
  request : Request
  outcome : Option (Option Subst)
  deriving Repr

def Result.Meaning (result : Result) : Prop :=
  ∃ initial pattern value outcome,
    result.request.bindings = GroundData.encode (bindingsData initial) ∧
    result.request.pattern = GroundData.encode pattern ∧
    result.request.value = GroundData.encode value ∧
    result.outcome = some outcome ∧
    AtomMatchOutcome result.request.mode initial pattern value outcome

def operation : AdmissionHom (⟨Request, Request.Meaning⟩ : AdmissionObject)
    (⟨Result, Result.Meaning⟩ : AdmissionObject) where
  run request := ⟨request, run request⟩
  preserves request admitted := by
    obtain ⟨initial, pattern, value, bindingsRead, patternRead, valueRead⟩ := admitted
    refine ⟨initial, pattern, value, onAtoms request.mode initial pattern value,
      bindingsRead, patternRead, valueRead, ?_, ?_⟩
    · apply (run_exact _ _).mpr
      exact ⟨initial, pattern, value, bindingsRead, patternRead, valueRead,
        (onAtoms_exact _ _ _ _ _).mp rfl⟩
    · exact (onAtoms_exact _ _ _ _ _).mp rfl

def nativeService : Service.{0, 0} (⟨Result, Result.Meaning⟩ : AdmissionObject) :=
  .nativeOperation (⟨Request, Request.Meaning⟩ : AdmissionObject) operation

/-- Only the fourth argument is an output position. The original first three
input byte trees are retained exactly in each successful result row. -/
def queryRows (mode : AtomMatchMode) : List Pattern → Option (List (List Pattern))
  | [bindings, pattern, value, _] => do
      let matched ← run ⟨mode, bindings, pattern, value⟩
      return match matched with
      | none => []
      | some final => [[bindings, pattern, value, GroundData.encode (bindingsData final)]]
  | _ => none

@[simp] theorem queryRows_encoded (mode : AtomMatchMode) (initial : Subst)
    (pattern value : Atom) (hole : Pattern) :
    queryRows mode [GroundData.encode (bindingsData initial), GroundData.encode pattern,
      GroundData.encode value, hole] = some
        (match onAtoms mode initial pattern value with
        | none => []
        | some final => [[GroundData.encode (bindingsData initial), GroundData.encode pattern,
            GroundData.encode value, GroundData.encode (bindingsData final)]]) := by
  simp only [queryRows, run, readInputs_encoded, bind, Option.bind, pure]

/-- Dynamic provider rows have source matching authority and the exact
original argument images; completed absence is represented by an empty table. -/
def RowsMeaning (mode : AtomMatchMode) (arguments : List Pattern)
    (rows : List (List Pattern)) : Prop :=
  ∃ initial pattern value hole outcome,
    arguments = [GroundData.encode (bindingsData initial), GroundData.encode pattern,
      GroundData.encode value, hole] ∧
    AtomMatchOutcome mode initial pattern value outcome ∧
    rows = outcome.toList.map (fun final =>
      [GroundData.encode (bindingsData initial), GroundData.encode pattern,
        GroundData.encode value, GroundData.encode (bindingsData final)])

@[simp] theorem queryRows_exact (mode : AtomMatchMode) (arguments : List Pattern)
    (rows : List (List Pattern)) :
    queryRows mode arguments = some rows ↔ RowsMeaning mode arguments rows := by
  constructor
  · intro computed
    unfold queryRows at computed
    split at computed
    next _ bindings pattern value hole =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
      obtain ⟨outcome, read, rowsEqual⟩ := computed
      obtain ⟨initial, patternAtom, valueAtom, bindingsRead, patternRead, valueRead, source⟩ :=
        (run_exact _ _).mp read
      dsimp only at bindingsRead patternRead valueRead source
      refine ⟨initial, patternAtom, valueAtom, hole, outcome, ?_, source, ?_⟩
      · simp only [bindingsRead, patternRead, valueRead]
      · cases outcome <;> simpa only [Option.toList, List.map_nil, List.map_cons, bindingsRead, patternRead, valueRead] using
          (Option.some.inj rowsEqual).symm
    next => contradiction
  · rintro ⟨initial, pattern, value, hole, outcome, rfl, source, rfl⟩
    rw [queryRows_encoded, (onAtoms_exact _ _ _ _ _).mpr source]
    cases outcome <;> rfl

theorem queryRows_unknown_exact (mode : AtomMatchMode) (arguments : List Pattern) :
    queryRows mode arguments = none ↔
      ¬ ∃ initial pattern value hole,
        arguments = [GroundData.encode (bindingsData initial), GroundData.encode pattern,
          GroundData.encode value, hole] := by
  constructor
  · intro unknown ⟨initial, pattern, value, hole, same⟩
    subst arguments
    rw [queryRows_encoded] at unknown
    contradiction
  · intro outside
    cases computed : queryRows mode arguments with
    | none => rfl
    | some rows =>
        obtain ⟨initial, pattern, value, hole, _, same, _, _⟩ :=
          (queryRows_exact _ _ _).mp computed
        exact (outside ⟨initial, pattern, value, hole, same⟩).elim

theorem queryRows_failed_exact (mode : AtomMatchMode) (initial : Subst)
    (pattern value : Atom) (hole : Pattern) :
    queryRows mode [GroundData.encode (bindingsData initial), GroundData.encode pattern,
      GroundData.encode value, hole] = some [] ↔
      ∀ final, ¬ AtomMatched mode initial pattern value final := by
  rw [← onAtoms_refused_exact, queryRows_encoded]
  cases onAtoms mode initial pattern value <;> simp

end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomMatching



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (DynamicProvider Signature ProviderSnapshot)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation (AtomMatchMode)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding (bindingsData)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

/-- Input admission fixes the actual source images and arity. Matcher output
schemas are not source input values and have no extra admission condition. -/
inductive Inputs : String → List Pattern → Prop where
  | freshness (nameValue subject : Atom) :
      Inputs "metta-atom-fresh-v1" [GroundData.encode nameValue, GroundData.encode subject]
  | matchValue (initial : Subst) (pattern value : Atom) (hole : Pattern) :
      Inputs "petta-match-value-v1" [GroundData.encode (bindingsData initial),
        GroundData.encode pattern, GroundData.encode value, hole]
  | matchBinding (initial : Subst) (pattern value : Atom) (hole : Pattern) :
      Inputs "petta-match-binding-v1" [GroundData.encode (bindingsData initial),
        GroundData.encode pattern, GroundData.encode value, hole]

/-- Each native primitive has independent source authority. Unknown service
names have no constructor and therefore no invented source interpretation. -/
inductive Source : String → List Pattern → List (List Pattern) → Prop where
  | freshness {arguments : List Pattern} {rows : List (List Pattern)}
      (source : AtomFreshness.RowsMeaning arguments rows) :
      Source "metta-atom-fresh-v1" arguments rows
  | matchValue {arguments : List Pattern} {rows : List (List Pattern)}
      (source : AtomMatching.RowsMeaning .value arguments rows) :
      Source "petta-match-value-v1" arguments rows
  | matchBinding {arguments : List Pattern} {rows : List (List Pattern)}
      (source : AtomMatching.RowsMeaning .binding arguments rows) :
      Source "petta-match-binding-v1" arguments rows

def rows? (relation : String) (arguments : List Pattern) : Option (List (List Pattern)) :=
  if relation = "metta-atom-fresh-v1" then AtomFreshness.queryRows arguments
  else if relation = "petta-match-value-v1" then AtomMatching.queryRows .value arguments
  else if relation = "petta-match-binding-v1" then AtomMatching.queryRows .binding arguments
  else none

@[simp] theorem rows_exact (relation : String) (arguments : List Pattern)
    (rows : List (List Pattern)) : rows? relation arguments = some rows ↔ Source relation arguments rows := by
  constructor
  · intro computed
    unfold rows? at computed
    split at computed
    next fresh =>
      subst relation
      exact .freshness ((AtomFreshness.queryRows_exact _ _).mp computed)
    next =>
      split at computed
      next value =>
        subst relation
        exact .matchValue ((AtomMatching.queryRows_exact _ _ _).mp computed)
      next =>
        split at computed
        next binding =>
          subst relation
          exact .matchBinding ((AtomMatching.queryRows_exact _ _ _).mp computed)
        next => contradiction
  · intro source
    cases source with
    | freshness held =>
        simpa only [rows?, ↓reduceIte] using (AtomFreshness.queryRows_exact _ _).mpr held
    | matchValue held =>
        simpa [rows?] using (AtomMatching.queryRows_exact _ _ _).mpr held
    | matchBinding held =>
        simpa [rows?] using (AtomMatching.queryRows_exact _ _ _).mpr held

theorem source_inputs {relation : String} {arguments : List Pattern}
    {rows : List (List Pattern)} (source : Source relation arguments rows) :
    Inputs relation arguments := by
  cases source with
  | freshness fresh =>
      cases fresh with
      | held image _ => cases image; exact .freshness _ _
      | failed image _ => cases image; exact .freshness _ _
  | matchValue source =>
      obtain ⟨initial, pattern, value, hole, _, image, _, _⟩ := source
      cases image
      exact .matchValue initial pattern value hole
  | matchBinding source =>
      obtain ⟨initial, pattern, value, hole, _, image, _, _⟩ := source
      cases image
      exact .matchBinding initial pattern value hole

/-- Each admitted finite source request has a complete primitive response.
This states local primitive totality, including failed matching and guards. -/
theorem inputs_have_source {relation : String} {arguments : List Pattern}
    (admitted : Inputs relation arguments) : ∃ rows, Source relation arguments rows := by
  cases admitted with
  | freshness nameValue subject =>
      cases decision : AtomFreshness.resolvedDecision nameValue subject with
      | false =>
          exact ⟨[], .freshness (.failed rfl
            ((AtomFreshness.resolvedDecision_refused_exact _ _).mp decision))⟩
      | true =>
          exact ⟨[[GroundData.encode nameValue, GroundData.encode subject]],
            .freshness (.held rfl ((AtomFreshness.resolvedDecision_exact _ _).mp decision))⟩
  | matchValue initial pattern value hole =>
      refine ⟨(AtomMatching.onAtoms .value initial pattern value).toList.map (fun final =>
        [GroundData.encode (bindingsData initial), GroundData.encode pattern,
          GroundData.encode value, GroundData.encode (bindingsData final)]), .matchValue ?_⟩
      exact ⟨initial, pattern, value, hole, AtomMatching.onAtoms .value initial pattern value,
        rfl, (AtomMatching.onAtoms_exact _ _ _ _ _).mp rfl, rfl⟩
  | matchBinding initial pattern value hole =>
      refine ⟨(AtomMatching.onAtoms .binding initial pattern value).toList.map (fun final =>
        [GroundData.encode (bindingsData initial), GroundData.encode pattern,
          GroundData.encode value, GroundData.encode (bindingsData final)]), .matchBinding ?_⟩
      exact ⟨initial, pattern, value, hole, AtomMatching.onAtoms .binding initial pattern value,
        rfl, (AtomMatching.onAtoms_exact _ _ _ _ _).mp rfl, rfl⟩

theorem inputs_iff_source (relation : String) (arguments : List Pattern) :
    Inputs relation arguments ↔ ∃ rows, Source relation arguments rows :=
  ⟨inputs_have_source, fun ⟨_, source⟩ => source_inputs source⟩

/-- Unknown means missing source admission. A completed negative source
decision remains a successful empty table. -/
theorem rows_unknown_exact (relation : String) (arguments : List Pattern) :
    rows? relation arguments = none ↔ ¬ Inputs relation arguments := by
  constructor
  · intro unknown admitted
    obtain ⟨rows, source⟩ := inputs_have_source admitted
    have completed := (rows_exact relation arguments rows).mpr source
    rw [unknown] at completed
    contradiction
  · intro outside
    cases computed : rows? relation arguments with
    | none => rfl
    | some rows => exact (outside (source_inputs ((rows_exact _ _ _).mp computed))).elim

/-- The shared dynamic provider carries original source relations and concrete
operations. It is not an external whole-program correctness callback. -/
def provider : DynamicProvider where
  Source := Source
  rows? := rows?
  rows_exact := rows_exact

/-- Service signatures are explicit data. Ground carrier admission is a
separate requirement of the caller's source language. -/
def signatures : List Signature :=
  [⟨"metta-atom-fresh-v1", [.base "GroundAtom", .base "GroundAtom"], [.input, .input]⟩,
   ⟨"petta-match-value-v1", [.base "GroundAtom", .base "GroundAtom", .base "GroundAtom", .base "GroundAtom"],
      [.input, .input, .input, .output]⟩,
   ⟨"petta-match-binding-v1", [.base "GroundAtom", .base "GroundAtom", .base "GroundAtom", .base "GroundAtom"],
      [.input, .input, .input, .output]⟩]

def registration : ProviderSnapshot where
  signatures := signatures
  rows := []
  dynamicRelations := ["metta-atom-fresh-v1", "petta-match-value-v1", "petta-match-binding-v1"]

/-- Exactly the input positions of the declared primitive are source Atoms;
the output schema of either matcher is deliberately not an input value. -/
def inputPatterns (relation : String) (arguments : List Pattern) : List Pattern :=
  if relation = "metta-atom-fresh-v1" then arguments
  else if relation = "petta-match-value-v1" ∨ relation = "petta-match-binding-v1"
    then arguments.take 3
  else []

def checkSourceCarrier (pattern : Pattern) : Bool :=
  Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType
    Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.dataLanguage
    (fun _ => none) [] pattern (.base "GroundAtom")

/-- Primitive source authority earns the actual declared builtin carrier
check. It does not assert constructor-only structural sorting. -/
theorem source_inputs_carrier {relation : String} {arguments : List Pattern}
    {rows : List (List Pattern)} (source : Source relation arguments rows) :
    (inputPatterns relation arguments).all checkSourceCarrier = true := by
  cases source with
  | freshness fresh =>
      cases fresh with
      | held image _ =>
          subst arguments
          simp [inputPatterns, checkSourceCarrier,
            Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.encode_checked]
      | failed image _ =>
          subst arguments
          simp [inputPatterns, checkSourceCarrier,
            Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.encode_checked]
  | matchValue source =>
      obtain ⟨initial, pattern, value, hole, outcome, image, _, _⟩ := source
      subst arguments
      simp [inputPatterns, checkSourceCarrier,
        Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.encode_checked]
  | matchBinding source =>
      obtain ⟨initial, pattern, value, hole, outcome, image, _, _⟩ := source
      subst arguments
      simp [inputPatterns, checkSourceCarrier,
        Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.encode_checked]

/-- Every returned cell is original encoded Atom data. In particular, the
new matching substitution is encoded by the existing source substitution wire. -/
theorem source_rows_carrier {relation : String} {arguments : List Pattern}
    {rows : List (List Pattern)} (source : Source relation arguments rows) :
    rows.all (fun row => row.all checkSourceCarrier) = true := by
  cases source with
  | freshness fresh =>
      cases fresh with
      | held image _ =>
          subst arguments
          simp [checkSourceCarrier,
            Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.encode_checked]
      | failed _ _ => rfl
  | matchValue source =>
      obtain ⟨initial, pattern, value, _, outcome, _, _, rfl⟩ := source
      cases outcome <;> simp [checkSourceCarrier,
        Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.encode_checked]
  | matchBinding source =>
      obtain ⟨initial, pattern, value, _, outcome, _, _, rfl⟩ := source
      cases outcome <;> simp [checkSourceCarrier,
        Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.encode_checked]

end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands

/-- Finite command state reuses the original machine packet. Control and
frames in this storage packet are unobserved by the command-store readout;
evaluation actions below retain their actual control and frames separately. -/
structure StateCode where
  packet : ProgramReplay.Snapshot
  bindings : Subst := []
  current : NamedSpaces.Handle := .self
  fuel : Nat
  revision : Nat := 0
  deriving Repr, DecidableEq

namespace StateCode

def decode (code : StateCode) : State where
  store := code.packet.decode.state
  bindings := code.bindings
  current := code.current
  fuel := code.fuel
  revision := code.revision
  input := code.packet.input
  output := code.packet.output

def configuration (state : State) : Eval.Configuration where
  state := state.store
  control := .returned []
  input := state.input
  output := state.output

def encode (names : List String) (state : State) : StateCode where
  packet := ProgramReplay.snapshot names (configuration state)
  bindings := state.bindings
  current := state.current
  fuel := state.fuel
  revision := state.revision

theorem encode_decode (names : List String) (state : State)
    (covers : ∀ name, name ∉ names → state.store.cells name = none)
    (vacant : NamedSpaces.Store.EmptyTail state.store []) :
    (encode names state).decode = state := by
  have exact := ProgramReplay.snapshot_decode names (configuration state) covers vacant
  simp only [decode, encode]
  rw [exact]
  cases state
  rfl

def normalizedPacket (code : StateCode) : ProgramReplay.Snapshot :=
  {code.packet with control := .returned [], frames := []}

def same (first second : StateCode) : Bool :=
  ProgramReplay.Snapshot.same first.normalizedPacket second.normalizedPacket &&
    decide (first.bindings = second.bindings ∧ first.current = second.current ∧
      first.fuel = second.fuel ∧ first.revision = second.revision)

theorem same_exact (first second : StateCode) :
    same first second = true ↔ first.decode = second.decode := by
  simp only [same, Bool.and_eq_true, ProgramReplay.Snapshot.same_exact, decide_eq_true_eq]
  cases first with
  | mk firstPacket firstBindings firstCurrent firstFuel firstRevision =>
      cases second with
      | mk secondPacket secondBindings secondCurrent secondFuel secondRevision =>
          simp only [normalizedPacket, ProgramReplay.Snapshot.decode, decode,
            State.mk.injEq, Eval.Configuration.mk.injEq]
          aesop

end StateCode

/-- Every action packet is finite data. An evaluation packet carries the
original pending machine rather than a claimed answer to its computation. -/
inductive ActionCode where
  | done (answers : List Atom)
  | evaluate (configuration : ProgramReplay.Snapshot)
  | importModule (target : NamedSpaces.Handle) (module : Atom)
  | retained (original : Command)
  | fault (reason : Effects.Fault)
  deriving Repr, DecidableEq

namespace ActionCode

def decode : ActionCode → Action
  | .done answers => .done answers
  | .evaluate configuration => .evaluate configuration.decode
  | .importModule target module => .importModule target module
  | .retained original => .retained original
  | .fault reason => .fault reason

def encode (names : List String) : Action → ActionCode
  | .done answers => .done answers
  | .evaluate configuration => .evaluate (ProgramReplay.snapshot names configuration)
  | .importModule target module => .importModule target module
  | .retained original => .retained original
  | .fault reason => .fault reason

def same : ActionCode → ActionCode → Bool
  | .done first, .done second => decide (first = second)
  | .evaluate first, .evaluate second => ProgramReplay.Snapshot.same first second
  | .importModule firstTarget firstModule, .importModule secondTarget secondModule =>
      decide (firstTarget = secondTarget ∧ firstModule = secondModule)
  | .retained first, .retained second => decide (first = second)
  | .fault first, .fault second => decide (first = second)
  | _, _ => false

@[simp] theorem same_exact (first second : ActionCode) :
    same first second = true ↔ first.decode = second.decode := by
  cases first <;> cases second <;>
    simp only [same, decode, ProgramReplay.Snapshot.same_exact, decide_eq_true_eq,
      reduceCtorEq, Action.done.injEq, Action.evaluate.injEq, Action.importModule.injEq,
      Action.retained.injEq, Action.fault.injEq]

/-- The source evaluation action gives the exact configuration whose store
support is already retained by the incoming finite packet. -/
theorem encode_decode_of_dispatch {command : Command} {before after : State}
    {action : Action} (source : Dispatch command before after action)
    (names : List String)
    (covers : ∀ name, name ∉ names → before.store.cells name = none)
    (vacant : NamedSpaces.Store.EmptyTail before.store []) :
    (encode names action).decode = action := by
  cases action with
  | done answers => rfl
  | importModule target module => rfl
  | retained original => rfl
  | fault reason => rfl
  | evaluate configuration =>
      obtain ⟨term, _, _, same⟩ := source.evaluation_origin
      subst configuration
      change Action.evaluate (ProgramReplay.snapshot names (before.evalConfiguration term)).decode = _
      rw [ProgramReplay.snapshot_decode names (before.evalConfiguration term) covers vacant]

end ActionCode

structure Result where
  after : StateCode
  action : ActionCode
  deriving Repr, DecidableEq

/-- Run the actual source dispatcher and retain its allocated space rows and
supported cells using the existing machine codec. -/
def run (command : Command) (before : StateCode) : Result :=
  let result := dispatch command before.decode
  ⟨StateCode.encode before.packet.cellNames result.1,
    ActionCode.encode before.packet.cellNames result.2⟩

/-- The realized command has the independently stated source derivation.
The proof charges no resource class to the functions executed here. -/
theorem run_source (command : Command) (before : StateCode) :
    Dispatch command before.decode (run command before).after.decode (run command before).action.decode := by
  have source := dispatch_sound command before.decode
  have covers : ∀ name, name ∉ before.packet.cellNames →
      (dispatch command before.decode).1.store.cells name = none := by
    intro name missing
    rw [source.cells]
    exact before.packet.decode_cell_support name missing
  have afterExact := StateCode.encode_decode before.packet.cellNames
    (dispatch command before.decode).1 covers (source.emptyTail before.packet.decode_empty_tail)
  have actionExact := ActionCode.encode_decode_of_dispatch source before.packet.cellNames
    before.packet.decode_cell_support before.packet.decode_empty_tail
  simpa only [run, afterExact, actionExact] using source

/-- A raw article may choose any finite representation of the same source
endpoint. Physical support-row order is not an extra language premise. -/
def check (command : Command) (before after : StateCode) (action : ActionCode) : Bool :=
  StateCode.same (run command before).after after && ActionCode.same (run command before).action action

@[simp] theorem check_exact (command : Command) (before after : StateCode) (action : ActionCode) :
    check command before after action = true ↔ Dispatch command before.decode after.decode action.decode := by
  simp only [check, Bool.and_eq_true, StateCode.same_exact, ActionCode.same_exact]
  constructor
  · rintro ⟨state, actionSame⟩
    have source := run_source command before
    rw [state, actionSame] at source
    exact source
  · intro source
    have observed := dispatch_complete (run_source command before)
    have original := dispatch_complete source
    have pairSame := observed.symm.trans original
    exact Prod.mk.inj pairSame

/-- Every independent source command step from a represented state has an
accepted finite article with exactly its source endpoint and continuation. -/
theorem source_has_article {command : Command} {before : StateCode} {after : State} {action : Action}
    (source : Dispatch command before.decode after action) :
    ∃ output : Result, check command before output.after output.action = true ∧
      output.after.decode = after ∧ output.action.decode = action := by
  refine ⟨run command before, (check_exact _ _ _ _).mpr (run_source _ _), ?_⟩
  have represented := dispatch_complete (run_source command before)
  have original := dispatch_complete source
  exact Prod.mk.inj (represented.symm.trans original)

end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands



set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchSourceGuard)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (Signature signature?)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

/-- Malformed evidence or a completed negative decision is refused. An
unavailable native primitive retains a different observable outcome. -/
inductive Result (α : Type) where
  | accepted (value : α)
  | refused
  | unavailable (relation : String)
  deriving Repr, DecidableEq

namespace Result

def bind {α β : Type} (result : Result α) (next : α → Result β) : Result β :=
  match result with
  | .accepted value => next value
  | .refused => .refused
  | .unavailable relation => .unavailable relation

def ofOption {α : Type} : Option α → Result α
  | some value => .accepted value
  | none => .refused

@[simp] theorem bind_accepted {α β : Type} (result : Result α) (next : α → Result β)
    (value : β) : bind result next = .accepted value ↔
      ∃ input, result = .accepted input ∧ next input = .accepted value := by
  cases result <;> simp [bind]

@[simp] theorem ofOption_accepted {α : Type} (input : Option α) (value : α) :
    ofOption input = .accepted value ↔ input = some value := by
  cases input <;> simp [ofOption]

end Result

/-- Source tuple positions are checked directly. A relation tuple cannot be
used with a builtin origin, or vice versa. -/
def tuple? (rows : List Atom) (kind relation : String) (index : Nat) : Option (List Atom) :=
  match rows[index]? with
  | some (.expression (.symbol actualKind :: .symbol actualRelation :: values)) =>
      if actualKind = kind ∧ actualRelation = relation then some values else none
  | _ => none

@[simp] theorem tuple?_exact (rows : List Atom) (kind relation : String) (index : Nat)
    (values : List Atom) : tuple? rows kind relation index = some values ↔
      rows[index]? = some (.expression (.symbol kind :: .symbol relation :: values)) := by
  unfold tuple?
  split
  next actualKind actualRelation actualValues found =>
    split
    next same =>
      rcases same with ⟨rfl, rfl⟩
      simp [found]
    next different =>
      constructor
      · intro impossible; cases impossible
      · intro same
        rw [found] at same
        cases same
        exact (different ⟨rfl, rfl⟩).elim
  next different =>
    constructor
    · intro impossible; cases impossible
    · intro found
      exact (different _ _ _ found).elim

def runQuery (environment : Environment) (relation : String) (arguments : List Atom)
    (initial : Subst) (origin : Origin) : Result Subst :=
  match origin with
  | .relation index =>
      (Result.ofOption (tuple? environment.rows "relation!" relation index)).bind fun values =>
        Result.ofOption (SpaceSemantics.matchValue initial (.expression arguments) (.expression values))
  | .builtin index =>
      (Result.ofOption (tuple? environment.rows "builtin!" relation index)).bind fun values =>
        Result.ofOption (SpaceSemantics.matchValue initial (.expression arguments) (.expression values))
  | .native index =>
      if relation ∈ environment.registration.dynamicRelations then
        match signature? environment.registration relation arguments.length with
        | none => .unavailable relation
        | some signature =>
            (Result.ofOption (resolveInputs initial arguments signature.modes)).bind fun resolved =>
              match environment.dynamic.rows? relation resolved with
              | none => .unavailable relation
              | some rows =>
                  (Result.ofOption rows[index]?).bind fun values =>
                    (Result.ofOption (GroundData.decodeList values)).bind fun atoms =>
                      Result.ofOption (matchArguments initial arguments atoms signature.modes)
      else .unavailable relation

@[simp] theorem runQuery_exact (environment : Environment) (relation : String)
    (arguments : List Atom) (initial : Subst) (origin : Origin) (final : Subst) :
    runQuery environment relation arguments initial origin = .accepted final ↔
      QueryHolds environment relation arguments initial origin final := by
  cases origin with
  | relation index =>
      simp only [runQuery, Result.bind_accepted, Result.ofOption_accepted, tuple?_exact,
        SpaceSemantics.matchValue_exact]
      constructor
      · rintro ⟨values, found, matched⟩
        exact .relation found matched
      · intro source
        cases source with
        | relation found matched => exact ⟨_, found, matched⟩
  | builtin index =>
      simp only [runQuery, Result.bind_accepted, Result.ofOption_accepted, tuple?_exact,
        SpaceSemantics.matchValue_exact]
      constructor
      · rintro ⟨values, found, matched⟩
        exact .builtin found matched
      · intro source
        cases source with
        | builtin found matched => exact ⟨_, found, matched⟩
  | native index =>
      constructor
      · intro computed
        simp only [runQuery] at computed
        split at computed
        next registered =>
          split at computed
          next => contradiction
          next signature declared =>
            obtain ⟨resolved, inputs, computed⟩ := (Result.bind_accepted _ _ _).mp computed
            have resolvedSource := (resolveInputs_exact _ _ _ _).mp
              ((Result.ofOption_accepted _ _).mp inputs)
            split at computed
            next => contradiction
            next rows available =>
              obtain ⟨values, selected, computed⟩ := (Result.bind_accepted _ _ _).mp computed
              obtain ⟨atoms, decoded, computed⟩ := (Result.bind_accepted _ _ _).mp computed
              have image := GroundData.encodeList_of_decodeList
                ((Result.ofOption_accepted _ _).mp decoded)
              apply QueryHolds.native (values := atoms) registered declared resolvedSource
                ((environment.dynamic.rows_exact _ _ _).mp available)
              · simpa only [image] using (Result.ofOption_accepted _ _).mp selected
              · exact (matchArguments_exact _ _ _ _ _).mp
                  ((Result.ofOption_accepted _ _).mp computed)
        next => contradiction
      · intro source
        cases source with
        | native registered declared inputs provided selected matched =>
            simp only [runQuery, registered, ↓reduceIte, declared, Result.bind_accepted,
              Result.ofOption_accepted]
            refine ⟨_, (resolveInputs_exact _ _ _ _).mpr inputs, ?_⟩
            rw [(environment.dynamic.rows_exact _ _ _).mpr provided]
            simp only [Result.bind_accepted, Result.ofOption_accepted]
            exact ⟨_, selected, _, GroundData.decodeList_encodeList _,
              (matchArguments_exact _ _ _ _ _).mpr matched⟩


mutual
  def runRoot (environment : Environment) : Evidence → Atom → Result Atom
    | .firing index proof, subject =>
        (Result.ofOption environment.rows[index]?).bind fun atom =>
          (Result.ofOption (readClause? atom)).bind fun (left, right, guards) =>
            (Result.ofOption (SpaceSemantics.matchValue [] left subject)).bind fun initial =>
              (runPremises environment proof guards initial).bind fun final =>
                .accepted (applySubst final right)
    | _, _ => .refused

  def runPremise (environment : Environment) : Evidence → Atom → Subst → Result Subst
    | .fresh, guard, initial =>
        match guard with
        | .expression [.symbol "fresh", .var name, subject] =>
            if matchSourceGuard initial (.freshness name subject) then .accepted initial else .refused
        | _ => .refused
    | .child proof, guard, initial =>
        match guard with
        | .expression [.symbol "==", source, target] =>
            (runRoot environment proof (applySubst initial source)).bind fun result =>
              Result.ofOption (SpaceSemantics.matchValue initial target result)
        | _ => .refused
    | .query origin, guard, initial =>
        match guard with
        | .expression (.symbol relation :: arguments) =>
            if relation ≠ "fresh" ∧ relation ≠ "==" then
              runQuery environment relation arguments initial origin else .refused
        | _ => .refused
    | _, _, _ => .refused

  def runPremises (environment : Environment) : Evidence → List Atom → Subst → Result Subst
    | .empty, [], initial => .accepted initial
    | .cons head tail, guard :: guards, initial =>
        (runPremise environment head guard initial).bind fun middle =>
          runPremises environment tail guards middle
    | _, _, _ => .refused
end


mutual
  theorem runRoot_sound {environment : Environment} {evidence : Evidence} {subject target : Atom}
      (checked : runRoot environment evidence subject = .accepted target) :
      RootFiring environment evidence subject target := by
    cases evidence with
    | firing index proof =>
        simp only [runRoot, Result.bind_accepted, Result.ofOption_accepted,
          Result.accepted.injEq] at checked
        obtain ⟨atom, positioned, ⟨⟨left, right, guards⟩, declared,
          ⟨initial, matched, ⟨final, premises, emitted⟩⟩⟩⟩ := checked
        exact .rule ⟨atom, positioned, (readClause?_exact _ _ _ _).mp declared⟩
          (SpaceSemantics.matchValue_sound matched) (runPremises_sound premises) emitted.symm
    | empty | cons _ _ | fresh | child _ | query _ => simp [runRoot] at checked
  termination_by evidence

  theorem runPremise_sound {environment : Environment} {evidence : Evidence}
      {guard : Atom} {initial final : Subst}
      (checked : runPremise environment evidence guard initial = .accepted final) :
      PremiseHolds environment evidence guard initial final := by
    cases evidence with
    | fresh =>
        simp only [runPremise] at checked
        split at checked
        next name subject =>
          split at checked
          next held =>
            cases Result.accepted.inj checked
            exact .fresh ((Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard_exact _ _).mp held)
          next => contradiction
        next => contradiction
    | child proof =>
        simp only [runPremise] at checked
        split at checked
        next source target =>
          obtain ⟨result, fired, matched⟩ := (Result.bind_accepted _ _ _).mp checked
          exact .child (runRoot_sound fired)
            (SpaceSemantics.matchValue_sound ((Result.ofOption_accepted _ _).mp matched))
        next => contradiction
    | query origin =>
        simp only [runPremise] at checked
        split at checked
        next relation arguments =>
          split at checked
          next admitted =>
            exact .query admitted.1 admitted.2 ((runQuery_exact _ _ _ _ _ _).mp checked)
          next => contradiction
        next => contradiction
    | firing _ _ | empty | cons _ _ => simp [runPremise] at checked
  termination_by evidence

  theorem runPremises_sound {environment : Environment} {evidence : Evidence}
      {guards : List Atom} {initial final : Subst}
      (checked : runPremises environment evidence guards initial = .accepted final) :
      PremisesHold environment evidence guards initial final := by
    cases evidence with
    | empty =>
        cases guards with
        | nil => cases Result.accepted.inj checked; exact .nil
        | cons _ _ => simp [runPremises] at checked
    | cons head tail =>
        cases guards with
        | nil => simp [runPremises] at checked
        | cons guard guards =>
            obtain ⟨middle, held, rest⟩ := (Result.bind_accepted _ _ _).mp checked
            exact .cons (runPremise_sound held) (runPremises_sound rest)
    | firing _ _ | fresh | child _ | query _ => simp [runPremises] at checked
  termination_by evidence
end

private theorem completeRule {environment : Environment} {index : Nat} {proof : Evidence}
    {left right subject target : Atom} {guards : List Atom} {initial final : Subst}
    (stored : ClauseAt environment.rows index left right guards)
    (matched : SpaceSemantics.ValueMatch [] left subject initial)
    (emitted : target = applySubst final right)
    (ih : runPremises environment proof guards initial = .accepted final) :
    runRoot environment (.firing index proof) subject = .accepted target := by
  obtain ⟨atom, positioned, declared⟩ := stored
  simp only [runRoot, positioned, Result.ofOption, Result.bind, (readClause?_exact _ _ _ _).mpr declared,
    SpaceSemantics.matchValue_complete matched, ih, emitted]

private theorem completeFresh {environment : Environment} {name : String} {subject : Atom}
    {initial : Subst}
    (held : Mettapedia.Languages.ProcessCalculi.MORK.SourceGuardHolds initial (.freshness name subject)) :
    runPremise environment .fresh
      (.expression [.symbol "fresh", .var name, subject]) initial = .accepted initial := by
  simp [runPremise, (Mettapedia.Languages.ProcessCalculi.MORK.matchSourceGuard_exact _ _).mpr held]

private theorem completeChild {environment : Environment} {proof : Evidence} {source target result : Atom}
    {initial final : Subst} (matched : SpaceSemantics.ValueMatch initial target result final)
    (ih : runRoot environment proof (applySubst initial source) = .accepted result) :
    runPremise environment (.child proof)
      (.expression [.symbol "==", source, target]) initial = .accepted final := by
  simp only [runPremise, ih, Result.bind, SpaceSemantics.matchValue_complete matched, Result.ofOption]

private theorem completeQuery {environment : Environment} {relation : String}
    {arguments : List Atom} {initial final : Subst} {origin : Origin}
    (ordinary : relation ≠ "fresh") (directed : relation ≠ "==")
    (queried : QueryHolds environment relation arguments initial origin final) :
    runPremise environment (.query origin)
      (.expression (.symbol relation :: arguments)) initial = .accepted final := by
  simp only [runPremise]
  rw [if_pos ⟨ordinary, directed⟩, (runQuery_exact _ _ _ _ _ _).mpr queried]

private theorem completeCons {environment : Environment} {head tail : Evidence}
    {guard : Atom} {guards : List Atom} {initial middle final : Subst}
    (ihHead : runPremise environment head guard initial = .accepted middle)
    (ihTail : runPremises environment tail guards middle = .accepted final) :
    runPremises environment (.cons head tail) (guard :: guards) initial = .accepted final := by
  simp only [runPremises, ihHead, Result.bind, ihTail]

/-- Source proof provenance is retained exactly: the checker accepts this
article if and only if this same article has the independent source judgment. -/
theorem runRoot_complete {environment : Environment} {evidence : Evidence} {subject target : Atom}
    (source : RootFiring environment evidence subject target) :
    runRoot environment evidence subject = .accepted target :=
  RootFiring.rec
    (motive_1 := fun evidence subject target _ =>
      runRoot environment evidence subject = .accepted target)
    (motive_2 := fun evidence guard initial final _ =>
      runPremise environment evidence guard initial = .accepted final)
    (motive_3 := fun evidence guards initial final _ =>
      runPremises environment evidence guards initial = .accepted final)
    (fun stored matched _ emitted ih => completeRule stored matched emitted ih)
    completeFresh (fun _ matched ih => completeChild matched ih) completeQuery
    rfl (fun _ _ ihHead ihTail => completeCons ihHead ihTail) source

theorem runPremise_complete {environment : Environment} {evidence : Evidence}
    {guard : Atom} {initial final : Subst}
    (source : PremiseHolds environment evidence guard initial final) :
    runPremise environment evidence guard initial = .accepted final :=
  PremiseHolds.rec
    (motive_1 := fun evidence subject target _ =>
      runRoot environment evidence subject = .accepted target)
    (motive_2 := fun evidence guard initial final _ =>
      runPremise environment evidence guard initial = .accepted final)
    (motive_3 := fun evidence guards initial final _ =>
      runPremises environment evidence guards initial = .accepted final)
    (fun stored matched _ emitted ih => completeRule stored matched emitted ih)
    completeFresh (fun _ matched ih => completeChild matched ih) completeQuery
    rfl (fun _ _ ihHead ihTail => completeCons ihHead ihTail) source

theorem runPremises_complete {environment : Environment} {evidence : Evidence}
    {guards : List Atom} {initial final : Subst}
    (source : PremisesHold environment evidence guards initial final) :
    runPremises environment evidence guards initial = .accepted final :=
  PremisesHold.rec
    (motive_1 := fun evidence subject target _ =>
      runRoot environment evidence subject = .accepted target)
    (motive_2 := fun evidence guard initial final _ =>
      runPremise environment evidence guard initial = .accepted final)
    (motive_3 := fun evidence guards initial final _ =>
      runPremises environment evidence guards initial = .accepted final)
    (fun stored matched _ emitted ih => completeRule stored matched emitted ih)
    completeFresh (fun _ matched ih => completeChild matched ih) completeQuery
    rfl (fun _ _ ihHead ihTail => completeCons ihHead ihTail) source

@[simp] theorem runRoot_exact (environment : Environment) (evidence : Evidence) (subject target : Atom) :
    runRoot environment evidence subject = .accepted target ↔
      RootFiring environment evidence subject target :=
  ⟨runRoot_sound, runRoot_complete⟩

@[simp] theorem runPremise_exact (environment : Environment) (evidence : Evidence)
    (guard : Atom) (initial final : Subst) :
    runPremise environment evidence guard initial = .accepted final ↔
      PremiseHolds environment evidence guard initial final :=
  ⟨runPremise_sound, runPremise_complete⟩

@[simp] theorem runPremises_exact (environment : Environment) (evidence : Evidence)
    (guards : List Atom) (initial final : Subst) :
    runPremises environment evidence guards initial = .accepted final ↔
      PremisesHold environment evidence guards initial final :=
  ⟨runPremises_sound, runPremises_complete⟩

@[simp] theorem derivable_iff_accepted (environment : Environment) (subject target : Atom) :
    Derives environment subject target ↔
      ∃ evidence, runRoot environment evidence subject = .accepted target := by
  simp only [Derives, runRoot_exact]

/-- Unavailability is retained through any finite continuation. It never
becomes a completed empty or an accepted root. -/
theorem unavailable_propagates {α β : Type} (relation : String) (next : α → Result β) :
    (Result.unavailable relation).bind next = .unavailable relation := rfl

open Mettapedia.GSLT.LanguageDef.SemanticEvidence

/-- Actual independently judged source articles, retaining physical source
occurrences and finite recursive child evidence. -/
def guest (environment : Environment) : NativeProofSystem (Atom × Atom) where
  ProofObject := Evidence
  Judges evidence claim := RootFiring environment evidence claim.1 claim.2

def kernel (environment : Environment) : NativeProofKernel (guest environment) where
  decide claim evidence := decide (runRoot environment evidence claim.1 = .accepted claim.2)
  correct claim evidence := by
    dsimp only [guest] at evidence ⊢
    simp only [decide_eq_true_eq, runRoot_exact]

/-- The primary certificate language is the independently judged source proof
language, with its entire fibre preserved. -/
def certificateEquivalence (environment : Environment) :
    CertificateEquivalence (kernel environment).toChecker (guest environment) :=
  (kernel environment).certificateEquivalence



/-- Successful conditional callable preparation emits the original body
continuation, retaining its assignment and syntax-sensitive source form. -/
def runCall (environment : Environment) (evidence : Evidence) (head : String)
    (values : List Atom) : Result (Nat × Eval.Control) :=
  match evidence with
  | .firing index proof =>
      (Result.ofOption environment.rows[index]?).bind fun atom =>
        (Result.ofOption (readRule? atom)).bind fun (equation, guards) =>
          if equation.head = head then
            (Result.ofOption (SpaceSemantics.matchValue []
              (.expression equation.arguments) (.expression values))).bind fun initial =>
              (runPremises environment proof guards initial).bind fun final =>
                .accepted (index, .evaluate final equation.body)
          else .refused
  | _ => .refused

theorem runCall_sound {environment : Environment} {evidence : Evidence} {head : String}
    {values : List Atom} {index : Nat} {control : Eval.Control}
    (checked : runCall environment evidence head values = .accepted (index, control)) :
    CallReady environment head values evidence index control := by
  cases evidence with
  | firing declaration proof =>
      simp only [runCall, Result.bind_accepted, Result.ofOption_accepted] at checked
      obtain ⟨atom, positioned, ⟨⟨equation, guards⟩, declared, checked⟩⟩ := checked
      split at checked
      next named =>
        obtain ⟨initial, matched, continued⟩ := (Result.bind_accepted _ _ _).mp checked
        obtain ⟨final, held, same⟩ := (Result.bind_accepted _ _ _).mp continued
        have equality := Result.accepted.inj same
        cases equality
        exact .guarded (.matched ⟨atom, positioned, (readRule?_exact _ _ _).mp declared⟩
          named (SpaceSemantics.matchValue_sound ((Result.ofOption_accepted _ _).mp matched)))
          (runPremises_sound held)
      next => contradiction
  | empty | cons _ _ | fresh | child _ | query _ => simp [runCall] at checked

theorem runCall_complete {environment : Environment} {evidence : Evidence} {head : String}
    {values : List Atom} {index : Nat} {control : Eval.Control}
    (source : CallReady environment head values evidence index control) :
    runCall environment evidence head values = .accepted (index, control) := by
  cases source with
  | guarded selected premises =>
      cases selected with
      | matched stored named matched =>
          obtain ⟨atom, positioned, declared⟩ := stored
          simp only [runCall, positioned, Result.ofOption, Result.bind,
            (readRule?_exact _ _ _).mpr declared, named, ↓reduceIte,
            SpaceSemantics.matchValue_complete matched, runPremises_complete premises]

@[simp] theorem runCall_exact (environment : Environment) (evidence : Evidence) (head : String)
    (values : List Atom) (index : Nat) (control : Eval.Control) :
    runCall environment evidence head values = .accepted (index, control) ↔
      CallReady environment head values evidence index control :=
  ⟨runCall_sound, runCall_complete⟩

/-- No body rewriting is performed while preparing an ordinary source
clause: this is exactly the actual evaluator's existing continuation. -/
theorem original_equation_checked {environment : Environment} {index : Nat} {head : String}
    {arguments values : List Atom} {body : Atom} {bindings : Subst}
    (stored : environment.rows[index]? =
      some (.expression [.symbol "=", .expression (.symbol head :: arguments), body]))
    (matched : SpaceSemantics.ValueMatch [] (.expression arguments) (.expression values) bindings) :
    runCall environment (.firing index .empty) head values = .accepted (index, .evaluate bindings body) :=
  runCall_complete (original_equation_ready stored matched)

end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional


namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional.Wire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open ConfigurationEncoding (index readIndex readIndex_index)
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional

/-- Article coordinates reuse the actual configuration packet's natural-number
reader. Negative integers and symbolic numerals are not occurrence indices. -/
private theorem index_of_readIndex {atom : Atom} {value : Nat}
    (read : readIndex atom = some value) : index value = atom := by
  unfold readIndex at read
  split at read
  next number =>
    split at read
    next nonnegative =>
      cases Option.some.inj read
      simp only [index, Int.toNat_of_nonneg nonnegative]
    next => contradiction
  next => contradiction

def originData : Origin → Atom
  | .relation occurrence => .expression [.symbol "metta-proof-relation-v1", index occurrence]
  | .builtin occurrence => .expression [.symbol "metta-proof-builtin-v1", index occurrence]
  | .native occurrence => .expression [.symbol "metta-proof-native-v1", index occurrence]

def readOrigin : Atom → Option Origin
  | .expression [.symbol "metta-proof-relation-v1", occurrence] => .relation <$> readIndex occurrence
  | .expression [.symbol "metta-proof-builtin-v1", occurrence] => .builtin <$> readIndex occurrence
  | .expression [.symbol "metta-proof-native-v1", occurrence] => .native <$> readIndex occurrence
  | _ => none

@[simp] theorem readOrigin_originData (origin : Origin) :
    readOrigin (originData origin) = some origin := by
  cases origin <;> simp [originData, readOrigin]

theorem originData_of_readOrigin {atom : Atom} {origin : Origin}
    (read : readOrigin atom = some origin) : originData origin = atom := by
  unfold readOrigin at read
  split at read
  all_goals first
    | (obtain ⟨occurrence, decoded, same⟩ := Option.map_eq_some_iff.mp read
       subst origin
       simp only [originData, index_of_readIndex decoded])
    | contradiction

/-- This wire records the existing finite evidence tree and physical source
coordinates. It is a compressed computed-checker article: intermediate matcher
captures and substituted targets are not claimed to be explicit here. -/
def evidenceData : Evidence → Atom
  | .firing declaration premises =>
      .expression [.symbol "metta-proof-firing-v1", index declaration, evidenceData premises]
  | .empty => .symbol "metta-proof-empty-v1"
  | .cons head tail =>
      .expression [.symbol "metta-proof-cons-v1", evidenceData head, evidenceData tail]
  | .fresh => .symbol "metta-proof-fresh-v1"
  | .child proof => .expression [.symbol "metta-proof-child-v1", evidenceData proof]
  | .query origin => .expression [.symbol "metta-proof-query-v1", originData origin]

def readEvidence : Atom → Option Evidence
  | .expression [.symbol "metta-proof-firing-v1", declaration, premises] => do
      return .firing (← readIndex declaration) (← readEvidence premises)
  | .symbol "metta-proof-empty-v1" => some .empty
  | .expression [.symbol "metta-proof-cons-v1", head, tail] => do
      return .cons (← readEvidence head) (← readEvidence tail)
  | .symbol "metta-proof-fresh-v1" => some .fresh
  | .expression [.symbol "metta-proof-child-v1", proof] => .child <$> readEvidence proof
  | .expression [.symbol "metta-proof-query-v1", origin] => .query <$> readOrigin origin
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem readEvidence_evidenceData (evidence : Evidence) :
    readEvidence (evidenceData evidence) = some evidence := by
  induction evidence with
  | firing declaration premises ih => simp [evidenceData, readEvidence, ih]
  | empty => simp [evidenceData, readEvidence]
  | cons head tail headIH tailIH => simp [evidenceData, readEvidence, headIH, tailIH]
  | fresh => simp [evidenceData, readEvidence]
  | child proof ih => simp [evidenceData, readEvidence, ih]
  | query origin => simp [evidenceData, readEvidence]

theorem evidenceData_of_readEvidence {atom : Atom} {evidence : Evidence}
    (read : readEvidence atom = some evidence) : evidenceData evidence = atom := by
  unfold readEvidence at read
  split at read
  next declaration premises =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨index, readIndex, premisesProof, readPremises, same⟩ := read
    change some (Evidence.firing index premisesProof) = some evidence at same
    cases Option.some.inj same
    simp only [evidenceData, index_of_readIndex readIndex,
      evidenceData_of_readEvidence readPremises]
  next => cases Option.some.inj read; rfl
  next head tail =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨headProof, readHead, tailProof, readTail, same⟩ := read
    change some (Evidence.cons headProof tailProof) = some evidence at same
    cases Option.some.inj same
    simp only [evidenceData, evidenceData_of_readEvidence readHead,
      evidenceData_of_readEvidence readTail]
  next => cases Option.some.inj read; rfl
  next proof =>
    obtain ⟨childProof, readChild, same⟩ := Option.map_eq_some_iff.mp read
    subst evidence
    simp only [evidenceData, evidenceData_of_readEvidence readChild]
  next origin =>
    obtain ⟨sourceOrigin, readSource, same⟩ := Option.map_eq_some_iff.mp read
    subst evidence
    simp only [evidenceData, originData_of_readOrigin readSource]
  next => contradiction
termination_by sizeOf atom

@[simp] theorem readEvidence_exact (atom : Atom) (evidence : Evidence) :
    readEvidence atom = some evidence ↔ evidenceData evidence = atom :=
  ⟨evidenceData_of_readEvidence, fun same => same ▸ readEvidence_evidenceData evidence⟩

theorem evidenceData_injective : Function.Injective evidenceData := by
  intro first second same
  have decoded := congrArg readEvidence same
  rw [readEvidence_evidenceData, readEvidence_evidenceData] at decoded
  exact Option.some.inj decoded

def runRoot (environment : Environment) (article subject : Atom) : Result Atom :=
  (Result.ofOption (readEvidence article)).bind fun evidence =>
    Conditional.runRoot environment evidence subject

def runPremises (environment : Environment) (article : Atom) (guards : List Atom)
    (initial : Subst) : Result Subst :=
  (Result.ofOption (readEvidence article)).bind fun evidence =>
    Conditional.runPremises environment evidence guards initial

def runCall (environment : Environment) (article : Atom) (head : String)
    (values : List Atom) : Result (Nat × Eval.Control) :=
  (Result.ofOption (readEvidence article)).bind fun evidence =>
    Conditional.runCall environment evidence head values

@[simp] theorem runRoot_exact (environment : Environment) (article subject target : Atom) :
    runRoot environment article subject = .accepted target ↔
      ∃ evidence, evidenceData evidence = article ∧ RootFiring environment evidence subject target := by
  simp only [runRoot, Result.bind_accepted, Result.ofOption_accepted, readEvidence_exact,
    Conditional.runRoot_exact]

@[simp] theorem runPremises_exact (environment : Environment) (article : Atom)
    (guards : List Atom) (initial final : Subst) :
    runPremises environment article guards initial = .accepted final ↔
      ∃ evidence, evidenceData evidence = article ∧
        PremisesHold environment evidence guards initial final := by
  simp only [runPremises, Result.bind_accepted, Result.ofOption_accepted, readEvidence_exact,
    Conditional.runPremises_exact]

@[simp] theorem runCall_exact (environment : Environment) (article : Atom) (head : String)
    (values : List Atom) (declaration : Nat) (control : Eval.Control) :
    runCall environment article head values = .accepted (declaration, control) ↔
      ∃ evidence, evidenceData evidence = article ∧
        CallReady environment head values evidence declaration control := by
  simp only [runCall, Result.bind_accepted, Result.ofOption_accepted, readEvidence_exact,
    Conditional.runCall_exact]

theorem source_root_has_wire {environment : Environment} {evidence : Evidence}
    {subject target : Atom} (source : RootFiring environment evidence subject target) :
    runRoot environment (evidenceData evidence) subject = .accepted target :=
  (runRoot_exact _ _ _ _).mpr ⟨evidence, rfl, source⟩

theorem malformed_root_refused (environment : Environment) (article subject : Atom)
    (noImage : ∀ evidence, evidenceData evidence ≠ article) :
    runRoot environment article subject = .refused := by
  cases decoded : readEvidence article with
  | none => simp only [runRoot, decoded, Result.ofOption, Result.bind]
  | some evidence => exact (noImage evidence (evidenceData_of_readEvidence decoded)).elim


open Mettapedia.GSLT.LanguageDef.SemanticEvidence

def checker (environment : Environment) :
    Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker (Atom × Atom) Atom where
  check claim article := decide (runRoot environment article claim.1 = .accepted claim.2)

@[simp] theorem checker_exact (environment : Environment) (claim : Atom × Atom) (article : Atom) :
    (checker environment).check claim article = true ↔
      ∃ evidence, evidenceData evidence = article ∧
        RootFiring environment evidence claim.1 claim.2 := by
  simp only [checker, decide_eq_true_eq, runRoot_exact]

private theorem accepted_present {environment : Environment} {claim : Atom × Atom}
    (accepted : AcceptedCertificateFibre (checker environment) claim) :
    (readEvidence accepted.1).isSome := by
  obtain ⟨evidence, image, _⟩ := (checker_exact _ _ _).mp accepted.2
  rw [(readEvidence_exact _ _).mpr image]
  rfl

/-- An accepted packet is decoded by the actual option reader. Its accepted
proof rules out the missing branch; no chosen fallback proof is introduced. -/
def acceptedEvidence {environment : Environment} {claim : Atom × Atom}
    (accepted : AcceptedCertificateFibre (checker environment) claim) : Evidence :=
  (readEvidence accepted.1).get (accepted_present accepted)

theorem acceptedEvidence_read {environment : Environment} {claim : Atom × Atom}
    (accepted : AcceptedCertificateFibre (checker environment) claim) :
    readEvidence accepted.1 = some (acceptedEvidence accepted) :=
  (Option.some_get (accepted_present accepted)).symm

theorem acceptedEvidence_source {environment : Environment} {claim : Atom × Atom}
    (accepted : AcceptedCertificateFibre (checker environment) claim) :
    RootFiring environment (acceptedEvidence accepted) claim.1 claim.2 := by
  obtain ⟨evidence, image, source⟩ := (checker_exact _ _ _).mp accepted.2
  have same := Option.some.inj
    ((acceptedEvidence_read accepted).symm.trans ((readEvidence_exact _ _).mpr image))
  exact same ▸ source

/-- Raw primary articles preserve the full independent native proof fibre.
Canonical admission prevents junk fields or alternate coordinate spellings
from introducing extra accepted proofs. -/
def certificateEquivalence (environment : Environment) :
    CertificateEquivalence (checker environment) (Conditional.guest environment) where
  fibreEquiv claim := {
    toFun := fun accepted => ⟨acceptedEvidence accepted, acceptedEvidence_source accepted⟩
    invFun := fun proof =>
      ⟨evidenceData proof.1, (checker_exact _ _ _).mpr ⟨proof.1, rfl, proof.2⟩⟩
    left_inv := by
      intro accepted
      apply Subtype.ext
      exact evidenceData_of_readEvidence (acceptedEvidence_read accepted)
    right_inv := by
      intro proof
      apply Subtype.ext
      apply Option.some.inj
      exact (acceptedEvidence_read _).symm.trans (readEvidence_evidenceData proof.1) }

theorem authority (environment : Environment) :
    (checker environment).Authority (fun claim => Derives environment claim.1 claim.2) := by
  constructor
  · intro claim article accepted
    obtain ⟨evidence, _, source⟩ := (checker_exact _ _ _).mp accepted
    exact ⟨evidence, source⟩
  · intro claim derived
    obtain ⟨evidence, source⟩ := derived
    exact ⟨evidenceData evidence, (checker_exact _ _ _).mpr ⟨evidence, rfl, source⟩⟩

end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional.Wire


namespace Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional.ExpansionBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional

private def a : Atom := .symbol "a"
private def done : Atom := .symbol "done"
private def call (name : String) (args : List Atom) : Atom := .expression (.symbol name :: args)

/-- A concrete original Atom tree. Equal subtrees may share host pointers;
the source free-variable traversal still materializes every leaf occurrence. -/
def tree : Nat → Atom
  | 0 => .var "leaf"
  | n + 1 => .expression [tree n, tree n]

/-- One fixed original source theory, including a final freshness check on
an expanded intermediate whose value is then discarded. -/
def environment : Environment where
  rows := [call "=" [a, .var "leaf"],
    call "rule!" [a, .expression [.var "x", .var "x"], call "==" [a, .var "x"]],
    call "rule!" [done, a, call "==" [a, .var "x"], call "fresh" [.var "absent", .var "x"]]]

def article : Nat → Evidence
  | 0 => .firing 0 .empty
  | n + 1 => .firing 1 (.cons (.child (article n)) .empty)

def finalArticle (n : Nat) : Evidence :=
  .firing 2 (.cons (.child (article n)) (.cons .fresh .empty))

private theorem match_symbol (name : String) :
    SpaceSemantics.ValueMatch [] (.symbol name) (.symbol name) [] :=
  .atomic (by intro fields same; cases same) .symbol

private theorem match_capture (value : Atom) :
    SpaceSemantics.ValueMatch [] (.var "x") value [("x", value)] :=
  .atomic (by intro fields same; cases same) (.var_fresh rfl)

/-- Every compressed child article is an actual independently authorized
source derivation. No Boolean replay result defines its validity. -/
theorem article_source (n : Nat) : RootFiring environment (article n) a (tree n) := by
  induction n with
  | zero =>
      exact .rule ⟨_, rfl, .equation _ _⟩ (match_symbol _) .nil rfl
  | succ n ih =>
      apply RootFiring.rule (initial := []) (final := [("x", tree n)])
        ⟨_, rfl, .guarded _ _ _⟩ (match_symbol _)
      · exact .cons (.child (by simpa only [applySubst_nil] using ih) (match_capture _)) .nil
      · simp [tree, applySubst, applySubst.applySubstList, Subst.lookup]

/-- This is the length of the actual list returned by the original source
operation, not a fabricated execution clock or an asymptotic runtime claim. -/
theorem free_variable_occurrences (n : Nat) : (atomFreeVars (tree n)).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (atomFreeVars (tree n) ++ (atomFreeVars (tree n) ++ [])).length = _
      simp only [List.length_append, List.length_nil, Nat.add_zero, ih, pow_succ]
      omega

theorem free_variables_are_leaves (n : Nat) :
    ∀ name ∈ atomFreeVars (tree n), name = "leaf" := by
  induction n with
  | zero => simp [tree, atomFreeVars]
  | succ n ih =>
      intro name member
      change name ∈ atomFreeVars (tree n) ++ (atomFreeVars (tree n) ++ []) at member
      simp only [List.mem_append, List.not_mem_nil, or_false] at member
      exact member.elim (ih name) (ih name)

/-- The fixed small final sequent still requires the original freshness
operation on the intermediate tree. -/
theorem final_source (n : Nat) : RootFiring environment (finalArticle n) done a := by
  apply RootFiring.rule (initial := []) (final := [("x", tree n)])
    ⟨_, rfl, .guarded _ _ _⟩ (match_symbol _)
  · apply PremisesHold.cons
    · exact .child (by simpa only [applySubst_nil] using article_source n) (match_capture _)
    · apply PremisesHold.cons
      · apply PremiseHolds.fresh
        apply SourceGuardHolds.unbound
        · simp [Subst.lookup]
        · have absent : "absent" ∉ atomFreeVars (tree n) := by
            intro member
            have same := free_variables_are_leaves n "absent" member
            contradiction
          simpa [applySubst, Subst.lookup] using absent
      · exact .nil
  · rfl

/-- Original finite proof syntax grows linearly although an intermediate
original operation materializes exponentially many variable occurrences. -/
theorem article_size (n : Nat) : sizeOf (article n) = 5 * n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [article, Evidence.firing.sizeOf_spec, Evidence.cons.sizeOf_spec,
        Evidence.child.sizeOf_spec, Evidence.empty.sizeOf_spec, sizeOf_nat, ih]
      omega


theorem final_article_size (n : Nat) : sizeOf (finalArticle n) = 5 * n + 10 := by
  simp only [finalArticle, Evidence.firing.sizeOf_spec, Evidence.cons.sizeOf_spec,
    Evidence.child.sizeOf_spec, Evidence.empty.sizeOf_spec, Evidence.fresh.sizeOf_spec,
    sizeOf_nat, article_size]
  omega

/-- The canonical raw Atom article has affine structural size as well.
All physical indices and tag strings are fixed; this is not a host heap metric. -/
theorem article_wire_size : ∃ factor offset : Nat, ∀ n,
    sizeOf (Wire.evidenceData (article n)) = factor * n + offset := by
  let offset := sizeOf (Wire.evidenceData (article 0))
  let factor := sizeOf (Wire.evidenceData (article 1)) - offset
  refine ⟨factor, offset, ?_⟩
  intro n
  induction n with
  | zero => simp only [Nat.mul_zero, Nat.zero_add]; rfl
  | succ n ih =>
      dsimp only [factor, offset] at ih ⊢
      simp only [article, Wire.evidenceData, Atom.expression.sizeOf_spec,
        Atom.symbol.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec,
        Nat.mul_add, Nat.mul_one] at ih ⊢
      omega

/-- The full submitted proof has affine raw syntax size, including the
outer child and freshness evidence for the fixed final sequent. -/
theorem final_article_wire_size : ∃ factor offset : Nat, ∀ n,
    sizeOf (Wire.evidenceData (finalArticle n)) = factor * n + offset := by
  obtain ⟨factor, offset, size⟩ := article_wire_size
  let extra := sizeOf (Wire.evidenceData (finalArticle 0)) -
    sizeOf (Wire.evidenceData (article 0))
  refine ⟨factor, offset + extra, ?_⟩
  intro n
  have original := size n
  dsimp only [extra]
  simp only [finalArticle, article, Wire.evidenceData, Atom.expression.sizeOf_spec,
    Atom.symbol.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec] at original ⊢
  omega

/-- Charging only a linear amount per compressed proof constructor cannot
pay even for the original source freshness operation's materialized list.
This is a source-result metric, not a claimed physical machine clock. -/
theorem not_affine_free_variable_work :
    ¬ ∃ factor offset : Nat, ∀ n,
      (atomFreeVars (tree n)).length ≤ factor * sizeOf (finalArticle n) + offset := by
  rintro ⟨factor, offset, bounded⟩
  have actual := bounded (2 * (10 * factor + offset + 10))
  rw [free_variable_occurrences, final_article_size] at actual
  have lower := Nat.two_mul_sq_add_one_le_two_pow_two_mul (10 * factor + offset + 10)
  nlinarith

/-- The same obstruction holds for the canonical raw Atom article size.
The source rows, subject and claimed result are fixed across this family. -/
theorem not_affine_raw_free_variable_work :
    ¬ ∃ factor offset : Nat, ∀ n,
      (atomFreeVars (tree n)).length ≤
        factor * sizeOf (Wire.evidenceData (finalArticle n)) + offset := by
  obtain ⟨wireFactor, wireOffset, wireSize⟩ := final_article_wire_size
  rintro ⟨factor, offset, bounded⟩
  let coefficient := factor * wireFactor
  let constant := factor * wireOffset + offset
  have actual := bounded (2 * (coefficient + constant + 1))
  rw [free_variable_occurrences, wireSize] at actual
  have lower := Nat.two_mul_sq_add_one_le_two_pow_two_mul (coefficient + constant + 1)
  have simplified : 2 ^ (2 * (coefficient + constant + 1)) ≤
      coefficient * (2 * (coefficient + constant + 1)) + constant := by
    simpa only [coefficient, constant, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using actual
  nlinarith

theorem final_guard_occurrences (n : Nat) :
    (atomFreeVars (applySubst [("x", tree n)] (.var "x"))).length = 2 ^ n := by
  simpa [applySubst, Subst.lookup] using free_variable_occurrences n

/-- No fixed polynomial in the compressed original evidence size pays for
the actual materialized free-variable list in this accepted family. This
does not exclude a different efficient freshness/checking implementation. -/
theorem not_polynomial_free_variable_work :
    ¬ ∃ bound : Polynomial Nat, ∀ n,
      (atomFreeVars (tree n)).length ≤ bound.eval (sizeOf (finalArticle n)) := by
  rintro ⟨bound, bounded⟩
  obtain ⟨n, tooSmall⟩ :=
    Mettapedia.GSLT.LanguageDef.ProofSystems.exists_eval_lt_two_pow bound 5 10
  have work := bounded n
  rw [free_variable_occurrences, final_article_size] at work
  omega

/-- The same precise materialized-result metric has no polynomial account
in the canonical raw Atom article's structural size. All other packet
components are fixed in this example. No physical clock is asserted. -/
theorem not_polynomial_raw_free_variable_work :
    ¬ ∃ bound : Polynomial Nat, ∀ n,
      (atomFreeVars (tree n)).length ≤
        bound.eval (sizeOf (Wire.evidenceData (finalArticle n))) := by
  obtain ⟨factor, offset, wireSize⟩ := final_article_wire_size
  rintro ⟨bound, bounded⟩
  obtain ⟨n, tooSmall⟩ :=
    Mettapedia.GSLT.LanguageDef.ProofSystems.exists_eval_lt_two_pow bound factor offset
  have work := bounded n
  rw [free_variable_occurrences, wireSize] at work
  omega

/-- The final sequent and source theory are fixed; only the submitted proof
article grows. Its emitted endpoint is the original constant symbol a. -/
theorem final_checked (n : Nat) :
    Wire.runRoot environment (Wire.evidenceData (finalArticle n)) done = .accepted a :=
  Wire.source_root_has_wire (final_source n)

end Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.Conditional.ExpansionBoundary
