import Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy
import Mettapedia.GSLT.LanguageDef.SemanticService
import Mettapedia.OSLF.MeTTaIL.MatchEvidence
import Mathlib.Data.List.NodupEquivFin

/-!
# Native proof checking for query-first MeTTa Zero

The semantic target is an actual step of the previously authored Zero GSLT.
The proof objects are the occurrence-specific query, equation, grounding and
inert articles of the independent staged source judgment. Both native checking
and direct finite one-step decision instantiate `SemanticService`.

This profile uses the declared model's matcher and grounding operation. The
structural instance runs the existing rich Pattern matcher. Its binder terms
are locally nameless syntax; contextual support-sensitive substitution is a
separate, stronger boundary in `MeTTaSupportIndexedABTWire`. No whole-dialect
HE/PeTTa adequacy, whole-program termination, or polynomial checking bound is
inferred from these finite one-step services.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZeroNativeKernel

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.SemanticService
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
open Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A request to the authored root and the one answer being justified. The
space term remains part of the authored request, independently of its model. -/
structure Claim (model : Model) where
  request : KernelRequest model
  result : Pattern

/-- Meaning is reduction by the previously authored five-field root. It is
not defined by a checker's acceptance or by inhabitation of its proof fibre. -/
def Claim.Meaning {model : Model} (claim : Claim model) : Prop :=
  match claim.request with
  | .query space spaceTerm pattern template =>
      (totalTheory model space spaceTerm).Step
        (queryRequestPattern spaceTerm pattern template)
        (queryAnswerPattern claim.result)
  | .evaluate space spaceTerm subject =>
      (totalTheory model space spaceTerm).Step
        (evaluationRequestPattern spaceTerm subject)
        (evaluationAnswerPattern claim.result)

theorem meaning_iff_source_answer (model : Model) (claim : Claim model) :
    claim.Meaning ↔ claim.result ∈
      MeTTaZeroStagedAdequacy.run model (classifiedRequest claim.request) := by
  rcases claim with ⟨request, result⟩
  cases request with
  | query space spaceTerm pattern template =>
      simpa [Claim.Meaning, classifiedRequest] using
        totalTheory_query_step_iff model space spaceTerm pattern template result
  | evaluate space spaceTerm subject =>
      simpa [Claim.Meaning, classifiedRequest] using
        totalTheory_evaluation_step_iff model space spaceTerm subject result

/-- The native article language retains all source evidence coordinates. -/
def proofSystem (model : Model) : NativeProofSystem (Claim model) where
  ProofObject := ObservationProof
  Judges proof claim :=
    proof.Valid model (classifiedRequest claim.request) claim.result

/-- Actual native article checking. -/
def proofKernel (model : Model) : NativeProofKernel (proofSystem model) where
  decide claim proof :=
    checkObservationProof model (classifiedRequest claim.request) claim.result proof
  correct claim proof :=
    checkObservationProof_exact model (classifiedRequest claim.request) claim.result proof

/-- Native article inhabitation is exact for the independently authored GSLT
step, rather than merely a definition of the target in terms of acceptance. -/
theorem meaning_iff_native_proof (model : Model) (claim : Claim model) :
    claim.Meaning ↔ Nonempty ((proofSystem model).ProofFibre claim) := by
  rw [meaning_iff_source_answer, observation_mem_iff_exists_valid]
  constructor
  · rintro ⟨proof, valid⟩
    exact ⟨⟨proof, valid⟩⟩
  · rintro ⟨⟨proof, valid⟩⟩
    exact ⟨proof, valid⟩

/-- The admitted target is the source reduction judgment. -/
def target (model : Model) : AdmissionObject where
  Carrier := Claim model
  Meaning := Claim.Meaning

/-- Native checking is exposed as the native-proof service face. -/
def nativeProofService (model : Model) : Service (target model) :=
  .nativeProof (proofSystem model) (proofKernel model)
    (meaning_iff_native_proof model)

/-- Finite one-step answer membership is also directly decidable at this
profile. This operation does not decide unbounded reachability or theoremhood. -/
def decisionKernel (model : Model) : Checker.DecisionKernel (Claim model)
    Claim.Meaning where
  decide claim := decide (claim.result ∈
    MeTTaZeroStagedAdequacy.run model (classifiedRequest claim.request))
  correct claim := by simp only [decide_eq_true_eq, meaning_iff_source_answer]

def directDecisionService (model : Model) : Service (target model) :=
  .directDecision (decisionKernel model)

/-- The same authored target has exact direct and intrinsic-proof services. -/
theorem decision_accepts_iff_proof_accepted (model : Model) (claim : Claim model) :
    (decisionKernel model).decide claim = true ↔
      ∃ proof, (proofKernel model).decide claim proof = true := by
  rw [(decisionKernel model).correct]
  exact (Service.nativeProof_accepts_iff_meaning (target := target model) (proofSystem model)
    (proofKernel model) (meaning_iff_native_proof model) claim)

/-- Neither service is incorrectly represented as an external certificate
boundary. Their implementation and exactness laws remain profile specific. -/
theorem services_have_no_external_boundary (model : Model) :
    Service.hasExternalCertificateBoundary (nativeProofService model) = false ∧
    Service.hasExternalCertificateBoundary (directDecisionService model) = false :=
  ⟨rfl, rfl⟩


/-! ## Intrinsic explicit-evidence structural matching -/

namespace StructuralMatching

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.MatchEvidence

/-- All inputs of the independent structural matching judgment. -/
structure Claim where
  pattern : Pattern
  target : Pattern
  bindings : Bindings
  deriving Repr, DecidableEq

def Claim.Meaning (claim : Claim) : Prop :=
  MatchRel claim.pattern claim.target claim.bindings

/-- The intrinsic proof objects are explicit residual bag choices. Their
source judgment is independent of the executable replay operation. -/
def proofSystem : NativeProofSystem Claim where
  ProofObject := List Nat
  Judges trace claim := GuidedMatchRel claim.pattern claim.target claim.bindings trace []

def proofKernel : NativeProofKernel proofSystem where
  decide claim trace := checkGuidedMatch claim.pattern claim.target claim.bindings trace
  correct claim trace := checkGuidedMatch_exact claim.pattern claim.target claim.bindings trace

theorem meaning_iff_native_proof (claim : Claim) :
    claim.Meaning ↔ Nonempty (proofSystem.ProofFibre claim) := by
  rw [Claim.Meaning, matchRel_iff_exists_guidance]
  constructor
  · rintro ⟨trace, accepted⟩
    exact ⟨⟨trace, (checkGuidedMatch_exact _ _ _ _).mp accepted⟩⟩
  · rintro ⟨⟨trace, guided⟩⟩
    exact ⟨trace, (checkGuidedMatch_exact _ _ _ _).mpr guided⟩

def target : AdmissionObject where
  Carrier := Claim
  Meaning := Claim.Meaning

/-- A native matching proof service which follows submitted choices instead
of computing the whole matcher bag. Query-driver integration and a unique
trace for each matching occurrence remain separate obligations. -/
def nativeProofService : Service target :=
  .nativeProof proofSystem proofKernel meaning_iff_native_proof

/-- A finite producer for this native proof language. It retains equal answer
occurrences when their matcher choices differ. Production may search; replay
of one submitted proof does not enumerate the result bag. -/
def proofChoices (claim : Claim) : List (List Nat) :=
  ((enumeratePattern claim.pattern claim.target).filter
    (fun row => row.1 == claim.bindings)).map Prod.snd

theorem mem_proofChoices_iff_accepted (claim : Claim) (trace : List Nat) :
    trace ∈ proofChoices claim ↔ proofKernel.decide claim trace = true := by
  simp only [proofChoices, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨row, ⟨member, bindings⟩, sameTrace⟩
    have sameBindings : row.1 = claim.bindings := by simpa using bindings
    have accepted := enumeratePattern_rows_accepted claim.pattern claim.target row member
    simpa only [proofKernel, sameBindings, sameTrace] using accepted
  · intro accepted
    exact ⟨(claim.bindings, trace),
      ⟨(mem_enumeratePattern_iff_accepted _ _ _).mpr accepted, by simp⟩, rfl⟩

theorem proofChoices_count (claim : Claim) :
    (proofChoices claim).length = (matchPattern claim.pattern claim.target).count claim.bindings := by
  rw [proofChoices, List.length_map, ← List.countP_eq_length_filter, enumeratePattern_count]


end StructuralMatching

/-! ## Positive and negative controls -/

namespace Controls

open Mettapedia.OSLF.MeTTaIL.Match

def a : Pattern := .apply "a" []
def b : Pattern := .apply "b" []
def c : Pattern := .apply "c" []
def spaceName : Pattern := .apply "native-space" []
def equation : Pattern := .apply "=" [a, b]
def model : Model := structuralModel

def queryClaim : Claim model :=
  ⟨.query ({a, a} : Multiset Pattern) spaceName (.fvar "x") (.fvar "x"), a⟩
def queryArticle (atomCopy matchCopy : Nat) : ObservationProof :=
  .produced (.query ⟨a, atomCopy, [("x", a)], matchCopy⟩)

def equationClaim : Claim model :=
  ⟨.evaluate ({equation, equation} : Multiset Pattern) spaceName a, b⟩
def equationArticle (atomCopy matchCopy : Nat) : ObservationProof :=
  .produced (.equation ⟨equation, atomCopy, [(allAtomsVariable, equation)], 0⟩
    equation a b [] matchCopy)

def inertClaim : Claim model :=
  ⟨.evaluate ({equation} : Multiset Pattern) spaceName c, c⟩
def identity : Pattern := .lambda none (.bvar 0)
def binderClaim : Claim model :=
  ⟨.query ({identity} : Multiset Pattern) spaceName (.fvar "x") (.fvar "x"), identity⟩
def binderArticle : ObservationProof :=
  .produced (.query ⟨identity, 0, [("x", identity)], 0⟩)

def bag : Pattern := .collection .hashBag [a, a] none
def bagPattern : Pattern := .collection .hashBag [.fvar "x"] (some "rest")
def bagBindings : Bindings :=
  [("rest", .collection .hashBag [a] none), ("x", a)]
def bagClaim : Claim model :=
  ⟨.query ({bag} : Multiset Pattern) spaceName bagPattern (.fvar "x"), a⟩
def bagArticle (matchCopy : Nat) : ObservationProof :=
  .produced (.query ⟨bag, 0, bagBindings, matchCopy⟩)

def groundingModel : Model := structuralModel fun subject =>
  if subject = a then {b, b} else 0
def groundClaim : Claim groundingModel :=
  ⟨.evaluate (0 : Multiset Pattern) spaceName a, b⟩

/-- Separate source and matcher multiplicities, actual binders as values,
public equation provenance, grounding provenance and inert refusal all
participate in the same executable native kernel. -/
theorem positive_controls :
    (proofKernel model).decide queryClaim (queryArticle 0 0) = true ∧
    (proofKernel model).decide queryClaim (queryArticle 1 0) = true ∧
    (proofKernel model).decide equationClaim (equationArticle 0 0) = true ∧
    (proofKernel model).decide equationClaim (equationArticle 1 0) = true ∧
    (proofKernel model).decide inertClaim .inert = true ∧
    (proofKernel model).decide binderClaim binderArticle = true ∧
    (proofKernel model).decide bagClaim (bagArticle 0) = true ∧
    (proofKernel model).decide bagClaim (bagArticle 1) = true ∧
    (proofKernel groundingModel).decide groundClaim (.produced (.ground 0)) = true ∧
    (proofKernel groundingModel).decide groundClaim (.produced (.ground 1)) = true := by
  simp [proofKernel, queryClaim, queryArticle, equationClaim, equationArticle,
    inertClaim, binderClaim, binderArticle, bagClaim, bagArticle, groundClaim,
    checkObservationProof, checkProductionProof, checkQueryProof,
    classifiedRequest, model, structuralModel, groundingModel, interpretedResults,
    equationResults, queryAll, query, viewEquation?, identity, bagPattern,
    bagBindings, bag, equation, a, b, c, allAtomsVariable, matchPattern,
    matchArgs, matchBag, mergeBindings, applyBindings]

/-- An absent source copy, absent match copy, forged answer, missing equation
provenance and a premature inert claim are rejected. -/
theorem negative_controls :
    (proofKernel model).decide queryClaim (queryArticle 2 0) = false ∧
    (proofKernel model).decide queryClaim (queryArticle 0 1) = false ∧
    (proofKernel model).decide equationClaim (equationArticle 2 0) = false ∧
    (proofKernel model).decide equationClaim (equationArticle 0 1) = false ∧
    (proofKernel model).decide equationClaim .inert = false ∧
    (proofKernel model).decide queryClaim .inert = false ∧
    (proofKernel model).decide { inertClaim with result := a } .inert = false ∧
    (proofKernel model).decide { queryClaim with result := b } (queryArticle 0 0) = false ∧
    (proofKernel model).decide bagClaim (bagArticle 2) = false ∧
    (proofKernel groundingModel).decide groundClaim (.produced (.ground 2)) = false ∧
    (proofKernel model).decide equationClaim (.produced (.ground 0)) = false := by
  simp [proofKernel, queryClaim, queryArticle, equationClaim, equationArticle,
    inertClaim, bagClaim, bagArticle, groundClaim, checkObservationProof,
    checkProductionProof, checkQueryProof, classifiedRequest, model, structuralModel,
    groundingModel, interpretedResults, equationResults, queryAll, query,
    viewEquation?, bagPattern, bagBindings, bag, equation, a, b, c,
    allAtomsVariable, matchPattern, matchArgs, matchBag, mergeBindings, applyBindings]

/-- Both valid source-copy articles remain distinct even though they prove
exactly the same endpoint claim. -/
theorem duplicate_articles_remain_distinct : queryArticle 0 0 ≠ queryArticle 1 0 := by
  decide

/-- The direct service computes the same native one-step answer judgment. -/
theorem direct_controls :
    (decisionKernel model).decide queryClaim = true ∧
    (decisionKernel model).decide equationClaim = true ∧
    (decisionKernel model).decide inertClaim = true ∧
    (decisionKernel model).decide { queryClaim with result := b } = false := by
  simp [decisionKernel, queryClaim, equationClaim, inertClaim, classifiedRequest,
    run_query, run_evaluate,
    model, structuralModel, interpretedResults, equationResults, evaluateOne,
    queryAll, query, viewEquation?, equation, a, b, c, allAtomsVariable,
    matchPattern, matchArgs, applyBindings]

end Controls


/-! ## Explicit occurrence-preserving query evidence -/

open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.SemanticService
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.MatchEvidence

namespace StructuralMatching

theorem proofChoices_nodup (claim : Claim) : (proofChoices claim).Nodup := by
  apply ((enumeratePattern_nodup claim.pattern claim.target).filter
    (fun row => row.1 == claim.bindings)).map_on
  intro first firstMember second secondMember same
  exact (enumeratePattern_valid claim.pattern claim.target).choice_injective
    (List.mem_filter.mp firstMember).1 (List.mem_filter.mp secondMember).1 same

/-- Exact finite matching-occurrence correspondence for a fixed
implementation, with no language-level answer-order promise. -/
def occurrenceEquiv (claim : Claim) :
    Fin ((matchPattern claim.pattern claim.target).count claim.bindings) ≃
      {trace : List Nat // proofKernel.decide claim trace = true} :=
  ((finCongr (proofChoices_count claim).symm).trans
    ((proofChoices_nodup claim).getEquiv (proofChoices claim))).trans
      (Equiv.subtypeEquivRight (mem_proofChoices_iff_accepted claim))

end StructuralMatching

namespace GuidedQuery

/-- Inputs and proposed answer of the existing public structural query. -/
structure Claim where
  space : Multiset Pattern
  pattern : Pattern
  template : Pattern
  result : Pattern

def Claim.Meaning (claim : Claim) : Prop :=
  claim.result ∈ query structuralModel claim.space claim.pattern claim.template

/-- Source-space occurrence identity and explicit matching choices remain
separate coordinates. No count of alternative matcher results is supplied. -/
structure Proof where
  candidate : Pattern
  atomOccurrence : Nat
  bindings : Bindings
  choices : List Nat
  deriving Repr, DecidableEq

/-- This source judgment uses an actual occurrence of the reflective space,
the independent guided matching relation and source template instantiation. -/
def Proof.Valid (claim : Claim) (proof : Proof) : Prop :=
  proof.atomOccurrence < Multiset.count proof.candidate claim.space ∧
    GuidedMatchRel claim.pattern proof.candidate proof.bindings proof.choices [] ∧
    applyBindings proof.bindings claim.template = claim.result

/-- Checking follows one submitted matcher path rather than counting every
possible match of the candidate. -/
def check (claim : Claim) (proof : Proof) : Bool :=
  decide (proof.atomOccurrence < Multiset.count proof.candidate claim.space) &&
    checkGuidedMatch claim.pattern proof.candidate proof.bindings proof.choices &&
    decide (applyBindings proof.bindings claim.template = claim.result)

@[simp] theorem check_exact (claim : Claim) (proof : Proof) :
    check claim proof = true ↔ proof.Valid claim := by
  simp [check, Proof.Valid, checkGuidedMatch_exact, and_assoc]

theorem meaning_iff_exists_valid (claim : Claim) :
    claim.Meaning ↔ ∃ proof : Proof, proof.Valid claim := by
  simp only [Claim.Meaning, query, structuralModel, id_eq, Multiset.mem_bind,
    Multiset.mem_map, Multiset.mem_coe]
  constructor
  · rintro ⟨candidate, candidateMember, bindings, bindingMember, resultEq⟩
    obtain ⟨trace, accepted⟩ := (matchPattern_mem_iff_exists_guidance _ _ _).mp bindingMember
    exact ⟨⟨candidate, 0, bindings, trace⟩,
      Multiset.count_pos.mpr candidateMember,
      (checkGuidedMatch_exact _ _ _ _).mp accepted, resultEq⟩
  · rintro ⟨proof, candidateBound, guided, resultEq⟩
    exact ⟨proof.candidate, Multiset.count_pos.mp (Nat.zero_lt_of_lt candidateBound),
      proof.bindings, matchRel_complete guided.erase, resultEq⟩


/-- Convert an original occurrence-indexed article to its explicit matching
path. This producer-side conversion can enumerate; the guided checker does
not call it. -/
def fromOrdinal (claim : Claim)
    (article : {proof : QueryProof //
      proof.Valid structuralModel claim.space claim.pattern claim.template claim.result}) :
    {proof : Proof // proof.Valid claim} := by
  let matching : StructuralMatching.Claim :=
    ⟨claim.pattern, article.1.candidate, article.1.bindings⟩
  have bound : article.1.matchOccurrence <
      (matchPattern claim.pattern article.1.candidate).count article.1.bindings := by
    simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP, Bool.beq_eq_decide_eq] using article.2.2.1
  let selected := StructuralMatching.occurrenceEquiv matching ⟨article.1.matchOccurrence, bound⟩
  refine ⟨⟨article.1.candidate, article.1.atomOccurrence, article.1.bindings, selected.1⟩,
    article.2.1, ?_, article.2.2.2⟩
  exact (checkGuidedMatch_exact _ _ _ _).mp selected.2

/-- Recover the original occurrence coordinate from a guided article.
This comparison is separate from guided checking. -/
def toOrdinal (claim : Claim) (article : {proof : Proof // proof.Valid claim}) :
    {proof : QueryProof //
      proof.Valid structuralModel claim.space claim.pattern claim.template claim.result} := by
  let matching : StructuralMatching.Claim :=
    ⟨claim.pattern, article.1.candidate, article.1.bindings⟩
  let accepted : {trace : List Nat // StructuralMatching.proofKernel.decide matching trace = true} :=
    ⟨article.1.choices, (checkGuidedMatch_exact _ _ _ _).mpr article.2.2.1⟩
  let ordinal := (StructuralMatching.occurrenceEquiv matching).symm accepted
  refine ⟨⟨article.1.candidate, article.1.atomOccurrence, article.1.bindings, ordinal.1⟩,
    article.2.1, ?_, article.2.2.2⟩
  simpa only [structuralModel, Multiset.coe_count, List.count_eq_countP, Bool.beq_eq_decide_eq] using ordinal.2

theorem toOrdinal_fromOrdinal (claim : Claim)
    (article : {proof : QueryProof //
      proof.Valid structuralModel claim.space claim.pattern claim.template claim.result}) :
    toOrdinal claim (fromOrdinal claim article) = article := by
  apply Subtype.ext
  rcases article with ⟨⟨candidate, atomOccurrence, bindings, matchOccurrence⟩, valid⟩
  change QueryProof.mk candidate atomOccurrence bindings
    (((StructuralMatching.occurrenceEquiv ⟨claim.pattern, candidate, bindings⟩).symm
      ((StructuralMatching.occurrenceEquiv ⟨claim.pattern, candidate, bindings⟩)
        ⟨matchOccurrence, _⟩)).1) = _
  congr 1
  exact congrArg Fin.val
    ((StructuralMatching.occurrenceEquiv ⟨claim.pattern, candidate, bindings⟩).symm_apply_apply
      ⟨matchOccurrence, _⟩)

theorem fromOrdinal_toOrdinal (claim : Claim)
    (article : {proof : Proof // proof.Valid claim}) :
    fromOrdinal claim (toOrdinal claim article) = article := by
  apply Subtype.ext
  rcases article with ⟨⟨candidate, atomOccurrence, bindings, choices⟩, valid⟩
  change Proof.mk candidate atomOccurrence bindings
    (((StructuralMatching.occurrenceEquiv ⟨claim.pattern, candidate, bindings⟩)
      ((StructuralMatching.occurrenceEquiv ⟨claim.pattern, candidate, bindings⟩).symm
        ⟨choices, _⟩)).1) = _
  congr 1
  exact congrArg Subtype.val
    ((StructuralMatching.occurrenceEquiv ⟨claim.pattern, candidate, bindings⟩).apply_symm_apply
      ⟨choices, _⟩)

/-- Explicit matching paths preserve the complete original query evidence
fibre, including both space and matcher occurrences. -/
def ordinalProofEquiv (claim : Claim) :
    {proof : QueryProof //
      proof.Valid structuralModel claim.space claim.pattern claim.template claim.result} ≃
      {proof : Proof // proof.Valid claim} where
  toFun := fromOrdinal claim
  invFun := toOrdinal claim
  left_inv := toOrdinal_fromOrdinal claim
  right_inv := fromOrdinal_toOrdinal claim

def proofSystem : NativeProofSystem Claim where
  ProofObject := Proof
  Judges proof claim := proof.Valid claim

def proofKernel : NativeProofKernel proofSystem where
  decide := check
  correct := check_exact

theorem meaning_iff_native_proof (claim : Claim) :
    claim.Meaning ↔ Nonempty (proofSystem.ProofFibre claim) := by
  rw [meaning_iff_exists_valid]
  exact ⟨fun ⟨proof, valid⟩ => ⟨⟨proof, valid⟩⟩, fun ⟨⟨proof, valid⟩⟩ => ⟨proof, valid⟩⟩

def target : AdmissionObject where
  Carrier := Claim
  Meaning := Claim.Meaning

def nativeProofService : Service target :=
  .nativeProof proofSystem proofKernel meaning_iff_native_proof


namespace Controls

open Mettapedia.OSLF.MeTTaIL.MatchEvidence.GuidedControls

def claim : Claim :=
  ⟨{duplicateTarget, duplicateTarget}, pairPattern,
    .apply "Pair" [.fvar "x", .fvar "y"], .apply "Pair" [atomA, atomA]⟩

def article (atomCopy : Nat) (choices : List Nat) : Proof :=
  ⟨duplicateTarget, atomCopy, duplicateBindings, choices⟩

theorem first_space_first_match : check claim (article 0 [0, 0]) = true := by decide +kernel

theorem second_space_second_match : check claim (article 1 [1, 0]) = true := by decide +kernel

theorem absent_space_copy : check claim (article 2 [0, 0]) = false := by decide +kernel

theorem nonexistent_matching_path : check claim (article 0 [2, 0]) = false := by decide +kernel

theorem unused_matching_path : check claim (article 0 [0, 0, 0]) = false := by decide +kernel

theorem forged_answer :
    check {claim with result := .apply "Pair" [atomA, atomB]} (article 0 [0, 0]) = false := by
  decide +kernel

theorem source_retains_four_occurrences :
    Multiset.count claim.result
      (query structuralModel claim.space claim.pattern claim.template) = 4 := by decide +kernel

def ordinalArticle : QueryProof := ⟨duplicateTarget, 1, duplicateBindings, 1⟩

theorem ordinalArticle_valid :
    ordinalArticle.Valid structuralModel claim.space claim.pattern claim.template claim.result := by
  unfold QueryProof.Valid
  decide +kernel

theorem ordinal_to_guided_preserves_occurrences :
    (fromOrdinal claim ⟨ordinalArticle, ordinalArticle_valid⟩).1 = article 1 [1, 0] := by
  decide +kernel

end Controls

end GuidedQuery

end Mettapedia.Languages.MeTTa.MeTTaZeroNativeKernel
