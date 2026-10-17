import Mettapedia.GSLT.LanguageDef.GeneralPremiseReceiptWire
import Mettapedia.GSLT.LanguageDef.FiniteCertificateSearch
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution

/-!
# Retained discovery of original finite authored proof articles

The exhaustive fallback enumerates canonical natural codes of the original
finite-alphabet receipt language. Alternate slots execute the existing
source runner as a heuristic; its caller-index restriction is unchanged.
Every proposed receipt is revalidated by the unrestricted total checker.
The public observation is discovery of complete finite proof articles,
not the number or order of operational events represented by those articles.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralPremiseNativeDiscovery

open Mettapedia.OSLF.MeTTaIL
open Syntax GeneralPremise GeneralExecutionAdmission
open Mettapedia.OSLF.Binding.WireCodec
open KernelAuthority SemanticEvidence

abbrev Claim := GeneralPremiseNativeEvidence.Claim
abbrev Proof := GeneralRuleJobs.Receipt
abbrev Article := List Binary.Alphabet
abbrev State := FiniteCertificateSearch.Retained.State Article

def articleCheck (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (article : Article) : Bool :=
  match GeneralPremiseReceiptWire.decodeReceipt article with
  | none => false
  | some proof => GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof

def articleChecker (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : Checker Claim Article := ⟨articleCheck dynamic plan bound type⟩

theorem articleCheck_exact (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (article : Article) :
    articleCheck dynamic plan bound type claim article = true ↔ ∃ proof : Proof,
      article = GeneralPremiseReceiptWire.encodeReceipt proof ∧
      proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  cases decoded : GeneralPremiseReceiptWire.decodeReceipt article with
  | none =>
      constructor
      · simp only [articleCheck, decoded, Bool.false_eq_true]; intro impossible; cases impossible
      · rintro ⟨proof, rfl, _⟩
        rw [GeneralPremiseReceiptWire.decodeReceipt_encodeReceipt] at decoded
        cases decoded
  | some proof =>
      have original := (GeneralPremiseReceiptWire.decodeReceipt_exact article proof).mp decoded
      constructor
      · intro checked
        rw [articleCheck, decoded] at checked
        exact ⟨proof, original.symm, (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mp checked⟩
      · rintro ⟨actual, encoded, valid⟩
        have same : proof = actual := by
          rw [encoded, GeneralPremiseReceiptWire.decodeReceipt_encodeReceipt] at decoded
          exact (Option.some.inj decoded).symm
        subst actual
        rw [articleCheck, decoded]
        exact (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mpr valid

/-- The existing source runner generates these proposals; no candidate
proof or source derivation is an input to the discovery operation. -/
def heuristicReceipts (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (fuel : Nat) : List Proof :=
  (GeneralRuleJobs.jobs plan bound type source).attach.flatMap fun job =>
    let request : GeneralRuleJobExecution.Request := ⟨plan, bound, type, source, job.val⟩
    let licensed := (GeneralRuleJobs.jobs_spec plan bound type source job.val).mp job.property
    (GeneralRuleJobExecution.answersWith request dynamic licensed
      (GeneralRuleJobExecution.runWith request dynamic fuel
        (GeneralRuleJobExecution.startWith request dynamic))).map Subtype.val

/-- Odd slots are the exhaustive fallback. Even slots are optional source
runner proposals; their incompleteness cannot remove a fallback slot. -/
def proposals (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (position : Nat) : List Article :=
  if position % 2 = 0 then
    (heuristicReceipts dynamic plan bound type claim.1 (position / 2)).map
      GeneralPremiseReceiptWire.encodeReceipt
  else (Encodable.decode₂ Article (position / 2)).toList

theorem original_article_proposed (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (article : Article) :
    article ∈ proposals dynamic plan bound type claim (2 * Encodable.encode article + 1) := by
  have odd : ¬ (2 * Encodable.encode article + 1) % 2 = 0 := by omega
  have divided : (2 * Encodable.encode article + 1) / 2 = Encodable.encode article := by omega
  simp only [proposals, odd, if_false, divided, Encodable.decode₂_encode, Option.toList_some,
    List.mem_singleton]

def initial : State := FiniteCertificateSearch.Retained.initial

def resume (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (budget : Nat) (state : State) : State :=
  FiniteCertificateSearch.Retained.run (articleChecker dynamic plan bound type)
    (proposals dynamic plan bound type claim) claim budget state

def search (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (budget : Nat) : State :=
  resume dynamic plan bound type claim budget initial

def readout (state : State) : List Proof :=
  state.articles.filterMap GeneralPremiseReceiptWire.decodeReceipt

theorem resume_add (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (first second : Nat) (state : State) :
    resume dynamic plan bound type claim (first + second) state =
      resume dynamic plan bound type claim second (resume dynamic plan bound type claim first state) :=
  FiniteCertificateSearch.Retained.run_add _ _ _ first second state

theorem resume_cursor (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (budget : Nat) (state : State) :
    (resume dynamic plan bound type claim budget state).cursor = state.cursor + budget :=
  FiniteCertificateSearch.Retained.run_cursor _ _ _ budget state

theorem search_sound (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (budget : Nat) (proof : Proof)
    (found : proof ∈ readout (search dynamic plan bound type claim budget)) :
    proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  obtain ⟨article, present, decoded⟩ := List.mem_filterMap.mp found
  have checked := FiniteCertificateSearch.Retained.search_sound
    (articleChecker dynamic plan bound type) (proposals dynamic plan bound type claim) claim budget article present
  change articleCheck dynamic plan bound type claim article = true at checked
  rw [articleCheck, decoded] at checked
  exact (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mp checked

def discoveryBound (proof : Proof) : Nat :=
  2 * Encodable.encode (GeneralPremiseReceiptWire.encodeReceipt proof) + 2

/-- Every original finite receipt itself is discovered. Another earlier
proof does not prevent this article from subsequently entering the journal. -/
theorem receipt_discovered (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (target : proof.target = claim.2) :
    proof ∈ readout (search dynamic plan bound type claim (discoveryBound proof)) := by
  let article := GeneralPremiseReceiptWire.encodeReceipt proof
  have checked : (articleChecker dynamic plan bound type).check claim article = true :=
    (articleCheck_exact dynamic plan bound type claim article).mpr ⟨proof, rfl, valid, target⟩
  have proposed := original_article_proposed dynamic plan bound type claim article
  have found := FiniteCertificateSearch.Retained.discovered_at
    (articleChecker dynamic plan bound type) (proposals dynamic plan bound type claim) claim article
    (2 * Encodable.encode article + 1) proposed checked
  exact List.mem_filterMap.mpr ⟨article, found, GeneralPremiseReceiptWire.decodeReceipt_encodeReceipt proof⟩

theorem source_iff_discovery (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔
      ∃ budget, readout (search dynamic plan bound type claim budget) ≠ [] := by
  constructor
  · rintro ⟨proof, valid, target⟩
    exact ⟨discoveryBound proof, List.ne_nil_of_mem (receipt_discovered dynamic plan bound type claim proof valid target)⟩
  · rintro ⟨budget, nonempty⟩
    obtain ⟨proof, found⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨proof, search_sound dynamic plan bound type claim budget proof found⟩

theorem readout_nodup (state : State) (distinct : state.articles.Nodup) : (readout state).Nodup := by
  apply List.Nodup.filterMap _ distinct
  intro first second proof one two
  have oneAt := (GeneralPremiseReceiptWire.decodeReceipt_exact first proof).mp one
  have twoAt := (GeneralPremiseReceiptWire.decodeReceipt_exact second proof).mp two
  exact oneAt.symm.trans twoAt

theorem search_nodup (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (budget : Nat) :
    (readout (search dynamic plan bound type claim budget)).Nodup :=
  readout_nodup _ (FiniteCertificateSearch.Retained.run_nodup _ _ _ budget initial .nil)

/-- Empty finite discovery retains unknown. Even budget zero can coexist
with an original proof, which the eventual-coverage theorem still finds. -/
theorem zero_unknown (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) : readout (search dynamic plan bound type claim 0) = [] := rfl


/-- Resuming retains every discovered article and advances only later slots. -/
theorem resume_retains (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (budget : Nat) (state : State) (proof : Proof)
    (found : proof ∈ readout state) :
    proof ∈ readout (resume dynamic plan bound type claim budget state) := by
  obtain ⟨article, present, decoded⟩ := List.mem_filterMap.mp found
  exact List.mem_filterMap.mpr ⟨article,
    (FiniteCertificateSearch.Retained.mem_run _ _ _ budget state article).mpr (Or.inl present), decoded⟩

/-- This source admission is ordinary authored sorting of the two endpoints;
it does not assume that a proof exists or provide a proof to search. -/
def QueryAdmitted (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) : Prop :=
  WellSorted.HasType (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound claim.1 type ∧
    WellSorted.HasType (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound claim.2 type

theorem source_admitted (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim)
    (meaning : GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim) :
    QueryAdmitted plan bound type claim := by
  obtain ⟨proof, valid, target⟩ := meaning
  exact ⟨valid.1.2.source_typed, target ▸ valid.2.2.2.2.1⟩

abbrev Query := Claim × Nat
abbrev Output := Claim × Nat × State

def source (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) : AdmissionObject where
  Carrier := Query
  Meaning input := QueryAdmitted plan bound type input.1

/-- The target carries original source validity for every discovered article,
not validation by definition. The raw retained cursor records attempted slots. -/
def target (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : AdmissionObject where
  Carrier := Output
  Meaning output := QueryAdmitted plan bound type output.1 ∧
    output.2.2.cursor = output.2.1 ∧ (readout output.2.2).Nodup ∧
    ∀ proof ∈ readout output.2.2,
      proof.ValidWith dynamic plan bound type output.1.1 ∧ proof.target = output.1.2

/-- This operation receives only a goal and a search budget. Its raw function
actually generates proposals, checks them and retains discovered evidence. -/
def operation (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : AdmissionHom (source plan bound type) (target dynamic plan bound type) where
  run input := (input.1, input.2, search dynamic plan bound type input.1 input.2)
  preserves input admitted := ⟨admitted,
    by simpa only [search, initial, FiniteCertificateSearch.Retained.initial, Nat.zero_add]
      using resume_cursor dynamic plan bound type input.1 input.2 initial,
    search_nodup dynamic plan bound type input.1 input.2,
    search_sound dynamic plan bound type input.1 input.2⟩

def service (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : SemanticService.Service.{0, 0} (target dynamic plan bound type) :=
  .nativeOperation (source plan bound type) (operation dynamic plan bound type)

def request (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (input : Query) : SemanticServiceInvocation.Request (service dynamic plan bound type) :=
  .nativeOperation input

/-- Actual service output has independently valid receipts on admitted goals.
An empty result carries no assertion that the goal is unprovable. -/
theorem invocation_sound (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (input : Query) (admitted : QueryAdmitted plan bound type input.1) :
    (target dynamic plan bound type).Meaning ((operation dynamic plan bound type).run input) :=
  (operation dynamic plan bound type).preserves input admitted

/-- Proof-article discovery, rather than operational run multiplicity, is
the service's declared observation. -/
def discovered (output : Output) : List Proof := readout output.2.2

/-- Every original receipt can be observed in an actual native operation
response without supplying that receipt as the operation's input. -/
theorem receipt_native_discovered (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (result : proof.target = claim.2) :
    ∃ output,
      (SemanticServiceInvocation.invoke
        (request dynamic plan bound type (claim, discoveryBound proof))).acceptedValue = some output ∧
      proof ∈ discovered output := by
  have found := receipt_discovered dynamic plan bound type claim proof valid result
  generalize budgetAt : discoveryBound proof = budget at found ⊢
  exact ⟨(claim, budget, search dynamic plan bound type claim budget), rfl, found⟩

theorem source_iff_native_discovery (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔ ∃ budget output,
      (SemanticServiceInvocation.invoke (request dynamic plan bound type (claim, budget))).acceptedValue = some output ∧
      discovered output ≠ [] := by
  constructor
  · intro meaningful
    obtain ⟨budget, found⟩ := (source_iff_discovery dynamic plan bound type claim).mp meaningful
    exact ⟨budget, (claim, budget, search dynamic plan bound type claim budget), rfl, found⟩
  · rintro ⟨budget, output, accepted, found⟩
    change some (claim, budget, search dynamic plan bound type claim budget) = some output at accepted
    cases Option.some.inj accepted
    exact (source_iff_discovery dynamic plan bound type claim).mpr ⟨budget, found⟩


abbrev StateReached (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (state : State) : Prop :=
  FiniteCertificateSearch.Retained.Reachable (articleChecker dynamic plan bound type)
    (proposals dynamic plan bound type claim) claim state

theorem search_reached (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (budget : Nat) :
    StateReached dynamic plan bound type claim (search dynamic plan bound type claim budget) :=
  FiniteCertificateSearch.Retained.run_reachable _ _ _ budget initial .initial

theorem reached_sound (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (state : State)
    (reached : StateReached dynamic plan bound type claim state) :
    ∀ proof ∈ readout state, proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  intro proof found
  have prefixAt := FiniteCertificateSearch.Retained.reachable_eq_search _ _ _ state reached
  rw [prefixAt] at found
  exact search_sound dynamic plan bound type claim state.cursor proof found

/-- Native resumption requires a checkpoint reached by this same profile and
goal. Validating arbitrary serialized checkpoints is a separate boundary. -/
def resumeSource (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : AdmissionObject where
  Carrier := Output
  Meaning input := QueryAdmitted plan bound type input.1 ∧
    StateReached dynamic plan bound type input.1 input.2.2

def resumeOperation (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : AdmissionHom (resumeSource dynamic plan bound type) (target dynamic plan bound type) where
  run input := (input.1, input.2.2.cursor + input.2.1,
    resume dynamic plan bound type input.1 input.2.1 input.2.2)
  preserves input admitted := by
    have reached := FiniteCertificateSearch.Retained.run_reachable
      (articleChecker dynamic plan bound type) (proposals dynamic plan bound type input.1)
      input.1 input.2.1 input.2.2 admitted.2
    exact ⟨admitted.1, resume_cursor dynamic plan bound type input.1 input.2.1 input.2.2,
      readout_nodup _ (FiniteCertificateSearch.Retained.reachable_nodup _ _ _ _ reached),
      reached_sound dynamic plan bound type input.1 _ reached⟩

def resumeService (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : SemanticService.Service.{0, 0} (target dynamic plan bound type) :=
  .nativeOperation (resumeSource dynamic plan bound type) (resumeOperation dynamic plan bound type)

/-- A successful output of the first operation supplies genuine checkpoint
provenance, not merely a list of plausible proof articles. -/
theorem output_reached (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (input : Query) :
    StateReached dynamic plan bound type input.1 ((operation dynamic plan bound type).run input).2.2 :=
  search_reached dynamic plan bound type input.1 input.2

/-- An article from another result cannot authorize this goal's resume input. -/
theorem stale_article_not_reached (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (state : State) (proof : Proof)
    (stored : GeneralPremiseReceiptWire.encodeReceipt proof ∈ state.articles)
    (wrong : proof.target ≠ claim.2) : ¬ StateReached dynamic plan bound type claim state := by
  intro reached
  have found := List.mem_filterMap.mpr ⟨GeneralPremiseReceiptWire.encodeReceipt proof,
    stored, GeneralPremiseReceiptWire.decodeReceipt_encodeReceipt proof⟩
  exact wrong ((reached_sound dynamic plan bound type claim state reached proof found).2)

/-- Every finite original article is eventually present after a genuine
resume, even when earlier proof articles were already retained. -/
theorem resume_discovers (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (state : State)
    (reached : StateReached dynamic plan bound type claim state) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (result : proof.target = claim.2) :
    proof ∈ readout (resume dynamic plan bound type claim (discoveryBound proof) state) := by
  have first := receipt_discovered dynamic plan bound type claim proof valid result
  generalize budgetAt : discoveryBound proof = budget at first ⊢
  obtain ⟨article, present, decoded⟩ := List.mem_filterMap.mp first
  have continued := FiniteCertificateSearch.Retained.search_monotone
    (articleChecker dynamic plan bound type) (proposals dynamic plan bound type claim) claim
    budget (state.cursor + budget) (by omega) present
  have prefixAt := FiniteCertificateSearch.Retained.reachable_eq_search _ _ _ state reached
  change article ∈ (resume dynamic plan bound type claim (state.cursor + budget) initial).articles at continued
  rw [resume_add] at continued
  change article ∈ (resume dynamic plan bound type claim budget
    (search dynamic plan bound type claim state.cursor)).articles at continued
  change state = search dynamic plan bound type claim state.cursor at prefixAt
  rw [← prefixAt] at continued
  exact List.mem_filterMap.mpr ⟨article, continued, decoded⟩

end Mettapedia.GSLT.LanguageDef.GeneralPremiseNativeDiscovery
