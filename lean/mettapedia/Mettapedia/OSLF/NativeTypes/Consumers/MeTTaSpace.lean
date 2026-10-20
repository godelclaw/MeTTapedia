import Mettapedia.Languages.MeTTa.MeTTaZeroNativeKernel
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Native query contracts for the Zero / PeTTa space boundary

The source is Zero's existing occurrence-labelled query GSLT, instantiated
with PeTTa's stored space and matcher. The executable decision uses PeTTa's
actual `spaceMatch`. A complete answer packet is accepted exactly when it
accounts for every source occurrence, including repeated equal answers.
Enumeration order is deliberately unobserved by this bag contract.

The existing Zero native article checker supplies the separate evidence
boundary. A rejected article is not a negative native judgment. In particular,
public visibility of an equation does not authorize it as a selected PeTTa
rule. The selected-rule comparison requires the existing `NoFactEquations`
condition. These are finite one-step contracts, not whole-dialect evaluation
or a comparison with CeTTa's finite-Horn quotation ABI.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace

open Mettapedia.Languages.MeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa (PeTTaSpace)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis


/-- The semantic type asks for a particular copy of an answer, rather than
only for its payload. Ordinals are per payload, not PeTTa list positions. -/
def queryOccurrenceType (space : PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) : GSLTNativeType (MeTTaZero.queryGSLT PeTTa.MeTTaZeroExtension.model) :=
  exactTargetNativeType (MeTTaZero.queryGSLT PeTTa.MeTTaZeroExtension.model)
    (.answer space pattern template occurrence result)

def QueryMember (space : PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) : Prop :=
  (gsltOSLF (MeTTaZero.queryGSLT PeTTa.MeTTaZeroExtension.model)).satisfies (S := ())
    (.request space pattern template)
    (queryOccurrenceType space pattern template result occurrence).pred

theorem queryMember_iff (space : PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) :
    QueryMember space pattern template result occurrence ↔
      occurrence < (space.spaceMatch pattern template).count result := by
  exact (satisfies_exactTargetNativeType_iff_step
    (MeTTaZero.queryGSLT PeTTa.MeTTaZeroExtension.model) _ _).trans
      ((MeTTaZero.queryGSLT_step_iff _ _ _ _ _ _).trans (by
        rw [PeTTa.MeTTaZeroExtension.query_eq_spaceMatch]
        simp))

/-- Finite exhaustive decision. There is no fuel parameter or inference from
an interrupted enumeration. -/
def checkOccurrence (space : PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) : Bool :=
  decide (occurrence < (space.spaceMatch pattern template).count result)

theorem checkOccurrence_exact (space : PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) :
    checkOccurrence space pattern template result occurrence = true ↔
      QueryMember space pattern template result occurrence := by
  simp only [checkOccurrence, decide_eq_true_eq, queryMember_iff]

theorem checkOccurrence_refutes (space : PeTTaSpace) (pattern template result : Pattern)
    (occurrence : Nat) :
    checkOccurrence space pattern template result occurrence = false ↔
      ¬ QueryMember space pattern template result occurrence := by
  simp only [checkOccurrence, decide_eq_false_iff_not, queryMember_iff]

/-- Checking all answer copies is stronger than checking each submitted
answer separately: omission of a valid copy also causes rejection. -/
def checkPacket (space : PeTTaSpace) (pattern template : Pattern)
    (answers : List Pattern) : Bool :=
  decide ((answers : Multiset Pattern) = (space.spaceMatch pattern template : Multiset Pattern))

/-- Exact native coverage, in both directions, for every answer and ordinal.
This theorem connects the executable packet check to the source-derived
types rather than defining the types by packet acceptance. -/
theorem checkPacket_exact (space : PeTTaSpace) (pattern template : Pattern)
    (answers : List Pattern) :
    checkPacket space pattern template answers = true ↔
      ∀ result occurrence,
        occurrence < answers.count result ↔
          QueryMember space pattern template result occurrence := by
  simp only [checkPacket, decide_eq_true_eq, queryMember_iff]
  constructor
  · intro equal result occurrence
    have counts := congrArg (Multiset.count result) equal
    simpa using congrArg (fun n => occurrence < n) counts
  · intro coverage
    apply Multiset.ext.mpr
    intro result
    have left := coverage result (answers.count result)
    have right := coverage result ((space.spaceMatch pattern template).count result)
    simp only [Multiset.coe_count]
    omega

theorem checkPacket_perm (space : PeTTaSpace) (pattern template : Pattern)
    {first second : List Pattern} (sameBag : first.Perm second) :
    checkPacket space pattern template first = checkPacket space pattern template second := by
  unfold checkPacket
  rw [Multiset.coe_eq_coe.mpr sameBag]

/-- Erasing answer occurrence labels reaches the already-authored Zero root;
the space name is retained as a dispatch parameter, not inferred. -/
theorem queryMember_iff_authored (space : PeTTaSpace)
    (spaceTerm pattern template result : Pattern) :
    (∃ occurrence, QueryMember space pattern template result occurrence) ↔
      (MeTTaZero.totalTheory PeTTa.MeTTaZeroExtension.model space spaceTerm).Step
        (MeTTaZero.queryRequestPattern spaceTerm pattern template)
        (MeTTaZero.queryAnswerPattern result) := by
  rw [MeTTaZeroLanguageAdequacy.totalTheory_query_step_iff,
    PeTTa.MeTTaZeroExtension.query_eq_spaceMatch]
  simp only [queryMember_iff, Multiset.mem_coe]
  constructor
  · rintro ⟨occurrence, bound⟩
    exact List.count_pos_iff.mp (Nat.zero_lt_of_lt bound)
  · intro member
    exact ⟨0, List.count_pos_iff.mpr member⟩

def queryClaim (space : PeTTaSpace) (spaceTerm pattern template result : Pattern) :
    MeTTaZeroNativeKernel.Claim PeTTa.MeTTaZeroExtension.model :=
  ⟨.query space spaceTerm pattern template, result⟩

/-- Reuse the native source article checker, retaining candidate, source-copy
ordinal, bindings and matcher-copy ordinal. -/
def checkArticle (space : PeTTaSpace) (spaceTerm pattern template result : Pattern)
    (article : MeTTaZeroStagedAdequacy.ObservationProof) : Bool :=
  (MeTTaZeroNativeKernel.proofKernel PeTTa.MeTTaZeroExtension.model).decide
    (queryClaim space spaceTerm pattern template result) article

theorem accepted_article_iff_native (space : PeTTaSpace)
    (spaceTerm pattern template result : Pattern) :
    (∃ article, checkArticle space spaceTerm pattern template result article = true) ↔
      ∃ occurrence, QueryMember space pattern template result occurrence := by
  rw [queryMember_iff_authored space spaceTerm pattern template result]
  change (∃ article, (MeTTaZeroNativeKernel.proofKernel PeTTa.MeTTaZeroExtension.model).decide
    (queryClaim space spaceTerm pattern template result) article = true) ↔
      (queryClaim space spaceTerm pattern template result).Meaning
  rw [← MeTTaZeroNativeKernel.decision_accepts_iff_proof_accepted, (MeTTaZeroNativeKernel.decisionKernel PeTTa.MeTTaZeroExtension.model).correct]

/-- Any bag observation can be transported through the existing PeTTa
realization. A list-order observation requires a different contract. -/
theorem packet_observation (space : PeTTaSpace) (pattern template : Pattern)
    (answers : List Pattern) (accepted : checkPacket space pattern template answers = true)
    (observation : Multiset Pattern → Prop) :
    observation (answers : Multiset Pattern) ↔
      observation (MeTTaZero.query PeTTa.MeTTaZeroExtension.model space pattern template) := by
  have exactBag := of_decide_eq_true accepted
  rw [PeTTa.MeTTaZeroExtension.query_eq_spaceMatch, exactBag]

/-- Exactness of the pure selected-rule service is conditional on the real
authority boundary. Equations stored as ordinary facts violate it. -/
theorem positive_articles_iff_selected_rules (space : PeTTaSpace)
    (subject result : Pattern) (authority : PeTTa.MeTTaZeroExtension.NoFactEquations space) :
    (∃ article, MeTTaZeroStagedAdequacy.checkProductionProof PeTTa.MeTTaZeroExtension.model
      (.evaluate space subject) result article = true) ↔
      result ∈ PeTTa.MeTTaZeroExtension.premiseFreeRuleResults space subject := by
  rw [PeTTa.MeTTaZeroExtension.accepted_positive_iff_rule_application space subject result authority,
    PeTTa.MeTTaZeroExtension.mem_premiseFreeRuleResults]

end Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace
