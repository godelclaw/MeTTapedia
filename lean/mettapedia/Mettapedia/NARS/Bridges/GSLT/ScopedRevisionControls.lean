import Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus

/-!
# Nested revision, overlap choice, and source-scope controls

Three identified observations support two nested core revisions. The checked
proof retains the source contracts and produces the exact sum of their binary
counts. Reusing the first observation fails the source-disjointness contract;
confidence choice retains it without manufacturing additional counts.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.GSLT.ScopedRevisionControls

open scoped NNReal ENNReal

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence.PathScopedBelief
open Mettapedia.NARS.Bridges.PLN
open Mettapedia.NARS.Bridges.PLN.RevisionSemantics
open Mettapedia.NARS.Bridges.PLN.SecondOrderProbability
open Mettapedia.NARS.TruthFunctions
open ScopedRevisionCalculus

def left : Pattern := app "left" []
def right : Pattern := app "right" []
def third : Pattern := app "third" []
def firstCounts : Pattern := app "e1" []
def secondCounts : Pattern := app "e2" []
def thirdCounts : Pattern := app "e3" []

private noncomputable def observation (index : Fin 3) : PathScopedBelief Unit (Fin 3) where
  statement := ()
  truth := if index.val = 0 then ⟨3/4, 1/2⟩ else if index.val = 1 then ⟨1/4, 1/2⟩ else ⟨1/2, 1/2⟩
  path := {steps := [.observation ()], sources := {index}}

noncomputable def model : Model where
  Statement := Unit
  Source := Fin 3
  sourceDecidableEq := inferInstance
  atomBelief name := if name = left then observation 0 else if name = right then observation 1
    else observation 2
  atomCounts name := EvidenceTranslation.TV.toEvidence
    (if name = firstCounts then observation 0 else if name = secondCounts then observation 1
      else observation 2).truth

private theorem belief_left : model.belief left = observation 0 := by
  rw [left, app, Model.belief] <;> simp [model, left, app]
  rfl

private theorem belief_right : model.belief right = observation 1 := by
  rw [right, app, Model.belief] <;> simp [model, left, right, app]
  rfl

private theorem belief_third : model.belief third = observation 2 := by
  rw [third, app, Model.belief] <;> simp [model, left, right, app]
  rfl

private theorem summary_first : model.summary firstCounts =
    EvidenceTranslation.TV.toEvidence (observation 0).truth := by
  rw [firstCounts, app, Model.summary] <;> simp [model, firstCounts, app]

private theorem summary_second : model.summary secondCounts =
    EvidenceTranslation.TV.toEvidence (observation 1).truth := by
  rw [secondCounts, app, Model.summary] <;> simp [model, firstCounts, secondCounts, app]

private theorem summary_third : model.summary thirdCounts =
    EvidenceTranslation.TV.toEvidence (observation 2).truth := by
  rw [thirdCounts, app, Model.summary] <;> simp [model, firstCounts, secondCounts, app]

def inner : Pattern := revision left right

def context : List Pattern :=
  [sameStatement left right, disjoint left right, validBelief left, validBelief right,
    counts left firstCounts, counts right secondCounts,
    sameStatement inner third, disjoint inner third, validBelief third, counts third thirdCounts]

def innerProof : RawOpenProof :=
  .node ⟨⟨"revise-counts"⟩, [left, right, firstCounts, secondCounts]⟩
    [.premise 0, .premise 1, .premise 2, .premise 3, .premise 4, .premise 5]

def innerValidProof : RawOpenProof :=
  .node ⟨⟨"revise-valid"⟩, [left, right]⟩ [.premise 0, .premise 1, .premise 2, .premise 3]

def proof : RawOpenProof :=
  .node ⟨⟨"revise-counts"⟩, [inner, third, countSum firstCounts secondCounts, thirdCounts]⟩
    [.premise 6, .premise 7, innerValidProof, .premise 8, innerProof, .premise 9]

def conclusion : Pattern :=
  counts (revision inner third) (countSum (countSum firstCounts secondCounts) thirdCounts)

theorem nested_proof_checks : checkOpenRaw validated context conclusion proof = true := by
  decide +kernel

theorem context_holds : ∀ premise ∈ context, model.meaning premise := by
  intro premise member
  simp only [context, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [sameStatement, disjoint, validBelief, counts, app, Model.meaning]
    simp only [inner, revision, app, Model.belief_revision, belief_left, belief_right,
      belief_third, summary_first, summary_second, summary_third]
  all_goals
    first
    | rfl
    | decide +kernel
    | norm_num [IsProbTV, observation, revisionCandidate]

/-- A real nested checker derivation composes the count interpretation. -/
theorem nested_counts_sound : model.meaning conclusion :=
  checked_proof_sound model context conclusion proof nested_proof_checks context_holds

theorem nested_counts_value :
    EvidenceTranslation.TV.toEvidence (model.belief (revision inner third)).truth =
      (⟨3/2, 3/2⟩ : Mettapedia.PLN.Evidence.BinaryEvidence) := by
  have sound := nested_counts_sound
  change EvidenceTranslation.TV.toEvidence (model.belief (revision inner third)).truth =
    model.summary (countSum (countSum firstCounts secondCounts) thirdCounts) at sound
  rw [sound]
  simp only [countSum, app, Model.summary_sum, summary_first, summary_second, summary_third]
  simp only [observation]
  have finite : (3/4 : ℝ≥0) + 1/4 + 1/2 = 3/2 := by norm_num
  have cast := congrArg (fun value : ℝ≥0 => (value : ℝ≥0∞)) finite
  have mass : (3/4 : ℝ≥0∞) + 4⁻¹ + 2⁻¹ = 3/2 := by
    simpa only [ENNReal.coe_add, ENNReal.coe_div', ENNReal.coe_inv', ENNReal.coe_one,
      ENNReal.coe_ofNat, one_div] using cast
  ext <;> norm_num [EvidenceTranslation.TV.toEvidence, c2w,
    Mettapedia.PLN.Evidence.BinaryEvidence.hplus_def, ENNReal.ofReal_div_of_pos]
  all_goals simpa only [add_comm] using mass

/-- The source union is retained, so the first observation cannot be licensed
as fresh evidence after the two revisions. -/
theorem repeated_source_is_not_disjoint :
    ¬ model.meaning (disjoint (revision inner third) left) := by
  simp only [disjoint, app, Model.meaning, revision, Model.belief_revision, inner,
    belief_left, belief_right, belief_third]
  change ¬ Disjoint ((({0} : Finset (Fin 3)) ∪ {1}) ∪ {2}) {0}
  decide +kernel

def choiceContext : List Pattern :=
  [sameStatement left left, overlap left left, confidenceLe left left, counts left firstCounts]

def choiceProof : RawOpenProof :=
  .node ⟨⟨"choose-left"⟩, [left, left, firstCounts]⟩
    [.premise 0, .premise 1, .premise 2, .premise 3]

theorem choice_proof_checks :
    checkOpenRaw validated choiceContext (counts (choice left left) firstCounts) choiceProof = true := by
  decide +kernel

theorem choice_context_holds : ∀ premise ∈ choiceContext, model.meaning premise := by
  intro premise member
  simp only [choiceContext, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    simp only [sameStatement, overlap, confidenceLe, counts, app, Model.meaning,
      belief_left, summary_first]
  all_goals first | rfl | exact le_rfl | decide +kernel

theorem overlap_choice_preserves_counts : model.meaning (counts (choice left left) firstCounts) :=
  checked_proof_sound model choiceContext _ choiceProof choice_proof_checks choice_context_holds

/-- Omitting the scope premise is rejected by the actual proof checker. -/
theorem missing_scope_premise_rejected :
    checkOpenRaw validated context (counts inner (countSum firstCounts secondCounts))
      (.node ⟨⟨"revise-counts"⟩, [left, right, firstCounts, secondCounts]⟩
        [.premise 0, .premise 2, .premise 3, .premise 4, .premise 5]) = false := by
  decide +kernel

end Mettapedia.NARS.Bridges.GSLT.ScopedRevisionControls
