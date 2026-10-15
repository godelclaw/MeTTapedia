import Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical

open Mettapedia.OSLF.Framework

/-!
# Operational controls on the original rho canonical backend

These controls execute the original language, including its equation-aware
channel matching and reflective substitution. Negative contexts are semantic
absence results with complete successor coverage, not conclusions from a
paused empty search.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement

def zero : Pattern := .apply "PZero" []
def channel : Pattern := .apply "NQuote" [zero]
def input : Pattern := .apply "PInput" [channel, .lambda none zero]
def output : Pattern := .apply "POutput" [channel, zero]
def redex : Pattern := .collection .hashBag [input, output] none
def parallelRedex : Pattern := .collection .hashBag [zero, redex] none
def payloadRedex : Pattern := .apply "POutput" [channel, redex]
def guardedRedex : Pattern := .apply "PInput" [channel, .lambda none redex]
def quotedRedex : Pattern := .apply "POutput" [.apply "NQuote" [redex], zero]
def stuckOutput : Pattern := .apply "POutput" [channel, zero]

def equivalentChannelRedex : Pattern :=
  .collection .hashBag
    [.apply "PInput" [.apply "NQuote" [.apply "PDrop" [channel]], .lambda none zero], output] none

def reflectiveRedex : Pattern :=
  .collection .hashBag
    [.apply "PInput" [channel, .lambda none (.apply "PDrop" [.bvar 0])], output] none

def duplicateRedex : Pattern := .collection .hashBag [input, input, output] none

theorem every_source_admitted :
    [zero, redex, parallelRedex, payloadRedex, guardedRedex, quotedRedex,
      stuckOutput, equivalentChannelRedex, reflectiveRedex, duplicateRedex].all admit = true := by
  cbv

theorem root_communication :
    ∃ item ∈ receipts redex, item.target = zero := by
  have step := rhoRewriteSystem_reduces_to_gsltStep closedCommSource_reduces_closedCommTarget
  have result := receipt_complete step
  change ∃ item ∈ receipts redex,
    item.target = canonicalize (.collection .hashBag [zero] none) at result
  rw [canonicalize_parallel_singleton] at result
  have fixed : canonicalize zero = zero :=
    canonicalize_eq_of_isCanonical (by simp [zero, IsCanonical, IsCanonicalList])
  rwa [fixed] at result

/-- No arbitrary constructor permits reduction below its arguments. -/
theorem constructor_receipts_empty (label : String) (arguments : List Pattern)
    (notQuote : label ≠ "NQuote") : receipts (.apply label arguments) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro item listed
  obtain ⟨bindings, matched, _⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness.rhoStepAt_one_inv
      (receipt_primitive listed)
  obtain ⟨elements, rest, i, hi, j, hj, name, body, binder, outName, payload,
    shape, _⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.rhoComm_match_shape matched
  rw [canonicalize_apply_general label arguments (fun quote => notQuote quote.1)] at shape
  cases shape

theorem output_payload_blocked (name payload : Pattern) :
    receipts (.apply "POutput" [name, payload]) = [] :=
  constructor_receipts_empty _ _ (by decide)

theorem input_guard_blocked (name body : Pattern) :
    receipts (.apply "PInput" [name, .lambda none body]) = [] :=
  constructor_receipts_empty _ _ (by decide)

theorem quoted_channel_blocked (process payload : Pattern) :
    receipts (.apply "POutput" [.apply "NQuote" [process], payload]) = [] :=
  constructor_receipts_empty _ _ (by decide)

theorem completed_normal_forms :
    [zero, payloadRedex, guardedRedex, quotedRedex, stuckOutput].all
      (fun source => closed 0 source && (targets 0 source).isEmpty) = true := by
  simp [zero, payloadRedex, guardedRedex, quotedRedex, stuckOutput, closed, targets,
    frontier, output_payload_blocked, input_guard_blocked,
    constructor_receipts_empty "PZero" [] (by decide)]

theorem paused_empty_is_not_complete :
    targets 0 redex = [] ∧ closed 0 redex = false := by
  constructor
  · rfl
  · apply Bool.eq_false_of_not_eq_true
    intro complete
    obtain ⟨item, listed, _⟩ := root_communication
    have absent : receipts redex = [] := by
      rw [← complete_frontier complete]
      rfl
    rw [absent] at listed
    exact List.not_mem_nil listed

theorem capture_rejected :
    admit (.apply "PInput" [channel, .lambda none
      (.apply "PDrop" [.apply "NQuote" [.apply "PDrop" [.bvar 0]]])]) = false := by
  cbv

theorem incorrect_sort_rejected : admit (.apply "POutput" [zero, zero]) = false := by
  cbv

theorem forbidden_output_semantics (source : RhoProcess) (name payload : Pattern)
    (shape : source.1 = .apply "POutput" [name, payload]) :
    ∀ target : RhoProcess, ¬ rhoLanguageDefGSLT.Step source target := by
  apply certified_empty_absence (budget := 0)
  · unfold closed
    rw [shape, output_payload_blocked]
    decide
  · simp [frontier]

theorem forbidden_input_semantics (source : RhoProcess) (name body : Pattern)
    (shape : source.1 = .apply "PInput" [name, .lambda none body]) :
    ∀ target : RhoProcess, ¬ rhoLanguageDefGSLT.Step source target := by
  apply certified_empty_absence (budget := 0)
  · unfold closed
    rw [shape, input_guard_blocked]
    decide
  · simp [frontier]

/-- Quotation has two distinct process origins even on the smallest name. -/
theorem quotation_origin_separation :
    canonicalize (.apply "NQuote" [zero]) =
      canonicalize (.apply "NQuote" [.apply "PDrop" [channel]]) ∧
    canonicalize zero ≠ canonicalize (.apply "PDrop" [channel]) := by
  constructor
  · rfl
  · intro same
    have labels := (Pattern.apply.inj same).1
    exact (by decide : ("PZero" : String) ≠ "PDrop") labels

#guard (targets 1 redex) == [zero]
#guard (targets 1 parallelRedex) == [zero]
#guard (targets 1 equivalentChannelRedex) == [zero]
#guard (targets 1 reflectiveRedex) == [zero]
#guard closed 0 stuckOutput && (targets 0 stuckOutput).isEmpty
#guard closed 0 payloadRedex && (targets 0 payloadRedex).isEmpty
#guard closed 0 guardedRedex && (targets 0 guardedRedex).isEmpty
#guard closed 0 quotedRedex && (targets 0 quotedRedex).isEmpty
#guard (receipts duplicateRedex).map Receipt.alternativeIndex == [0, 1]
#guard (receipts duplicateRedex).map Receipt.target == [input, input]
#guard receipts (.collection .hashBag [output, input] none) == receipts redex
#guard admit (.collection .hashBag
  [input, .apply "POutput" [.apply "NQuote" [stuckOutput], zero]] none) &&
  closed 0 (.collection .hashBag
    [input, .apply "POutput" [.apply "NQuote" [stuckOutput], zero]] none)
#guard (targets 0 redex).isEmpty && !closed 0 redex

#print axioms constructor_receipts_empty
#print axioms forbidden_output_semantics
#print axioms forbidden_input_semantics
#print axioms quotation_origin_separation

end Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls
