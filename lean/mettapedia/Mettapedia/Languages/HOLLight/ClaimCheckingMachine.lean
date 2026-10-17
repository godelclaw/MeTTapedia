import Mettapedia.Languages.HOLLight.SourceQuantifierEmission
import Mettapedia.Languages.HOLLight.InferenceCompiler
import Mettapedia.GSLT.LanguageDef.SharedReferenceExecution

/-!
# Executed source-claim comparison against the original HOL theorem

The supplied source pattern and original theorem are independent serialized
fields. The machine renders the source judgment, extracts the theorem's actual
sequent, and compares the complete hypothesis and conclusion fields. Axiom
provenance stays in the caller's theorem; it is not replaced by the claim guard.
The input domain is every original encoded pattern/theorem pair, including
invalid source scope. Arbitrary malformed packets and chronological cache
lookup belong to separate admission and driver joins.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ClaimCheckingMachine
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open ArgumentRenderingMachine InferenceStorageBounds InferenceHosting
open Mettapedia.Logic.HOL.Embedding.InferenceRules (encode judgment)

abbrev expected (goal : Pattern) : Sequent := ⟨∅, InferenceCompiler.compileClaim goal⟩
def expectedWire (goal : Pattern) : List Alphabet := encodeWith sequentCodec (expected goal)

/-- Fixed original sequent and HOL application framing, with one raw argument hole. -/
def opening : List Alphabet :=
  [4] ++ encodeData ((finsetCodec canonicalCodec).put ∅) ++ [4, 4] ++
    encodeData (.atom 3) ++ [4] ++ encodeData (putTerm holdsTerm)
def closing : List Alphabet := encodeData (putTy Ty.bool)
def claimTemplate : Template Alphabet := opening.map some ++ [none] ++ closing.map some

theorem raw_eq (goal : Pattern) :
    SourceQuantifierEmission.rawWire goal = encodeWith dbTermCodec (dataTerm goal) := by
  apply congrArg (encodeWith dbTermCodec)
  change ReverseTranslation.reverseTerm ReverseTranslation.Naming.empty (term (encode goal)) = _
  rw [ReverseTranslation.reverseTerm_eq_reverseTermOpen, render_encode]

theorem claimTemplate_exact (goal : Pattern) :
    instantiate claimTemplate (SourceQuantifierEmission.rawWire goal) = expectedWire goal := by
  rw [raw_eq]
  simp only [claimTemplate, instantiate, List.flatMap_append, List.flatMap_map,
    List.flatMap_cons, List.flatMap_nil]
  simp only [List.flatMap_singleton', List.append_nil]
  simp only [expectedWire, expected, encodeWith, sequentCodec, Codec.mapped, Codec.prod,
    canonicalCodec, InferenceCompiler.compileClaim, render_judgment_term]
  change opening ++ encodeData (putTerm (dataTerm goal)) ++ closing =
    encodeData (.pair ((finsetCodec canonicalCodec).put ∅)
      (.pair (putTerm (.app holdsTerm (dataTerm goal))) (putTy Ty.bool)))
  simp [opening, closing, putTerm, encodeData_pair, List.append_assoc]

local instance : Fintype (SourceQuantifierEmission.renderMachine.Γ
    SourceQuantifierEmission.renderMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (SourceQuantifierEmission.renderMachine.Γ
    SourceQuantifierEmission.renderMachine.k₁) := inferInstanceAs (Inhabited Alphabet)

def claimMachine : FinTM2 := StackMachineComposition.machine
  SourceQuantifierEmission.renderMachine (WordTemplateMachine.machine claimTemplate) (Equiv.refl Alphabet)

def claimClock (goal : Pattern) : Nat :=
  3000100000 * ((patternWire goal).length + 1)^3 +
    (4 * (claimTemplate.length + 1) + 2) * ((SourceQuantifierEmission.rawWire goal).length + 1)

noncomputable def claimOutputs (goal : Pattern) (valid : argumentValidAt 0 goal = true) :
    TM2OutputsInTime claimMachine (patternWire goal) (some (expectedWire goal)) (claimClock goal) := by
  have wrapped := WordTemplateMachine.outputs claimTemplate (SourceQuantifierEmission.rawWire goal)
  rw [claimTemplate_exact] at wrapped
  have joined := StackMachineComposition.outputs SourceQuantifierEmission.renderMachine
    (WordTemplateMachine.machine claimTemplate) (Equiv.refl Alphabet)
    (patternWire goal) (SourceQuantifierEmission.rawWire goal) (expectedWire goal) _ _
    (SourceQuantifierEmission.renderOutputs goal valid) (by
      change TM2OutputsInTime (WordTemplateMachine.machine claimTemplate)
        ((SourceQuantifierEmission.rawWire goal).map id) _ _
      simpa only [List.map_id] using wrapped)
  apply WordEqualityMachine.within joined
  unfold claimClock
  nlinarith

abbrev sequentField := Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.machine true
local instance : Fintype (sequentField.Γ sequentField.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (sequentField.Γ sequentField.k₁) := inferInstanceAs (Inhabited Alphabet)
def sequentMachine : FinTM2 := StackMachineComposition.machine sequentField
  SourceQuantifierEmission.stripStatus (Equiv.refl Alphabet)

theorem sequent_length_le (out : Theorem) :
    (encodeWith sequentCodec out.sequent).length ≤ (encodeWith theoremCodec out).length := by
  exact Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.selected_length_le true
    ((finsetCodec sequentCodec).put out.axioms) (sequentCodec.put out.sequent)

noncomputable def sequentOutputs (out : Theorem) :
    TM2OutputsInTime sequentMachine (encodeWith theoremCodec out)
      (some (encodeWith sequentCodec out.sequent)) (10 * ((encodeWith theoremCodec out).length + 1)) := by
  have selected := (Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.selectSecondCodec
    (finsetCodec sequentCodec) sequentCodec).outputsFun (out.axioms, out.sequent)
  dsimp only [Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.selectSecondCodec,
    Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.computable,
    Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.successEncoding] at selected
  simp only [eval_add, eval_mul, eval_C, eval_X] at selected
  change TM2OutputsInTime sequentField ((encodeWith theoremCodec out).map id)
    (some (((1 : Alphabet) :: encodeWith sequentCodec out.sequent).map id))
    (4 * (encodeWith theoremCodec out).length + 3) at selected
  simp only [List.map_id] at selected
  have copied := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol])
    (encodeWith sequentCodec out.sequent)
  simp only [List.flatMap_singleton'] at copied
  have stripped := StackMachineComposition.Dispatch.outputs_success SourceQuantifierEmission.rawIdentity
    AdmittedArgumentRendering.accept [] (1 : Alphabet) (encodeWith sequentCodec out.sequent)
    (encodeWith sequentCodec out.sequent) _ (by decide) copied
  have joined := StackMachineComposition.outputs sequentField SourceQuantifierEmission.stripStatus
    (Equiv.refl Alphabet) (encodeWith theoremCodec out) ((1 : Alphabet) :: encodeWith sequentCodec out.sequent)
    (encodeWith sequentCodec out.sequent) _ _ selected (by
      change TM2OutputsInTime SourceQuantifierEmission.stripStatus
        (((1 : Alphabet) :: encodeWith sequentCodec out.sequent).map id) _ _
      simpa only [List.map_id, SourceQuantifierEmission.stripStatus] using stripped)
  apply WordEqualityMachine.within joined
  have bounded := sequent_length_le out
  simp only [List.length_cons]
  omega

theorem sequent_eq_iff (goal : Pattern) (out : Theorem) :
    out.sequent = expected goal ↔
      out.sequent.hyp = ∅ ∧ out.sequent.concl = InferenceCompiler.compileClaim goal := by
  cases out.sequent
  simp only [expected, Sequent.mk.injEq]

theorem word_comparison (goal : Pattern) (out : Theorem) :
    decide (expectedWire goal = encodeWith sequentCodec out.sequent) =
      InferenceCompiler.hasClaim goal out := by
  unfold expectedWire InferenceCompiler.hasClaim
  congr 1
  apply propext
  rw [(encodeWith_injective sequentCodec).eq_iff, eq_comm, sequent_eq_iff]


/-- Independent submitted fields; no expected target claim is supplied. -/
def fields (goal : Pattern) (out : Theorem) : Fin 2 → List Alphabet :=
  ![patternWire goal, encodeWith theoremCodec out]
def inputWire (goal : Pattern) (out : Theorem) : List (Option Alphabet) := Indexed.argumentWire (fields goal out)
def claimSelector : Indexed.Template Alphabet 2 := [.inr 0]
local instance : Fintype ((Indexed.machine claimSelector).Γ (Indexed.machine claimSelector).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine claimSelector).Γ (Indexed.machine claimSelector).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Fintype (claimMachine.Γ claimMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (claimMachine.Γ claimMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def selectedClaimMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine claimSelector)
  claimMachine (Equiv.refl Alphabet)
local instance : Fintype (selectedClaimMachine.Γ selectedClaimMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedClaimMachine.Γ selectedClaimMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (selectedClaimMachine.Γ selectedClaimMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def claimedMachine : FinTM2 := RetainedWordExecution.WithOutput.Framed.machine selectedClaimMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
def claimedFields (goal : Pattern) (out : Theorem) : Fin 3 → List Alphabet :=
  ![patternWire goal, encodeWith theoremCodec out, expectedWire goal]
def claimedWire (goal : Pattern) (out : Theorem) : List (Option Alphabet) :=
  Indexed.argumentWire (claimedFields goal out)
def selectedClaimClock (goal : Pattern) (out : Theorem) : Nat :=
  8 * ((inputWire goal out).length + 1) + 2 * (patternWire goal).length + 2 + claimClock goal

theorem claimed_framing (goal : Pattern) (out : Theorem) :
    claimedWire goal out = inputWire goal out ++ (expectedWire goal).map some ++ [none] := by
  simp [claimedWire, claimedFields, inputWire, fields, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc]

noncomputable def selectedClaimOutputs (goal : Pattern) (out : Theorem) (valid : argumentValidAt 0 goal = true) :
    TM2OutputsInTime selectedClaimMachine (inputWire goal out) (some (expectedWire goal))
      (selectedClaimClock goal out) := by
  have selected := Indexed.outputs claimSelector (fields goal out)
  have rendered := claimOutputs goal valid
  have selectedExact : Indexed.instantiate claimSelector (fields goal out) = patternWire goal := by
    simp [claimSelector, fields]
  rw [selectedExact] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine claimSelector) claimMachine
    (Equiv.refl Alphabet) (inputWire goal out) (patternWire goal) (expectedWire goal) _ _ selected (by
      change TM2OutputsInTime claimMachine ((patternWire goal).map id) _ _
      simpa only [List.map_id] using rendered)
  apply WordEqualityMachine.within joined
  simp only [claimSelector, List.length_cons, List.length_nil, selectedClaimClock, inputWire]
  omega

def claimedClock (goal : Pattern) (out : Theorem) : Nat :=
  selectedClaimClock goal out + 23 * (inputWire goal out).length + 22 * (expectedWire goal).length + 23

noncomputable def claimedOutputs (goal : Pattern) (out : Theorem) (valid : argumentValidAt 0 goal = true) :
    TM2OutputsInTime claimedMachine (inputWire goal out) (some (claimedWire goal out))
      (claimedClock goal out) := by
  have saved := RetainedWordExecution.WithOutput.Framed.outputs selectedClaimMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire goal out) (expectedWire goal)
    _ (selectedClaimOutputs goal out valid)
  have framing : RetainedWordExecution.WithOutput.Framed.outputWord selectedClaimMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire goal out) (expectedWire goal) =
      claimedWire goal out := by
    change (inputWire goal out).map id ++ (expectedWire goal).map some ++ [none] = _
    rw [List.map_id, claimed_framing]
  rw [framing] at saved
  exact saved

def sequentSelector : Indexed.Template Alphabet 3 := [.inr 1]
local instance : Fintype ((Indexed.machine sequentSelector).Γ (Indexed.machine sequentSelector).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine sequentSelector).Γ (Indexed.machine sequentSelector).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def selectedSequentMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine sequentSelector)
  sequentMachine (Equiv.refl Alphabet)
local instance : Fintype (selectedSequentMachine.Γ selectedSequentMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedSequentMachine.Γ selectedSequentMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (selectedSequentMachine.Γ selectedSequentMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def projectedMachine : FinTM2 := RetainedWordExecution.WithOutput.Framed.machine selectedSequentMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
def projectedFields (goal : Pattern) (out : Theorem) : Fin 4 → List Alphabet :=
  ![patternWire goal, encodeWith theoremCodec out, expectedWire goal, encodeWith sequentCodec out.sequent]
def projectedWire (goal : Pattern) (out : Theorem) : List (Option Alphabet) :=
  Indexed.argumentWire (projectedFields goal out)
def selectedSequentClock (goal : Pattern) (out : Theorem) : Nat :=
  8 * ((claimedWire goal out).length + 1) + 12 * ((encodeWith theoremCodec out).length + 1)
def projectedClock (goal : Pattern) (out : Theorem) : Nat :=
  selectedSequentClock goal out + 23 * (claimedWire goal out).length +
    22 * (encodeWith sequentCodec out.sequent).length + 23

noncomputable def selectedSequentOutputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime selectedSequentMachine (claimedWire goal out)
      (some (encodeWith sequentCodec out.sequent)) (selectedSequentClock goal out) := by
  have selected := Indexed.outputs sequentSelector (claimedFields goal out)
  have selectedExact : Indexed.instantiate sequentSelector (claimedFields goal out) = encodeWith theoremCodec out := by
    simp [sequentSelector, claimedFields]
  rw [selectedExact] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine sequentSelector) sequentMachine
    (Equiv.refl Alphabet) (claimedWire goal out) (encodeWith theoremCodec out)
    (encodeWith sequentCodec out.sequent) _ _ selected (by
      change TM2OutputsInTime sequentMachine ((encodeWith theoremCodec out).map id) _ _
      simpa only [List.map_id] using sequentOutputs out)
  apply WordEqualityMachine.within joined
  simp only [sequentSelector, List.length_cons, List.length_nil, selectedSequentClock, claimedWire]
  omega

theorem projected_framing (goal : Pattern) (out : Theorem) :
    projectedWire goal out = claimedWire goal out ++ (encodeWith sequentCodec out.sequent).map some ++ [none] := by
  simp [projectedWire, projectedFields, claimedWire, claimedFields, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc]

noncomputable def projectedOutputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime projectedMachine (claimedWire goal out) (some (projectedWire goal out))
      (projectedClock goal out) := by
  have saved := RetainedWordExecution.WithOutput.Framed.outputs selectedSequentMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (claimedWire goal out) (encodeWith sequentCodec out.sequent)
    _ (selectedSequentOutputs goal out)
  have framing : RetainedWordExecution.WithOutput.Framed.outputWord selectedSequentMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (claimedWire goal out) (encodeWith sequentCodec out.sequent) =
      projectedWire goal out := by
    change (claimedWire goal out).map id ++ (encodeWith sequentCodec out.sequent).map some ++ [none] = _
    rw [List.map_id, projected_framing]
  rw [framing] at saved
  exact saved


namespace Comparison
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck (liftSymbol lift_frame lifted_length)
def fields (goal : Pattern) (out : Theorem) : Fin 4 → List (Option Alphabet) :=
  fun index => (projectedFields goal out index).map some
def wire (goal : Pattern) (out : Theorem) : List (Option (Option Alphabet)) := Indexed.argumentWire (fields goal out)
def selector : Indexed.Template (Option Alphabet) 4 := [.inr 2, .inl none, .inr 3]

theorem lift_exact (goal : Pattern) (out : Theorem) :
    (projectedWire goal out).flatMap liftSymbol = wire goal out := by
  unfold projectedWire Indexed.argumentWire
  rw [lift_frame]
  simp only [List.map_map, Function.comp_def]
  rfl

theorem selector_exact (goal : Pattern) (out : Theorem) :
    Indexed.instantiate selector (fields goal out) =
      WordEqualityMachine.packet (expectedWire goal) (encodeWith sequentCodec out.sequent) := by
  simp [selector, fields, projectedFields, WordEqualityMachine.packet]

local instance : Fintype ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def compareMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine selector)
  (WordEqualityMachine.machine Alphabet) (Equiv.refl (Option Alphabet))
local instance : Fintype ((WordHomomorphismMachine.machine liftSymbol).Γ
    (WordHomomorphismMachine.machine liftSymbol).k₁) := inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance : Inhabited ((WordHomomorphismMachine.machine liftSymbol).Γ
    (WordHomomorphismMachine.machine liftSymbol).k₁) := inferInstanceAs (Inhabited (Option (Option Alphabet)))
def machine : FinTM2 := StackMachineComposition.machine (WordHomomorphismMachine.machine liftSymbol)
  compareMachine (Equiv.refl (Option (Option Alphabet)))

def clock (goal : Pattern) (out : Theorem) : Nat :=
  22 * ((projectedWire goal out).length + 1) +
    5 * (expectedWire goal).length + 3 * (encodeWith sequentCodec out.sequent).length + 8

noncomputable def outputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime machine (projectedWire goal out) (some [InferenceCompiler.hasClaim goal out])
      (clock goal out) := by
  have lifted := WordHomomorphismMachine.outputs liftSymbol (projectedWire goal out)
  have length := lifted_length (projectedWire goal out)
  rw [lift_exact] at lifted length
  have selected := Indexed.outputs selector (fields goal out)
  rw [selector_exact] at selected
  have compared := WordEqualityMachine.outputs (expectedWire goal) (encodeWith sequentCodec out.sequent)
  rw [word_comparison] at compared
  have second := StackMachineComposition.outputs (Indexed.machine selector) (WordEqualityMachine.machine Alphabet)
    (Equiv.refl (Option Alphabet)) (wire goal out)
    (WordEqualityMachine.packet (expectedWire goal) (encodeWith sequentCodec out.sequent))
    [InferenceCompiler.hasClaim goal out] _ _ selected (by
      change TM2OutputsInTime (WordEqualityMachine.machine Alphabet)
        ((WordEqualityMachine.packet (expectedWire goal) (encodeWith sequentCodec out.sequent)).map id) _ _
      simpa only [List.map_id] using compared)
  have joined := StackMachineComposition.outputs (WordHomomorphismMachine.machine liftSymbol) compareMachine
    (Equiv.refl (Option (Option Alphabet))) (projectedWire goal out) (wire goal out)
    [InferenceCompiler.hasClaim goal out] _ _ lifted (by
      change TM2OutputsInTime compareMachine ((wire goal out).map id) _ _
      simpa only [List.map_id, compareMachine] using second)
  apply WordEqualityMachine.within joined
  have packetLength := WordEqualityMachine.packet_length (expectedWire goal) (encodeWith sequentCodec out.sequent)
  change 2 * (projectedWire goal out).length + 2 * (wire goal out).length + 2 +
    2 * (wire goal out).length + 2 + (16 * ((wire goal out).length + 1) +
      2 * (WordEqualityMachine.packet (expectedWire goal) (encodeWith sequentCodec out.sequent)).length + 2 +
      (3 * (expectedWire goal).length + (encodeWith sequentCodec out.sequent).length + 4)) ≤ _
  unfold clock
  omega
end Comparison

local instance : Fintype (claimedMachine.Γ claimedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (claimedMachine.Γ claimedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (projectedMachine.Γ projectedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (projectedMachine.Γ projectedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def preparedMachine : FinTM2 := StackMachineComposition.machine claimedMachine projectedMachine (Equiv.refl (Option Alphabet))
local instance : Fintype (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def successMachine : FinTM2 := StackMachineComposition.machine preparedMachine Comparison.machine (Equiv.refl (Option Alphabet))

def successClock (goal : Pattern) (out : Theorem) : Nat :=
  claimedClock goal out + 2 * (claimedWire goal out).length + 2 + projectedClock goal out +
    2 * (projectedWire goal out).length + 2 + Comparison.clock goal out

noncomputable def successOutputs (goal : Pattern) (out : Theorem) (valid : argumentValidAt 0 goal = true) :
    TM2OutputsInTime successMachine (inputWire goal out) (some [InferenceCompiler.hasClaim goal out])
      (successClock goal out) := by
  have first := StackMachineComposition.outputs claimedMachine projectedMachine (Equiv.refl (Option Alphabet))
    (inputWire goal out) (claimedWire goal out) (projectedWire goal out) _ _ (claimedOutputs goal out valid) (by
      change TM2OutputsInTime projectedMachine ((claimedWire goal out).map id) _ _
      simpa only [List.map_id] using projectedOutputs goal out)
  have joined := StackMachineComposition.outputs preparedMachine Comparison.machine (Equiv.refl (Option Alphabet))
    (inputWire goal out) (projectedWire goal out) [InferenceCompiler.hasClaim goal out] _ _ first (by
      change TM2OutputsInTime Comparison.machine ((projectedWire goal out).map id) _ _
      simpa only [List.map_id] using Comparison.outputs goal out)
  exact joined


theorem input_length (goal : Pattern) (out : Theorem) :
    (inputWire goal out).length = (patternWire goal).length + (encodeWith theoremCodec out).length + 2 := by
  simp [inputWire, fields, Indexed.argumentWire_length, List.finRange_succ]

theorem input_parts (goal : Pattern) (out : Theorem) :
    (patternWire goal).length ≤ (inputWire goal out).length ∧
      (encodeWith theoremCodec out).length ≤ (inputWire goal out).length := by
  have counted := input_length goal out
  omega

local instance : Fintype ((Indexed.machine SourceQuantifierEmission.selector).Γ
    (Indexed.machine SourceQuantifierEmission.selector).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine SourceQuantifierEmission.selector).Γ
    (Indexed.machine SourceQuantifierEmission.selector).k₁) := inferInstanceAs (Inhabited Alphabet)
local instance : Fintype (SourceQuantifierEmission.selectedScopeMachine.Γ
    SourceQuantifierEmission.selectedScopeMachine.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (SourceQuantifierEmission.selectedScopeMachine.Γ
    SourceQuantifierEmission.selectedScopeMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (SourceQuantifierEmission.savedScopeMachine.Γ
    SourceQuantifierEmission.savedScopeMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance : Inhabited (SourceQuantifierEmission.savedScopeMachine.Γ
    SourceQuantifierEmission.savedScopeMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))

/-- Reuse the same source-scope machine on the first field; the second is opaque here. -/
noncomputable def scopeOutputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime SourceQuantifierEmission.selectedScopeMachine (inputWire goal out)
      (some [some (argumentValidAt 0 goal)]) (20020 * ((inputWire goal out).length + 1)^2) := by
  have selected := Indexed.outputs SourceQuantifierEmission.selector (fields goal out)
  simp only [SourceQuantifierEmission.selector, Indexed.instantiate_hole, Indexed.instantiate_nil,
    List.append_nil, fields, Matrix.cons_val_zero] at selected
  have admissionRun := Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.outputs goal
  have joined := StackMachineComposition.outputs (Indexed.machine SourceQuantifierEmission.selector)
    SourceQuantifierEmission.scopeMachine (Equiv.refl Alphabet)
    (inputWire goal out) (patternWire goal) [some (argumentValidAt 0 goal)] _ _ selected (by
      change TM2OutputsInTime SourceQuantifierEmission.scopeMachine ((patternWire goal).map id) _ _
      simpa only [List.map_id, SourceQuantifierEmission.scopeMachine, patternWire] using admissionRun)
  apply WordEqualityMachine.within joined
  have bound := (input_parts goal out).1
  have square := Nat.pow_le_pow_left (Nat.add_le_add_right bound 1) 2
  have linear : (inputWire goal out).length + 1 ≤ ((inputWire goal out).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  change 8 * ((inputWire goal out).length + 1) + 2 * (patternWire goal).length + 2 +
    20000 * ((patternWire goal).length + 1)^2 ≤ _
  nlinarith

def tagged (goal : Pattern) (out : Theorem) : List (Option Alphabet ⊕ Bool) :=
  .inr (argumentValidAt 0 goal) :: (inputWire goal out).map Sum.inl

noncomputable def savedScopeOutputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime SourceQuantifierEmission.savedScopeMachine (inputWire goal out)
      (some (tagged goal out)) (20030 * ((inputWire goal out).length + 1)^2) := by
  have saved := RetainedWordExecution.outputs SourceQuantifierEmission.selectedScopeMachine
    AdmittedArgumentRendering.readResult (inputWire goal out) (some (argumentValidAt 0 goal)) [] _ (scopeOutputs goal out)
  change TM2OutputsInTime SourceQuantifierEmission.savedScopeMachine (inputWire goal out) (some (tagged goal out))
    (20020 * ((inputWire goal out).length + 1)^2 + 3 * (inputWire goal out).length + 0 + 5) at saved
  apply WordEqualityMachine.within saved
  have linear : (inputWire goal out).length + 1 ≤ ((inputWire goal out).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  nlinarith

theorem tagged_project (goal : Pattern) (out : Theorem) :
    (tagged goal out).flatMap SourceQuantifierEmission.project =
      SourceQuantifierEmission.status (argumentValidAt 0 goal) :: inputWire goal out := by
  simp only [tagged, List.flatMap_cons, SourceQuantifierEmission.project, List.singleton_append, List.flatMap_map]
  congr 1
  induction inputWire goal out with
  | nil => rfl
  | cons symbol rest ih => simp [ih]

noncomputable def admissionOutputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime SourceQuantifierEmission.admissionMachine (inputWire goal out)
      (some (SourceQuantifierEmission.status (argumentValidAt 0 goal) :: inputWire goal out))
      (20050 * ((inputWire goal out).length + 1)^2) := by
  have mapped := WordHomomorphismMachine.outputs SourceQuantifierEmission.project (tagged goal out)
  rw [tagged_project] at mapped
  have joined := StackMachineComposition.outputs SourceQuantifierEmission.savedScopeMachine
    (WordHomomorphismMachine.machine SourceQuantifierEmission.project) (Equiv.refl _)
    (inputWire goal out) (tagged goal out)
    (SourceQuantifierEmission.status (argumentValidAt 0 goal) :: inputWire goal out) _ _
    (savedScopeOutputs goal out) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine SourceQuantifierEmission.project)
        ((tagged goal out).map id) _ _
      simpa only [List.map_id] using mapped)
  apply WordEqualityMachine.within joined
  simp only [tagged, List.length_cons, List.length_map]
  have linear : (inputWire goal out).length + 1 ≤ ((inputWire goal out).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  nlinarith

local instance : Inhabited (successMachine.Γ successMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (successMachine.Γ successMachine.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (successMachine.Γ successMachine.k₁) := inferInstanceAs (Inhabited Bool)
def guardedMachine : FinTM2 := StackMachineComposition.Dispatch.machine successMachine
  SourceQuantifierEmission.accept [false]
local instance : Fintype (SourceQuantifierEmission.admissionMachine.Γ
    SourceQuantifierEmission.admissionMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (SourceQuantifierEmission.admissionMachine.Γ
    SourceQuantifierEmission.admissionMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def machine : FinTM2 := StackMachineComposition.machine SourceQuantifierEmission.admissionMachine
  guardedMachine (Equiv.refl (Option Alphabet))
def result (goal : Pattern) (out : Theorem) : Bool :=
  argumentValidAt 0 goal && InferenceCompiler.hasClaim goal out

def clock (goal : Pattern) (out : Theorem) : Nat :=
  20050 * ((inputWire goal out).length + 1)^2 + 3 * (inputWire goal out).length + 10 + successClock goal out

noncomputable def guardedOutputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime guardedMachine
      (SourceQuantifierEmission.status (argumentValidAt 0 goal) :: inputWire goal out)
      (some [result goal out]) (successClock goal out + (inputWire goal out).length + 6) := by
  cases valid : argumentValidAt 0 goal with
  | false =>
    have refused := StackMachineComposition.Dispatch.outputs_refused successMachine SourceQuantifierEmission.accept [false]
      (some (0 : Alphabet)) (inputWire goal out) (by decide)
    have run : TM2OutputsInTime guardedMachine
        (SourceQuantifierEmission.status false :: inputWire goal out)
        (some [result goal out]) ((inputWire goal out).length + 2) := by
      simpa [guardedMachine, result, valid, SourceQuantifierEmission.status,
        AdmittedArgumentRendering.status] using refused
    exact WordEqualityMachine.within run (by omega)
  | true =>
    have accepted := StackMachineComposition.Dispatch.outputs_success successMachine SourceQuantifierEmission.accept [false]
      (some (1 : Alphabet)) (inputWire goal out) [InferenceCompiler.hasClaim goal out]
      _ (by decide) (successOutputs goal out valid)
    have run : TM2OutputsInTime guardedMachine
        (SourceQuantifierEmission.status true :: inputWire goal out)
        (some [result goal out]) (successClock goal out + 1) := by
      simpa [guardedMachine, result, valid, SourceQuantifierEmission.status,
        AdmittedArgumentRendering.status] using accepted
    exact WordEqualityMachine.within run (by omega)

noncomputable def outputs (goal : Pattern) (out : Theorem) :
    TM2OutputsInTime machine (inputWire goal out) (some [result goal out]) (clock goal out) := by
  have joined := StackMachineComposition.outputs SourceQuantifierEmission.admissionMachine guardedMachine
    (Equiv.refl (Option Alphabet)) (inputWire goal out)
    (SourceQuantifierEmission.status (argumentValidAt 0 goal) :: inputWire goal out)
    [result goal out] _ _ (admissionOutputs goal out) (by
      change TM2OutputsInTime guardedMachine
        ((SourceQuantifierEmission.status (argumentValidAt 0 goal) :: inputWire goal out).map id) _ _
      simpa only [List.map_id] using guardedOutputs goal out)
  apply WordEqualityMachine.within joined
  simp only [clock, List.length_cons]
  omega


theorem claimed_length (goal : Pattern) (out : Theorem) :
    (claimedWire goal out).length = (inputWire goal out).length + (expectedWire goal).length + 1 := by
  rw [claimed_framing]
  simp [Nat.add_assoc]

theorem projected_length (goal : Pattern) (out : Theorem) :
    (projectedWire goal out).length = (claimedWire goal out).length +
      (encodeWith sequentCodec out.sequent).length + 1 := by
  rw [projected_framing]
  simp [Nat.add_assoc]

theorem raw_length (goal : Pattern) :
    (SourceQuantifierEmission.rawWire goal).length ≤ 7400 * ((patternWire goal).length + 1) := by
  have bounded := SourceQuantifierEmission.term_length_le (renderedArgument goal)
  have size := ArgumentVectorRendering.argument_length goal
  change (SourceQuantifierEmission.rawWire goal).length ≤ (argumentWire goal).length at bounded
  omega

theorem expected_length (goal : Pattern) :
    (expectedWire goal).length ≤ claimTemplate.length * (7401 * ((patternWire goal).length + 1)) := by
  have bounded := WordTemplateMachine.instantiate_length claimTemplate (SourceQuantifierEmission.rawWire goal)
  rw [claimTemplate_exact] at bounded
  have raw := raw_length goal
  exact bounded.trans (Nat.mul_le_mul_left _ (by omega))

/-- One fixed machine and one cubic clock, including every refusal branch.
The input size counts the entire submitted theorem, including axiom tags. -/
def coefficient : Nat := 4000000000 + 10000000 * (claimTemplate.length + 1)

theorem clock_polynomial (goal : Pattern) (out : Theorem) :
    clock goal out ≤ coefficient * ((inputWire goal out).length + 1)^3 := by
  have parts := input_parts goal out
  have raw := raw_length goal
  have expectedBound := expected_length goal
  have sequentBound := sequent_length_le out
  have cube : (inputWire goal out).length + 1 ≤ ((inputWire goal out).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  have square : ((inputWire goal out).length + 1)^2 ≤ ((inputWire goal out).length + 1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have sourceCube := Nat.pow_le_pow_left (Nat.add_le_add_right parts.1 1) 3
  have rawBound : (SourceQuantifierEmission.rawWire goal).length + 1 ≤ 7401 * ((inputWire goal out).length + 1) := by omega
  have termBound := Nat.mul_le_mul_left (4 * (claimTemplate.length + 1) + 2) rawBound
  have expectedInput := Nat.mul_le_mul_left claimTemplate.length
    (Nat.mul_le_mul_left 7401 (Nat.add_le_add_right parts.1 1))
  have weightedCube := Nat.mul_le_mul_left (claimTemplate.length + 1) cube
  unfold clock successClock claimedClock selectedClaimClock claimClock projectedClock selectedSequentClock Comparison.clock
  rw [projected_length, claimed_length]
  unfold coefficient
  nlinarith

noncomputable def realization : TM2ComputableInPolyTime
    (fun pair : Pattern × Theorem => inputWire pair.1 pair.2)
    (fun accepted : Bool => [accepted]) (fun pair : Pattern × Theorem => result pair.1 pair.2) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Bool
  time := C coefficient * (X + C 1)^3
  outputsFun pair := by
    change TM2OutputsInTime machine ((inputWire pair.1 pair.2).map id)
      (some ([result pair.1 pair.2].map id)) _
    simp only [List.map_id]
    apply WordEqualityMachine.within (outputs pair.1 pair.2)
    simpa only [eval_mul, eval_C, eval_pow, eval_add, eval_X] using clock_polynomial pair.1 pair.2

theorem run_readout (goal : Pattern) (out : Theorem) {word : List Bool}
    (finished : TM2Outputs machine (inputWire goal out) (some word)) : word = [result goal out] := by
  exact StackMachineComposition.outputs_unique finished (outputs goal out).toEvalsTo

theorem run_accepted (goal : Pattern) (out : Theorem)
    (finished : TM2Outputs machine (inputWire goal out) (some [true])) :
    argumentValidAt 0 goal = true ∧ out.sequent.hyp = ∅ ∧ out.sequent.concl = InferenceCompiler.compileClaim goal := by
  have same : result goal out = true := (List.cons.inj (run_readout goal out finished)).1.symm
  simpa only [result, Bool.and_eq_true, InferenceCompiler.hasClaim, decide_eq_true_eq] using same

theorem hypothesis_refusal (goal : Pattern) (out : Theorem) (nonempty : out.sequent.hyp ≠ ∅) :
    result goal out = false := by
  simp [result, InferenceCompiler.hasClaim, nonempty]

theorem changed_claim_refusal (goal : Pattern) (out : Theorem)
    (different : out.sequent.concl ≠ InferenceCompiler.compileClaim goal) : result goal out = false := by
  simp [result, InferenceCompiler.hasClaim, different]

theorem scope_refusal (goal : Pattern) (out : Theorem) (invalid : argumentValidAt 0 goal = false) :
    result goal out = false := by simp [result, invalid]

namespace Controls

def taggedClaim (goal : Pattern) : Theorem := Theorem.axiomResult (expected goal)
  ⟨rfl, by simp⟩

def conditionalClaim (goal : Pattern) : Theorem :=
  Theorem.emptyResult {InferenceCompiler.compileClaim goal} (InferenceCompiler.compileClaim goal)

theorem exact_claim (goal : Pattern) (valid : argumentValidAt 0 goal = true) :
    result goal (taggedClaim goal) = true := by
  simp [result, valid, InferenceCompiler.hasClaim, taggedClaim, Theorem.axiomResult, expected]

theorem conditional_claim_refused (goal : Pattern) : result goal (conditionalClaim goal) = false := by
  apply hypothesis_refusal
  exact Finset.nonempty_iff_ne_empty.mp (Finset.singleton_nonempty _)

theorem opaque_binder_accepted :
    result (.lambda none (.bvar 0)) (taggedClaim (.lambda none (.bvar 0))) = true := by
  apply exact_claim
  decide

theorem open_bound_refused : result (.bvar 0) (taggedClaim (.bvar 0)) = false := by
  apply scope_refusal
  decide

end Controls

end Mettapedia.Languages.HOLLight.ClaimCheckingMachine
