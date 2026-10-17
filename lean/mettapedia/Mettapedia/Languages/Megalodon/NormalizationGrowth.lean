import Mettapedia.Languages.Megalodon.ConversionElaboration
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
import Mettapedia.Computability.StackMachineSpaceGrowth

/-!
# Expanded output growth in a Mathdata normalization pass

The original bottom-up normalizer first normalizes an argument, then substitutes
that expanded argument into a lambda body. Repeating `λx:A. f x x` around a base
leaf therefore produces a complete binary tree in one changing pass. One further
stable pass suffices, so fuel one accepts every member of this typed family.

The size account uses the existing encoded Mathdata term and the existing
finite-alphabet pattern wire codec, retaining every physical tree occurrence.
Its exponential output forces superpolynomial work for a machine emitting that
expanded representation. This is not a lower bound on Boolean conversion tests:
a checker can avoid expansion in particular cases, and shared representations
have different storage contracts. The pass-based Lean model is not a verified
execution of Megalodon's source normalizer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NormalizationGrowth

open MathdataKernel
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Turing Polynomial

/-- Two fixed declarations: the binary constructor and a base leaf. -/
def environment : Environment where
  primitives := [.arr (.base 0) (.arr (.base 0) (.base 0)), .base 0]

theorem primitive_types_formed : environment.primitives.all (Tp.plainWellFormed 0) = true := rfl

/-- The variable occurs twice, so eta contraction cannot discard this binder. -/
def duplicator : Tm := .lam (.base 0) (.app (.app (.prim 0) (.db 0)) (.db 0))

def input : Nat → Tm
  | 0 => .prim 1
  | n + 1 => .app duplicator (input n)

def expanded : Nat → Tm
  | 0 => .prim 1
  | n + 1 => .app (.app (.prim 0) (expanded n)) (expanded n)

theorem duplicator_typed (context : List Tp) :
    inferTerm environment 0 context duplicator = some (.arr (.base 0) (.base 0)) := rfl

theorem input_typed (n : Nat) (context : List Tp) :
    inferTerm environment 0 context (input n) = some (.base 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [input, inferTerm, duplicator_typed, ih]; rfl

theorem expanded_typed (n : Nat) (context : List Tp) :
    inferTerm environment 0 context (expanded n) = some (.base 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expanded, inferTerm, ih]; rfl

theorem expanded_shift (n cutoff amount : Nat) :
    Tm.shift cutoff amount (expanded n) = expanded n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expanded, Tm.shift, ih]

theorem duplicator_normalizeOne : Tm.normalizeOne duplicator = (duplicator, true) := rfl

theorem expanded_normalizeOne (n : Nat) :
    Tm.normalizeOne (expanded n) = (expanded n, true) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expanded, Tm.normalizeOne, ih]; rfl

theorem input_normalizeOne (n : Nat) :
    Tm.normalizeOne (input n) = (expanded n, decide (n = 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [input, Tm.normalizeOne, duplicator_normalizeOne, ih]
    simp [duplicator, Tm.instantiate, Tm.instantiateAt, expanded_shift, expanded]

/-- Fuel counts changing passes; one changing and one stable pass handle the
whole family, although the resulting expanded tree is exponentially large. -/
theorem normalize_fuel_one (n : Nat) : Tm.normalize 1 (input n) = some (expanded n) := by
  cases n with
  | zero => rfl
  | succ n => simp [Tm.normalize, input_normalizeOne, expanded_normalizeOne]

theorem zero_fuel_refuses_changing_input (n : Nat) :
    Tm.normalize 0 (input (n + 1)) = none := by
  simp [Tm.normalize, input_normalizeOne]

theorem delta_input (n fuel : Nat) : deltaNormalize environment fuel (input n) = some (input n) := by
  induction n with
  | zero => cases fuel <;> simp [input, deltaNormalize]
  | succ n ih => simp [input, deltaNormalize, duplicator, ih]

theorem environment_normalize_fuel_one (n : Nat) :
    MathdataKernel.normalize environment 1 (input n) = some (expanded n) := by
  rw [MathdataKernel.normalize, delta_input]
  exact normalize_fuel_one n

/-! ## The original instrumented pass -/

variable (declarations : List TermDecl)

theorem duplicator_elaboratePass :
    ConversionElaboration.elaboratePass declarations duplicator = ((duplicator, true), []) := rfl

theorem expanded_elaboratePass (n : Nat) :
    ConversionElaboration.elaboratePass declarations (expanded n) = ((expanded n, true), []) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expanded, ConversionElaboration.elaboratePass, ih]; rfl

theorem input_elaboratePass_result (n : Nat) :
    (ConversionElaboration.elaboratePass declarations (input n)).1 =
      (expanded n, decide (n = 0)) :=
  (ConversionElaboration.elaboratePass_fst declarations (input n)).trans (input_normalizeOne n)

/-- Each authored wrapper causes one recorded beta contraction. Counting those
contractions still does not charge the expanded data carried by its article. -/
theorem input_elaboratePass_length (n : Nat) :
    (ConversionElaboration.elaboratePass declarations (input n)).2.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hpass : ConversionElaboration.elaboratePass declarations (input n) with
      ⟨⟨argument, stable⟩, steps⟩
    have result := input_elaboratePass_result declarations n
    rw [hpass] at result ih
    simp only [Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    rw [input, ConversionElaboration.elaboratePass, duplicator_elaboratePass, hpass]
    simp only [duplicator, List.map_nil, List.nil_append, List.length_append, List.length_map,
      List.length_cons, List.length_nil]
    simpa only [Nat.add_zero] using congrArg (fun value => value + 1) ih

theorem input_elaborateRun (n : Nat) :
    ConversionElaboration.elaborateRun declarations 1 (input n) =
      some (expanded n, (ConversionElaboration.elaboratePass declarations (input n)).2) := by
  have pair : ConversionElaboration.elaboratePass declarations (input n) =
      ((expanded n, decide (n = 0)),
        (ConversionElaboration.elaboratePass declarations (input n)).2) := by
    exact Prod.ext (input_elaboratePass_result declarations n) rfl
  cases n with
  | zero => rfl
  | succ n =>
    rw [ConversionElaboration.elaborateRun, pair]
    simp only [Nat.succ_ne_zero, decide_false, Bool.false_eq_true, if_false,
      ConversionElaboration.elaborateRun, expanded_elaboratePass, if_true, List.append_nil]

theorem input_elaboratePass_valid (n : Nat) :
    ConversionElaboration.Chain (input n)
        (ConversionElaboration.elaboratePass declarations (input n)).2 (expanded n) ∧
      ∀ step ∈ (ConversionElaboration.elaboratePass declarations (input n)).2,
        step.Valid declarations := by
  have spec := ConversionElaboration.elaboratePass_spec declarations (input n)
  rw [input_elaboratePass_result] at spec
  exact spec.2

/-! ## Full original finite-alphabet storage -/

/-- The existing GSLT quotation and pattern codec, not a node-count surrogate. -/
def wire (term : Tm) : List Alphabet :=
  encodeWith CertificateDataEncoding.patternCodec (TermQuantifiedKernel.encodeTm term)

private def tokenWeight (tokens : List String) : Nat :=
  (tokens.map (fun token => 1 + dataWeight (Codec.string.put token))).sum

private theorem tokens_length (tokens : List String) :
    (encodeWith (Codec.list Codec.string) tokens).length = tokenWeight tokens + 2 := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [encodeWith, encodeData, writeData_length, List.length_nil, Nat.add_zero] at ih ⊢
    simp only [dataWeight_list_cons, tokenWeight, List.map_cons, List.sum_cons] at ih ⊢
    omega

private theorem wire_length (term : Tm) :
    (wire term).length = tokenWeight (PatternTokens.encode (TermQuantifiedKernel.encodeTm term)) + 2 := by
  exact tokens_length _

theorem wire_app_length (function argument : Tm) :
    (wire (.app function argument)).length = 113 + (wire function).length + (wire argument).length := by
  rw [wire_length, wire_length, wire_length]
  simp only [TermQuantifiedKernel.encodeTm, TermQuantifiedKernel.a, PatternTokens.encode,
    PatternTokens.write, PatternTokens.writeList]
  have appended (value : Syntax.Pattern) (tail : List String) :
      PatternTokens.write value tail = PatternTokens.encode value ++ tail := by
    simpa only [PatternTokens.encode, List.nil_append] using
      PatternTokens.write_append value [] tail
  rw [appended, appended]
  have fixed : tokenWeight ["a", "MTmApp", "h", "h", "z"] = 115 := by decide
  simp only [tokenWeight, PatternTokens.encode, List.map_cons, List.sum_cons, List.map_append, List.sum_append,
    List.map_nil, List.sum_nil] at fixed ⊢
  omega

set_option maxRecDepth 4096 in
theorem wire_leaf_length : (wire (expanded 0)).length = 305 := by decide

set_option maxRecDepth 16384 in
theorem wire_duplicator_length : (wire duplicator).length = 1131 := by decide

theorem input_wire_length (n : Nat) : (wire (input n)).length = 1244 * n + 305 := by
  induction n with
  | zero => exact wire_leaf_length
  | succ n ih => rw [input, wire_app_length, wire_duplicator_length, ih]; omega

set_option maxRecDepth 4096 in
theorem expanded_wire_length (n : Nat) : (wire (expanded n)).length + 429 = 734 * 2 ^ n := by
  induction n with
  | zero => rw [wire_leaf_length]; rfl
  | succ n ih =>
    rw [expanded, wire_app_length, wire_app_length]
    have head : (wire (.prim 0)).length = 203 := by decide
    rw [head, pow_succ]
    omega

theorem exponential_le_output (n : Nat) : 2 ^ n ≤ (wire (expanded n)).length := by
  have size := expanded_wire_length n
  have positive : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
  omega

/-- Every actual tree-emitting execution pays for the expanded output cells.
A pass-fuel counter is absent from this inequality. -/
theorem emitted_output_work (machine : FinTM2)
    (sourceAlphabet : machine.Γ machine.k₀ ≃ Alphabet)
    (targetAlphabet : machine.Γ machine.k₁ ≃ Alphabet) (n time : Nat)
    (run : TM2OutputsInTime machine ((wire (input n)).map sourceAlphabet.symm)
      (some ((wire (expanded n)).map targetAlphabet.symm)) time) :
    2 ^ n ≤ 1244 * n + 305 +
      Mettapedia.Computability.StackMachineSpaceGrowth.machinePushBound machine * time := by
  have emitted := Mettapedia.Computability.StackMachineSpaceGrowth.output_length_le machine run
  simp only [List.length_map, input_wire_length] at emitted
  exact (exponential_le_output n).trans emitted

/-- No polynomial-time machine can emit this family's full expanded original
wire representation from its linear-size inputs. This concerns normalization
output, not the complexity of every conversion decision procedure. -/
theorem no_polynomial_expanded_normalization : IsEmpty
    (TM2ComputableInPolyTime (fun n => wire (input n)) wire expanded) := by
  refine ⟨fun implementation => ?_⟩
  let bound : Nat[X] := X + C
    (Mettapedia.Computability.StackMachineSpaceGrowth.machinePushBound implementation.tm) *
      implementation.time
  obtain ⟨n, tooSmall⟩ := exists_eval_lt_two_pow bound 1244 305
  have emitted := emitted_output_work implementation.tm implementation.inputAlphabet
    implementation.outputAlphabet n _ (implementation.outputsFun n)
  simp only [input_wire_length] at emitted
  have paid : 2 ^ n ≤ bound.eval (1244 * n + 305) := by
    simpa only [bound, eval_add, eval_X, eval_mul, eval_C] using emitted
  omega

namespace Controls

theorem missing_leaf_refused : inferTerm {} 0 [] (input 0) = none := rfl

theorem nonfunctional_constructor_refused (n : Nat) :
    inferTerm { primitives := [.base 0, .base 0] } 0 [] (input (n + 1)) = none := rfl

theorem stable_leaf_needs_no_fuel : Tm.normalize 0 (input 0) = some (expanded 0) := rfl

end Controls

end Mettapedia.Languages.Megalodon.NormalizationGrowth
