import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction

/-!
# An authored natural-number counter and eliminator fragment

The existing `.module` reader supplies every operational row. Peano numerals
are data; only the `Counter` wrapper advances. The eliminator has its own two
root computation rules. These operational facts do not assert datatype
initiality or grant dependent typing authority to an arbitrary rule instance.

The file reader is the existing Lean command reader. Its use here does not
identify that host parser with the separate packed source-grammar pipeline.
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

#module_file "../../../../../../metta/gslt/module/NativeNaturalCounter.module"
#module_roundtrip NativeNaturalCounter

namespace Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.OSLF.MeTTaIL.ContextualStep

def language : LanguageDef :=
  _root_.NativeNaturalCounter.language.toOption.getD (LanguageDef.empty "invalid")

theorem elaboration_succeeds : _root_.NativeNaturalCounter.language = .ok language := by
  rfl

theorem rewrite_rows : language.rewrites = [
    { «name» := "Advance", typeContext := [], premises := [],
      left := .apply "Counter" [.fvar "n"],
      right := .apply "Counter" [.apply "NSucc" [.fvar "n"]] },
    { «name» := "NatZero", typeContext := [], premises := [],
      left := .apply "NatEliminate" [.fvar "p", .fvar "z", .fvar "s", .apply "NZero" []],
      right := .fvar "z" },
    { «name» := "NatSucc", typeContext := [], premises := [],
      left := .apply "NatEliminate" [.fvar "p", .fvar "z", .fvar "s", .apply "NSucc" [.fvar "n"]],
      right := .apply "Apply" [.apply "Apply" [.fvar "s", .apply "Embed" [.fvar "n"]],
        .apply "NatEliminate" [.fvar "p", .fvar "z", .fvar "s", .fvar "n"]] }] := by
  rfl

theorem unconditional : isUnconditionalAligned language = true := by decide +kernel

def numeral : Nat → Pattern
  | 0 => .apply "NZero" []
  | number + 1 => .apply "NSucc" [numeral number]

def decodeNumeral : Pattern → Option Nat
  | .apply "NZero" [] => some 0
  | .apply "NSucc" [predecessor] => (decodeNumeral predecessor).map (· + 1)
  | _ => none

@[simp] theorem decode_numeral (number : Nat) : decodeNumeral (numeral number) = some number := by
  induction number with
  | zero => rfl
  | succ number ih => simp [numeral, decodeNumeral, ih]

theorem numeral_injective : Function.Injective numeral := by
  intro first second same
  have equal := congrArg decodeNumeral same
  simpa only [decode_numeral, Option.some.injEq] using equal

def counter (number : Nat) : Pattern := .apply "Counter" [numeral number]

theorem counter_injective : Function.Injective counter := by
  intro first second same
  apply numeral_injective
  simpa only [counter, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] using same

/-- Independently specified source behavior, before any authored rule matching. -/
def CounterStep (source target : Nat) : Prop := target = source + 1

theorem counter_rootReducts (number : Nat) :
    rootReducts language (counter number) = [counter (number + 1)] := by
  simp [rootReducts, rewrite_rows, counter, numeral, matchPattern, matchArgs,
    mergeBindings, applyBindings]

/-- Exact preservation and reflection of the independent counter relation. -/
theorem counter_step_iff (base : BasePremiseEvaluator) (source target : Nat) :
    Step base language (counter source) (counter target) ↔ CounterStep source target := by
  rw [step_iff_mem_rootReducts base language unconditional, counter_rootReducts]
  simp only [List.mem_singleton, CounterStep]
  exact counter_injective.eq_iff

/-- Authored execution cannot escape the encoded counter states. -/
theorem counter_step_target_iff (base : BasePremiseEvaluator) (source : Nat) (target : Pattern) :
    Step base language (counter source) target ↔ target = counter (source + 1) := by
  rw [step_iff_mem_rootReducts base language unconditional, counter_rootReducts]
  exact List.mem_singleton

/-- Numeric constructor syntax is inert; advancement belongs to the state rule. -/
theorem numeral_rootReducts (number : Nat) : rootReducts language (numeral number) = [] := by
  cases number <;>
    simp [rootReducts, rewrite_rows, numeral, matchPattern]

theorem numeral_does_not_step (base : BasePremiseEvaluator) (number : Nat) (target : Pattern) :
    ¬ Step base language (numeral number) target := by
  rw [step_iff_mem_rootReducts base language unconditional, numeral_rootReducts]
  simp

/-- The open eliminator fragment, independent of the pattern matcher. -/
inductive Term where
  | leaf : String → Term
  | number : Nat → Term
  | app : Term → Term → Term
  | eliminate : Term → Term → Term → Nat → Term
  deriving DecidableEq, Repr

def Term.encode : Term → Pattern
  | .leaf atom => .fvar atom
  | .number count => .apply "Embed" [numeral count]
  | .app fn arg => .apply "Apply" [fn.encode, arg.encode]
  | .eliminate motive zeroCase succCase count =>
      .apply "NatEliminate" [motive.encode, zeroCase.encode, succCase.encode, numeral count]

theorem Term.encode_injective : Function.Injective Term.encode := by
  intro first
  induction first with
  | leaf atom => intro second; cases second <;> simp [encode]
  | number number =>
      intro second; cases second <;> simp [encode, numeral_injective.eq_iff]
  | app fn arg fnIH argIH =>
      intro second; cases second <;> simp_all [encode]
      intro sameFunction sameArgument
      exact ⟨fnIH sameFunction, argIH sameArgument⟩
  | eliminate motive zeroCase succCase number motiveIH zeroIH succIH =>
      intro second; cases second <;> simp_all [encode, numeral_injective.eq_iff]
      intro sameMotive sameZero sameSucc _
      exact ⟨motiveIH sameMotive, zeroIH sameZero, succIH sameSucc⟩

inductive Iota : Term → Term → Prop where
  | zero (motive zeroCase succCase : Term) :
      Iota (.eliminate motive zeroCase succCase 0) zeroCase
  | succ (motive zeroCase succCase : Term) (number : Nat) :
      Iota (.eliminate motive zeroCase succCase (number + 1))
        (.app (.app succCase (.number number)) (.eliminate motive zeroCase succCase number))

def iotaReducts : Term → List Term
  | .eliminate _ zeroCase _ 0 => [zeroCase]
  | .eliminate motive zeroCase succCase (number + 1) =>
      [.app (.app succCase (.number number)) (.eliminate motive zeroCase succCase number)]
  | _ => []

theorem iota_iff_mem (source target : Term) : Iota source target ↔ target ∈ iotaReducts source := by
  constructor
  · intro step; cases step <;> simp [iotaReducts]
  · intro member
    cases source with
    | leaf _ | number _ | app _ _ => simp [iotaReducts] at member
    | eliminate motive zeroCase succCase number =>
      cases number with
      | zero =>
        simp only [iotaReducts, List.mem_singleton] at member
        subst target
        exact .zero _ _ _
      | succ number =>
        simp only [iotaReducts, List.mem_singleton] at member
        subst target
        exact .succ _ _ _ _

theorem rootReducts_encode (source : Term) :
    rootReducts language source.encode = (iotaReducts source).map Term.encode := by
  cases source with
  | leaf _ | number _ | app _ _ =>
    simp [rootReducts, rewrite_rows, Term.encode, matchPattern, iotaReducts]
  | eliminate motive zeroCase succCase number =>
    cases number <;>
      simp [rootReducts, rewrite_rows, Term.encode, iotaReducts, numeral,
        matchPattern, matchArgs, mergeBindings, applyBindings]

/-- Both directions relate actual authored execution to independent iota rules. -/
theorem iota_step_iff (base : BasePremiseEvaluator) (source target : Term) :
    Step base language source.encode target.encode ↔ Iota source target := by
  rw [step_iff_mem_rootReducts base language unconditional, rootReducts_encode, iota_iff_mem]
  simp only [List.mem_map, Term.encode_injective.eq_iff]
  simp

theorem counter_does_not_skip (base : BasePremiseEvaluator) :
    ¬ Step base language (counter 0) (counter 2) := by
  rw [counter_step_iff]
  unfold CounterStep
  decide +kernel

theorem wrong_iota_result_refused (base : BasePremiseEvaluator) :
    ¬ Step base language (Term.eliminate (.leaf "p") (.leaf "z") (.leaf "s") 0).encode
      (Term.leaf "s").encode := by
  rw [iota_step_iff, iota_iff_mem]
  decide +kernel

/-- The module's full row data enters the established declaration coGSLT. -/
def declaration : ModuleAlgebra.NativeAuthoring.Document :=
  .declaration (ModuleAlgebra.NativeAuthoring.coreDelta language)

theorem declaration_elaborates (base : LanguageDef) :
    (ModuleAlgebra.NativeAuthoring.coGSLT LanguageDef).elaborate base declaration =
      some (ModuleAlgebra.NativeAuthoring.coreDelta language) := by
  exact congrArg some (ModuleAlgebra.NativeAuthoring.compileDelta_declaration _)

theorem declaration_retains_rewrites :
    (ModuleAlgebra.NativeAuthoring.compileDelta declaration).newRewrites = language.rewrites := by
  rw [declaration, ModuleAlgebra.NativeAuthoring.compileDelta_declaration]
  rfl

end Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter
