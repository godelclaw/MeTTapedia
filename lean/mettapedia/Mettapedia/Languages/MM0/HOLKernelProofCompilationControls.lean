import Mettapedia.Languages.MM0.HOLKernelProofCompilation

/-!
# Retained source controls for maintained-MM0 HOL compilation

The first panel contains one proof rooted at every source constructor. Further
proofs retain duplicate assumption occurrences, quantified assumptions and a
binder-containing CHOOSE result. These are source proof data for independent
checking and native export, rather than an alternative checking calculus.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofCompilationControls
open Mettapedia.Logic.HOL

inductive Constant : Ty Unit → Type where
  | truth : Constant .prop
abbrev F := ClosedFormula Constant
abbrev T (type : Ty Unit) := ClosedTerm Constant type
abbrev P (assumptions : List F) (conclusion : F) := ProofSyntax Constant assumptions conclusion

def identity : T (.arr .prop .prop) := .lam (.var .vz)
structure Example where
  name : String
  hypotheses : List F
  conclusion : F
  proof : P hypotheses conclusion

def examples : List Example :=
  [⟨"hyp", [.top], .top, .hyp 0⟩,
   ⟨"topI", [], .top, .topI⟩,
   ⟨"botE", [.bot], .top, .botE (.hyp 0)⟩,
   ⟨"andI", [], .and .top .top, .andI .topI .topI⟩,
   ⟨"andEL", [], .top, .andEL (.andI .topI .topI)⟩,
   ⟨"andER", [], .top, .andER (.andI .topI .topI)⟩,
   ⟨"orIL", [], .or .top .bot, .orIL .topI⟩,
   ⟨"orIR", [], .or .bot .top, .orIR .topI⟩,
   ⟨"orE", [], .top, .orE (.orIL (ψ := .top) .topI) .topI .topI⟩,
   ⟨"impI", [], .imp .top .top, .impI (.hyp 0)⟩,
   ⟨"impE", [], .top, .impE (.impI (.hyp 0)) .topI⟩,
   ⟨"notI", [], .not .bot, .notI (.hyp 0)⟩,
   ⟨"notE", [.bot], .bot, .notE (.notI (.hyp 0)) (.hyp 0)⟩,
   ⟨"allI", [], .all (.imp (.var .vz) (.var .vz)), .allI (.impI (.hyp 0))⟩,
   ⟨"allE", [], .imp .top .top, .allE (φ := .imp (.var .vz) (.var .vz)) .top (.allI (.impI (.hyp 0)))⟩,
   ⟨"exI", [], .ex (σ := .prop) .top, .exI .top .topI⟩,
   ⟨"exE", [], .top, .exE (.exI (φ := (Term.top : Formula Constant [.prop])) .top .topI) .topI⟩,
   ⟨"eqRefl", [], .eq .top .top, .eqRefl .top⟩,
   ⟨"eqSymm", [], .eq .top .top, .eqSymm (.eqRefl .top)⟩,
   ⟨"eqTrans", [], .eq .top .top, .eqTrans (.eqRefl .top) (.eqRefl .top)⟩,
   ⟨"eqPropI", [], .eq .top .top, .eqPropI (.impI (.hyp 0)) (.impI (.hyp 0))⟩,
   ⟨"eqPropEL", [], .imp .top .top, .eqPropEL (.eqRefl .top)⟩,
   ⟨"eqPropER", [], .imp .top .top, .eqPropER (.eqRefl .top)⟩,
   ⟨"eqApp", [], .eq (.app identity .top) (.app identity .top), .eqApp .top (.eqRefl identity)⟩,
   ⟨"eqAppArg", [], .eq (.app identity .top) (.app identity .top), .eqAppArg identity (.eqRefl .top)⟩,
   ⟨"eqLam", [], .eq identity identity, .eqLam (.eqRefl (.var .vz))⟩,
   ⟨"funExt", [], .eq identity identity, .funExt (.allI (.eqRefl (.app (weaken identity) (.var .vz))))⟩,
   ⟨"beta", [], .eq (.app identity .top) .top, .beta .top (.var .vz)⟩,
   ⟨"eta", [], .eq (.lam (.app (weaken identity) (.var .vz))) identity, .eta identity⟩]

theorem constructor_count : examples.length = 29 := by decide
theorem constructor_names_distinct : (examples.map Example.name).Nodup := by decide

def retainedFormula : F := .all (σ := .prop) (.eq (.var .vz) (.var .vz))
def retainedConclusion : F := .all (σ := .prop) (.imp (weaken retainedFormula) (weaken retainedFormula))
def inheritedProof (second : Bool) : P [retainedFormula, retainedFormula] retainedConclusion := by
  cases second with
  | false => exact .allI (.impI (.hyp ⟨1, by decide⟩))
  | true => exact .allI (.impI (.hyp ⟨2, by decide⟩))

def retainedExamples : List Example := [
  ⟨"first_inherited_occurrence", [retainedFormula, retainedFormula], retainedConclusion, inheritedProof false⟩,
  ⟨"second_inherited_occurrence", [retainedFormula, retainedFormula], retainedConclusion, inheritedProof true⟩,
  ⟨"allE_retained", [.all (σ := .prop) (.imp (.var .vz) (.var .vz))], .imp .top .top,
    .allE (φ := .imp (.var .vz) (.var .vz)) .top (.hyp 0)⟩,
  ⟨"exI_retained", [.imp .top .top], .ex (σ := .prop) (.imp (.var .vz) (.var .vz)),
    .exI .top (.hyp 0)⟩,
  ⟨"exE_retained_result", [retainedFormula], retainedFormula,
    .exE (.exI (φ := (Term.top : Formula Constant [.prop])) .top .topI) (.hyp ⟨1, by decide⟩)⟩]

theorem retained_count : retainedExamples.length = 5 := by decide
#print axioms constructor_count
#print axioms constructor_names_distinct
#print axioms retained_count
end Mettapedia.Languages.MM0.HOLKernelProofCompilationControls
