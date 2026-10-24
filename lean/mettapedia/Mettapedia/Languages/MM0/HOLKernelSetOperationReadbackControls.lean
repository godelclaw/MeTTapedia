import Mettapedia.Languages.MM0.HOLKernelSetOperationSequentReadback

/-!
# Representation and inference boundaries of material HOL readback

The constructor indices are the maintained HOL table's indices. The controls
retain distinct union/powerset parameters, typed binders, ordered duplicate
assumptions and exact changed-sequent refusal. Malformed type annotations,
parameter capture and unknown constructors are refused by the syntax reader.

Renamed binders can have the same intrinsic reading while their raw preterms
differ. The canonical image check retains the exact chosen spelling. Reading
a false statement supplies its exact syntax. Source derivability is a separate
boundary checked with the actual material model in the companion module.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationReadbackControls
open Mettapedia.Logic.HOL
open HOLKernelTermReadback
open Kernel HOLKernelSyntax HOLKernelSetOperationReadback
open NamedElaboration (BinderNames)
open Embedding.ZFSetHenkinInterpretation (Symbol set mapping)

/-- The actual indices used by the maintained HOL constructor table. -/
def references : HOLKernelSyntax.Symbol → Nat
  | .im => 0 | .an => 1 | .bool => 2 | .function => 3 | .ty => 4
  | .app => 5 | .lam => 6 | .eqc => 8 | .thm => 9 | .truth => 11
  | .andc => 17 | .impc => 19 | .allc => 21 | .exc => 23
  | .orc => 25 | .falsity => 26 | .notc => 28

theorem references_injective : Function.Injective references := by
  intro first second same
  cases first <;> cases second <;> simp_all [references]

def emptyNames : Names [] := .nil

theorem emptyScope : InScope emptyNames 0 :=
  ⟨by simp [emptyNames, BinderNames.toList], by simp [emptyNames, BinderNames.toList]⟩

theorem closed_term_roundtrip {type : Ty Unit} (term : ClosedTerm Symbol type) :
    readCanonicalTerm references emptyNames 0 (encode references emptyNames 0 term) = some ⟨type, term⟩ :=
  readCanonicalTerm_encode references references_injective term emptyNames 0 emptyScope

theorem closed_encoding_injective :
    Function.Injective (fun decoded : Decoded Symbol [] => encode references emptyNames 0 decoded.term) :=
  encode_injective references references_injective emptyNames 0 emptyScope

theorem closed_sequent_injective :
    Function.Injective (fun sequent : SourceSequent =>
      HOLKernelSetOperationInterpretation.statement references sequent.1 sequent.2) :=
  statement_injective references references_injective

theorem union_readback : readTerm references emptyNames (.var 3) = some ⟨mapping, .const Symbol.union⟩ :=
  HOLKernelSetOperationReadback.readTerm_encode references references_injective (.const .union) emptyNames 0 emptyScope

theorem power_readback : readTerm references emptyNames (.var 4) = some ⟨mapping, .const Symbol.power⟩ :=
  HOLKernelSetOperationReadback.readTerm_encode references references_injective (.const .power) emptyNames 0 emptyScope

theorem mapping_type_readback :
    readType references (applySymbol references .function [.var 0, .var 0]) = some mapping := by
  decide +kernel

theorem mapping_type_encoding :
    encodeType references (fun _ : Unit => Preterm.var 0) mapping =
      applySymbol references .function [.var 0, .var 0] :=
  HOLKernelTermReadback.readType_sound references _ mapping mapping_type_readback

theorem identity_canonical_image :
    readCanonicalTerm references emptyNames 0
        (encode references emptyNames 0 (Term.lam (.var .vz) : ClosedTerm Symbol (.arr .prop .prop))) =
      some ⟨Ty.arr .prop .prop, Term.lam (.var .vz)⟩ :=
  (readCanonicalTerm_iff references references_injective emptyNames 0 emptyScope _ _).mpr rfl

def openNames : Names [.prop, set] := .cons 8 (.cons 7 .nil)

theorem openScope : InScope openNames 2 := by
  simp [HOLKernelSetOperationReadback.InScope, HOLKernelTermReadback.InScope, openNames, BinderNames.toList]

theorem open_term_roundtrip {type : Ty Unit} (term : Term Symbol [.prop, set] type) :
    readCanonicalTerm references openNames 2 (encode references openNames 2 term) = some ⟨type, term⟩ :=
  readCanonicalTerm_encode references references_injective term openNames 2 openScope

def openFormation : Preterm :=
  HOLKernelJudgment.conjunction references
    (HOLKernelJudgment.conjunction references (HOLKernelSetOperationInterpretation.formation references)
      (HOLKernelJudgment.hasType references (.var 7) (.var 0)))
    (HOLKernelJudgment.hasType references (.var 8) (applySymbol references .bool []))

theorem open_sequent_roundtrip (sequent : ScopedSequent [.prop, set]) :
    readSequentIn references openNames 2 openFormation
      (encodeSequent references openNames 2 openFormation sequent) = some sequent :=
  readSequentIn_encode references references_injective openNames 2 openScope openFormation sequent

theorem wrong_equality_annotation_refused :
    readTerm references emptyNames
      (applySymbol references .eqc [.var 0, applySymbol references .truth [], applySymbol references .truth []]) = none := by
  decide +kernel

theorem ill_typed_application_refused :
    readTerm references emptyNames (applySymbol references .app [applySymbol references .truth [], .var 2]) = none := by
  decide +kernel

theorem parameter_capture_refused :
    readTerm references emptyNames (applySymbol references .lam [.var 3, .var 0, .var 3]) = none := by
  decide +kernel

theorem unknown_constructor_refused : readTerm references emptyNames (.term 999) = none := by decide +kernel

def identityAt (name : Nat) : Preterm :=
  applySymbol references .lam [.var name, applySymbol references .bool [], .var name]

theorem identity_readback (depth : Nat) :
    readTerm references emptyNames (identityAt (7 + depth)) =
      some ⟨Ty.arr .prop .prop, Term.lam (.var .vz)⟩ := by
  have scope : HOLKernelSetOperationReadback.InScope emptyNames depth :=
    ⟨by simp [emptyNames, BinderNames.toList], by simp [emptyNames, BinderNames.toList]⟩
  exact HOLKernelSetOperationReadback.readTerm_encode references references_injective
    (Term.lam (Term.var .vz) : ClosedTerm Symbol (.arr .prop .prop)) emptyNames depth scope

theorem alpha_readback_forgets_spelling :
    identityAt 7 ≠ identityAt 42 ∧
      readTerm references emptyNames (identityAt 7) =
        some ⟨Ty.arr .prop .prop, Term.lam (.var .vz)⟩ ∧
      readTerm references emptyNames (identityAt 42) =
        some ⟨Ty.arr .prop .prop, Term.lam (.var .vz)⟩ ∧
      readCanonicalTerm references emptyNames 0 (identityAt 42) = none := by
  exact ⟨by decide +kernel, identity_readback 0, identity_readback 35, by decide +kernel⟩

def collapsedNames : Names [.prop, .prop] := .cons 7 (.cons 7 .nil)

theorem collapsed_names_lose_occurrence :
    ¬ InScope collapsedNames 2 ∧
      encode references collapsedNames 2 (Term.var .vz : Formula Symbol [.prop, .prop]) =
        encode references collapsedNames 2 (Term.var (.vs .vz) : Formula Symbol [.prop, .prop]) ∧
      readTerm references collapsedNames (.var 7) = some ⟨Ty.prop, Term.var .vz⟩ := by
  refine ⟨by simp [HOLKernelSetOperationReadback.InScope, HOLKernelTermReadback.InScope, collapsedNames, BinderNames.toList], rfl, ?_⟩
  simp [HOLKernelSetOperationReadback.readTerm, HOLKernelTermReadback.readTerm, readTermWith, readVariable,
    collapsedNames]

def duplicateSequent : SourceSequent := ([.top, .bot, .top], .top)

theorem ordered_duplicates_readback :
    readSequent references (HOLKernelSetOperationInterpretation.statement references
      duplicateSequent.1 duplicateSequent.2) = some duplicateSequent :=
  readSequent_statement references references_injective duplicateSequent.1 duplicateSequent.2

theorem truth_sequent_readback :
    readSequent references (HOLKernelSetOperationInterpretation.statement references [] .top) =
      some ([], .top) :=
  readSequent_statement references references_injective [] .top

theorem false_sequent_readback :
    readSequent references (HOLKernelSetOperationInterpretation.statement references [] .bot) =
      some ([], .bot) :=
  readSequent_statement references references_injective [] .bot


def nativeTruth : Preterm := HOLKernelSetOperationInterpretation.statement references [] .top

/-- An actual local MM0 hypothesis supplies the first exact statement. The
same witness cannot be reused at a different decoded conclusion. -/
theorem changed_conclusion_refused :
    ProofWitness.check (fun _ => none) (fun _ => none) (fun _ => none) [] [nativeTruth] (.hyp 0)
      (HOLKernelSetOperationInterpretation.statement references [] .bot) = false := by
  apply refuses_changed_sequent references references_injective (first := ([], .top)) (second := ([], .bot))
  · decide +kernel
  · intro same
    have conclusions := congrArg Prod.snd same
    cases conclusions

theorem contracted_assumptions_refused :
    let original := HOLKernelSetOperationInterpretation.statement references [.top, .top] .top
    ProofWitness.check (fun _ => none) (fun _ => none) (fun _ => none) [] [original] (.hyp 0)
      (HOLKernelSetOperationInterpretation.statement references [.top] .top) = false := by
  dsimp only
  apply refuses_changed_sequent references references_injective
    (first := ([.top, .top], .top)) (second := ([.top], .top))
  · decide +kernel
  · intro same
    have lengths := congrArg (fun sequent : SourceSequent => sequent.1.length) same
    cases lengths

#print axioms closed_term_roundtrip
#print axioms closed_encoding_injective
#print axioms ordered_duplicates_readback
#print axioms alpha_readback_forgets_spelling
#print axioms collapsed_names_lose_occurrence
#print axioms changed_conclusion_refused
#print axioms contracted_assumptions_refused
end Mettapedia.Languages.MM0.HOLKernelSetOperationReadbackControls
