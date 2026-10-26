import Mettapedia.Languages.MM0.HOLKernelStructuralRules

/-!
# Ordered logical assumptions over a HOL formation context

The native antecedent retains every assumption occurrence in order. Adding
a source head assumption produces the conjunction of the tail antecedent
with that head. Checked structural projections recover the formation context
and each selected assumption, indexed by its actual list position.

Equal formulas at different positions produce different supplied witnesses.
Their accepted conclusions agree, so acceptance alone does not recover the
selected occurrence. These are native context proofs, independent of a full
source-proof compiler or byte serializer.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelAssumptions
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelStructuralRules
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

def antecedent (references : Symbol → Nat) (formation : Preterm) : List Preterm → Preterm
  | [] => formation
  | first :: rest => conjunction references (antecedent references formation rest) first

theorem antecedent_sorted (signature : Signature sorts terms) (formation : Preterm)
    (formationSorted : Preterm.HasType terms context formation [] signature.ids.wff) :
    ∀ (assumptions : List Preterm),
      (∀ proposition ∈ assumptions, Preterm.HasType terms context proposition [] signature.ids.wff) →
      Preterm.HasType terms context (antecedent signature.symbol formation assumptions) [] signature.ids.wff
  | [], _ => formationSorted
  | first :: rest, sorted => conjunction_sorted signature context
      (antecedent_sorted signature formation formationSorted rest
        (fun proposition member => sorted proposition (List.mem_cons_of_mem _ member)))
      (sorted first List.mem_cons_self)

def formationProjection (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff) (formation : Preterm)
    (formationSorted : Preterm.HasType terms context formation [] signature.ids.wff) :
    ∀ (assumptions : List Preterm),
      (∀ proposition ∈ assumptions, Preterm.HasType terms context proposition [] signature.ids.wff) →
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (entails signature.symbol (antecedent signature.symbol formation assumptions) formation)
  | [], _ => identity signature rules formation formationSorted
  | first :: rest, sorted =>
      weaken signature rules (antecedent signature.symbol formation rest) first formation
        (antecedent_sorted signature formation formationSorted rest
          (fun proposition member => sorted proposition (List.mem_cons_of_mem _ member)))
        (sorted first List.mem_cons_self) formationSorted
        (formationProjection signature rules formation formationSorted rest
          (fun proposition member => sorted proposition (List.mem_cons_of_mem _ member)))

def proofContext (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff) (formation : Preterm)
    (formationSorted : Preterm.HasType terms context formation [] signature.ids.wff)
    (assumptions : List Preterm)
    (sorted : ∀ proposition ∈ assumptions, Preterm.HasType terms context proposition [] signature.ids.wff) :
    ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff :=
  ⟨formation, antecedent signature.symbol formation assumptions, formationSorted,
    antecedent_sorted signature formation formationSorted assumptions sorted,
    formationProjection signature rules formation formationSorted assumptions sorted⟩

def hypothesis (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff) (formation : Preterm)
    (formationSorted : Preterm.HasType terms context formation [] signature.ids.wff) :
    ∀ (assumptions : List Preterm),
      (∀ proposition ∈ assumptions, Preterm.HasType terms context proposition [] signature.ids.wff) →
      ∀ occurrence : Fin assumptions.length,
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (entails signature.symbol (antecedent signature.symbol formation assumptions) (assumptions.get occurrence))
  | [], _, occurrence => nomatch occurrence
  | first :: rest, sorted, ⟨0, _⟩ =>
      right signature rules (antecedent signature.symbol formation rest) first
        (antecedent_sorted signature formation formationSorted rest
          (fun proposition member => sorted proposition (List.mem_cons_of_mem _ member)))
        (sorted first List.mem_cons_self)
  | first :: rest, sorted, ⟨index + 1, smaller⟩ => by
      let position : Fin rest.length := ⟨index, by simpa using smaller⟩
      exact weaken signature rules (antecedent signature.symbol formation rest) first (rest.get position)
        (antecedent_sorted signature formation formationSorted rest
          (fun proposition member => sorted proposition (List.mem_cons_of_mem _ member)))
        (sorted first List.mem_cons_self) (sorted _ (List.mem_cons_of_mem _ (List.get_mem _ _)))
        (hypothesis signature rules formation formationSorted rest
          (fun proposition member => sorted proposition (List.mem_cons_of_mem _ member)) position)

private theorem right_index_ne_compose (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff) : rules.index .anr ≠ rules.index .syl := by
  intro same
  have declarations := (rules.declared .anr).symm.trans (same ▸ rules.declared .syl)
  have lengths := congrArg (fun declaration : TheoremDecl => declaration.arguments.length)
    (Option.some.inj declarations)
  simp [Rule.declaration] at lengths

private theorem duplicate_sorted (signature : Signature sorts terms) (proposition : Preterm)
    (sorted : Preterm.HasType terms context proposition [] signature.ids.wff) :
    ∀ value ∈ [proposition, proposition], Preterm.HasType terms context value [] signature.ids.wff := by
  intro value member
  have same : value = proposition := by simpa using member
  simpa only [same] using sorted

theorem duplicate_occurrences_distinct (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff) (formation proposition : Preterm)
    (formationSorted : Preterm.HasType terms context formation [] signature.ids.wff)
    (propositionSorted : Preterm.HasType terms context proposition [] signature.ids.wff) :
    (hypothesis (definitions := definitions) (hypotheses := hypotheses) signature rules formation formationSorted
      [proposition, proposition] (duplicate_sorted signature proposition propositionSorted) ⟨0, by simp⟩).val ≠
    (hypothesis (definitions := definitions) (hypotheses := hypotheses) signature rules formation formationSorted
      [proposition, proposition] (duplicate_sorted signature proposition propositionSorted) ⟨1, by simp⟩).val := by
  intro same
  have heads := congrArg (fun witness => match witness with
    | ProofWitness.theoremApp index _ _ => some index
    | _ => none) same
  change some (rules.index .anr) = some (rules.index .syl) at heads
  exact right_index_ne_compose signature rules (Option.some.inj heads)

#print axioms antecedent_sorted
#print axioms formationProjection
#print axioms proofContext
#print axioms hypothesis
#print axioms duplicate_occurrences_distinct
theorem antecedent_varsBelow (references : Symbol → Nat) (bound : Nat) (formation : Preterm)
    (formationBound : Preterm.VarsBelow bound formation) (assumptions : List Preterm)
    (bounded : ∀ proposition ∈ assumptions, Preterm.VarsBelow bound proposition) :
    Preterm.VarsBelow bound (antecedent references formation assumptions) := by
  induction assumptions with
  | nil => exact formationBound
  | cons first rest ih =>
      exact ⟨⟨trivial, ih (fun proposition member => bounded proposition (List.mem_cons_of_mem _ member))⟩,
        bounded first List.mem_cons_self⟩

theorem formationProjection_varsBelow (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff) (bound : Nat) (formation : Preterm)
    (formationSorted : Preterm.HasType terms context formation [] signature.ids.wff)
    (formationBound : Preterm.VarsBelow bound formation) (assumptions : List Preterm)
    (sorted : ∀ proposition ∈ assumptions, Preterm.HasType terms context proposition [] signature.ids.wff)
    (bounded : ∀ proposition ∈ assumptions, Preterm.VarsBelow bound proposition) :
    (formationProjection (definitions := definitions) (hypotheses := hypotheses)
      signature rules formation formationSorted assumptions sorted).val.VarsBelow bound := by
  induction assumptions with
  | nil => exact identity_varsBelow signature rules bound formation formationSorted formationBound
  | cons first rest ih =>
      simp only [formationProjection]
      apply weaken_varsBelow signature rules bound
      · exact antecedent_varsBelow signature.symbol bound formation formationBound rest
          (fun proposition member => bounded proposition (List.mem_cons_of_mem _ member))
      · exact bounded first List.mem_cons_self
      · exact formationBound
      · exact ih (fun proposition member => sorted proposition (List.mem_cons_of_mem _ member))
          (fun proposition member => bounded proposition (List.mem_cons_of_mem _ member))

theorem hypothesis_varsBelow (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids.wff) (bound : Nat) (formation : Preterm)
    (formationSorted : Preterm.HasType terms context formation [] signature.ids.wff)
    (formationBound : Preterm.VarsBelow bound formation) (assumptions : List Preterm)
    (sorted : ∀ proposition ∈ assumptions, Preterm.HasType terms context proposition [] signature.ids.wff)
    (bounded : ∀ proposition ∈ assumptions, Preterm.VarsBelow bound proposition)
    (occurrence : Fin assumptions.length) :
    (hypothesis (definitions := definitions) (hypotheses := hypotheses)
      signature rules formation formationSorted assumptions sorted occurrence).val.VarsBelow bound := by
  induction assumptions with
  | nil => nomatch occurrence
  | cons first rest ih =>
      have tailBound : ∀ proposition ∈ rest, Preterm.VarsBelow bound proposition :=
        fun proposition member => bounded proposition (List.mem_cons_of_mem _ member)
      have contextBound := antecedent_varsBelow signature.symbol bound formation formationBound rest tailBound
      rcases occurrence with ⟨index, smaller⟩
      cases index with
      | zero =>
          exact right_varsBelow signature rules bound _ _ _ _ contextBound (bounded first List.mem_cons_self)
      | succ index =>
          simp only [hypothesis]
          apply weaken_varsBelow signature rules bound
          · exact contextBound
          · exact bounded first List.mem_cons_self
          · exact tailBound _ (List.get_mem _ _)
          · exact ih (fun proposition member => sorted proposition (List.mem_cons_of_mem _ member)) tailBound _

#print axioms hypothesis_varsBelow

end Mettapedia.Languages.MM0.HOLKernelAssumptions
