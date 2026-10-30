import Mettapedia.Languages.VibeITP.Presentation.SimultaneousFormation
import Mettapedia.Languages.VibeITP.Presentation.SignatureExtensionDerivation
import Mettapedia.Languages.VibeITP.Spec.DerivationV2

/-!
# Simultaneous derivations under theory growth

Successful preparation fixes every replacement's allocated symbol and arity.
Known source and replacement terms retain their operation results when the
signature grows. Derived v2 statements therefore survive admissible theory and
observation extension. No reflection or conservativity is asserted.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousExtension

open Mettapedia.Languages.VibeITP.Spec
open Spec.SimultaneousInstantiation SimultaneousFormation

theorem prepare_sigExt {source target : Sig} (extension : SigExt source target) :
    ∀ (replacements : List (SymId × Term)) (entries : List Entry),
      ValuesShape source replacements → prepare source replacements = some entries →
        prepare target replacements = some entries
  | [], entries, _, accepted => accepted
  | (symbol, value) :: rest, entries, formed, accepted => by
      cases signature : source symbol with
      | none => simp [prepare, signature] at accepted
      | some info =>
          have preserved := extension symbol info signature
          have valueShape := formed (symbol, value) (List.mem_cons_self)
          simp only [prepare, signature] at accepted
          split at accepted
          · rename_i guard
            cases trailing : prepare source rest with
            | none => simp [trailing] at accepted
            | some tail =>
                have later := prepare_sigExt extension rest tail
                  (fun pair member => formed pair (List.mem_cons_of_mem _ member)) trailing
                simp only [trailing, Option.map_some, Option.some.injEq] at accepted
                subst entries
                simp [prepare, preserved, depth_sigExt extension value valueShape, guard, later]
          · simp at accepted

mutual
theorem go_sigExt {source target : Sig} (extension : SigExt source target)
    (entries : List Entry) (valid : EntriesShape source entries)
    (offset : Nat) (term : Term) (shape : TermShape source term) :
    go target entries offset term = go source entries offset term := by
  cases term with
  | bvar index => rfl
  | lit bytes => rfl
  | app symbol children =>
      obtain ⟨info, signature, _, childrenShape⟩ := TermShape.app_iff.mp shape
      simp only [go, hasFvar_sigExt extension (.app symbol children) shape,
        args_sigExt extension entries valid symbol ⟨info, signature⟩ offset 0 children childrenShape]
      split
      · rfl
      · cases traversed : args source entries symbol offset 0 children with
        | none => rfl
        | some output =>
            have outputShape := (args_shape source entries valid symbol offset 0 children output
              childrenShape traversed).1
            cases selected : lookup entries symbol with
            | none => rfl
            | some entry =>
                have entryShape := (valid entry (lookup_member entries symbol entry selected).1).2
                dsimp only
                rw [shift_sigExt extension offset entry.arity entry.value entryShape]
                cases shifted : shift source offset entry.arity entry.value with
                | none => rfl
                | some value =>
                    exact substBVars_sigExt extension entry.arity output outputShape value
                      (shift_termShape source offset entry.arity entry.value value entryShape shifted) 0
termination_by sizeOf term
decreasing_by
  subst_vars
  exact Term.args_sizeOf_lt_app _ _

theorem args_sigExt {source target : Sig} (extension : SigExt source target)
    (entries : List Entry) (valid : EntriesShape source entries)
    (symbol : SymId) (known : KnownSymbol source symbol) (offset index : Nat)
    (terms : List Term) (shape : TermShapeList source terms) :
    args target entries symbol offset index terms = args source entries symbol offset index terms := by
  cases shape with
  | nil => rfl
  | @cons child rest childShape restShape =>
      simp only [args, binderAt_sigExt extension known index,
        go_sigExt extension entries valid (offset + binderAt source symbol index) child childShape,
        args_sigExt extension entries valid symbol known offset (index + 1) rest restShape]
termination_by sizeOf terms
decreasing_by
  all_goals subst_vars
  · exact term_head_sizeOf_lt_cons _ _
  · exact term_tail_sizeOf_lt_cons _ _
end

theorem statement_sigExt_of_prepared {source target : Sig} (extension : SigExt source target)
    (replacements : List (SymId × Term)) (entries : List Entry) (term : Term)
    (values : ValuesShape source replacements) (shape : TermShape source term)
    (prepared : prepare source replacements = some entries) :
    SimultaneousInstantiation.statement target replacements term =
      SimultaneousInstantiation.statement source replacements term := by
  have entriesShape := prepare_shape source replacements entries values prepared
  have targetPrepared := prepare_sigExt extension replacements entries values prepared
  simp only [SimultaneousInstantiation.statement, prepared, targetPrepared,
    go_sigExt extension entries entriesShape 0 term shape]
  cases computed : (if entries.isEmpty then some term else go source entries 0 term) with
  | none => rfl
  | some result =>
      have resultShape : TermShape source result := by
        by_cases empty : entries.isEmpty = true
        · have same : term = result := by simpa [empty] using computed
          simpa only [← same] using shape
        · have step : go source entries 0 term = some result := by simpa [empty] using computed
          exact go_shape source entries entriesShape 0 term result shape step
      simp only [depth_sigExt extension result resultShape]

theorem statement_success_sigExt {source target : Sig} (extension : SigExt source target)
    (replacements : List (SymId × Term)) (term result : Term)
    (values : ValuesShape source replacements) (shape : TermShape source term)
    (accepted : SimultaneousInstantiation.statement source replacements term = some result) :
    SimultaneousInstantiation.statement target replacements term = some result := by
  cases prepared : prepare source replacements with
  | none => simp [SimultaneousInstantiation.statement, prepared] at accepted
  | some entries =>
      rw [statement_sigExt_of_prepared extension replacements entries term values shape prepared]
      exact accepted

theorem derived_termShape {theory : Theory} {allocated : Nat} (hosted : Hosted theory allocated)
    {observations : List ExecutionObservation} {statement : Term}
    (derived : DerivesWithExecutionV2 theory observations statement) :
    TermShape theory.sig statement := by
  induction derived with
  | base original => exact derivesWithExecution_termShape hosted original
  | modusPonens _ _ implication _ =>
      obtain ⟨_, _, _, arguments⟩ := TermShape.app_iff.mp implication
      exact arguments.of_mem (by simp)
  | @instantiateMany source result replacements _ formed accepted sourceShape =>
      exact statement_shape theory.sig replacements source result
        (fun pair member => wellFormed_termShape theory.sig pair.2 (formed pair member))
        sourceShape accepted
  | jit _ _ _ _ => exact executionObservation_termShape hosted.builtin _

theorem theory_extension {source target : Theory} {allocated : Nat}
    (hosted : Hosted source allocated) (extension : TheoryExt source target)
    {before after : List ExecutionObservation}
    (included : ∀ observation ∈ before, observation ∈ after) {statement : Term}
    (derived : DerivesWithExecutionV2 source before statement) :
    DerivesWithExecutionV2 target after statement := by
  induction derived with
  | base original => exact .base (derives_with_execution_theory_extension hosted extension included original)
  | modusPonens _ _ implication premise => exact .modusPonens implication premise
  | @instantiateMany term result replacements premise formed accepted transported =>
      exact .instantiateMany transported
        (fun pair member => wellFormed_true_sigExt extension.sig (formed pair member))
        (statement_success_sigExt extension.sig replacements term result
          (fun pair member => wellFormed_termShape source.sig pair.2 (formed pair member))
          (derived_termShape hosted premise) accepted)
  | jit _ member guarded premise => exact .jit premise (included _ member) guarded

instance : HostedCalculus DerivesWithExecutionV2 where
  toExecutionCalculus := inferInstance
  theory_extension := fun hosted extension included derived =>
    SimultaneousExtension.theory_extension hosted extension included derived

#print axioms statement_success_sigExt
#print axioms derived_termShape
#print axioms theory_extension

end Mettapedia.Languages.VibeITP.Presentation.SimultaneousExtension
