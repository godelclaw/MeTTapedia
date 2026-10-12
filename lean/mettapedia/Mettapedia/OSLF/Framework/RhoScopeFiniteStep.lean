import Mettapedia.OSLF.Syntax.RhoFiniteQuotedParallel
import Mettapedia.OSLF.Syntax.RhoDroppedNameReadout
import Mettapedia.OSLF.Framework.RhoEquationGeneratedScope

/-!
# Exact finite testing of the actual atomic scope transformer

The finite value catalogue covers every possible quoted parallel split. The
optional dropped-name readout covers exactly the recursive part alternative.
The authored scope transformer is therefore an existential test over this
constructed finite catalogue. This provides a finite one-step decision for
decidable atomic and candidate-name predicates; the least fixed point still
requires its separate circular-dependency analysis.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeFiniteStep

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoFiniteQuotedParallel RhoDroppedNameReadout
open RhoEquationGeneratedScope

def recursivePart {context : Ctx sig} (names : Name context → Prop) (process : Process context) : Prop :=
  ∃ child, child? process = some child ∧ names child

theorem recursive_part_iff {context : Ctx sig} (names : Name context → Prop)
    (process : Process context) :
    recursivePart names process ↔ ∃ child, names child ∧ process = drop child := by
  constructor
  · rintro ⟨child, readout, member⟩
    exact ⟨child, member, (child_sound readout).symm⟩
  · rintro ⟨child, member, rfl⟩
    exact ⟨child, child_drop child, member⟩

theorem part_readout_iff {context : Ctx sig} (atom : Process context → Prop)
    (names : Name context → Prop) (process : Process context) :
    Part atom names process ↔ atom process ∨ recursivePart names process := by
  rw [recursive_part_iff]
  rfl

def finiteStep {context : Ctx sig} (left right : Process context → Prop)
    (names : Name context → Prop) (name : Name context) : Prop :=
  ∃ pair ∈ decompositions name,
    (left pair.1 ∨ recursivePart names pair.1) ∧
    (right pair.2 ∨ recursivePart names pair.2)

theorem step_iff_finite {context : Ctx sig} (left right : Process context → Prop)
    (names : Name context → Prop) (name : Name context) :
    step left right names name ↔ finiteStep left right names name := by
  constructor
  · rintro ⟨first, second, readout, firstPart, secondPart⟩
    exact ⟨(first, second), (quoted_parallel_iff _ _ _).mp readout,
      (part_readout_iff _ _ _).mp firstPart, (part_readout_iff _ _ _).mp secondPart⟩
  · rintro ⟨⟨first, second⟩, admitted, firstPart, secondPart⟩
    exact ⟨first, second, (quoted_parallel_iff _ _ _).mpr admitted,
      (part_readout_iff _ _ _).mpr firstPart, (part_readout_iff _ _ _).mpr secondPart⟩

def recursivePartDecision {context : Ctx sig} (names : Name context → Prop)
    [DecidablePred names] (process : Process context) : Decidable (recursivePart names process) :=
  match readout : child? process with
  | none => isFalse (by
      rintro ⟨child, impossible, _⟩
      rw [readout] at impossible
      cases impossible)
  | some child =>
      if member : names child then isTrue ⟨child, readout, member⟩
      else isFalse (by
        rintro ⟨other, sameReadout, admitted⟩
        have same : child = other := Option.some.inj (readout.symm.trans sameReadout)
        exact member (same ▸ admitted))

def finiteStepDecision {context : Ctx sig} (left right : Process context → Prop)
    (names : Name context → Prop) [DecidablePred left] [DecidablePred right] [DecidablePred names]
    (name : Name context) : Decidable (finiteStep left right names name) := by
  letI : DecidablePred (recursivePart names) := recursivePartDecision names
  unfold finiteStep
  infer_instance

def stepDecision {context : Ctx sig} (left right : Process context → Prop)
    (names : Name context → Prop) [DecidablePred left] [DecidablePred right] [DecidablePred names]
    (name : Name context) : Decidable (step left right names name) := by
  letI := finiteStepDecision left right names name
  exact decidable_of_iff' (finiteStep left right names name) (step_iff_finite left right names name)

end Mettapedia.OSLF.Framework.RhoScopeFiniteStep
