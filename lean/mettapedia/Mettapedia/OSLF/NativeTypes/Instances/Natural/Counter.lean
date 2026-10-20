import Mettapedia.OSLF.NativeTypes.Executable.Successor

/-!
# Natural successor and its finite parity observation

This is the reusable source instance behind the infinite-counter controls.
Its complete outgoing observation does not imply complete incoming coverage.
The carrier is Lean's inductive natural type; initiality is a separate
algebraic property from this operational presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Executable.Finite

def counter : ReductionSpan Nat where
  Edge := Nat
  source := id
  target index := index + 1

def phase (index : Nat) : Fin 2 := ⟨index % 2, Nat.mod_lt _ (by decide)⟩

def toggle (value : Fin 2) : Fin 2 := phase (value.val + 1)

def parity : ReductionSpan (Fin 2) where
  Edge := Fin 2
  source := id
  target := toggle

theorem phase_successor (index : Nat) : toggle (phase index) = phase (index + 1) := by
  apply Fin.ext
  simp [toggle, phase, Nat.add_mod]

def observation : SpanMap counter parity where
  states := phase
  events := phase
  source_comm _ := rfl
  target_comm := phase_successor

theorem outgoing_coverage : observation.SourceLifts := by
  intro state event starts
  change event = phase state at starts
  refine ⟨state, rfl, ?_⟩
  change phase (state + 1) = toggle event
  rw [starts, phase_successor]

theorem no_incoming_coverage : ¬ observation.TargetLifts := by
  intro covers
  obtain ⟨lift, ends, _⟩ := covers 0 (1 : Fin 2) (by decide +kernel)
  simp [counter] at ends

def table : FiniteGraph.Table parity where
  edge source target := decide (target = toggle source)
  exact := by
    intro source target
    change decide (target = toggle source) = true ↔
      ∃ event : Fin 2, event = source ∧ toggle event = target
    simp [eq_comm]

/-- The concrete finite observation exported to runtime checking. -/
def edges : List (Fin 2 × Fin 2) :=
  (List.finRange 2).flatMap fun source =>
    ((List.finRange 2).filter fun target => table.edge source target).map (source, ·)

theorem edges_exact (source target : Fin 2) :
    (source, target) ∈ edges ↔ ∃ event : parity.Edge,
      parity.source event = source ∧ parity.target event = target := by
  rw [← table.exact]
  revert source target
  decide +kernel

def accepting : FiniteMuCalculus.Environment (Fin 2) 1 := fun _ => {0}

theorem accepting_preimage :
    observation.states ⁻¹' ({0} : Set (Fin 2)) = {index | index % 2 = 0} := by
  ext index
  simp [observation, phase, Fin.ext_iff]

theorem coverage : CoversFormula observation (Formula.buchi .future) :=
  buchi_coverage observation outgoing_coverage

end Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter
