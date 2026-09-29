import Mettapedia.GraphTheory.FourColor.DiamondBoundaryElimination
import MettapediaFourColor.DiamondInsertionGSLT
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# A common boundary summary for the diamond configurations

The two centres carry boundary fans of independently specified lengths. The
same witness-level elimination applies to all lengths. Configurations 1, 2 and
4 are the literal instances with fan parameters (0,0), (1,0) and (1,1).
Their graph isomorphisms and ordered reference rings are kernel checked.

The summary retains the joint choice of centre colours and reconstructs both
tips. It preserves arbitrary boundary constraints and supplies genuine
reference colourings with compatible insertion histories. This theorem does
not assert reducibility of longer fans or geometric coverage of arbitrary maps.
-/

namespace FourColor.DiamondBoundarySummary

open DiamondConfigurations
open Mettapedia.GraphTheory.FourColor

/-- Boundary neighbours in the cyclic order, with four interior positions. -/
def attachments (left right : ℕ) (i : Fin 4) (v : Fin (6 + left + right)) : Prop :=
  match i.val with
  | 0 => v.val ≤ left + 1
  | 1 => v.val = left + 1 ∨ v.val = left + 2 ∨ v.val = left + 3
  | 2 => left + 3 ≤ v.val ∧ v.val ≤ left + right + 4
  | _ => v.val = left + right + 4 ∨ v.val = left + right + 5 ∨ v.val = 0

instance (left right : ℕ) : ∀ i v, Decidable (attachments left right i v) :=
  fun i v => by unfold attachments; split <;> infer_instance

def fan (left right : ℕ) :=
  DiamondBoundaryElimination.graph
    (SimpleGraph.cycleGraph (6 + left + right)) (attachments left right)

instance (left right : ℕ) : DecidableRel (fan left right).Adj := by
  unfold fan
  infer_instance

/-- The boundary assignment and all remaining interior choices. -/
abbrev Plan (left right : ℕ) (C : Type*) :=
  Σ b : (SimpleGraph.cycleGraph (6 + left + right)).Coloring C,
    DiamondBoundaryElimination.Summary (attachments left right) b

/-- One elimination law, with no bound on the fan lengths or colour alphabet. -/
def fanEquiv (left right : ℕ) (C : Type*) :
    (fan left right).Coloring C ≃ Plan left right C :=
  DiamondBoundaryElimination.coloringEquiv _ _

def graph001Iso : fan 0 0 ≃g graph001 where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

def graph002Iso : fan 1 0 ≃g graph002 where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

def graph004Iso : fan 1 1 ≃g graph004 where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

variable {V C : Type*} {G : SimpleGraph V} {left right : ℕ}

/-- Transport the common summary to an actual configuration graph. -/
def planEquiv (e : fan left right ≃g G) : G.Coloring C ≃ Plan left right C :=
  (SimpleGraph.coloringCongr e.symm (Equiv.refl C)).trans (fanEquiv left right C)

@[simp] theorem eliminate_boundary (e : fan left right ≃g G)
    (k : G.Coloring C) (v : Fin (6 + left + right)) :
    (planEquiv e k).1 v = k (e (.inl v)) := rfl

@[simp] theorem reconstruct_boundary (e : fan left right ≃g G)
    (p : Plan left right C) (v : Fin (6 + left + right)) :
    (planEquiv e).symm p (e (.inl v)) = p.1 v := by
  change DiamondBoundaryElimination.reconstruct _ _ p.1 p.2 (e.symm (e (.inl v))) = p.1 v
  rw [e.symm_apply_apply]
  rfl

/-- A context can constrain the whole boundary jointly. -/
theorem context_iff (e : fan left right ≃g G)
    (accepts : (Fin (6 + left + right) → C) → Prop) :
    (∃ k : G.Coloring C, accepts (fun v => k (e (.inl v)))) ↔
      ∃ p : Plan left right C, accepts p.1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨planEquiv e k, hk⟩
  · rintro ⟨p, hp⟩
    refine ⟨(planEquiv e).symm p, ?_⟩
    simpa only [reconstruct_boundary] using hp

/-- Ring traces observe the same ordered boundary after elimination. -/
theorem trace_iff (e : fan left right ≃g G)
    (ports : List (Fin (6 + left + right))) (et : List Color) :
    (∃ k : G.Coloring Color, et = trace (ports.map fun v => k (e (.inl v)))) ↔
      ∃ p : Plan left right Color, et = trace (ports.map p.1) :=
  context_iff e (fun b => et = trace (ports.map b))

def ports001 : List (Fin 6) := [4, 5, 0, 1, 2, 3]
def ports002 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]
def ports004 : List (Fin 8) := [4, 5, 6, 7, 0, 1, 2, 3]

theorem ring001 : ports001.map (fun v => graph001Iso (.inl v)) = boundary001.reverse := by
  decide +kernel

theorem ring002 : ports002.map (fun v => graph002Iso (.inl v)) = boundary002.reverse := by
  decide +kernel

theorem ring004 : ports004.map (fun v => graph004Iso (.inl v)) = boundary004.reverse := by
  decide +kernel

/-- Exact semantics of the boundary used by the first reducibility obligation. -/
theorem reference001 (et : List Color) :
    (cfmap cf001).map.RingTrace (cfring cf001).reverse et ↔
      ∃ p : Plan 0 0 Color, et = trace (ports001.map p.1) := by
  rw [reducibilityTrace001, ← ring001]
  simp only [List.map_map]
  exact trace_iff graph001Iso ports001 et

theorem reference002 (et : List Color) :
    (cfmap cf002).map.RingTrace (cfring cf002).reverse et ↔
      ∃ p : Plan 1 0 Color, et = trace (ports002.map p.1) := by
  rw [reducibilityTrace002, ← ring002]
  simp only [List.map_map]
  exact trace_iff graph002Iso ports002 et

theorem reference004 (et : List Color) :
    (cfmap cf004).map.RingTrace (cfring cf004).reverse et ↔
      ∃ p : Plan 1 1 Color, et = trace (ports004.map p.1) := by
  rw [reducibilityTrace004, ← ring004]
  simp only [List.map_map]
  exact trace_iff graph004Iso ports004 et

/-- Reconstruction produces a reference-map witness with a compatible history. -/
theorem compatible_history (p : Plan 1 1 (Fin 4)) :
    ∃ x, DiamondInsertionGSLT.semantics.Supports DiamondInsertionGSLT.route x
      (coloring004 ((planEquiv graph004Iso).symm p)) :=
  DiamondInsertionGSLT.every_coloring _

end FourColor.DiamondBoundarySummary
