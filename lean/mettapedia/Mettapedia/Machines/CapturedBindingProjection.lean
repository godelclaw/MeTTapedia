import Mathlib.Tactic

/-!
# Projection through opaque binding ports

A finite checkpoint has visible syntax support and ports carried by saved
substitution values. Syntax substitution does not open those values. Projection
nevertheless keeps the binding coordinates that their restoration can expose.

The indexed saturation algorithm is proved equal to an independent inductive
reachability judgment, including alias edges. Finiteness bounds one checkpoint's
coordinate inventory; it is not a bound on the runtime's variable-id supply.
Native support construction, C storage/ownership, constraints and opaque-value
application remain separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CapturedBindingProjection

variable {Key : Type} [DecidableEq Key]

structure RootSupport (Key : Type) where
  ordinary : Finset Key
  captured : Finset Key

def RootSupport.ports (root : RootSupport Key) : Finset Key :=
  root.ordinary ∪ root.captured

inductive Reachable (edges : Key → Finset Key) (seed : Finset Key) : Key → Prop where
  | root {key} : key ∈ seed → Reachable edges seed key
  | follow {key next} : Reachable edges seed key → next ∈ edges key →
      Reachable edges seed next

def expand (edges : Key → Finset Key) (known : Finset Key) : Finset Key :=
  known ∪ known.biUnion edges

def saturate (edges : Key → Finset Key) (seed : Finset Key) : Nat → Finset Key
  | 0 => seed
  | n + 1 => expand edges (saturate edges seed n)

theorem known_subset_expand (edges : Key → Finset Key) (known : Finset Key) :
    known ⊆ expand edges known := Finset.subset_union_left

theorem seed_subset_saturate (edges : Key → Finset Key) (seed : Finset Key) (n : Nat) :
    seed ⊆ saturate edges seed n := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact ih.trans (known_subset_expand edges _)

theorem saturate_sound (edges : Key → Finset Key) (seed : Finset Key) (n : Nat)
    {key : Key} (member : key ∈ saturate edges seed n) : Reachable edges seed key := by
  induction n generalizing key with
  | zero => exact .root member
  | succ n ih =>
      simp only [saturate, expand, Finset.mem_union, Finset.mem_biUnion] at member
      rcases member with old | ⟨previous, reached, edge⟩
      · exact ih old
      · exact .follow (ih reached) edge

theorem stable_persists (edges : Key → Finset Key) (seed : Finset Key) (n : Nat)
    (stable : expand edges (saturate edges seed n) = saturate edges seed n) :
    expand edges (saturate edges seed (n + 1)) = saturate edges seed (n + 1) := by
  simp only [saturate, stable]

/-- Every changing round adds at least one fresh coordinate. -/
theorem changing_card_bound (edges : Key → Finset Key) (seed : Finset Key) (n : Nat)
    (changing : expand edges (saturate edges seed n) ≠ saturate edges seed n) :
    seed.card + n + 1 ≤ (expand edges (saturate edges seed n)).card := by
  have strict {known : Finset Key} (changed : expand edges known ≠ known) :
      known.card + 1 ≤ (expand edges known).card := by
    have proper : known ⊂ expand edges known :=
      Finset.ssubset_iff_subset_ne.mpr ⟨known_subset_expand edges known, Ne.symm changed⟩
    exact Finset.card_lt_card proper
  induction n with
  | zero => simpa [saturate] using strict changing
  | succ n ih =>
      have earlier : expand edges (saturate edges seed n) ≠ saturate edges seed n := by
        intro stable
        exact changing (stable_persists edges seed n stable)
      have grew := ih earlier
      have next := strict changing
      simp only [saturate] at next ⊢
      omega

section FiniteCheckpoint

variable [Fintype Key]

theorem saturate_fixed (edges : Key → Finset Key) (seed : Finset Key) :
    expand edges (saturate edges seed (Fintype.card Key)) =
      saturate edges seed (Fintype.card Key) := by
  by_contra changing
  have grew := changing_card_bound edges seed (Fintype.card Key) changing
  have bounded := Finset.card_le_univ (expand edges (saturate edges seed (Fintype.card Key)))
  omega

theorem saturate_complete (edges : Key → Finset Key) (seed : Finset Key)
    {key : Key} (reached : Reachable edges seed key) :
    key ∈ saturate edges seed (Fintype.card Key) := by
  induction reached with
  | root member => exact seed_subset_saturate edges seed _ member
  | @follow key next _ edge ih =>
      have member : next ∈ expand edges (saturate edges seed (Fintype.card Key)) :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨key, ih, edge⟩)
      simpa only [saturate_fixed] using member

/-- Array/set saturation computes exactly the independently declared paths. -/
theorem saturate_refines (edges : Key → Finset Key) (seed : Finset Key) (key : Key) :
    key ∈ saturate edges seed (Fintype.card Key) ↔ Reachable edges seed key :=
  ⟨saturate_sound edges seed _, saturate_complete edges seed⟩

def project {Value : Type} (edges : Key → Finset Key) (root : RootSupport Key)
    (source : Key → Option Value) : Key → Option Value :=
  fun key => if key ∈ saturate edges root.ports (Fintype.card Key) then source key else none

theorem projected_reachable_lookup {Value : Type} (edges : Key → Finset Key)
    (root : RootSupport Key) (source : Key → Option Value) (key : Key)
    (reached : Reachable edges root.ports key) : project edges root source key = source key := by
  simp only [project, if_pos (saturate_complete edges root.ports reached)]

/-- The original binding of every saved port survives publication. -/
theorem captured_ports_retained {Value : Type} (edges : Key → Finset Key)
    (root : RootSupport Key) (source : Key → Option Value) (key : Key)
    (captured : key ∈ root.captured) : project edges root source key = source key := by
  exact projected_reachable_lookup edges root source key
    (.root (Finset.mem_union_right root.ordinary captured))

/-- Unreachable bindings are removed even when the caller uses the same
printed spelling for another coordinate. The model compares identities. -/
theorem unreachable_removed {Value : Type} (edges : Key → Finset Key)
    (root : RootSupport Key) (source : Key → Option Value) (key : Key)
    (unreachable : ¬Reachable edges root.ports key) : project edges root source key = none := by
  have missing : key ∉ saturate edges root.ports (Fintype.card Key) := by
    intro member
    exact unreachable (saturate_sound edges root.ports _ member)
  simp [project, missing]

end FiniteCheckpoint

theorem syntax_ground_does_not_close_ports :
    let root : RootSupport (Fin 2) := ⟨∅, {0}⟩
    let source : Fin 2 → Option Nat := fun key => if key = 0 then some 7 else none
    project (fun _ => ∅) root source 0 = some 7 ∧
      project (fun _ => ∅) {root with captured := ∅} source 0 = none := by
  decide +kernel

theorem alias_edges_retained_without_unrelated_key :
    let root : RootSupport (Fin 3) := ⟨∅, {0}⟩
    let edges : Fin 3 → Finset (Fin 3) := fun key => if key = 0 then {1} else ∅
    saturate edges root.ports 3 = {0, 1} := by
  decide +kernel

end Mettapedia.Machines.CapturedBindingProjection

#print axioms Mettapedia.Machines.CapturedBindingProjection.changing_card_bound
#print axioms Mettapedia.Machines.CapturedBindingProjection.saturate_fixed
#print axioms Mettapedia.Machines.CapturedBindingProjection.saturate_refines
#print axioms Mettapedia.Machines.CapturedBindingProjection.projected_reachable_lookup
#print axioms Mettapedia.Machines.CapturedBindingProjection.captured_ports_retained
#print axioms Mettapedia.Machines.CapturedBindingProjection.unreachable_removed
#print axioms Mettapedia.Machines.CapturedBindingProjection.syntax_ground_does_not_close_ports
#print axioms Mettapedia.Machines.CapturedBindingProjection.alias_edges_retained_without_unrelated_key
