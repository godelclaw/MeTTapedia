import Mettapedia.GraphTheory.FourColor.BoundaryConnectivity
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# A finite compositional record for zero- and one-edge cuts

Record which boundary bits a vertex subset realizes, whether it and its
complement are nonempty, and its internal cut size capped at two. The
realized set of records detects nontrivial cuts of size at most one in
every literal sewing context. Hidden components, disconnected pieces,
empty interfaces and parallel edges need no exceptional hypotheses.

This module proves the exact low-cut composition and replacement laws.
The identification with connected bridgeless rotation systems, the
executable extractor and global descent are separate consumers.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundarySmallCutProfile

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24BoundaryEssentialGluing.Multigraph

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E P : Type*}

def cutSize [Fintype E] (G : Multigraph V E) (s : V → Bool) : Nat :=
  ∑ e, if s (G.fst e) = s (G.snd e) then 0 else 1

def IsSmallCut [Fintype E] (G : Multigraph V E) (s : V → Bool) : Prop :=
  (∃ v, s v = true) ∧ (∃ v, s v = false) ∧ cutSize G s ≤ 1

def HasSmallCut [Fintype E] (G : Multigraph V E) : Prop := ∃ s, IsSmallCut G s

structure State (P : Type*) where
  boundary : P → Bool
  selected : Bool
  omitted : Bool
  cost : Fin 3
  deriving Fintype

def state [Fintype E] (G : Multigraph V E) (ports : P → V) (s : V → Bool) : State P :=
  ⟨s ∘ ports, decide (∃ v, s v = true), decide (∃ v, s v = false),
    ⟨min 2 (cutSize G s), by omega⟩⟩

/-- All physically realized subset records, not all formal records. -/
def profile [Fintype E] (G : Multigraph V E) (ports : P → V) : Set (State P) :=
  Set.range (state G ports)

def reindex {Q : Type*} (f : Q → P) (a : State P) : State Q :=
  ⟨a.boundary ∘ f, a.selected, a.omitted, a.cost⟩

theorem profile_reindex [Fintype E] {Q : Type*} (G : Multigraph V E)
    (ports : P → V) (f : Q → P) :
    profile G (ports ∘ f) = reindex f '' profile G ports := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨state G ports s, ⟨s, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩

def Compatible [Fintype P] (a b : State P) : Prop :=
  (a.selected || b.selected) = true ∧ (a.omitted || b.omitted) = true ∧
    (a.cost.val + b.cost.val + ∑ p, if a.boundary p = b.boundary p then 0 else 1) ≤ 1

theorem card_state [Fintype P] : Fintype.card (State P) = 12 * 2 ^ Fintype.card P := by
  let e : State P ≃ (P → Bool) × Bool × Bool × Fin 3 :=
    ⟨fun s => ⟨s.boundary, s.selected, s.omitted, s.cost⟩,
      fun s => ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩,
      by intro s; cases s; rfl, by intro s; rcases s with ⟨a,b,c,d⟩; rfl⟩
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  omega

theorem card_profile_carrier [Fintype P] :
    Fintype.card (Set (State P)) = 2 ^ (12 * 2 ^ Fintype.card P) := by
  rw [Fintype.card_set, card_state]

variable {W F : Type*} [Fintype E] [Fintype F] [Fintype P]
  (H : Multigraph V E) (K : Multigraph W F) (pH : P → V) (pK : P → W)

theorem cutSize_glue (s : V → Bool) (t : W → Bool) :
    cutSize (glue H K pH pK) (Sum.elim s t) =
      cutSize H s + cutSize K t + ∑ p, if s (pH p) = t (pK p) then 0 else 1 := by
  simp only [cutSize, Fintype.sum_sum_type, glue, Sum.elim_inl, Sum.elim_inr]
  exact (Nat.add_assoc _ _ _).symm

theorem cap_two_le_one (a b c : Nat) :
    min 2 a + min 2 b + c ≤ 1 ↔ a + b + c ≤ 1 := by omega

theorem compatible_iff (s : V → Bool) (t : W → Bool) :
    Compatible (state H pH s) (state K pK t) ↔
      IsSmallCut (glue H K pH pK) (Sum.elim s t) := by
  simp only [Compatible, state, Bool.or_eq_true, decide_eq_true_eq,
    Function.comp_apply, cap_two_le_one, IsSmallCut, cutSize_glue]
  simp only [Sum.exists, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- The entire low-cut test factors through the finite realized profiles. -/
theorem hasSmallCut_glue_iff : HasSmallCut (glue H K pH pK) ↔
    ∃ a ∈ profile H pH, ∃ b ∈ profile K pK, Compatible a b := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨state H pH (s ∘ Sum.inl), ⟨_, rfl⟩,
      state K pK (s ∘ Sum.inr), ⟨_, rfl⟩, ?_⟩
    apply (compatible_iff H K pH pK _ _).mpr
    have h : Sum.elim (s ∘ Sum.inl) (s ∘ Sum.inr) = s := by
      funext v; cases v <;> rfl
    simpa only [h] using hs
  · rintro ⟨a, ⟨s, rfl⟩, b, ⟨t, rfl⟩, h⟩
    exact ⟨Sum.elim s t, (compatible_iff H K pH pK s t).mp h⟩

variable {W' F' : Type*} [Fintype F'] (K' : Multigraph W' F') (pK' : P → W')

/-- Same realized low-cut signature, same result in every fixed exterior.
No port visibility or connectedness premise is needed. -/
theorem replacement_hasSmallCut (h : profile K pK = profile K' pK') :
    HasSmallCut (glue H K pH pK) ↔ HasSmallCut (glue H K' pH pK') := by
  rw [hasSmallCut_glue_iff, hasSmallCut_glue_iff, h]

end
end Mettapedia.GraphTheory.FourColor.BoundarySmallCutProfile
