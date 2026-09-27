import Mettapedia.GraphTheory.FourColor.SmallCutConnectedBridgeless

/-!
# The part of a cut profile that can affect a bridge

Only realized states of cost at most one can participate in a zero- or
one-edge cut after sewing. For a nonempty connected bridgeless piece these
are exactly the two constant states. Thus any two such pieces are
interchangeable for connectedness and bridge-freedom in a fixed exterior.
No claim about colourings or planarity is made by this structural criterion.
-/

namespace Mettapedia.GraphTheory.FourColor.SmallCutReplacementCore

open GoertzelV24BoundaryEssentialGluing Multigraph
open BoundarySmallCutProfile SmallCutConnectedBridgeless

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E P : Type*} [Fintype E]

def core (S : Set (State P)) : Set (State P) := {a | a ∈ S ∧ a.cost.val ≤ 1}

def uniformState (b : Bool) : State P := ⟨fun _ => b, b, !b, 0⟩

/-- A small cut of a graph without nontrivial small cuts is constant. -/
theorem constant_of_small (G : Multigraph V E) (hG : ¬ HasSmallCut G)
    (s : V → Bool) (hs : cutSize G s ≤ 1) : ∃ b, ∀ v, s v = b := by
  by_cases ht : ∃ v, s v = true
  · refine ⟨true, fun v => ?_⟩
    cases hv : s v with
    | true => rfl
    | false => exact (hG ⟨s, ht, ⟨v, hv⟩, hs⟩).elim
  · refine ⟨false, fun v => ?_⟩
    cases hv : s v with
    | false => rfl
    | true => exact (ht ⟨v, hv⟩).elim

theorem state_constant [Nonempty V] (G : Multigraph V E) (ports : P → V) (b : Bool) :
    state G ports (fun _ => b) = uniformState b := by
  cases b <;> simp [state, uniformState, cutSize, Function.comp_def]

/-- Cost-two records can differ without affecting the bridge test. -/
theorem core_eq_uniform [Nonempty V] (G : Multigraph V E) (ports : P → V)
    (hG : ¬ HasSmallCut G) : core (profile G ports) = Set.range (uniformState (P := P)) := by
  ext a
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    have hsize : cutSize G s ≤ 1 := by
      change min 2 (cutSize G s) ≤ 1 at hs
      omega
    obtain ⟨b, hb⟩ := constant_of_small G hG s hsize
    have he : s = fun _ => b := funext hb
    exact ⟨b, by rw [he, state_constant]⟩
  · rintro ⟨b, rfl⟩
    refine ⟨⟨fun _ => b, state_constant G ports b⟩, by simp [uniformState]⟩

section Cycles

variable {A : Type*} [Fintype A]

/-- The directed edges of a permutation, viewed as an undirected multigraph.
Two-cycles retain their two distinct edge identifiers. -/
def permutationGraph (p : Equiv.Perm A) : Multigraph A A := ⟨id, p⟩

/-- A union of finite cycles has no cut of size one. A cut of size at most
one is constant along every edge, including when there are several cycles. -/
theorem permutation_small_cut (p : Equiv.Perm A) (s : A → Bool)
    (hs : cutSize (permutationGraph p) s ≤ 1) (a : A) : s a = s (p a) := by
  by_contra hne
  have hrest (b : A) (hb : b ≠ a) : s b = s (p b) :=
    unique_of_small_cut (permutationGraph p) s hs a hne b hb
  have hsum : (∑ b : A, (((s b).toNat : ℤ) - (s (p b)).toNat)) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp p (fun b => ((s b).toNat : ℤ))]
    exact sub_self _
  have he : (∑ b : A, (((s b).toNat : ℤ) - (s (p b)).toNat)) =
      ((s a).toNat : ℤ) - (s (p a)).toNat := by
    apply Finset.sum_eq_single a
    · intro b _ hb
      rw [hrest b hb, sub_self]
    · simp
  rw [he] at hsum
  cases ha : s a <;> cases hb : s (p a) <;> simp_all

end Cycles

variable {W F W' F' : Type*} [Fintype F] [Fintype F'] [Fintype P]
  (G : Multigraph V E) (K : Multigraph W F) (K' : Multigraph W' F')
  (pG : P → V) (pK : P → W) (pK' : P → W')

/-- The full exterior is arbitrary; only the replacement's small-cost
fragment must agree. -/
theorem replacement_hasSmallCut (h : core (profile K pK) = core (profile K' pK')) :
    HasSmallCut (glue G K pG pK) ↔ HasSmallCut (glue G K' pG pK') := by
  rw [hasSmallCut_glue_iff, hasSmallCut_glue_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hc⟩
    have hbcore : b ∈ core (profile K pK) := ⟨hb, by have := hc.2.2; omega⟩
    rw [h] at hbcore
    exact ⟨a, ha, b, hbcore.1, hc⟩
  · rintro ⟨a, ha, b, hb, hc⟩
    have hbcore : b ∈ core (profile K' pK') := ⟨hb, by have := hc.2.2; omega⟩
    rw [← h] at hbcore
    exact ⟨a, ha, b, hbcore.1, hc⟩

theorem replacement_connected_bridgeless
    (h : core (profile K pK) = core (profile K' pK')) :
    ((glue G K pG pK).Connected ∧ (glue G K pG pK).Bridgeless) ↔
      ((glue G K' pG pK').Connected ∧ (glue G K' pG pK').Bridgeless) := by
  rw [← no_small_cut_iff, ← no_small_cut_iff]
  exact not_congr (replacement_hasSmallCut G K K' pG pK pK' h)

/-- Nonempty connected bridgeless interiors have the same contextual
connectivity and bridge behaviour, even with different port vertices. -/
theorem replacement_of_internal [Nonempty W] [Nonempty W']
    (hK : K.Connected ∧ K.Bridgeless) (hK' : K'.Connected ∧ K'.Bridgeless) :
    ((glue G K pG pK).Connected ∧ (glue G K pG pK).Bridgeless) ↔
      ((glue G K' pG pK').Connected ∧ (glue G K' pG pK').Bridgeless) := by
  apply replacement_connected_bridgeless G K K' pG pK pK'
  rw [core_eq_uniform K pK ((no_small_cut_iff K).mpr hK),
    core_eq_uniform K' pK' ((no_small_cut_iff K').mpr hK')]

end
end Mettapedia.GraphTheory.FourColor.SmallCutReplacementCore
