import Mettapedia.GraphTheory.FourColor.ZigzagTubeReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion

/-!
# Finite boundary certificates normalize an infinite tube family

The existing width-five certificate equates four and five ring transfers.
Here it is connected to the literal tube geometry: every tube of at least
four rings has exactly the support of the four-ring tube. A closed exterior
keeps its colours, and shortening preserves the spherical cubic map class.
This uses the local ring certificate, not the Four Colour theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24CorridorPumping TubeRingOrbit

variable (k : Nat) [NeZero k]

omit [NeZero k] in
theorem encW_wordOf {X : Nat} (hX : X < 3 ^ k) : encW k (wordOf k X) = X := by
  unfold encW
  calc
    encB 3 (fun i => if h : i < k then idx (wordOf k X ⟨i, h⟩) else 0) k =
        encB 3 (digit X) k := by
      apply encB_congr
      intro i hi
      simp only [hi, dite_true, wordOf, idx_col (digit_lt X i)]
    _ = X := encB_digB_of_lt hX

private theorem transfer_zero_endpoints {State : Type*} {R : State → State → Prop}
    {x y : State} (h : ExactRelationalTransfer R 0 x y) : x = y := by
  cases h
  rfl

private theorem transfer_snoc_iff {State : Type*} (R : State → State → Prop)
    (n : Nat) (x y : State) :
    ExactRelationalTransfer R (n + 1) x y ↔
      ∃ z, ExactRelationalTransfer R n x z ∧ R z y := by
  induction n generalizing x with
  | zero =>
      constructor
      · intro h
        cases h with
        | succ hs ht => cases ht; exact ⟨x, .zero _, hs⟩
      · rintro ⟨z, hz, hs⟩
        cases hz
        exact .succ hs (.zero _)
  | succ n ih =>
      constructor
      · intro h
        cases h with
        | succ hs ht =>
          obtain ⟨z, hz, hy⟩ := (ih _).mp ht
          exact ⟨z, .succ hs hz, hy⟩
      · rintro ⟨z, hz, hy⟩
        exact hz.comp (.succ hy (.zero _))

/-- The tabulated set iteration retains exactly the possible colour words,
including all intermediate choices of actual ring colourings. -/
theorem mem_iterate_singleton_iff_transfer {X Y : Nat}
    (hX : X < 3 ^ k) (hY : Y < 3 ^ k) (n : Nat) :
    Y ∈ (stepS k)^[n] {X} ↔
      ExactRelationalTransfer (Step k) n (wordOf k X) (wordOf k Y) := by
  induction n generalizing Y with
  | zero =>
      change Y = X ↔ _
      constructor
      · rintro rfl
        exact .zero _
      · intro h
        have equal := transfer_zero_endpoints h
        have := congrArg (encW k) equal
        simpa only [encW_wordOf k hX, encW_wordOf k hY] using this.symm
  | succ n ih =>
      rw [Function.iterate_succ_apply', transfer_snoc_iff]
      change (Y < 3 ^ k ∧ ∃ Z, Z < 3 ^ k ∧
        Z ∈ (stepS k)^[n] {X} ∧ (stepMask k Z (2 ^ k)).testBit Y = true) ↔ _
      constructor
      · rintro ⟨_, Z, hZ, hz, hy⟩
        exact ⟨wordOf k Z, (ih hZ).mp hz, (accepts_iff_testBit k Z Y hY).mpr hy⟩
      · rintro ⟨z, hz, hy⟩
        have hnz : ∀ i, z i ≠ 0 := by
          obtain ⟨a, ha, _⟩ := (accepts_iff k z (wordOf k Y)).mp hy
          exact ha.x_ne_zero
        refine ⟨hY, encW k z, encW_lt k z, ?_, ?_⟩
        · apply (ih (encW_lt k z)).mpr
          rwa [wordOf_encW k z hnz]
        · apply (accepts_iff_testBit k _ Y hY).mp
          rwa [wordOf_encW k z hnz]

private theorem positive_transfer_input {n : Nat} {x y : Fin k → Color}
    (hn : 0 < n) (h : ExactRelationalTransfer (Step k) n x y) : ∀ i, x i ≠ 0 := by
  cases h with
  | zero => omega
  | succ hs _ =>
      obtain ⟨a, ha, _⟩ := (accepts_iff k _ _).mp hs
      exact ha.x_ne_zero

private theorem positive_transfer_output {n : Nat} {x y : Fin k → Color}
    (hn : 0 < n) (h : ExactRelationalTransfer (Step k) n x y) : ∀ i, y i ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact HiddenTangle.ne_zero_of_accepts (tube k m) ((tube_accepts_iff k m x y).mpr h)

/-- One finite equality yields an equality of the complete boundary relations,
including the failure of words containing a zero colour. -/
theorem transfer_adjacent_of_stabilizes (hk : 2 ≤ k) (certificate : stabilizes k = true)
    (x y : Fin k → Color) :
    ExactRelationalTransfer (Step k) k x y ↔
      ExactRelationalTransfer (Step k) (k - 1) x y := by
  by_cases hx : ∀ i, x i ≠ 0
  · by_cases hy : ∀ i, y i ≠ 0
    · have equal := stepS_iterate_singleton_of_stabilizes k certificate (encW_lt k x)
      have observations := congrArg (fun S : Set Nat => encW k y ∈ S) equal
      rw [propext (mem_iterate_singleton_iff_transfer k (encW_lt k x) (encW_lt k y) k),
        propext (mem_iterate_singleton_iff_transfer k (encW_lt k x) (encW_lt k y) (k - 1)),
        wordOf_encW k x hx, wordOf_encW k y hy] at observations
      exact Iff.of_eq observations
    · exact ⟨fun h => False.elim (hy (positive_transfer_output k (by omega) h)),
        fun h => False.elim (hy (positive_transfer_output k (by omega) h))⟩
  · exact ⟨fun h => False.elim (hx (positive_transfer_input k (by omega) h)),
      fun h => False.elim (hx (positive_transfer_input k (by omega) h))⟩

theorem tube_adjacent_of_stabilizes (hk : 2 ≤ k) (certificate : stabilizes k = true)
    (x y : Fin k → Color) :
    (tube k (k - 1)).Accepts x y ↔ (tube k (k - 2)).Accepts x y := by
  rw [tube_accepts_iff, tube_accepts_iff]
  simpa only [show k - 1 + 1 = k by omega, show k - 2 + 1 = k - 1 by omega] using
    transfer_adjacent_of_stabilizes k hk certificate x y

/-- Arbitrarily many further rings are covered by the same certificate. -/
theorem tube_add_of_stabilizes (hk : 2 ≤ k) (certificate : stabilizes k = true)
    (extra : Nat) (x y : Fin k → Color) :
    (tube k (k - 2 + extra)).Accepts x y ↔ (tube k (k - 2)).Accepts x y := by
  induction extra generalizing y with
  | zero => simp
  | succ extra ih =>
      rw [show k - 2 + (extra + 1) = (k - 2 + extra) + 1 by omega, tube_succ]
      rw [HiddenTangle.appendRing_accepts_iff]
      simp_rw [ih]
      have heq : k - 2 + 1 = k - 1 := by omega
      exact ((HiddenTangle.appendRing_accepts_iff k (tube k (k - 2)) x y).symm).trans
        (by simpa only [← tube_succ, heq] using
          tube_adjacent_of_stabilizes k hk certificate x y)

/-- A finite normal form for length, without a finite bound on all graph widths. -/
theorem tube_normalize_of_stabilizes (hk : 2 ≤ k) (certificate : stabilizes k = true)
    (n : Nat) (x y : Fin k → Color) :
    (tube k n).Accepts x y ↔ (tube k (min n (k - 2))).Accepts x y := by
  by_cases hn : k - 2 ≤ n
  · rw [Nat.min_eq_right hn]
    simpa only [Nat.add_sub_of_le hn] using
      tube_add_of_stabilizes k hk certificate (n - (k - 2)) x y
  · rw [Nat.min_eq_left (by omega : n ≤ k - 2)]

theorem five_tube_normalize (n : Nat) (x y : Fin 5 → Color) :
    (tube 5 n).Accepts x y ↔ (tube 5 (min n 3)).Accepts x y :=
  tube_normalize_of_stabilizes 5 (by omega)
    GoertzelV24FiveTubeExclusion.five_ring_stabilizes n x y

theorem five_tube_support (r s : Nat) (hr : 3 ≤ r) (hs : 3 ≤ s)
    (x y : Fin 5 → Color) :
    (tube 5 r).Accepts x y ↔ (tube 5 s).Accepts x y := by
  have left : (tube 5 r).Accepts x y ↔ (tube 5 3).Accepts x y := by
    simpa only [Nat.min_eq_right hr] using five_tube_normalize r x y
  have right : (tube 5 s).Accepts x y ↔ (tube 5 3).Accepts x y := by
    simpa only [Nat.min_eq_right hs] using five_tube_normalize s x y
  exact left.trans right.symm

open OpenTangleWitnessComposition Mettapedia.GSLT.LooseRelationEquipment

/-- Eliminate redundant rings while keeping the ordered seam words. -/
noncomputable def fiveTubeNormalizeCell (n : Nat) :
    Cell id id (colourRelation (tube 5 n).data)
      (colourRelation (tube 5 (min n 3)).data) where
  map := fun {x y} witness => Classical.choice <|
    (nonempty_colourRelation_iff _ x y).mpr <|
      (five_tube_normalize n x y).mp ⟨witness.val, witness.property⟩

/-- Reconstruct all removed rings; no arbitrary initial colouring needs
to extend through an operation that changes its seam word. -/
noncomputable def fiveTubeReconstructCell (n : Nat) :
    Cell id id (colourRelation (tube 5 (min n 3)).data)
      (colourRelation (tube 5 n).data) where
  map := fun {x y} witness => Classical.choice <|
    (nonempty_colourRelation_iff _ x y).mpr <|
      (five_tube_normalize n x y).mpr ⟨witness.val, witness.property⟩

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24TwoEdgeCutMinimality GoertzelV24CompositeSeamCubic

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] tubeVertexFintype tubeInteriorFintype

variable {V I B : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]

/-- The four-ring normal form has the same colouring behaviour in every
closed exterior, even when that exterior is disconnected or nonplanar. -/
theorem five_tube_closed_normalize (n : Nat) (outside : OpenTangleData V I B)
    (m : B ≃ Fin 5 ⊕ Fin 5) :
    RotationSystemTaitColorable (outside.composeRotationSystem (asOpen (tube 5 n).data) m) ↔
      RotationSystemTaitColorable
        (outside.composeRotationSystem (asOpen (tube 5 (min n 3)).data) m) :=
  OpenTangleClosedBoundary.compose_colorable_iff (tube 5 n).data
    (tube 5 (min n 3)).data (five_tube_normalize n) outside m

/-- Reconstruct a physical colouring from a colouring of the normalized
map, retaining every exterior edge colour. -/
def reconstructFiveTube (n : Nat) (outside : OpenTangleData V I B)
    (m : B ≃ Fin 5 ⊕ Fin 5)
    (c : (outside.composeRotationSystem (asOpen (tube 5 (min n 3)).data) m).EdgeColoring Color)
    (hc : (outside.composeRotationSystem (asOpen (tube 5 (min n 3)).data) m).IsTaitEdgeColoring c) :
    (outside.composeRotationSystem (asOpen (tube 5 n).data) m).EdgeColoring Color :=
  OpenTangleClosedBoundary.replaceEdgeColoring (tube 5 (min n 3)).data (tube 5 n).data
    (fun x y => (five_tube_normalize n x y).mpr) outside m c hc

theorem reconstructFiveTube_isTait (n : Nat) (outside : OpenTangleData V I B)
    (m : B ≃ Fin 5 ⊕ Fin 5)
    (c : (outside.composeRotationSystem (asOpen (tube 5 (min n 3)).data) m).EdgeColoring Color)
    (hc : (outside.composeRotationSystem (asOpen (tube 5 (min n 3)).data) m).IsTaitEdgeColoring c) :
    (outside.composeRotationSystem (asOpen (tube 5 n).data) m).IsTaitEdgeColoring
      (reconstructFiveTube n outside m c hc) :=
  OpenTangleClosedBoundary.replaceEdgeColoring_isTait (tube 5 (min n 3)).data (tube 5 n).data
    (fun x y => (five_tube_normalize n x y).mpr) outside m c hc

theorem reconstructFiveTube_exterior (n : Nat) (outside : OpenTangleData V I B)
    (m : B ≃ Fin 5 ⊕ Fin 5)
    (c : (outside.composeRotationSystem (asOpen (tube 5 (min n 3)).data) m).EdgeColoring Color)
    (hc : (outside.composeRotationSystem (asOpen (tube 5 (min n 3)).data) m).IsTaitEdgeColoring c)
    (d : I ⊕ B) :
    reconstructFiveTube n outside m c hc
        ((GoertzelV24CompositeSeamMultigraph.compositeDarts outside (asOpen (tube 5 n).data) m).edgeOf
          (composeDartEquiv (.inl d))) =
      c ((GoertzelV24CompositeSeamMultigraph.compositeDarts outside
        (asOpen (tube 5 (min n 3)).data) m).edgeOf (composeDartEquiv (.inl d))) :=
  OpenTangleClosedBoundary.replaceEdgeColoring_exterior
    (tube 5 (min n 3)).data (tube 5 n).data
    (fun x y => (five_tube_normalize n x y).mpr) outside m c hc d

/-- Any literal five-port tube with at least five rings can be reduced to
four rings inside the same bridgeless spherical cubic map class. -/
theorem strict_five_tube_reduction (n : Nat) (hn : 4 ≤ n)
    (outside : OpenTangleData V I B) (m : B ≃ Fin 5 ⊕ Fin 5)
    (h : BridgelessSphericalCubicMapData
      (outside.composeRotationSystem (asOpen (tube 5 n).data) m)) :
    Fintype.card (V ⊕ (tube 5 3).V) < Fintype.card (V ⊕ (tube 5 n).V) ∧
      BridgelessSphericalCubicMapData
        (outside.composeRotationSystem (asOpen (tube 5 3).data) m) ∧
      (RotationSystemTaitColorable (outside.composeRotationSystem (asOpen (tube 5 n).data) m) ↔
        RotationSystemTaitColorable (outside.composeRotationSystem (asOpen (tube 5 3).data) m)) := by
  refine ⟨?_, tube_replacement_class 5 (by omega) n 3 outside m h, ?_⟩
  · have smaller : Nat.card (tube 5 3).V < Nat.card (tube 5 n).V := by
      rw [tube_vertex_card, tube_vertex_card]
      omega
    simpa only [Fintype.card_sum, Nat.add_lt_add_iff_left, Nat.card_eq_fintype_card] using smaller
  · exact OpenTangleClosedBoundary.compose_colorable_iff (tube 5 n).data (tube 5 3).data
      (five_tube_support n 3 (by omega) (by omega)) outside m

end

end Mettapedia.GraphTheory.FourColor.ZigzagRing
