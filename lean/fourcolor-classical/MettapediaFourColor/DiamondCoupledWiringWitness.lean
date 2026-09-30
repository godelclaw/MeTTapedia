import MettapediaFourColor.DiamondCoupledWiringRotation
import MettapediaFourColor.OpenTangleKempeRepair

/-!
# Actual colouring witnesses for the coupled wiring

Restriction retains a complete exterior colouring and a colouring of all
seven wiring edges. Their boundary values agree jointly. Conversely these
witnesses reconstruct a Tait colouring of the actual closed rotation system.
-/

namespace FourColor.DiamondCoupledWiring.Rotation

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24RotationSpliceConstructor
open OpenTangleClosedWitness GoertzelV24RotationDartColoring
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin 8)) (h : Separated O)

private theorem physical_proper (c : (closed O h).EdgeColoring PhysicalColor)
    {a b : Dart I} (hv : vertex O a = vertex O b) (hne : a ≠ b) :
    c ((closed O h).edgeOf a) ≠ c ((closed O h).edgeOf b) := by
  apply c.valid
  apply (closed O h).edgeAdjacencyGraph_adj_iff.mpr
  refine ⟨?_, (closed O h).vertOf a, ?_, ?_⟩
  · intro he
    exact hne ((closed O h).edgeOf_injOn_dartsAt ((closed O h).vertOf a)
      (by simp [RotationSystem.dartsAt]) (by
        simp only [Finset.mem_coe, RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hv.symm) he)
  · exact (closed O h).mem_endpoints_iff.mpr ⟨a, (closed O h).mem_dartsOn.mpr rfl, rfl⟩
  · exact (closed O h).mem_endpoints_iff.mpr ⟨b, (closed O h).mem_dartsOn.mpr rfl, hv.symm⟩

-- This is the scalar Klein-group law at one proper cubic vertex.
private theorem three_sum : ∀ a b c : FourColor.Color,
    a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c → a + b = c := by decide

/-- Genuine edge colours restrict to a joint exterior/wiring witness. -/
theorem restrict (c : (closed O h).EdgeColoring PhysicalColor)
    (hc : (closed O h).IsTaitEdgeColoring c) :
    ∃ l : I ⊕ Fin 8 → PhysicalColor, ∃ k : DiamondCoupledWiring.Coloring,
      IsColor O l ∧ (∀ i, l (.inr i) = palette (k.edge (portEdge i))) ∧
        ∀ d, l d = c ((closed O h).edgeOf (.inl d)) := by
  let f : Dart I → FourColor.Color := fun d => palette.symm (c ((closed O h).edgeOf d))
  have hn (d) : f d ≠ 0 := by
    intro he
    exact hc _ (by simpa [f] using congrArg palette he)
  have ha (d) : f (alpha O d) = f d :=
    congrArg palette.symm (congrArg c ((closed O h).edge_alpha d))
  have hp {a b} (hv : vertex O a = vertex O b) (hne : a ≠ b) : f a ≠ f b := by
    intro he
    exact physical_proper O h c hv hne (palette.symm.injective he)
  let k : DiamondCoupledWiring.Coloring := {
    edge := ![f (.inl (.inr 0)), f (.inr 0), f (.inr 1), f (.inl (.inr 4)),
      f (.inr 3), f (.inr 4), f (.inr 2)]
    nonzero := by intro i; fin_cases i <;> exact hn _
    left := three_sum _ _ _ (hn _) (hn _) (hn _)
      (hp rfl (by simp)) (hp rfl (by simp)) (hp rfl (by simp))
    right := by
      change f (.inr 3) + f (.inr 4) = f (.inr 2)
      have he : f (.inr 5) = f (.inr 2) := ha (.inr 2)
      rw [← he]
      exact three_sum _ _ _ (hn _) (hn _) (hn _)
        (hp rfl (by simp)) (hp rfl (by simp)) (hp rfl (by simp)) }
  have hb (i : Fin 8) : f (.inl (.inr i)) = k.edge (portEdge i) := by
    fin_cases i
    · rfl
    · exact ha (.inl (.inr 0))
    · exact (ha (.inl (.inr 2))).symm
    · exact (ha (.inl (.inr 3))).symm
    · rfl
    · exact ha (.inl (.inr 4))
    · exact (ha (.inl (.inr 6))).symm
    · exact (ha (.inl (.inr 7))).symm
  let l : I ⊕ Fin 8 → PhysicalColor := fun d => c ((closed O h).edgeOf (.inl d))
  refine ⟨l, k, ⟨?_, ?_, fun _ => hc _⟩, ?_, fun _ => rfl⟩
  · intro i
    exact congrArg c ((closed O h).edge_alpha (.inl (.inl i)))
  · intro a b hv hne
    exact physical_proper O h c (congrArg Sum.inl hv) (fun he => hne (Sum.inl.inj he))
  · intro i
    exact (palette.apply_symm_apply _).symm.trans (congrArg palette (hb i))

private theorem pairwise_of_sum {a b c : FourColor.Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hs : a + b = c) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨fun he => hc (by rw [← hs, he, Color.add_self]), ?_, ?_⟩
  · intro he
    exact hb (add_left_cancel (hs.trans (he.symm.trans (add_zero _).symm)))
  · intro he
    exact ha (add_right_cancel (hs.trans (he.symm.trans (zero_add _).symm)))

private theorem core_proper (k : DiamondCoupledWiring.Coloring) {a b : Fin 6}
    (hv : coreVertex a = coreVertex b) (hne : a ≠ b) :
    k.edge (coreEdge a) ≠ k.edge (coreEdge b) := by
  obtain ⟨h12, h16, h26⟩ := pairwise_of_sum (k.nonzero 1) (k.nonzero 2) (k.nonzero 6) k.left
  obtain ⟨h45, h46, h56⟩ := pairwise_of_sum (k.nonzero 4) (k.nonzero 5) (k.nonzero 6) k.right
  fin_cases a <;> fin_cases b <;> simp_all [coreVertex, coreEdge, Ne.symm]

/-- Jointly matching colours reconstruct every edge of the rewired graph,
and preserve the complete exterior assignment. -/
theorem glue (l : I ⊕ Fin 8 → PhysicalColor) (k : DiamondCoupledWiring.Coloring)
    (hl : IsColor O l) (hm : ∀ i, l (.inr i) = palette (k.edge (portEdge i))) :
    ∃ c : (closed O h).EdgeColoring PhysicalColor,
      (closed O h).IsTaitEdgeColoring c ∧
        ∀ d, c ((closed O h).edgeOf (.inl d)) = l d := by
  let f : Dart I → PhysicalColor := Sum.elim l (fun j => palette (k.edge (coreEdge j)))
  have ha : ∀ d, f ((closed O h).alpha d) = f d := by
    rintro ((i | b) | j)
    · exact hl.1 i
    · fin_cases b <;> dsimp [closed, data, alpha, seam, seamFun, f] <;>
        simp only [hm, portEdge, coreEdge] <;> rfl
    · fin_cases j <;> dsimp [closed, data, alpha, seam, seamFun, f] <;>
        simp only [hm, portEdge, coreEdge] <;> rfl
  have hp : ∀ {a b}, (closed O h).vertOf a = (closed O h).vertOf b →
      a ≠ b → f a ≠ f b := by
    rintro (a | a) (b | b) hv hne
    · exact hl.2.1 (Sum.inl.inj hv) (fun he => hne (congrArg Sum.inl he))
    · exact (Sum.inl_ne_inr hv).elim
    · exact (Sum.inr_ne_inl hv).elim
    · exact fun he => core_proper k (Sum.inr.inj hv)
        (fun he => hne (congrArg Sum.inr he)) (palette.injective he)
  have hn : ∀ d, f d ≠ 0 := by
    rintro (d | j)
    · exact hl.2.2 d
    · exact fun he => k.nonzero _ (palette.injective he)
  exact ⟨edgeColoringOfDartColor (closed O h) f ha hp,
    edgeColoringOfDartColor_isTait (closed O h) f ha hp hn,
    fun d => edgeColoringOfDartColor_edgeOf (closed O h) f ha hp (.inl d)⟩

/-- Existential boundary elimination works inside every exterior satisfying
the two explicit wire-separation conditions. -/
theorem colorable_iff : RotationSystemTaitColorable (closed O h) ↔
    ∃ k : DiamondCoupledWiring.Coloring,
      OpenTangleKempeRepair.Trace O (Equiv.refl _) (word k) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨l, k, hl, hm, _⟩ := restrict O h c hc
    refine ⟨k, l, hl, ?_⟩
    rw [← word_ports, List.map_map]
    exact List.map_congr_left fun i _ => hm i
  · rintro ⟨k, l, hl, he⟩
    have hm (i) : l (.inr i) = palette (k.edge (portEdge i)) := by
      rw [← word_ports, List.map_map] at he
      exact List.map_inj_left.mp he i (List.mem_finRange i)
    obtain ⟨c, hc, _⟩ := glue O h l k hl hm
    exact ⟨c, hc⟩

/-- A colourable actual wiring starts a compatible repair through both
insertions, retaining a genuine exterior witness at the repaired word. -/
theorem compatible_history
    (hc : RotationSystemTaitColorable (closed O h))
    (hclosed : KempeClosed (OpenTangleKempeRepair.Trace O (Equiv.refl _))) :
    ∃ et', ∃ c : DiamondInsertionGSLT.State .reference,
      ∃ x : DiamondInsertionGSLT.State .alternatives,
      OpenTangleKempeRepair.Trace O (Equiv.refl _) et' ∧
        et' = FourColor.trace ((cfring cf004).reverse.map c.val) ∧
        DiamondInsertionGSLT.semantics.Supports DiamondInsertionGSLT.route x c := by
  obtain ⟨k, hk⟩ := (colorable_iff O h).mp hc
  exact DiamondCoupledWiring.compatible_history k hclosed hk

end
end FourColor.DiamondCoupledWiring.Rotation
