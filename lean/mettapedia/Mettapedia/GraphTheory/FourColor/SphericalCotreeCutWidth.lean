import Mettapedia.GraphTheory.FourColor.FiniteEdgeParity
import Mettapedia.GraphTheory.FourColor.SphericalDualBFSTree

/-!
# Complete cut widths from an original-edge dual BFS tree

Root paths are represented by sets of original edges. Their parity boundary
consists of their two endpoints. This avoids identifying parallel dual edges
when comparing complete primal cuts with dual fundamental cycles.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalCotreeCutWidth

open SimpleGraphDartRotation GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided GoertzelV24PrimalCycleFacialBond
open GoertzelV24FaceDualConnectedness
open GoertzelV24FramedLocalDualCycleBond SphericalDualBFSTree
open FiniteEdgeParity
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

abbrev incidence (data : Data G) (e : G.edgeSet)
    (f : OrbitFace data.toRotationSystem) : Prop := e ∈ orbitFaceBoundary data.toRotationSystem f

variable {data : Data G} {root : OrbitFace data.toRotationSystem}
  (T : DualBFSTree data root)

theorem selected_edge_boundary (e : G.edgeSet) (he : e ∈ T.edges)
    (v : OrbitFace data.toRotationSystem) :
    boundary (incidence data) {e} v = mark (T.child e) v + mark (T.parent e) v := by
  have hne : T.child e ≠ T.parent e := by
    intro h
    have hd := T.descending e he
    rw [h] at hd
    exact Nat.lt_irrefl _ hd
  exact boundary_singleton_eq_marks (incidence data) e (T.child e) (T.parent e)
    hne (T.incidence e he) v

/-- Root-path support, its length bound, and its exact parity boundary. -/
theorem exists_root_support (f : OrbitFace data.toRotationSystem) :
    ∃ s : Finset G.edgeSet, s ⊆ T.edges ∧ s.card ≤ T.rank f ∧
      (∀ e ∈ s, T.rank (T.child e) ≤ T.rank f) ∧
      ∀ v, boundary (incidence data) s v = mark f v + mark root v := by
  classical
  have aux : ∀ n, ∀ f, T.rank f = n →
      ∃ s : Finset G.edgeSet, s ⊆ T.edges ∧ s.card ≤ n ∧
        (∀ e ∈ s, T.rank (T.child e) ≤ n) ∧
        ∀ v, boundary (incidence data) s v = mark f v + mark root v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hrank
      by_cases hf : f = root
      · subst f
        refine ⟨∅, Finset.empty_subset _, by simp, by simp, ?_⟩
        intro v
        simp only [boundary_empty, CharTwo.add_self_eq_zero]
      · obtain ⟨e, he, hc⟩ := T.covers f hf
        have hd := T.step e he
        rw [hc, hrank] at hd
        obtain ⟨s, hsub, hcard, hbelow, hbound⟩ :=
          ih (T.rank (T.parent e)) (by omega) (T.parent e) rfl
        have hnot : e ∉ s := by
          intro hs
          have h := hbelow e hs
          rw [hc, hrank] at h
          omega
        refine ⟨insert e s, Finset.insert_subset he hsub, ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hnot]
          omega
        · intro d hdmem
          rcases Finset.mem_insert.mp hdmem with rfl | hdmem
          · exact (congrArg T.rank hc).trans hrank |>.le
          · exact (hbelow d hdmem).trans (by omega)
        · intro v
          rw [boundary_insert _ _ _ hnot, selected_edge_boundary T e he, hc, hbound]
          simp only [add_assoc, CharTwo.add_cancel_left]
  exact aux (T.rank f) f rfl

/-- Even original-edge support contained in the ranked forest is empty. -/
theorem eq_empty_of_boundary_zero (s : Finset G.edgeSet) (hsub : s ⊆ T.edges)
    (hzero : ∀ v, boundary (incidence data) s v = 0) : s = ∅ := by
  classical
  apply RankedForestParity.eq_empty_of_even_incidence s T.child T.parent T.rank
    (T.child_injective.mono hsub) (fun e he => T.descending e (hsub he))
  intro v
  have h := (boundary_eq_zero_iff_even (incidence data) s v).mp (hzero v)
  have heq : s.filter (fun e => T.child e = v ∨ T.parent e = v) =
      s.filter (fun e => incidence data e v) := by
    ext e
    simp only [Finset.mem_filter]
    exact and_congr_right fun he => (T.incidence e (hsub he) v).symm
  rw [heq]
  exact h

/-- The parity boundary and all edges outside the forest uniquely determine a set. -/
theorem eq_of_boundary_eq_of_sdiff_eq (s t : Finset G.edgeSet)
    (hout : s \ T.edges = t \ T.edges)
    (hboundary : ∀ v, boundary (incidence data) s v = boundary (incidence data) t v) :
    s = t := by
  classical
  have hsub : s ∆ t ⊆ T.edges := by
    intro e he
    by_contra hn
    have hm : e ∈ s ↔ e ∈ t := by
      have h := congrArg (fun a : Finset G.edgeSet => e ∈ a) hout
      simpa only [Finset.mem_sdiff, hn, not_false_eq_true, and_true] using Iff.of_eq h
    rcases Finset.mem_symmDiff.mp he with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact ht (hm.mp hs)
    · exact hs (hm.mpr ht)
  apply Finset.symmDiff_eq_empty.mp
  apply eq_empty_of_boundary_zero T (s ∆ t) hsub
  intro v
  rw [boundary_symmDiff, hboundary]
  exact CharTwo.add_self_eq_zero _

/-- Two root paths and one nonforest edge give an even fundamental support. -/
theorem exists_fundamental_support (e : G.edgeSet) (he : e ∉ T.edges)
    (f g : OrbitFace data.toRotationSystem) (hfg : f ≠ g)
    (hf : incidence data e f) (hg : incidence data e g) :
    ∃ s t : Finset G.edgeSet,
      s ⊆ T.edges ∧ t ⊆ T.edges ∧ s.card ≤ T.rank f ∧ t.card ≤ T.rank g ∧
      ((s ∆ t) ∆ {e}) \ T.edges = {e} ∧
      ((s ∆ t) ∆ {e}).card ≤ T.rank f + T.rank g + 1 ∧
      ∀ v, boundary (incidence data) ((s ∆ t) ∆ {e}) v = 0 := by
  classical
  obtain ⟨s, hs, hsc, _, hsb⟩ := exists_root_support T f
  obtain ⟨t, ht, htc, _, htb⟩ := exists_root_support T g
  have hst : s ∆ t ⊆ T.edges :=
    Finset.symmDiff_subset_union.trans (Finset.union_subset hs ht)
  have hout : ((s ∆ t) ∆ {e}) \ T.edges = {e} := by
    ext a
    by_cases ha : a ∈ T.edges
    · have hne : a ≠ e := by rintro rfl; exact he ha
      simp [Finset.mem_sdiff, ha, hne]
    · have hnot : a ∉ s ∆ t := fun h => ha (hst h)
      simp [Finset.mem_sdiff, Finset.mem_symmDiff, ha, hnot]
  have hcard : ((s ∆ t) ∆ {e}).card ≤ T.rank f + T.rank g + 1 := by
    have h1 : (s ∆ t).card ≤ s.card + t.card :=
      (Finset.card_le_card Finset.symmDiff_subset_union).trans (Finset.card_union_le s t)
    have h2 : ((s ∆ t) ∆ {e}).card ≤ (s ∆ t).card + 1 := by
      simpa only [Finset.card_singleton] using
        (Finset.card_le_card (Finset.symmDiff_subset_union (s := s ∆ t) (t := {e}))).trans
          (Finset.card_union_le (s ∆ t) {e})
    omega
  refine ⟨s, t, hs, ht, hsc, htc, hout, hcard, ?_⟩
  intro v
  have hb := boundary_singleton_eq_marks (incidence data) e f g hfg
    (SphericalDualBFSTree.edge_incidence_iff_pair data e hfg hf hg) v
  rw [boundary_symmDiff, boundary_symmDiff, hsb, htb, hb]
  calc
    _ = (mark f v + mark f v) + (mark g v + mark g v) +
        (mark root v + mark root v) := by abel
    _ = 0 := by simp only [CharTwo.add_self_eq_zero]

/-- Full primal cuts have zero parity boundary on every two-sided quotient face. -/
theorem crossing_boundary_zero (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (side : V → Prop) (v : OrbitFace data.toRotationSystem) :
    boundary (incidence data) (localCrossingEdgeFinset G side) v = 0 := by
  classical
  apply (boundary_eq_zero_iff_even _ _ _).mpr
  have heq : (localCrossingEdgeFinset G side).filter (fun e => incidence data e v) =
      localCrossingEdgeFinset G side ∩ orbitFaceBoundary data.toRotationSystem v := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter, incidence]
  rw [heq]
  exact even_card_crossingEdgeFinset_inter_orbitFaceBoundary_of_faceTwoSided
    data side v (fun d _ => htwo d)

/-- Identify the whole primal cut, retaining every original crossing edge. -/
theorem crossing_eq_fundamental_support
    (htwo : OrbitFacesTwoSided data.toRotationSystem) (side : V → Prop)
    (e : G.edgeSet) (hout : localCrossingEdgeFinset G side \ T.edges = {e})
    (f g : OrbitFace data.toRotationSystem) (hfg : f ≠ g)
    (hf : incidence data e f) (hg : incidence data e g) :
    ∃ s t : Finset G.edgeSet,
      s ⊆ T.edges ∧ t ⊆ T.edges ∧ s.card ≤ T.rank f ∧ t.card ≤ T.rank g ∧
      localCrossingEdgeFinset G side = (s ∆ t) ∆ {e} ∧
      (localCrossingEdgeFinset G side).card ≤ T.rank f + T.rank g + 1 := by
  classical
  have he : e ∉ T.edges := by
    have hm : e ∈ localCrossingEdgeFinset G side \ T.edges := by rw [hout]; simp
    exact (Finset.mem_sdiff.mp hm).2
  obtain ⟨s, t, hs, ht, hsc, htc, hsupport, hcard, hzero⟩ :=
    exists_fundamental_support T e he f g hfg hf hg
  have heq : localCrossingEdgeFinset G side = (s ∆ t) ∆ {e} := by
    apply eq_of_boundary_eq_of_sdiff_eq T _ _ (hout.trans hsupport.symm)
    intro v
    rw [crossing_boundary_zero htwo side v, hzero]
  exact ⟨s, t, hs, ht, hsc, htc, heq, heq ▸ hcard⟩

/-- A complete cut meeting the primal cotree once has width at most 2h+1. -/
theorem crossing_card_le_of_singleton_sdiff
    (htwo : OrbitFacesTwoSided data.toRotationSystem) (side : V → Prop)
    (e : G.edgeSet) (hout : localCrossingEdgeFinset G side \ T.edges = {e})
    (h : ℕ) (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h) :
    (localCrossingEdgeFinset G side).card ≤ 2 * h + 1 := by
  classical
  let RS := data.toRotationSystem
  obtain ⟨d, hd⟩ := RS.dartsOn_nonempty e
  have hed : RS.edgeOf d = e := RS.mem_dartsOn.mp hd
  let f := dartOrbitFace RS d
  let g := dartOrbitFace RS (RS.alpha d)
  have hf : incidence data e f := by
    rw [← hed]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS d
  have hg : incidence data e g := by
    rw [← hed, ← RS.edge_alpha d]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha d)
  obtain ⟨_, _, _, _, _, _, _, hcard⟩ :=
    crossing_eq_fundamental_support T htwo side e hout f g (htwo d) hf hg
  have hfr : T.rank f ≤ h := by simpa only [T.rank_eq] using hradius f
  have hgr : T.rank g ≤ h := by simpa only [T.rank_eq] using hradius g
  omega

end
end Mettapedia.GraphTheory.FourColor.SphericalCotreeCutWidth
