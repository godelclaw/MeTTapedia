import Mettapedia.GraphTheory.FourColor.SphericalNestedBoundaryOrder

/-!
# Components of the actual capped vertex side

Delete every edge not internal to a vertex side, keeping the original
dart carrier. The resulting permutation map has one component for each
component of the induced side and one isolated rotation orbit for each
outside vertex. Neither the side nor its complement must be connected.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSideCappedComponents

open Equiv Equiv.Perm
open GoertzelV24MapEulerBound GoertzelV24InvolutionEdgeList
open GoertzelV24WordReachability GoertzelV24PermutationOrbitSurgery
open GoertzelV24FaceDualConnectedness GoertzelV24RotationCutDartDecomposition
open SphericalNestedBoundaryOrder

noncomputable section
attribute [local instance] Classical.propDecidable

section Invariants
variable {D A : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] in
theorem map_swap_eq (f : D → A) {a b : D} (h : f a = f b) (x : D) :
    f (swap a b x) = f x := by
  by_cases ha : x = a
  · subst x; simpa using h.symm
  by_cases hb : x = b
  · subst x; simpa using h
  rw [swap_apply_of_ne_of_ne ha hb]

/-- A permutation invariant remains constant on every transposition in
its edge presentation, including intermediate stripped permutations. -/
theorem invariant_edgeListAux (f : D → A) (fuel : ℕ) (p : Perm D)
    (hp : ∀ x, f (p x) = f x) :
    ∀ e ∈ edgeListAux fuel p, f e.1 = f e.2 := by
  induction fuel generalizing p with
  | zero => simp [edgeListAux]
  | succ n ih =>
    simp only [edgeListAux]
    split_ifs with h
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact (hp _).symm
      · apply ih (swap h.choose (p h.choose) * p) ?_ e he
        intro x
        rw [Perm.mul_apply, map_swap_eq f (hp h.choose).symm, hp]
    · simp

theorem invariant_edgeList (f : D → A) (p : Perm D)
    (hp : ∀ x, f (p x) = f x) :
    ∀ e ∈ edgeList p, f e.1 = f e.2 :=
  invariant_edgeListAux f (Fintype.card D) p hp

theorem invariant_word (f : D → A) (rho p : Perm D)
    (hr : ∀ x, f (rho x) = f x) (hp : ∀ x, f (p x) = f x)
    {x y : D} (h : WordReachable (rho :: swapGenerators (edgeList p)) x y) :
    f x = f y := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨g, hg, rfl⟩ := hs
    apply ih.trans
    rcases List.mem_cons.mp hg with rfl | hg
    · exact (hr _).symm
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
      exact (map_swap_eq f (invariant_edgeList f p hp e he) _).symm
end Invariants

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev SideGraph (RS : RotationSystem V E) (side : V → Prop) :=
  (rotationPrimalGraph RS).induce {v | side v}

instance sideComponentFintype (RS : RotationSystem V E) (side : V → Prop) :
    Fintype (SideGraph RS side).ConnectedComponent := Fintype.ofFinite _

abbrev Labels (RS : RotationSystem V E) (side : V → Prop) :=
  (SideGraph RS side).ConnectedComponent ⊕ {v // ¬ side v}

def label (RS : RotationSystem V E) (side : V → Prop) (d : RS.D) : Labels RS side :=
  if h : side (RS.vertOf d) then
    .inl ((SideGraph RS side).connectedComponentMk ⟨RS.vertOf d, h⟩)
  else .inr ⟨RS.vertOf d, h⟩

theorem label_rho (RS : RotationSystem V E) (side : V → Prop) (d : RS.D) :
    label RS side (RS.rho d) = label RS side d := by
  simp only [label, RS.vert_rho]

theorem label_cappedAlpha (RS : RotationSystem V E) (side : V → Prop) (d : RS.D) :
    label RS side (cappedAlpha RS side d) = label RS side d := by
  rw [cappedAlpha_apply]
  split_ifs with h
  · simp only [label, dif_pos h.1, dif_pos h.2]
    apply congrArg Sum.inl
    apply SimpleGraph.ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    exact (rotationPrimalGraph_adj_iff RS).mpr
      ⟨RS.alpha d, rfl, congrArg RS.vertOf (RS.alpha_involutive d)⟩
  · rfl

theorem word_iff_label (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (side : V → Prop) (x y : RS.D) :
    WordReachable (RS.rho :: swapGenerators (edgeList (cappedAlpha RS side))) x y ↔
      label RS side x = label RS side y := by
  constructor
  · exact invariant_word (label RS side) _ _ (label_rho RS side) (label_cappedAlpha RS side)
  intro h
  by_cases hx : side (RS.vertOf x) <;> by_cases hy : side (RS.vertOf y)
  · simp only [label, dif_pos hx, dif_pos hy, Sum.inl.injEq] at h
    obtain ⟨walk⟩ := SimpleGraph.ConnectedComponent.exact h
    exact wordReachable_capped_of_walk RS hrot side walk x y rfl rfl
  · simp [label, hx, hy] at h
  · simp [label, hx, hy] at h
  · simp only [label, dif_neg hx, dif_neg hy, Sum.inr.injEq] at h
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq (hrot x y (congrArg Subtype.val h))
    simpa only [hn] using wordReachable_pow
      (L := RS.rho :: swapGenerators (edgeList (cappedAlpha RS side))) List.mem_cons_self x n

theorem label_surjective (RS : RotationSystem V E) (hsurj : Function.Surjective RS.vertOf)
    (side : V → Prop) : Function.Surjective (label RS side) := by
  intro l
  rcases l with c | v
  · induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      obtain ⟨d, hd⟩ := hsurj v.1
      refine ⟨d, ?_⟩
      have hv : side v.1 := v.2
      simp only [label, hd, dif_pos hv]
  · obtain ⟨d, hd⟩ := hsurj v.1
    exact ⟨d, by simp [label, hd, v.2]⟩

/-- Components on the full dart carrier, including outside rotation orbits. -/
def componentEquiv (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) (side : V → Prop) :
    Quotient (wordSetoid (RS.rho :: swapGenerators (edgeList (cappedAlpha RS side)))) ≃
      Labels RS side :=
  Equiv.ofBijective (Quotient.lift (label RS side)
    (fun x y h => (word_iff_label RS hrot side x y).mp h)) (by
      constructor
      · intro a b
        induction a using Quotient.inductionOn with
        | h x =>
          induction b using Quotient.inductionOn with
          | h y =>
            intro h
            exact Quotient.sound ((word_iff_label RS hrot side x y).mpr h)
      · intro l
        obtain ⟨d, hd⟩ := label_surjective RS hsurj side l
        exact ⟨Quotient.mk _ d, hd⟩)

theorem wordOrbitCount_capped (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) (side : V → Prop) :
    wordOrbitCount (RS.rho :: swapGenerators (edgeList (cappedAlpha RS side))) =
      Fintype.card (SideGraph RS side).ConnectedComponent + Fintype.card {v // ¬ side v} := by
  rw [wordOrbitCount, Fintype.card_congr (componentEquiv RS hrot hsurj side)]
  exact Fintype.card_sum

/-- The component visible at a genuine exposed dart. -/
def boundaryComponent (RS : RotationSystem V E) (side : V → Prop) (b : BoundaryDart RS side) :
    (SideGraph RS side).ConnectedComponent :=
  (SideGraph RS side).connectedComponentMk ⟨RS.vertOf b.val.val, b.val.2⟩

/-- Every component of a proper side of a connected graph meets a port.
This statement needs neither planarity nor cubicity. -/
theorem boundaryComponent_surjective (RS : RotationSystem V E)
    (hconn : (rotationPrimalGraph RS).Connected) (side : V → Prop)
    (hproper : ∃ v, ¬ side v) : Function.Surjective (boundaryComponent RS side) := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    let marked : V → Prop := fun x => ∃ hx : side x,
      (SideGraph RS side).connectedComponentMk ⟨x, hx⟩ = (SideGraph RS side).connectedComponentMk v
    have hm : marked v.val := ⟨v.2, rfl⟩
    obtain ⟨w, hw⟩ := hproper
    have hn : ¬ marked w := by rintro ⟨h, _⟩; exact hw h
    obtain ⟨x, y, hxy, ⟨hx, hc⟩, hy⟩ :=
      GoertzelV24PlanarBondBoundaryOrder.exists_adjacent_crossing_of_connected
        hconn marked ⟨v.val, hm⟩ ⟨w, hn⟩
    have hny : ¬ side y := by
      intro hsy
      apply hy
      refine ⟨hsy, ?_⟩
      have he : (SideGraph RS side).connectedComponentMk ⟨x, hx⟩ =
          (SideGraph RS side).connectedComponentMk ⟨y, hsy⟩ :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
      exact he.symm.trans hc
    obtain ⟨d, hdx, hdy⟩ := (rotationPrimalGraph_adj_iff RS).mp hxy
    let b : BoundaryDart RS side := ⟨⟨d, hdx ▸ hx⟩, hdy ▸ hny⟩
    refine ⟨b, ?_⟩
    change (SideGraph RS side).connectedComponentMk ⟨RS.vertOf d, _⟩ = _
    simpa only [hdx] using hc

theorem components_le_boundary (RS : RotationSystem V E)
    (hconn : (rotationPrimalGraph RS).Connected) (side : V → Prop)
    (hproper : ∃ v, ¬ side v) :
    Fintype.card (SideGraph RS side).ConnectedComponent ≤ Fintype.card (BoundaryDart RS side) :=
  Fintype.card_le_of_surjective _ (boundaryComponent_surjective RS hconn side hproper)

end
end Mettapedia.GraphTheory.FourColor.VertexSideCappedComponents
