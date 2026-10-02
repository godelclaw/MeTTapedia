import Mettapedia.Combinatorics.PolymerGas.ConnectedCount

/-!
# Finite connected-component decompositions

Every finite vertex set has a unique decomposition into nonempty connected
sets with no edges between distinct parts. Products over vertices factor over
these parts.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Mettapedia.Combinatorics.PolymerGas

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A partition into connected sets separated by the absence of edges. -/
def IsComponentFamily (Γ : Finset (Finset V)) : Prop :=
  (∀ C ∈ Γ, (G.induce (C : Set V)).Connected) ∧
  (Γ : Set (Finset V)).PairwiseDisjoint id ∧
  ∀ C ∈ Γ, ∀ D ∈ Γ, C ≠ D → ∀ u ∈ C, ∀ v ∈ D, ¬ G.Adj u v

/-- A component of the induced graph, as a subset of the original vertices. -/
def componentVertices (A : Finset V) (c : (G.induce (A : Set V)).ConnectedComponent) :
    Finset V := c.supp.toFinset.image Subtype.val

omit [Fintype V] in
@[simp] theorem mem_componentVertices (A : Finset V)
    (c : (G.induce (A : Set V)).ConnectedComponent) (v : V) :
    v ∈ componentVertices G A c ↔ ∃ h : v ∈ A,
      (G.induce (A : Set V)).connectedComponentMk ⟨v, h⟩ = c := by
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
    have hx' : x ∈ c.supp := Set.mem_toFinset.mp hx
    exact ⟨x.2, hx'⟩
  · rintro ⟨hv, hc⟩
    exact mem_image.mpr ⟨⟨v, hv⟩, Set.mem_toFinset.mpr hc, rfl⟩

/-- The connected-component decomposition of a vertex set. -/
def componentFamily (A : Finset V) : Finset (Finset V) :=
  univ.image (componentVertices G A)

theorem componentVertices_connected (A : Finset V)
    (c : (G.induce (A : Set V)).ConnectedComponent) :
    (G.induce (componentVertices G A c : Set V)).Connected := by
  let f : c.toSimpleGraph →g G.induce (componentVertices G A c : Set V) :=
    { toFun := fun v => ⟨v.1.1,
        (mem_componentVertices G A c _).mpr ⟨v.1.2, v.2⟩⟩
      map_rel' := fun h => h }
  apply c.connected_toSimpleGraph.map f
  rintro ⟨v, hv⟩
  obtain ⟨hA, hc⟩ := (mem_componentVertices G A c v).mp hv
  exact ⟨⟨⟨v, hA⟩, hc⟩, rfl⟩

theorem componentVertices_disjoint (A : Finset V)
    {c d : (G.induce (A : Set V)).ConnectedComponent} (hcd : c ≠ d) :
    Disjoint (componentVertices G A c) (componentVertices G A d) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨hA, hc⟩ := (mem_componentVertices G A c v).mp hv
  obtain ⟨_, hd⟩ := (mem_componentVertices G A d v).mp hw
  exact hcd (hc.symm.trans hd)

theorem isComponentFamily_componentFamily (A : Finset V) :
    IsComponentFamily G (componentFamily G A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨c, _, rfl⟩ := mem_image.mp hC
    exact componentVertices_connected G A c
  · intro C hC D hD hCD
    obtain ⟨c, _, rfl⟩ := mem_image.mp hC
    obtain ⟨d, _, rfl⟩ := mem_image.mp hD
    exact componentVertices_disjoint G A (fun h => hCD (congrArg _ h))
  · intro C hC D hD hCD u hu v hv huv
    obtain ⟨c, _, rfl⟩ := mem_image.mp hC
    obtain ⟨d, _, rfl⟩ := mem_image.mp hD
    obtain ⟨huA, huc⟩ := (mem_componentVertices G A c u).mp hu
    obtain ⟨hvA, hvd⟩ := (mem_componentVertices G A d v).mp hv
    have h : c = d := huc.symm.trans
      ((SimpleGraph.ConnectedComponent.sound
        (show (G.induce (A : Set V)).Adj ⟨u, huA⟩ ⟨v, hvA⟩ from huv).reachable).trans hvd)
    exact hCD (congrArg _ h)

@[simp] theorem biUnion_componentFamily (A : Finset V) :
    (componentFamily G A).biUnion id = A := by
  ext v
  simp only [mem_biUnion, componentFamily, mem_image, mem_univ, true_and, id_eq]
  constructor
  · rintro ⟨C, ⟨c, rfl⟩, hv⟩
    exact ((mem_componentVertices G A c v).mp hv).choose
  · intro hv
    refine ⟨_, ⟨(G.induce (A : Set V)).connectedComponentMk ⟨v, hv⟩, rfl⟩, ?_⟩
    exact (mem_componentVertices G A _ v).mpr ⟨hv, rfl⟩

variable {G}

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsComponentFamily.mem_of_adj {Γ : Finset (Finset V)}
    (hΓ : IsComponentFamily G Γ) {C : Finset V} (hC : C ∈ Γ)
    {u v : V} (hu : u ∈ C) (hv : v ∈ Γ.biUnion id) (huv : G.Adj u v) : v ∈ C := by
  obtain ⟨D, hD, hvD⟩ := mem_biUnion.mp hv
  by_cases hCD : C = D
  · simpa [hCD] using hvD
  · exact (hΓ.2.2 C hC D hD hCD u hu v hvD huv).elim

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsComponentFamily.mem_of_walk {Γ : Finset (Finset V)}
    (hΓ : IsComponentFamily G Γ) {C : Finset V} (hC : C ∈ Γ)
    {u v : Γ.biUnion id} (p : (G.induce (Γ.biUnion id : Set V)).Walk u v)
    (hu : u.1 ∈ C) : v.1 ∈ C := by
  induction p with
  | nil => exact hu
  | @cons u v w huv q ih => exact ih (hΓ.mem_of_adj hC hu v.2 huv)

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsComponentFamily.connected_subset_part {Γ : Finset (Finset V)}
    (hΓ : IsComponentFamily G Γ) {D : Finset V}
    (hD : (G.induce (D : Set V)).Connected) (hsub : D ⊆ Γ.biUnion id) :
    ∃ C ∈ Γ, D ⊆ C := by
  obtain ⟨u⟩ := hD.nonempty
  obtain ⟨C, hC, huC⟩ := mem_biUnion.mp (hsub u.2)
  refine ⟨C, hC, fun v hv => ?_⟩
  obtain ⟨p⟩ := hD.preconnected u ⟨v, hv⟩
  let f : G.induce (D : Set V) →g G.induce (Γ.biUnion id : Set V) :=
    { toFun := fun z => ⟨z.1, hsub z.2⟩
      map_rel' := fun h => h }
  exact hΓ.mem_of_walk hC (p.map f) huC

/-- Connected partitions without cross edges are uniquely determined by their union. -/
theorem IsComponentFamily.eq_of_biUnion_eq {Γ Θ : Finset (Finset V)}
    (hΓ : IsComponentFamily G Γ) (hΘ : IsComponentFamily G Θ)
    (hU : Γ.biUnion id = Θ.biUnion id) : Γ = Θ := by
  suffices h : ∀ Γ Θ : Finset (Finset V), IsComponentFamily G Γ →
      IsComponentFamily G Θ → Γ.biUnion id = Θ.biUnion id → Γ ⊆ Θ from
    Subset.antisymm (h Γ Θ hΓ hΘ hU) (h Θ Γ hΘ hΓ hU.symm)
  intro Γ Θ hΓ hΘ hU C hC
  have hCU : C ⊆ Θ.biUnion id := by
    rw [← hU]
    exact fun x hx => mem_biUnion.mpr ⟨C, hC, hx⟩
  obtain ⟨D, hD, hCD⟩ := hΘ.connected_subset_part (hΓ.1 C hC) hCU
  have hDU : D ⊆ Γ.biUnion id := by
    rw [hU]
    exact fun x hx => mem_biUnion.mpr ⟨D, hD, hx⟩
  obtain ⟨C', hC', hDC'⟩ := hΓ.connected_subset_part (hΘ.1 D hD) hDU
  have hCC' : C = C' := by
    by_contra hne
    obtain ⟨x⟩ := (hΓ.1 C hC).nonempty
    exact disjoint_left.mp (hΓ.2.1 hC hC' hne) x.2 (hDC' (hCD x.2))
  have : C = D := Subset.antisymm hCD (hCC' ▸ hDC')
  exact this ▸ hD

/-- All connected-component families in a finite graph. -/
def componentFamilies : Finset (Finset (Finset V)) := by
  classical
  exact univ.filter (IsComponentFamily G)

/-- Expanding a product and collecting the connected components of each subset. -/
theorem sum_componentFamilies {R : Type*} [CommSemiring R] (w : V → R) :
    ∑ Γ ∈ componentFamilies (G := G), ∏ C ∈ Γ, ∏ v ∈ C, w v =
      ∏ v, (1 + w v) := by
  classical
  rw [Finset.prod_one_add]
  apply Finset.sum_bij (fun Γ _ => Γ.biUnion id)
  · intro Γ hΓ
    simp
  · intro Γ hΓ Θ hΘ hU
    exact (mem_filter.mp hΓ).2.eq_of_biUnion_eq (mem_filter.mp hΘ).2 hU
  · intro A _
    exact ⟨componentFamily G A,
      mem_filter.mpr ⟨mem_univ _, isComponentFamily_componentFamily G A⟩,
      biUnion_componentFamily G A⟩
  · intro Γ hΓ
    exact (Finset.prod_biUnion (mem_filter.mp hΓ).2.2.1).symm

variable (G) in
/-- After removing a vertex from a connected induced graph, every remaining
component contains a neighbour of that vertex. -/
theorem componentFamily_erase_touches {C : Finset V} {p : V}
    (hC : (G.induce (C : Set V)).Connected) (hp : p ∈ C)
    {D : Finset V} (hD : D ∈ componentFamily G (C.erase p)) :
    ∃ q ∈ D, G.Adj p q := by
  have hΓ := isComponentFamily_componentFamily G (C.erase p)
  have hsub : D ⊆ C.erase p := by
    intro v hv
    rw [← biUnion_componentFamily G (C.erase p)]
    exact mem_biUnion.mpr ⟨D, hD, hv⟩
  by_contra h
  push Not at h
  have hstep : ∀ {u v : V}, u ∈ D → v ∈ C → G.Adj u v → v ∈ D := by
    intro u v hu hv huv
    have hvp : v ≠ p := by
      intro hvp
      subst v
      exact h u hu huv.symm
    apply hΓ.mem_of_adj hD hu
    · rw [biUnion_componentFamily]
      exact mem_erase.mpr ⟨hvp, hv⟩
    · exact huv
  obtain ⟨u⟩ := (hΓ.1 D hD).nonempty
  have huC : u.val ∈ C := mem_of_mem_erase (hsub u.property)
  obtain ⟨w⟩ := hC.preconnected ⟨u.val, huC⟩ ⟨p, hp⟩
  have hwalk : ∀ {x y : C}, (G.induce (C : Set V)).Walk x y →
      x.val ∈ D → y.val ∈ D := by
    intro x y w
    induction w with
    | nil => exact id
    | @cons x y z hxy w ih =>
      intro hx
      exact ih (hstep hx y.property hxy)
  exact (notMem_erase p C) (hsub (hwalk w u.property))


#print axioms isComponentFamily_componentFamily
#print axioms IsComponentFamily.eq_of_biUnion_eq
#print axioms sum_componentFamilies

end Mettapedia.Combinatorics.PolymerGas
