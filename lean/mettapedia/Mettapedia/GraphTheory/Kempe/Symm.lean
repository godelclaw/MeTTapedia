import Mettapedia.GraphTheory.Kempe
import Mettapedia.GraphTheory.RelationExtras

/-!
# Kempe switches are reversible

A Kempe component depends only on the graph and the set of vertices carrying
one of its two colours.  Switching a component leaves that set unchanged, so
the switched colouring has a component with the same vertex set, and switching
it restores the original colouring.  Hence the Kempe step relation is
symmetric and Kempe closures are equivalence classes.

These facts were previously available only inside a four-colour module; they
are stated here on the generic colouring layer.
-/

namespace SimpleGraph

namespace Coloring

variable {V α : Type*} {G : SimpleGraph V}

/-- Reachability inside an induced subgraph depends only on the vertex set. -/
theorem induce_reachable_congr {S T : Set V} (hST : S = T) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (hu' : u ∈ T) (hv' : v ∈ T) :
    (G.induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩ ↔ (G.induce T).Reachable ⟨u, hu'⟩ ⟨v, hv'⟩ := by
  subst hST
  rfl

/-- Membership in the Kempe component of a vertex is reachability from it
inside the two-coloured vertex set. -/
theorem mem_kempeComponentSet_mk_iff (C : G.Coloring α) {a b : α} {u v : V}
    (hv : v ∈ C.bicoloredSet a b) :
    u ∈ C.kempeComponentSet a b ((C.bicoloredSubgraph a b).connectedComponentMk ⟨v, hv⟩) ↔
      ∃ hu : u ∈ C.bicoloredSet a b,
        (C.bicoloredSubgraph a b).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  constructor
  · rintro ⟨hu, hK⟩
    exact ⟨hu, ConnectedComponent.exact hK⟩
  · rintro ⟨hu, hreach⟩
    exact ⟨hu, ConnectedComponent.sound hreach⟩

/-- **Closure criterion.**  A set containing `v` and closed under adjacency to
two-coloured vertices contains the Kempe component of `v`. -/
theorem kempeComponentSet_subset_of_closed (C : G.Coloring α) {a b : α} {v : V}
    (hv : v ∈ C.bicoloredSet a b) {T : Set V} (hvT : v ∈ T)
    (hclosed : ∀ u w, u ∈ T → G.Adj u w → w ∈ C.bicoloredSet a b → w ∈ T) :
    C.kempeComponentSet a b ((C.bicoloredSubgraph a b).connectedComponentMk ⟨v, hv⟩) ⊆ T := by
  intro u hu
  obtain ⟨hu', hreach⟩ := (C.mem_kempeComponentSet_mk_iff hv).1 hu
  obtain ⟨p⟩ := hreach.symm
  suffices ∀ (x y : C.bicoloredSet a b), (C.bicoloredSubgraph a b).Walk x y →
      x.1 ∈ T → y.1 ∈ T from this _ _ p hvT
  intro x y q
  induction q with
  | nil => exact id
  | cons hadj _ ih => exact fun hx => ih (hclosed _ _ hx hadj (Subtype.prop _))

/-- Every Kempe component is the component of each of its vertices. -/
theorem exists_eq_mk_of_kempeComponent (C : G.Coloring α) {a b : α}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    ∃ v, ∃ hv : v ∈ C.bicoloredSet a b,
      K = (C.bicoloredSubgraph a b).connectedComponentMk ⟨v, hv⟩ := by
  induction K using ConnectedComponent.ind with
  | h v => exact ⟨v.1, v.2, rfl⟩

/-- **Kempe components depend only on the two-coloured set.**  If two
colourings, with possibly different colour pairs, have the same two-coloured
vertex set, the component of a vertex has the same vertex set in both. -/
theorem kempeComponentSet_mk_eq_of_bicoloredSet_eq (C D : G.Coloring α) {a b a' b' : α}
    (hCD : C.bicoloredSet a b = D.bicoloredSet a' b') {v : V}
    (hv : v ∈ C.bicoloredSet a b) (hv' : v ∈ D.bicoloredSet a' b') :
    D.kempeComponentSet a' b' ((D.bicoloredSubgraph a' b').connectedComponentMk ⟨v, hv'⟩) =
      C.kempeComponentSet a b ((C.bicoloredSubgraph a b).connectedComponentMk ⟨v, hv⟩) := by
  ext u
  rw [D.mem_kempeComponentSet_mk_iff, C.mem_kempeComponentSet_mk_iff]
  constructor
  · rintro ⟨hu, hreach⟩
    exact ⟨hCD.symm ▸ hu, (induce_reachable_congr hCD _ _ _ _).2 hreach⟩
  · rintro ⟨hu, hreach⟩
    exact ⟨hCD ▸ hu, (induce_reachable_congr hCD _ _ _ _).1 hreach⟩

/-- Two colourings with the same `a`/`b`-coloured vertex set have the same Kempe
component vertex sets. -/
theorem exists_kempeComponentSet_eq_of_bicoloredSet_eq (C D : G.Coloring α) {a b : α}
    (hCD : C.bicoloredSet a b = D.bicoloredSet a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    ∃ L : (D.bicoloredSubgraph a b).ConnectedComponent,
      D.kempeComponentSet a b L = C.kempeComponentSet a b K := by
  obtain ⟨v, hv, rfl⟩ := C.exists_eq_mk_of_kempeComponent K
  exact ⟨_, kempeComponentSet_mk_eq_of_bicoloredSet_eq C D hCD hv (hCD ▸ hv)⟩

/-- The two-coloured set does not depend on the order of the two colours. -/
theorem bicoloredSet_comm (C : G.Coloring α) (a b : α) :
    C.bicoloredSet a b = C.bicoloredSet b a := by
  ext v
  exact Or.comm

variable [DecidableEq α]

/-- Switching two components with the same vertex set in succession, the second
in the switched colouring, restores the colouring. -/
theorem swapOnKempeComponent_swapOnKempeComponent_of_eq (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (L : ((C.swapOnKempeComponent a b K).bicoloredSubgraph a b).ConnectedComponent)
    (hL : (C.swapOnKempeComponent a b K).kempeComponentSet a b L = C.kempeComponentSet a b K) :
    (C.swapOnKempeComponent a b K).swapOnKempeComponent a b L = C := by
  ext v
  by_cases hv : v ∈ C.kempeComponentSet a b K
  · rw [swapOnKempeComponent_apply_of_mem _ (hL ▸ hv), swapOnKempeComponent_apply_of_mem _ hv]
    simp
  · rw [swapOnKempeComponent_apply_of_not_mem _ (hL ▸ hv),
      swapOnKempeComponent_apply_of_not_mem _ hv]

/-- **The inverse switch.**  After a Kempe switch there is a component of the new
colouring with the same vertex set, and switching it restores the original. -/
theorem exists_swapOnKempeComponent_inverse (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    ∃ L : ((C.swapOnKempeComponent a b K).bicoloredSubgraph a b).ConnectedComponent,
      (C.swapOnKempeComponent a b K).kempeComponentSet a b L = C.kempeComponentSet a b K ∧
        (C.swapOnKempeComponent a b K).swapOnKempeComponent a b L = C := by
  obtain ⟨L, hL⟩ := exists_kempeComponentSet_eq_of_bicoloredSet_eq C
    (C.swapOnKempeComponent a b K) (C.bicoloredSet_swapOnKempeComponent a b K).symm K
  exact ⟨L, hL, swapOnKempeComponent_swapOnKempeComponent_of_eq C a b K L hL⟩

end Coloring

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- **Kempe steps are symmetric.** -/
theorem KempeStep.symm {C C' : G.Coloring α} (h : G.KempeStep C C') : G.KempeStep C' C := by
  obtain ⟨a, b, K, rfl⟩ := h
  obtain ⟨L, -, hinv⟩ := C.exists_swapOnKempeComponent_inverse a b K
  exact ⟨a, b, L, hinv.symm⟩

theorem kempeStep_comm {C C' : G.Coloring α} : G.KempeStep C C' ↔ G.KempeStep C' C :=
  ⟨KempeStep.symm, KempeStep.symm⟩

/-- **Kempe reachability is symmetric.** -/
theorem mem_kempeClosure_comm {C₀ C : G.Coloring α} :
    C ∈ G.KempeClosure C₀ ↔ C₀ ∈ G.KempeClosure C :=
  ⟨fun h => Mettapedia.GraphTheory.ReflTransGen.reverse_of_symmetric
      (fun _ _ => KempeStep.symm) h,
    fun h => Mettapedia.GraphTheory.ReflTransGen.reverse_of_symmetric
      (fun _ _ => KempeStep.symm) h⟩

/-- **Kempe reachability is symmetric**, one direction. -/
theorem KempeClosure.mem_symm {C₀ C : G.Coloring α} (h : C ∈ G.KempeClosure C₀) :
    C₀ ∈ G.KempeClosure C :=
  mem_kempeClosure_comm.1 h

/-- Two colourings generate the same Kempe closure exactly when one reaches the
other. -/
theorem kempeClosure_eq_iff_mem {C₀ C : G.Coloring α} :
    G.KempeClosure C₀ = G.KempeClosure C ↔ C ∈ G.KempeClosure C₀ := by
  constructor
  · intro h
    rw [h]
    exact G.mem_kempeClosure_self C
  · intro h
    exact G.kempeClosure_eq_of_mem_of_mem h (mem_kempeClosure_comm.1 h)

end SimpleGraph
