import Mettapedia.GraphTheory.Coloring
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkInterfaceSupport

/-!
# Physical component switches in incidence-profile semantics

The vertices of the incidence graph are original edge identifiers. Two
retained edges are adjacent exactly when they meet. This lets the existing
Kempe-component operation act on the same witnesses as the support fork.
At each original vertex its profile is either unchanged or transformed by
the selected colour transposition, according to literal component contact.
-/

namespace Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch

open GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [DecidableEq V]
variable (inc : E → Finset V) (S : Finset E)

/-- The line graph of the retained incidence data, with unused edges isolated. -/
def graph : _root_.SimpleGraph E where
  Adj x y := x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ (inc x ∩ inc y).Nonempty
  symm := ⟨by
    rintro x y ⟨hne, hx, hy, hm⟩
    exact ⟨hne.symm, hy, hx, by rwa [Finset.inter_comm]⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

instance graphDecidableRel [DecidableEq E] : DecidableRel (graph inc S).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ (inc x ∩ inc y).Nonempty))

/-- A proper incidence assignment is a colouring of this literal line graph. -/
def colouring (a : E → Fin 3) (ha : Proper inc S a) : (graph inc S).Coloring (Fin 3) :=
  _root_.SimpleGraph.Coloring.mk a (by
    rintro x y ⟨hne, hx, hy, hm⟩
    exact ha x hx y hy hne hm)

theorem colouring_apply (a : E → Fin 3) (ha : Proper inc S a) (x : E) :
    colouring inc S a ha x = a x := rfl

theorem proper (C : (graph inc S).Coloring (Fin 3)) : Proper inc S C := by
  intro x hx y hy hne hm
  exact C.valid ⟨hne, hx, hy, hm⟩

variable {inc S}
variable (C : (graph inc S).Coloring (Fin 3)) (r s : Fin 3)
variable (K : (C.bicoloredSubgraph r s).ConnectedComponent)

/-- Contact with an original vertex uses a retained edge of the actual component. -/
def Touches (v : V) : Prop :=
  ∃ x ∈ S, v ∈ inc x ∧ x ∈ C.kempeComponentSet r s K

/-- All active retained edges at one vertex belong to the same component. -/
theorem mem_component_of_touches {v : V} (hv : Touches C r s K v)
    {x : E} (hx : x ∈ S) (hvx : v ∈ inc x)
    (hactive : C x = r ∨ C x = s) : x ∈ C.kempeComponentSet r s K := by
  obtain ⟨y, hy, hvy, hyK⟩ := hv
  by_cases heq : y = x
  · exact heq ▸ hyK
  · exact C.mem_kempeComponentSet_of_adj hyK
      ⟨heq, hy, hx, v, Finset.mem_inter.mpr ⟨hvy, hvx⟩⟩ hactive

/-- The switch is a single colour permutation at every touched vertex,
including on its inactive-colour edges. -/
theorem switch_at_vertex {v : V} {x : E} (hx : x ∈ S) (hvx : v ∈ inc x) :
    C.swapOnKempeComponent r s K x =
      if Touches C r s K v then Equiv.swap r s (C x) else C x := by
  by_cases hv : Touches C r s K v
  · rw [ite_eq_left hv]
    by_cases hactive : C x = r ∨ C x = s
    · exact C.swapOnKempeComponent_apply_of_mem
        (mem_component_of_touches C r s K hv hx hvx hactive)
    · rw [C.swapOnKempeComponent_apply_of_not_mem
        (fun h => hactive (C.mem_bicoloredSet_of_mem_kempeComponentSet h))]
      exact (Equiv.swap_apply_of_ne_of_ne
        (fun h => hactive (Or.inl h)) (fun h => hactive (Or.inr h))).symm
  · rw [ite_eq_right hv]
    exact C.swapOnKempeComponent_apply_of_not_mem (fun h => hv ⟨x, hx, hvx, h⟩)

/-- This is exactly the existing proper component switch, interpreted on
the original edge incidence; properness is not a certificate assumption. -/
theorem switch_proper : Proper inc S (C.swapOnKempeComponent r s K) :=
  proper inc S _

/-- Exact boundary-profile transport under one physical component switch. -/
theorem profile_switch (v : V) :
    profile inc S (C.swapOnKempeComponent r s K) v =
      if Touches C r s K v then (profile inc S C v).image (Equiv.swap r s)
      else profile inc S C v := by
  by_cases hv : Touches C r s K v
  · rw [ite_eq_left hv]
    unfold profile
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    obtain ⟨hxS, hvx⟩ := Finset.mem_filter.mp hx
    change C.swapOnKempeComponent r s K x = Equiv.swap r s (C x)
    simpa only [hv, ite_true] using switch_at_vertex C r s K hxS hvx
  · rw [ite_eq_right hv]
    apply Finset.image_congr
    intro x hx
    obtain ⟨hxS, hvx⟩ := Finset.mem_filter.mp hx
    simpa only [hv, ite_false] using switch_at_vertex C r s K hxS hvx

/-- A unique missing colour is swapped exactly at the vertices touched by
the actual component. This does not assert that a separating component exists. -/
theorem missing_switch {v : V} {m : Fin 3}
    (hm : ∀ q, q ∉ profile inc S C v ↔ q = m) (q : Fin 3) :
    q ∉ profile inc S (C.swapOnKempeComponent r s K) v ↔
      q = if Touches C r s K v then Equiv.swap r s m else m := by
  rw [profile_switch C r s K v]
  by_cases hv : Touches C r s K v
  · simp only [hv, ite_true, Finset.mem_image, Equiv.swap_apply_eq_iff,
      exists_eq_right, hm, Equiv.swap_apply_eq_iff]
  · simpa only [hv, ite_false] using hm q

omit K in
/-- A missing colour and a distinct second colour supply a real component
at the vertex. Only separation from another vertex remains undecided. -/
theorem exists_component_touches_of_missing {v : V}
    (hm : ∀ q, q ∉ profile inc S C v ↔ q = r) (hne : r ≠ s) :
    ∃ K : (C.bicoloredSubgraph r s).ConnectedComponent, Touches C r s K v := by
  have hs : s ∈ profile inc S C v := by
    by_contra hh
    exact hne ((hm s).mp hh).symm
  obtain ⟨x, hx, hxs⟩ := Finset.mem_image.mp hs
  have hactive : x ∈ C.bicoloredSet r s := Or.inr hxs
  exact ⟨_, x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2,
    C.mem_kempeComponentSet_self hactive⟩

omit K in
/-- Every edge along such a walk is retained, including a walk of length zero. -/
theorem walk_retained {x y : C.bicoloredSet r s}
    (p : (C.bicoloredSubgraph r s).Walk x y) (hx : x.val ∈ S) :
    ∀ z ∈ p.support, z.val ∈ S := by
  induction p with
  | nil => simpa using hx
  | @cons x y z hxy p ih =>
      intro t ht
      rcases List.mem_cons.mp ht with ht | ht
      · exact ht ▸ hx
      · exact ih hxy.2.2.1 t ht

/-- Contact at both ends gives an actual two-colour walk through old edges,
rather than merely an abstract boundary pairing. -/
theorem exists_walk_of_touches {u v : V}
    (hu : Touches C r s K u) (hv : Touches C r s K v) :
    ∃ x y : C.bicoloredSet r s,
      u ∈ inc x.val ∧ v ∈ inc y.val ∧
        ∃ p : (C.bicoloredSubgraph r s).Walk x y, ∀ z ∈ p.support, z.val ∈ S := by
  obtain ⟨x, hx, hux, hxc, hxK⟩ := hu
  obtain ⟨y, hy, hvy, hyc, hyK⟩ := hv
  have hreach := _root_.SimpleGraph.ConnectedComponent.exact (hxK.trans hyK.symm)
  obtain ⟨p⟩ := hreach
  exact ⟨⟨x, hxc⟩, ⟨y, hyc⟩, hux, hvy, p, walk_retained C r s p hx⟩

omit K in
/-- An active edge with no active neighbour is its entire physical component. -/
theorem component_singleton {x : E} (hx : x ∈ C.bicoloredSet r s)
    (hiso : ∀ y, (graph inc S).Adj x y → ¬ (C y = r ∨ C y = s)) (y : E) :
    y ∈ C.kempeComponentSet r s ((C.bicoloredSubgraph r s).connectedComponentMk ⟨x, hx⟩) ↔
      y = x := by
  constructor
  · rintro ⟨hy, hcomp⟩
    by_contra hne
    have he : (C.bicoloredSubgraph r s).neighborSet ⟨x, hx⟩ = ∅ := by
      ext z
      exact ⟨fun hz => (hiso z.val hz z.property).elim, fun hz => hz.elim⟩
    have hneq : (⟨y, hy⟩ : C.bicoloredSet r s) ≠ ⟨x, hx⟩ :=
      fun h => hne (congrArg Subtype.val h)
    exact _root_.SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hneq he
      (_root_.SimpleGraph.ConnectedComponent.exact hcomp)
  · rintro rfl
    exact C.mem_kempeComponentSet_self hx

omit K in
/-- A computable singleton-component certificate gives the literal pointwise switch. -/
theorem switch_singleton_apply [DecidableEq E] {x : E} (hx : x ∈ C.bicoloredSet r s)
    (hiso : ∀ y, (graph inc S).Adj x y → ¬ (C y = r ∨ C y = s)) (y : E) :
    C.swapOnKempeComponent r s ((C.bicoloredSubgraph r s).connectedComponentMk ⟨x, hx⟩) y =
      if y = x then Equiv.swap r s (C y) else C y := by
  by_cases hy : y = x
  · rw [ite_eq_left hy]
    exact C.swapOnKempeComponent_apply_of_mem ((component_singleton C r s hx hiso y).mpr hy)
  · rw [ite_eq_right hy]
    exact C.swapOnKempeComponent_apply_of_not_mem
      (fun h => hy ((component_singleton C r s hx hiso y).mp h))

end
end Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
