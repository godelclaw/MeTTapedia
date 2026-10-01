import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Reconstructing a graph colouring across a patch boundary

A patch map is injective on its interior and covers every ambient edge
incident with that interior. Its boundary may identify vertices. Agreement
with one actual exterior assignment retains precisely those shared choices.
The resulting colouring fixes the whole exterior, not only the named ports.
-/

namespace FourColor.PatchBoundaryGluing

variable {A V C : Type*} {P : SimpleGraph A} {G : SimpleGraph V}

/-- Compatible genuine patch and exterior colourings reconstruct a genuine
ambient colouring. The theorem does not assert existence of a compatible pair. -/
theorem reconstruct (f : P →g G) (interior : Set A)
    (injective : Set.InjOn f interior)
    (no_capture : ∀ a, a ∉ interior → f a ∉ f '' interior)
    (covers : ∀ i ∈ interior, ∀ v, G.Adj (f i) v →
      ∃ a, P.Adj i a ∧ f a = v)
    (inside : P.Coloring C) (outside : V → C)
    (outside_valid : ∀ {v w}, v ∉ f '' interior → w ∉ f '' interior →
      G.Adj v w → outside v ≠ outside w)
    (agree : ∀ a, a ∉ interior → inside a = outside (f a)) :
    ∃ k : G.Coloring C, (∀ a, k (f a) = inside a) ∧
      ∀ v, v ∉ f '' interior → k v = outside v := by
  classical
  let color (v : V) : C :=
    if h : v ∈ f '' interior then inside h.choose else outside v
  have at_interior (a : A) (ha : a ∈ interior) : color (f a) = inside a := by
    have h : f a ∈ f '' interior := ⟨a, ha, rfl⟩
    dsimp only [color]
    rw [dite_eq_left h]
    exact congrArg inside (injective h.choose_spec.1 ha h.choose_spec.2)
  have at_exterior (v : V) (hv : v ∉ f '' interior) : color v = outside v := by
    simp only [color, dite_eq_right hv]
  have at_patch (a : A) : color (f a) = inside a := by
    by_cases ha : a ∈ interior
    · exact at_interior a ha
    · exact (at_exterior (f a) (no_capture a ha)).trans (agree a ha).symm
  have valid {v w : V} (adj : G.Adj v w) : color v ≠ color w := by
    by_cases hv : v ∈ f '' interior
    · obtain ⟨i, hi, rfl⟩ := hv
      obtain ⟨a, ha, rfl⟩ := covers i hi w adj
      rw [at_patch, at_patch]
      exact inside.valid ha
    · by_cases hw : w ∈ f '' interior
      · obtain ⟨i, hi, rfl⟩ := hw
        obtain ⟨a, ha, rfl⟩ := covers i hi v adj.symm
        rw [at_patch, at_patch]
        exact (inside.valid ha).symm
      · rw [at_exterior v hv, at_exterior w hw]
        exact outside_valid hv hw adj
  exact ⟨SimpleGraph.Coloring.mk color valid, at_patch, at_exterior⟩

end FourColor.PatchBoundaryGluing
