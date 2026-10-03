import Mettapedia.GraphTheory.Kempe.IndependentLift

/-!
# Kempe histories across a clique attachment

A proper partial transposition acts on a clique either as the identity or
as the full transposition. Consequently a hidden patch attached only along
a retained clique can follow every retained pair move by applying that
same permutation throughout the patch. No hypothesis on its interior or
on connectivity of its colouring fibres is needed. The initial full
colouring is retained, and later hidden colourings are constructed from it.
-/

namespace SimpleGraph.KempeCliqueLift

open Relation Mettapedia.Combinatorics.Reconfiguration KempeIndependentLift

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- On a clique, proper partial transpositions cannot make independent
choices at two active vertices. -/
theorem uniform_on_clique (C D : G.Coloring α) (a b : α) (N : Set V)
    (clique : G.IsClique N)
    (pair : ∀ x, D x = C x ∨ D x = Equiv.swap a b (C x)) :
    (∀ x ∈ N, D x = C x) ∨ (∀ x ∈ N, D x = Equiv.swap a b (C x)) := by
  classical
  by_cases fixed : ∀ x ∈ N, D x = C x
  · exact Or.inl fixed
  · obtain ⟨u, hu⟩ := not_forall.mp fixed
    obtain ⟨hu, changed⟩ := not_imp.mp hu
    right
    intro v hv
    by_cases active : C v = a ∨ C v = b
    · have hc : D v ≠ C v := by
        by_cases h : u = v
        · simpa [h] using changed
        · exact C.changed_neighbour_of_pointwise_swap D a b pair changed
            (clique hu hv h) active
      exact (pair v).resolve_left hc
    · have hn := not_or.mp active
      simpa [Equiv.swap_apply_of_ne_of_ne hn.1 hn.2] using pair v

/-- Every retained pair move lifts from the specified full colouring.
The hidden vertices may form an arbitrary graph of arbitrary finite size. -/
theorem lift_pair [Fintype V] [DecidableEq V]
    (S : Finset V) (N B : Set V) (clique : G.IsClique N)
    (_retained : N ⊆ (↑S)ᶜ) (boundary_retained : B ⊆ (↑S)ᶜ)
    (attachment : ∀ x ∈ S, ∀ y, y ∉ S → G.Adj x y → y ∈ N)
    (C : G.Coloring α) (D : (G.induce (↑S)ᶜ).Coloring α)
    (step : PairStep (G.induce (↑S)ᶜ) (Subtype.val ⁻¹' B) (C.restrictInduce (↑S)ᶜ) D) :
    ∃ E : G.Coloring α, E.restrictInduce (↑S)ᶜ = D ∧
      ReflTransGen (G.KempeStepAvoiding B) C E := by
  classical
  obtain ⟨⟨a, b, pair⟩, fixed⟩ := step
  have nc : (G.induce (↑S)ᶜ).IsClique (Subtype.val ⁻¹' N) := by
    intro x hx y hy hxy
    exact clique hx hy (fun h => hxy (Subtype.ext h))
  obtain ⟨σ, choice, onN⟩ : ∃ σ : Equiv.Perm α,
      (σ = Equiv.refl α ∨ σ = Equiv.swap a b) ∧
        ∀ x : ↥((↑S : Set V)ᶜ), x.val ∈ N → D x = σ (C x) := by
    rcases uniform_on_clique (C.restrictInduce (↑S)ᶜ) D a b _ nc pair with h | h
    · exact ⟨Equiv.refl α, Or.inl rfl, h⟩
    · exact ⟨Equiv.swap a b, Or.inr rfl, h⟩
  let E : G.Coloring α := .mk
    (fun x => if hx : x ∈ S then σ (C x) else D ⟨x, hx⟩) (by
      intro x y hxy
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
      · simpa [hx, hy] using σ.injective.ne (C.valid hxy)
      · simpa [hx, hy, onN ⟨y, hy⟩ (attachment x hx y hy hxy)] using
          σ.injective.ne (C.valid hxy)
      · simpa [hx, hy, onN ⟨x, hx⟩ (attachment y hy x hx hxy.symm)] using
          σ.injective.ne (C.valid hxy)
      · simpa [hx, hy] using D.valid
          (show (G.induce (↑S)ᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy))
  have applyE (x : V) : E x = if hx : x ∈ S then σ (C x) else D ⟨x, hx⟩ := rfl
  refine ⟨E, ?_, C.avoiding_of_pointwise_swap E a b B ?_ ?_⟩
  · apply DFunLike.ext
    intro x
    have hx : x.val ∉ S := x.property
    simp [Coloring.restrictInduce_apply, applyE, hx]
  · intro x hx
    have hn : x ∉ S := boundary_retained hx
    simpa [applyE, hn] using fixed ⟨x, hn⟩ hx
  · intro x
    by_cases hx : x ∈ S
    · rcases choice with h | h <;> simp [applyE, hx, h]
    · simpa [applyE, hx] using pair ⟨x, hx⟩

/-- The existing path-lifting interface composes these patch operations.
It does not assert that arbitrary hidden endpoint colourings are reachable. -/
theorem lifts_steps [Fintype V] [DecidableEq V]
    (S : Finset V) (N B : Set V) (clique : G.IsClique N)
    (retained : N ⊆ (↑S)ᶜ) (boundary_retained : B ⊆ (↑S)ᶜ)
    (attachment : ∀ x ∈ S, ∀ y, y ∉ S → G.Adj x y → y ∈ N) :
    LiftsSteps (G.KempeStepAvoiding (α := α) B)
      (PairStep (G.induce (↑S)ᶜ) (Subtype.val ⁻¹' B))
      (fun C : G.Coloring α => C.restrictInduce (↑S)ᶜ) :=
  lift_pair S N B clique retained boundary_retained attachment

/-- Exact reachability of retained targets, from every specified full start.
This transports successful repairs through the clique filling without
requiring a selected hidden endpoint to lie in the same Kempe class. -/
theorem history_iff [Fintype V] [DecidableEq V]
    (S : Finset V) (N B : Set V) (clique : G.IsClique N)
    (retained : N ⊆ (↑S)ᶜ) (boundary_retained : B ⊆ (↑S)ᶜ)
    (attachment : ∀ x ∈ S, ∀ y, y ∉ S → G.Adj x y → y ∈ N)
    (C : G.Coloring α) (D : (G.induce (↑S)ᶜ).Coloring α) :
    ReflTransGen (PairStep (G.induce (↑S)ᶜ) (Subtype.val ⁻¹' B))
      (C.restrictInduce (↑S)ᶜ) D ↔
      ∃ E : G.Coloring α, E.restrictInduce (↑S)ᶜ = D ∧
        ReflTransGen (G.KempeStepAvoiding B) C E := by
  constructor
  · exact (lifts_steps S N B clique retained boundary_retained attachment).lift
  · rintro ⟨E, rfl, h⟩
    exact ReflTransGen.mono (fun _ _ step => step.1) _ _
      ((projects_pair_steps S B).reach h)

end SimpleGraph.KempeCliqueLift
