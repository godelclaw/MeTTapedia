import Mettapedia.GraphTheory.Kempe.IndependentLift

/-!
# Two hidden vertices have connected colouring fibres

Any two proper colourings agreeing outside two vertices are Kempe connected
without touching that exterior. The hidden vertices may be adjacent. Either
one can be recoloured first, or the two colours interchange in a component
contained in the hidden pair. This does not assert lifting of exterior moves.
-/

namespace SimpleGraph.KempeTwoVertexFibre

open Relation

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

private theorem cross_ne (u v : V) (C D : G.Coloring α)
    (agree : ∀ x, x ≠ u → x ≠ v → C x = D x) (safe : C v ≠ D u) :
    ReflTransGen (G.KempeStepAvoiding ({u, v} : Set V)ᶜ) C D := by
  classical
  let E : G.Coloring α := .mk (fun x => if x = u then D x else C x) (by
    intro x y hxy
    by_cases hx : x = u <;> by_cases hy : y = u
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · subst x
      by_cases hyv : y = v
      · subst y; simpa [hy] using safe.symm
      · simpa [hy, agree y hy hyv] using D.valid hxy
    · subst y
      by_cases hxv : x = v
      · subst x; simpa [hx] using safe
      · simpa [hx, agree x hx hxv] using D.valid hxy
    · simpa [hx, hy] using C.valid hxy)
  have applyE (x : V) : E x = if x = u then D x else C x := rfl
  have first : G.KempeStepAvoiding ({u, v} : Set V)ᶜ C E :=
    KempeIndependentLift.single_vertex u (fun x hx => by simp [applyE, hx]) _ (by simp)
  have last : G.KempeStepAvoiding ({u, v} : Set V)ᶜ E D :=
    KempeIndependentLift.single_vertex v (by
      intro x hx
      by_cases hxu : x = u
      · simp [applyE, hxu]
      · simpa [applyE, hxu] using agree x hxu hx) _ (by simp)
  exact (ReflTransGen.single first).tail last

/-- Connected fibres hold for an arbitrary palette and any two hidden vertices,
including an adjacent pair. No bounded-degree or state-table hypothesis occurs. -/
theorem fibre_path [Fintype V] (u v : V) (C D : G.Coloring α)
    (agree : ∀ x, x ≠ u → x ≠ v → C x = D x) :
    ReflTransGen (G.KempeStepAvoiding ({u, v} : Set V)ᶜ) C D := by
  classical
  by_cases safe : C v ≠ D u
  · exact cross_ne u v C D agree safe
  by_cases safe' : C u ≠ D v
  · simpa only [Set.pair_comm v u] using
      cross_ne v u C D (fun x hxv hxu => agree x hxu hxv) safe'
  have first : C v = D u := not_not.mp safe
  have last : C u = D v := not_not.mp safe'
  apply C.avoiding_of_pointwise_swap D (C u) (C v) ({u, v} : Set V)ᶜ
  · intro x hx
    have hn : x ≠ u ∧ x ≠ v := by simpa using hx
    exact agree x hn.1 hn.2
  · intro x
    by_cases hxu : x = u
    · subst x; exact Or.inr (by simpa using first.symm)
    by_cases hxv : x = v
    · subst x; exact Or.inr (by simpa using last.symm)
    · exact Or.inl (agree x hxu hxv).symm

end SimpleGraph.KempeTwoVertexFibre
