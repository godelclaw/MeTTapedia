import Mettapedia.GraphTheory.Kempe.PairHistory

/-!
# Projecting a fixed-pair phase through bichromatic edge routes

An observed edge need not remain an edge in a refined graph. A path using
its two original endpoint colours suffices to preserve properness after
any phase using one fixed colour pair. The paths are hypotheses about the
initial colouring; they need not survive a change of pair. Consequently
this theorem does not project arbitrary mixed-pair histories.
-/

namespace SimpleGraph.KempeRouteProjection

variable {V W α : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  [DecidableEq α]

theorem changed_along_walk (C D : H.Coloring α) (a b : α)
    (pair : ∀ x, D x = C x ∨ D x = Equiv.swap a b (C x))
    {u v : W} (p : H.Walk u v)
    (active : ∀ x ∈ p.support, C x = a ∨ C x = b)
    (changed : D u ≠ C u) : D v ≠ C v := by
  induction p with
  | nil => exact changed
  | @cons u w v edge p ih =>
      have tailActive : ∀ x ∈ p.support, C x = a ∨ C x = b :=
        fun x hx => active x (by simp only [Walk.support_cons, List.mem_cons]; exact Or.inr hx)
      exact ih tailActive
        (C.changed_neighbour_of_pointwise_swap D a b pair changed edge
          (tailActive w p.start_mem_support))

/-- An initially bichromatic route keeps its endpoint colours distinct
through any proper partial transposition of the whole colouring. -/
theorem routed_endpoints_ne (C D : H.Coloring α) (a b : α)
    (pair : ∀ x, D x = C x ∨ D x = Equiv.swap a b (C x))
    {u v : W} (different : C u ≠ C v) (p : H.Walk u v)
    (route : ∀ x ∈ p.support, C x = C u ∨ C x = C v) : D u ≠ D v := by
  intro equal
  have oneSide {u v : W} (different : C u ≠ C v) (p : H.Walk u v)
      (route : ∀ x ∈ p.support, C x = C u ∨ C x = C v)
      (fixed : D u = C u) (swapped : D v = Equiv.swap a b (C v))
      (equal : D u = D v) : False := by
    have changed : D v ≠ C v := fun h => different (fixed.symm.trans (equal.trans h))
    have va : C v = a ∨ C v = b :=
      Equiv.eq_or_eq_of_swap_apply_ne_self (fun h => changed (swapped.trans h))
    have us : C u = Equiv.swap a b (C v) := fixed.symm.trans (equal.trans swapped)
    have ua : C u = a ∨ C u = b := by
      rcases va with va | va
      · exact Or.inr (by simpa only [va, Equiv.swap_apply_left] using us)
      · exact Or.inl (by simpa only [va, Equiv.swap_apply_right] using us)
    have active : ∀ x ∈ p.reverse.support, C x = a ∨ C x = b := by
      intro x hx
      have hx' : x ∈ p.support := by simpa using hx
      rcases route x hx' with h | h
      · simpa only [h] using ua
      · simpa only [h] using va
    exact changed_along_walk C D a b pair p.reverse active changed fixed
  rcases pair u with hu | hu <;> rcases pair v with hv | hv
  · exact different (hu.symm.trans (equal.trans hv))
  · exact oneSide different p route hu hv equal
  · exact oneSide different.symm p.reverse
      (fun x hx => (route x (by simpa using hx)).symm) hv hu equal.symm
  · exact different ((Equiv.swap a b).injective (hu.symm.trans (equal.trans hv)))

/-- A phase in the refined graph restricts to a proper partial
transposition on the observed graph, using the same original routes. -/
theorem project_phase (f : V → W) (C : G.Coloring α) (D E : H.Coloring α)
    (initial : ∀ v, D (f v) = C v)
    (routes : ∀ u v, G.Adj u v → ∃ p : H.Walk (f u) (f v),
      ∀ x ∈ p.support, D x = C u ∨ D x = C v)
    {a b : α} (history : Relation.ReflTransGen (KempePairHistory.Step a b) D E) :
    ∃ F : G.Coloring α, (∀ v, F v = E (f v)) ∧
      ∀ v, F v = C v ∨ F v = Equiv.swap a b (C v) := by
  have pair := KempePairHistory.pointwise history
  have proper : ∀ u v, G.Adj u v → E (f u) ≠ E (f v) := by
    intro u v edge
    obtain ⟨p, hp⟩ := routes u v edge
    apply routed_endpoints_ne D E a b pair
      (by simpa only [initial] using C.valid edge) p
    simpa only [initial] using hp
  refine ⟨.mk (fun v => E (f v)) (fun h => proper _ _ h), fun _ => rfl, ?_⟩
  intro v
  change E (f v) = C v ∨ E (f v) = Equiv.swap a b (C v)
  simpa only [initial] using pair (f v)

end SimpleGraph.KempeRouteProjection
