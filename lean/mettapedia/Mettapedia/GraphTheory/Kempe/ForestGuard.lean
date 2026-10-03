import Mettapedia.GraphTheory.Kempe.ForestFibre

/-!
# Leaf elimination for joint transition guards

A hidden vertex's state is its old colour and a Boolean choice to apply the
common transposition. Both endpoints and every hidden edge are checked.
For four colours this is an eight-element alphabet, independently of the
forest's size. Removing a leaf sends a unary constraint to its sole remaining
neighbour, preserves all other edges, and reconstructs a genuine assignment.
-/

namespace SimpleGraph.BinaryConstraints

variable {V A : Type*} (G : SimpleGraph V) (L : V → A → Prop)
    (R : V → V → A → A → Prop)

/-- Joint unary and ordered binary constraints on one common assignment. -/
def Valid (f : V → A) : Prop :=
  (∀ x, L x (f x)) ∧ ∀ x y, G.Adj x y → R x y (f x) (f y)

/-- Removing a leaf adds only a unary condition at its remaining neighbour.
Both orientations are retained, so the binary relations need not be symmetric. -/
def LeafLists (v : V) (x : ↥(({v} : Set V)ᶜ)) (c : A) : Prop :=
  L x c ∧ (G.Adj v x → ∃ z, L v z ∧ R v x z c ∧ R x v c z)

/-- Exact elimination and reconstruction of a leaf, including the isolated
vertex case. This can be iterated on a forest without raising constraint arity. -/
theorem leaf_iff (v : V)
    (leaf : ∀ x y, G.Adj v x → G.Adj v y → x = y) :
    (∃ f, Valid G L R f) ↔ (∃ z, L v z) ∧
      ∃ f : ↥(({v} : Set V)ᶜ) → A,
        Valid (G.induce ({v} : Set V)ᶜ) (LeafLists G L R v)
          (fun x y => R x y) f := by
  classical
  constructor
  · rintro ⟨f, hL, hR⟩
    refine ⟨⟨f v, hL v⟩, fun x => f x, ?_, ?_⟩
    · exact fun x => ⟨hL x, fun hx => ⟨f v, hL v, hR v x hx, hR x v hx.symm⟩⟩
    · exact fun x y hxy => hR x y hxy
  · rintro ⟨⟨z, hz⟩, f, hL, hR⟩
    have choice : ∃ c, L v c ∧ ∀ x : ↥(({v} : Set V)ᶜ),
        G.Adj v x → R v x c (f x) ∧ R x v (f x) c := by
      by_cases edge : ∃ x : ↥(({v} : Set V)ᶜ), G.Adj v x
      · obtain ⟨x, hx⟩ := edge
        obtain ⟨c, hc, forward, backward⟩ := (hL x).2 hx
        refine ⟨c, hc, fun y hy => ?_⟩
        have same : y = x := Subtype.ext (leaf y x hy hx)
        subst y
        exact ⟨forward, backward⟩
      · exact ⟨z, hz, fun x hx => (edge ⟨x, hx⟩).elim⟩
    obtain ⟨c, hc, incident⟩ := choice
    let F (x : V) : A := if hx : x = v then c else f ⟨x, hx⟩
    refine ⟨F, ?_, ?_⟩
    · intro x
      by_cases hx : x = v
      · subst x; simpa [F] using hc
      · simpa [F, hx] using (hL ⟨x, hx⟩).1
    · intro x y hxy
      by_cases hx : x = v <;> by_cases hy : y = v
      · exact (hxy.ne (hx.trans hy.symm)).elim
      · subst x; simpa [F, hy] using (incident ⟨y, hy⟩ hxy).1
      · subst y; simpa [F, hx] using (incident ⟨x, hx⟩ hxy.symm).2
      · simpa [F, hx, hy] using hR ⟨x, hx⟩ ⟨y, hy⟩ hxy

end SimpleGraph.BinaryConstraints

namespace SimpleGraph.KempeForestGuard

open KempeGuardedLift BinaryConstraints

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- An old colour and a choice to perform the common transposition. -/
def after (a b : α) (s : α × Bool) : α :=
  if s.2 then Equiv.swap a b s.1 else s.1

/-- Both observations use the same retained before/after colourings. -/
def Allowed (S : Set V) (C D : (G.induce Sᶜ).Coloring α) (a b : α)
    (x : S) (s : α × Bool) : Prop :=
  ∀ y : ↥(Sᶜ), G.Adj x y → s.1 ≠ C y ∧ after a b s ≠ D y

/-- Every hidden edge must be proper at both ends of the transition. -/
def Compatible (a b : α) (s t : α × Bool) : Prop :=
  s.1 ≠ t.1 ∧ after a b s ≠ after a b t

/-- The finite local alphabet represents the exact joint guard, rather than
independent marginal extension possibilities. The bridge holds for any graph. -/
theorem transition_iff (S : Set V) (C D : (G.induce Sᶜ).Coloring α) (a b : α) :
    Transition S C D a b ↔ ∃ f : S → α × Bool,
      Valid (G.induce S) (Allowed S C D a b) (fun _ _ => Compatible a b) f := by
  classical
  constructor
  · rintro ⟨h, k, hf, kf, pair⟩
    let f (x : S) : α × Bool := (h x, decide (k x ≠ h x))
    have old (x : S) : (f x).1 = h x := rfl
    have new (x : S) : after a b (f x) = k x := by
      by_cases same : k x = h x
      · simp [after, f, same]
      · simpa [after, f, same] using ((pair x).resolve_left same).symm
    exact ⟨f, fun x y hxy => ⟨hf x y hxy, new x ▸ kf x y hxy⟩,
      fun x y hxy => ⟨h.valid hxy, by simpa only [new] using k.valid hxy⟩⟩
  · rintro ⟨f, unary, edges⟩
    let h : (G.induce S).Coloring α := .mk (fun x => (f x).1)
      (by intro x y hxy; exact (edges x y hxy).1)
    let k : (G.induce S).Coloring α := .mk (fun x => after a b (f x))
      (by intro x y hxy; exact (edges x y hxy).2)
    refine ⟨h, k, fun x y hxy => (unary x y hxy).1,
      fun x y hxy => (unary x y hxy).2, fun x => ?_⟩
    change after a b (f x) = (f x).1 ∨ after a b (f x) = Equiv.swap a b (f x).1
    cases bit : (f x).2 <;> simp [after, bit]

/-- One exact guard reduction, retaining a common assignment on the remaining
hidden vertices and a witness for reconstructing the removed leaf. -/
theorem peel_transition_iff (S : Set V) (C D : (G.induce Sᶜ).Coloring α) (a b : α)
    (v : S) (leaf : ∀ x y : S, G.Adj v x → G.Adj v y → x = y) :
    Transition S C D a b ↔
      (∃ z, Allowed S C D a b v z) ∧
      ∃ f : ↥(({v} : Set S)ᶜ) → α × Bool,
        Valid ((G.induce S).induce ({v} : Set S)ᶜ)
          (LeafLists (G.induce S) (Allowed S C D a b) (fun _ _ => Compatible a b) v)
          (fun _ _ => Compatible a b) f := by
  rw [transition_iff]
  exact leaf_iff _ _ _ v leaf

/-- Four colours require eight labelled states per hidden vertex, even for
forests of unbounded size. Some labels may represent the same colour pair. -/
theorem four_colour_alphabet : Fintype.card (Fin 4 × Bool) = 8 := by decide

end SimpleGraph.KempeForestGuard
