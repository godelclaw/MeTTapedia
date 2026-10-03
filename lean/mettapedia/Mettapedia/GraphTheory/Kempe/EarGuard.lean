import Mettapedia.GraphTheory.Kempe.ForestGuard

/-!
# Exact two-port elimination at a triangular ear

Removing a vertex whose two neighbours are adjacent adds a joint relation
on that existing edge. The relation requires one common colour for the
removed vertex, including both directions of each incident constraint.
Independent port marginals do not express this common-witness requirement.

The theorem applies to arbitrary unary and binary constraints, so subsequent
ears can consume the relations introduced by previous eliminations.
It preserves satisfiability and reconstructs assignments; it is not by
itself a recolouring theorem or an ordinary smaller-map reduction.
-/

namespace SimpleGraph.BinaryConstraints

variable {V A : Type*} (G : SimpleGraph V) (L : V → A → Prop)
    (R : V → V → A → A → Prop)

/-- The ordered joining constraint remembers a common eliminated witness. -/
def EarRelation (v : V) (u w : ↥(({v} : Set V)ᶜ))
    (x y : ↥(({v} : Set V)ᶜ)) (a b : A) : Prop :=
  R x y a b ∧ (x = u → y = w → ∃ c, L v c ∧
    R v u c a ∧ R u v a c ∧ R v w c b ∧ R w v b c)

/-- Exact elimination of a degree-two vertex on a triangle. No bounds on the
remaining graph, colour lists or binary relations are needed. -/
theorem ear_iff (v : V) (u w : ↥(({v} : Set V)ᶜ))
    (vu : G.Adj v u) (vw : G.Adj v w) (uw : G.Adj u w)
    (neighbours : ∀ x, G.Adj v x → x = u.val ∨ x = w.val) :
    (∃ f, Valid G L R f) ↔ ∃ f : ↥(({v} : Set V)ᶜ) → A,
      Valid (G.induce ({v} : Set V)ᶜ) (fun x => L x)
        (EarRelation L R v u w) f := by
  classical
  constructor
  · rintro ⟨f, unary, binary⟩
    refine ⟨fun x => f x, fun x => unary x, fun x y hxy => ⟨binary x y hxy, ?_⟩⟩
    intro hx hy
    subst x
    subst y
    exact ⟨f v, unary v, binary v u vu, binary u v vu.symm,
      binary v w vw, binary w v vw.symm⟩
  · rintro ⟨f, unary, binary⟩
    obtain ⟨c, hc, hcu, huc, hcw, hwc⟩ := (binary u w uw).2 rfl rfl
    have incident (x : ↥(({v} : Set V)ᶜ)) (hx : G.Adj v x) :
        R v x c (f x) ∧ R x v (f x) c := by
      rcases neighbours x hx with h | h
      · have same : x = u := Subtype.ext h
        subst x; exact ⟨hcu, huc⟩
      · have same : x = w := Subtype.ext h
        subst x; exact ⟨hcw, hwc⟩
    let F (x : V) : A := if hx : x = v then c else f ⟨x, hx⟩
    refine ⟨F, ?_, ?_⟩
    · intro x
      by_cases hx : x = v
      · subst x; simpa [F] using hc
      · simpa [F, hx] using unary ⟨x, hx⟩
    · intro x y hxy
      by_cases hx : x = v <;> by_cases hy : y = v
      · exact (hxy.ne (hx.trans hy.symm)).elim
      · subst x; simpa [F, hy] using (incident ⟨y, hy⟩ hxy).1
      · subst y; simpa [F, hx] using (incident ⟨x, hx⟩ hxy.symm).2
      · simpa [F, hx, hy] using (binary ⟨x, hx⟩ ⟨y, hy⟩ hxy).1

/-- A minimal common-witness obstruction: both ports separately allow a
colour from `{a,b}`, but the pair `(a,b)` leaves no common interior colour. -/
theorem separate_ports_not_joint {a b : A} (different : a ≠ b) :
    (∃ c, (c = a ∨ c = b) ∧ c ≠ a) ∧
    (∃ c, (c = a ∨ c = b) ∧ c ≠ b) ∧
    ¬ ∃ c, (c = a ∨ c = b) ∧ c ≠ a ∧ c ≠ b := by
  refine ⟨⟨b, Or.inr rfl, different.symm⟩, ⟨a, Or.inl rfl, different⟩, ?_⟩
  rintro ⟨c, rfl | rfl, hca, hcb⟩
  · exact hca rfl
  · exact hcb rfl

end SimpleGraph.BinaryConstraints
