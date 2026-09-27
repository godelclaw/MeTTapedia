import Mettapedia.GraphTheory.FourColor.EdgeColouringGluing

/-!
# Exact witness compatibility for a matching closure

When the new edges have disjoint endpoint sets, an old colouring extends
exactly when every new edge has a colour absent at all its endpoints.
The theorem constructs the enlarged witness on the original edge IDs.
-/

namespace Mettapedia.GraphTheory.FourColor.MatchingEdgeClosure

open GoertzelV24ForkInterfaceSupport EdgeColouringGluing

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable {inc : E → Finset V} {A B : Finset E}

omit [DecidableEq E] in
/-- Every new edge of an extension avoids the old profile at its endpoints. -/
theorem fresh_colour_avoids (a d : E → Fin 3)
    (hd : Proper inc B d) (hAB : A ⊆ B) (hagrees : ∀ x ∈ A, d x = a x)
    {x : E} (hx : x ∈ B) (hfresh : x ∉ A) {v : V} (hvx : v ∈ inc x) :
    d x ∉ profile inc A a v := by
  intro h
  obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp h
  obtain ⟨hyA, hvy⟩ := Finset.mem_filter.mp hy
  have hxy : x ≠ y := by rintro rfl; exact hfresh hyA
  exact hd x hx y (hAB hyA) hxy ⟨v, Finset.mem_inter.mpr ⟨hvx, hvy⟩⟩
    ((hagrees y hyA).trans hya).symm

/-- A matching of new edges has no constraints between its own witnesses;
all constraints are exactly the endpoint profiles of the original piece. -/
theorem extension_iff (hAB : Disjoint A B)
    (hmatching : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → Disjoint (inc x) (inc y))
    (a : E → Fin 3) (ha : Proper inc A a) :
    (∃ d : E → Fin 3, Proper inc (A ∪ B) d ∧ ∀ x ∈ A, d x = a x) ↔
      ∀ x ∈ B, ∃ q : Fin 3, ∀ v ∈ inc x, q ∉ profile inc A a v := by
  classical
  constructor
  · rintro ⟨d, hd, hda⟩ x hx
    refine ⟨d x, fun v hv => ?_⟩
    exact fresh_colour_avoids a d hd (Finset.subset_union_left) hda
      (Finset.mem_union_right _ hx) (Finset.disjoint_right.mp hAB hx) hv
  · intro h
    let b : E → Fin 3 := fun x => if hx : x ∈ B then Classical.choose (h x hx) else 0
    have hb (x : E) (hx : x ∈ B) (v : V) (hv : v ∈ inc x) :
        b x ∉ profile inc A a v := by
      dsimp only [b]
      rw [dite_eq_left hx]
      exact Classical.choose_spec (h x hx) v hv
    refine ⟨glue A a b, (glue_proper_iff inc A B hAB a b).mpr ⟨ha, ?_, ?_⟩,
      fun _ hx => glue_left A a b hx⟩
    · intro x hx y hy hxy hmeet
      exact (Finset.not_nonempty_empty
        (Finset.disjoint_iff_inter_eq_empty.mp (hmatching x hx y hy hxy) ▸ hmeet)).elim
    · apply (compatible_iff inc A B a b).mpr
      intro x hx y hy hmeet heq
      obtain ⟨v, hv⟩ := hmeet
      have hm : a x ∈ profile inc A a v :=
        Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, (Finset.mem_inter.mp hv).1⟩, rfl⟩
      exact hb y hy v (Finset.mem_inter.mp hv).2 (heq ▸ hm)

omit [DecidableEq E] in
/-- Distinct unique endpoint requests block any extension containing the edge. -/
theorem no_extension_of_distinct_requests {x : E} {u v : V}
    (hx : x ∈ B) (hfresh : x ∉ A) (hAB : A ⊆ B)
    (hu : u ∈ inc x) (hv : v ∈ inc x) (a : E → Fin 3) (r s : Fin 3) (hne : r ≠ s)
    (hr : ∀ q, q ∉ profile inc A a u ↔ q = r)
    (hs : ∀ q, q ∉ profile inc A a v ↔ q = s) :
    ¬ ∃ d : E → Fin 3, Proper inc B d ∧ ∀ e ∈ A, d e = a e := by
  rintro ⟨d, hd, hda⟩
  exact hne (((hr _).mp (fresh_colour_avoids a d hd hAB hda hx hfresh hu)).symm.trans
    ((hs _).mp (fresh_colour_avoids a d hd hAB hda hx hfresh hv)))

end Mettapedia.GraphTheory.FourColor.MatchingEdgeClosure
