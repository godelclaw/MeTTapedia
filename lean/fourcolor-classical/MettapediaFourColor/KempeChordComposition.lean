import MettapediaFourColor.KempeChordExchange

/-!
# Composition through the structural chord cover

Each possible answer carries a proved continuation. The actual exterior
selects its chord, and that continuation retains the same exterior predicate.
The construction has no bound on boundary length.
-/

namespace FourColor.KempeChordExchange

/-- A structural chord cover composes already proved continuations in the
same arbitrary exterior. No fixed-point or chromogram enumeration is used. -/
theorem coclosure_of_answers {P : List Color → Prop} (et : List Color) (anchor : ℕ)
    (ha : anchor ≤ et.length) (hh : ((et.rotate anchor).headD 0).hi = true)
    (repairs : ∀ t ∈ answers et anchor, KempeCoclosure P t) : KempeCoclosure P et := by
  intro outside hout hold
  obtain ⟨_, w, hw, hall⟩ := hout et hold
  obtain ⟨t, ht, hm⟩ := answer_exists et anchor w ha hh hw
  exact repairs t ht outside hout (hall t hm)

end FourColor.KempeChordExchange
