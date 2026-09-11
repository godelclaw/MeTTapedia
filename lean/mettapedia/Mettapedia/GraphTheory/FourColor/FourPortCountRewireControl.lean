import Mettapedia.GraphTheory.FourColor.FourPortCountRewire
import Mettapedia.GraphTheory.FourColor.FourPortCompositeEndpoint
import Mettapedia.GraphTheory.FourColor.PhysicalContextLanguage

/-!
# A nonvacuous physical control for the Count reconnection

Reuse the two disjoint digons with one port at each vertex. The I closure
is uncolourable; the H closure is colourable. Both are literal serial
composites of cubic port tangles. The I closure has a bridge, so this is
not a least-counterexample specimen. It tests a generic rewrite law.
-/

namespace Mettapedia.GraphTheory.FourColor.FourPortCountRewireControl

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24ClosedCountReplacement GoertzelV24PortTangleCutParity
open GoertzelV24PhysicalClosedCountBridge PhysicalContextBits FourPortCountRewire

def outside := leftClosedPortTangle (localData .a)

theorem outside_cubic : IsCubic outside := by
  unfold IsCubic dartsAt outside
  decide +kernel

private theorem local_vert (d : D) :
    (ofOpenTangleData (localData .a)).vert d = vertex .a d := by cases d <;> rfl

theorem mem_outside_iff (w : SquareBoundaryWord) :
    w ∈ outerSupport outside ↔ ∃ x, Valid .a w x := by
  rw [outside, left_realizes]
  constructor
  · rintro ⟨⟨c, hc, hw⟩⟩
    let x : Fin 4 → Color := fun e => c.color (.inl (e, false))
    have he : c.color = colors w x := by
      funext d
      rcases d with ⟨e, b⟩ | p
      · cases b
        · rfl
        · exact c.invariant (e, false)
      · exact congrFun hw p
    refine ⟨x, ?_⟩
    simpa only [IsProper, Valid, he, local_vert] using hc
  · rintro ⟨x, hx⟩
    let c : Coloring (ofOpenTangleData (localData .a)) :=
      ⟨colors w x, by rintro ⟨e, b⟩; cases b <;> rfl⟩
    refine ⟨⟨c, ?_, rfl⟩⟩
    simpa only [IsProper, Valid, c, local_vert] using hx

private theorem unique_third : ∀ a b x y : Color,
    ProperColorTriple x a b → ProperColorTriple y a b → x = y := by decide

theorem original_not_colorable : ¬ ClosedColorable outside (cap false) := by
  rw [closedColorable_iff]
  rintro ⟨w, hw, hz⟩
  obtain ⟨x, hx⟩ := (mem_outside_iff w).1 hw
  obtain ⟨z, hz⟩ := (mem_innerSupport_cap_iff false w).1 hz
  have hv := (valid_a w x).1 hx
  have he := unique_third _ _ _ _ hv.1 hv.2.1
  exact hz.1.2.2.2.1 he

theorem flip_colorable : ClosedColorable outside (cap true) := by
  rw [closedColorable_iff]
  let w : SquareBoundaryWord := ![red, red, blue, blue]
  refine ⟨w, (mem_outside_iff w).2 ?_, (mem_innerSupport_cap_iff true w).2 ?_⟩
  · exact ⟨![blue, purple, red, purple], by decide⟩
  · exact ⟨purple, by decide⟩

/-- Both ends of the generic obstruction occur on an actual cubic exterior. -/
theorem nonvacuous_rewire_obstruction :
    IsCubic outside ∧ (∃ c : Coloring outside, IsProper c) ∧
      ¬ ClosedColorable outside (cap false) ∧ ClosedColorable outside (cap true) := by
  obtain ⟨c, hc, _⟩ := (closedColorable_cap_iff outside true).1 flip_colorable
  exact ⟨outside_cubic, ⟨c, hc⟩, original_not_colorable, flip_colorable⟩

/-- The endpoint hypotheses are inhabited, independently of the executable controls. -/
theorem nonvacuous_endpoint_obstruction :
    ∃ hne : ∃ c : Coloring outside, IsProper c,
      ∀ m : FourPortCompositeEndpoint.Pairing,
        Nonempty (Col (FourPortCompositeEndpoint.wireClosure outside m
          (FourPortCompositeEndpoint.ports_injective_of_zero outside outside_cubic
            hne original_not_colorable)) PEmpty.elim) := by
  obtain ⟨_, hne, _, _⟩ := nonvacuous_rewire_obstruction
  exact ⟨hne, fun m => FourPortCompositeEndpoint.every_wire_endpoint_colorable
    outside outside_cubic hne original_not_colorable m⟩

end Mettapedia.GraphTheory.FourColor.FourPortCountRewireControl
