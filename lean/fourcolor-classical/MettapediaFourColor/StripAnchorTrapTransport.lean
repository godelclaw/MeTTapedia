import MettapediaFourColor.StripAnchorTrapHistory

/-!
# The guarded anchor obstruction survives graph extensions

Restricting a proper colouring along a graph homomorphism preserves the
pointwise effect of a fixed-pair history. Consequently adding vertices or
edges cannot overcome the anchor trap while the same guard is enforced on
its retained ports. No finiteness, planarity or injectivity is assumed.
This concerns the specified policy, not unrestricted recolouring.
-/

namespace FourColor.StripAnchorTrapTransport

open SimpleGraph StripAnchoredExtension

variable {V : Type*} {G : SimpleGraph V} (ι : StripAnchorTrap.exterior →g G)

def restrict (C : G.Coloring Color) : StripAnchorTrap.exterior.Coloring Color :=
  .mk (fun v => C (ι v)) (fun edge => C.valid (ι.map_adj edge))

/-- A phase contains any finite number of switches of one chosen pair.
The guard observes the original ports, including their shared choices. -/
def Phase (C D : G.Coloring Color) : Prop :=
  ∃ a b : Color, Relation.ReflTransGen (KempePairHistory.Step a b) C D ∧
    StripAnchorTrap.Guard (restrict ι C) (restrict ι D)

theorem phase_stays {C D : G.Coloring Color}
    (initial : StripAnchorTrap.Orbit (restrict ι C)) (phase : Phase ι C D) :
    StripAnchorTrap.Orbit (restrict ι D) := by
  obtain ⟨a,b,history,guard⟩ := phase
  exact StripAnchorTrap.pointwise_stays initial a b
    (fun v => KempePairHistory.pointwise history (ι v)) guard

/-- The initial colouring may be any extension of the trap's palette orbit. -/
theorem history_stays {C D : G.Coloring Color}
    (initial : StripAnchorTrap.Orbit (restrict ι C))
    (history : Relation.ReflTransGen (Phase ι) C D) :
    StripAnchorTrap.Orbit (restrict ι D) := by
  induction history with
  | refl => exact initial
  | tail _ phase ih => exact phase_stays ι ih phase

theorem history_nonextension {C D : G.Coloring Color}
    (initial : StripAnchorTrap.Orbit (restrict ι C))
    (history : Relation.ReflTransGen (Phase ι) C D) :
    ¬ Full (StripAnchorTrap.read (restrict ι D)) :=
  (StripAnchorTrap.orbit_profile (history_stays ι initial history)).1

/-- No genuine source colouring can agree with the final retained ports. -/
theorem history_no_source {C D : G.Coloring Color}
    (initial : StripAnchorTrap.Orbit (restrict ι C))
    (history : Relation.ReflTransGen (Phase ι) C D) :
    ¬ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (ι (StripAnchorTrap.port i)) := by
  rintro ⟨k,hk⟩
  apply history_nonextension ι initial history
  apply (full_iff _).mpr
  exact ⟨_,StripResponseSummary.valid_of_colouring _ k hk⟩

end FourColor.StripAnchorTrapTransport
