import Mettapedia.GraphTheory.FourColor.OpenTangleSmallCutReplacement

/-!
# Replacement in a connected exterior

An exterior cut out of a bridgeless sewing is boundary-essential: every
internal bridge has a port on both sides. Consequently any connected,
boundary-essential replacement preserves connectedness and bridge-freedom
when the exterior is connected and there are at least two seam edges.

The replacement may itself be a tree. No equality of the two interiors'
small-cut profiles is required. The connected-exterior hypothesis is explicit.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleConnectedReplacement

open GoertzelV24BoundaryEssentialGluing Multigraph

section Graph

variable {V W W' E F F' P : Type*}
  (H : Multigraph V E) (K : Multigraph W F) (pH : P → V) (pK : P → W)

/-- Without a reachable port, an ambient path avoiding an interior edge
cannot leave its side. -/
theorem stays_left (e : E) (u : V)
    (hno : ∀ p, ¬ H.ReachAvoiding e u (pH p))
    {x : V ⊕ W}
    (h : (glue H K pH pK).ReachAvoiding (.inl e) (.inl u) x) :
    ∃ v, x = .inl v ∧ H.ReachAvoiding e u v := by
  induction h with
  | refl => exact ⟨u, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨v, rfl, hv⟩ := ih
    obtain ⟨f, hf, he⟩ := hs
    rcases f with f | f | p
    · have hfe : f ≠ e := fun h => hf (congrArg Sum.inl h)
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨H.snd f, hb.symm,
          hv.tail ⟨f, hfe, .inl ⟨Sum.inl.inj ha, rfl⟩⟩⟩
      · exact ⟨H.fst f, ha.symm,
          hv.tail ⟨f, hfe, .inr ⟨rfl, Sum.inl.inj hb⟩⟩⟩
    · rcases he with ⟨ha, _⟩ | ⟨_, hb⟩
      · cases ha
      · cases hb
    · rcases he with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact (hno p ((Sum.inl.inj ha).symm ▸ hv)).elim
      · cases hb

/-- Both sides of every exterior bridge reach the seam. This follows from
the original whole graph's bridge-freedom, without assumptions on its interior. -/
theorem essential_left (hb : (glue H K pH pK).Bridgeless) :
    BoundaryEssential H pH := by
  classical
  intro e he
  have hp : (glue H K pH pK).ReachAvoiding (.inl e)
      (.inl (H.fst e)) (.inl (H.snd e)) := not_not.mp (hb (.inl e))
  constructor
  · by_contra! hno
    obtain ⟨v, hv, hr⟩ := stays_left H K pH pK e (H.fst e) hno hp
    exact he ((Sum.inl.inj hv).symm ▸ hr)
  · by_contra! hno
    obtain ⟨v, hv, hr⟩ := stays_left H K pH pK e (H.snd e) hno
      (reachAvoiding_symm hp)
    exact he (reachAvoiding_symm ((Sum.inl.inj hv).symm ▸ hr))

/-- A port at every vertex is a sufficient boundary-essentiality test,
even when every internal edge is a bridge. -/
theorem essential_of_surjective (hs : Function.Surjective pH) :
    BoundaryEssential H pH := by
  intro e _
  obtain ⟨p, hp⟩ := hs (H.fst e)
  obtain ⟨q, hq⟩ := hs (H.snd e)
  exact ⟨⟨p, hp.symm ▸ Relation.ReflTransGen.refl⟩,
    ⟨q, hq.symm ▸ Relation.ReflTransGen.refl⟩⟩

/-- One argument covers all connected boundary-essential replacements in
a connected exterior, with the original sewing certifying that exterior. -/
theorem replace (K' : Multigraph W' F') (pK' : P → W')
    (hH : H.Connected) (hK' : K'.Connected)
    (he : BoundaryEssential K' pK')
    (hb : (glue H K pH pK).Bridgeless) {p q : P} (hpq : p ≠ q) :
    (glue H K' pH pK').Connected ∧ (glue H K' pH pK').Bridgeless :=
  ⟨glue_connected hH hK' p,
    glue_bridgeless hH hK' (essential_left H K pH pK hb) he hpq⟩

end Graph

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge

section Tangle

variable {V W W' I J J' L R R' : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype W'] [DecidableEq W'] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype R'] [DecidableEq R']

/-- The graph argument applies to the literal rotation-system constructor,
retaining every seam edge and the entire fixed exterior. -/
theorem replacement_structural (outside : OpenTangleData V I L)
    (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
    (mo : L ≃ R) (mn : L ≃ R')
    (hout : (sideMultigraph outside).Connected)
    (hnew : (sideMultigraph new).Connected)
    (he : BoundaryEssential (sideMultigraph new) (new.boundaryVert ∘ mn))
    (h : (rotationPrimalGraph (outside.composeRotationSystem old mo)).Connected ∧
      EdgeBridgeFree (outside.composeRotationSystem old mo))
    {p q : L} (hpq : p ≠ q) :
    (rotationPrimalGraph (outside.composeRotationSystem new mn)).Connected ∧
      EdgeBridgeFree (outside.composeRotationSystem new mn) := by
  rw [OpenTangleSmallCutReplacement.composite_structural_iff] at h ⊢
  exact replace (sideMultigraph outside) (sideMultigraph old) outside.boundaryVert
    (old.boundaryVert ∘ mo) (sideMultigraph new) (new.boundaryVert ∘ mn)
    hout hnew he h.2 hpq

end Tangle
end Mettapedia.GraphTheory.FourColor.OpenTangleConnectedReplacement
