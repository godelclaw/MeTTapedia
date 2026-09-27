import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryView
import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalClosedCountBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleColorExtension
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# The serial boundary relation in a closed sewing context

The two displayed boundaries of a tangle form one ordered closed seam.
Reindexing that seam and removing an empty output boundary gives exactly
the support used by the existing physical closed-colouring bridge.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleClosedBoundary

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PhysicalClosedCountBridge GoertzelV24ClosedCountReplacement
open GoertzelV24TwoEdgeCutMinimality SerialTangleSmallCutTransfer
open GoertzelV24PortTangleColorExtension GoertzelV24CompositeSeamMultigraph

noncomputable section
universe u
variable {V W W' I J J' B L R : Type u}

/-- Delete the empty boundary and undo the seam relabelling. -/
def rightDartEquiv (m : B ≃ R) : J ⊕ (B ⊕ EmptyPort.{u}) ≃ J ⊕ R where
  toFun
    | .inl j => .inl j
    | .inr (.inl b) => .inr (m b)
    | .inr (.inr e) => PEmpty.elim e
  invFun
    | .inl j => .inl j
    | .inr r => .inr (.inl (m.symm r))
  left_inv := by rintro (j | (b | e)); rfl; simp; exact PEmpty.elim e
  right_inv := by rintro (j | r); rfl; simp

theorem rightDartEquiv_vert (T : OpenTangleData W J R) (m : B ≃ R)
    (d : J ⊕ (B ⊕ EmptyPort.{u})) :
    (rightClosedPortTangle T m).vert d = T.vertOf (rightDartEquiv m d) := by
  rcases d with j | (b | e)
  · rfl
  · rfl
  · exact PEmpty.elim e

theorem innerSupport_asOpen_iff (T : TwoSidedOpenTangleData W J L R)
    (m : B ≃ L ⊕ R) (word : B → Color) :
    word ∈ innerSupport (rightClosedPortTangle (asOpen T) m) ↔
      T.AcceptsBoundaryWords (fun l => word (m.symm (.inl l)))
        (fun r => word (m.symm (.inr r))) := by
  let e := rightDartEquiv (J := J) m
  have hv (d) : (rightClosedPortTangle (asOpen T) m).vert d = T.vertOf (e d) := by
    rw [rightDartEquiv_vert, asOpen_vertOf]
  constructor
  · rintro ⟨c⟩
    let f : T.Coloring := fun d => c.1.color (e.symm d)
    refine ⟨f, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro j
      exact c.1.invariant j
    · intro d d' hd hne
      apply c.2.1.2 (e.symm d) (e.symm d')
      · simpa only [hv, Equiv.apply_symm_apply] using hd
      · exact fun h => hne (e.symm.injective h)
    · intro d
      exact c.2.1.1 (e.symm d)
    · funext l
      exact congrFun c.2.2 (.inl (m.symm (.inl l)))
    · funext r
      exact congrFun c.2.2 (.inl (m.symm (.inr r)))
  · rintro ⟨f, hf, hl, hr⟩
    let c : Coloring (rightClosedPortTangle (asOpen T) m) :=
      { color := fun d => f (e d)
        invariant := fun j => hf.1 j }
    have hw (b : L ⊕ R) : f (.inr b) = word (m.symm b) := by
      rcases b with l | r
      · exact congrFun hl l
      · exact congrFun hr r
    refine ⟨⟨c, ⟨?_, ?_⟩, ?_⟩⟩
    · intro d
      exact hf.2.2 (e d)
    · intro d d' hd hne
      exact hf.2.1 (by simpa only [hv] using hd) (fun h => hne (e.injective h))
    · funext b
      rcases b with b | empty
      · change f (.inr (m b)) = word b
        rw [hw, Equiv.symm_apply_apply]
      · exact PEmpty.elim empty

theorem innerSupport_mono (old : TwoSidedOpenTangleData W J L R)
    (new : TwoSidedOpenTangleData W' J' L R)
    (hs : ∀ x y, old.AcceptsBoundaryWords x y → new.AcceptsBoundaryWords x y)
    (m : B ≃ L ⊕ R) :
    innerSupport (rightClosedPortTangle (asOpen old) m) ⊆
      innerSupport (rightClosedPortTangle (asOpen new) m) := by
  intro word hw
  exact (innerSupport_asOpen_iff new m word).mpr
    (hs _ _ ((innerSupport_asOpen_iff old m word).mp hw))

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype W'] [DecidableEq W'] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
  [Fintype B] [DecidableEq B] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- Equal two-sided support preserves colourability of the literal closed
map. The proof uses the existing physical colouring conversion and gluing. -/
theorem compose_colorable_iff (old : TwoSidedOpenTangleData W J L R)
    (new : TwoSidedOpenTangleData W' J' L R)
    (hs : ∀ x y, old.AcceptsBoundaryWords x y ↔ new.AcceptsBoundaryWords x y)
    (outside : OpenTangleData V I B) (m : B ≃ L ⊕ R) :
    RotationSystemTaitColorable (outside.composeRotationSystem (asOpen old) m) ↔
      RotationSystemTaitColorable (outside.composeRotationSystem (asOpen new) m) := by
  apply (closedColorable_iff_composeRotationSystem_taitColorable outside (asOpen old) m).symm.trans
  apply Iff.trans _ (closedColorable_iff_composeRotationSystem_taitColorable outside (asOpen new) m)
  apply closedColorable_iff_of_innerSupport_eq
  ext word
  rw [innerSupport_asOpen_iff, innerSupport_asOpen_iff]
  exact hs _ _

variable (old : TwoSidedOpenTangleData W J L R) (new : TwoSidedOpenTangleData W' J' L R)
  (hs : ∀ x y, old.AcceptsBoundaryWords x y → new.AcceptsBoundaryWords x y)
  (outside : OpenTangleData V I B) (m : B ≃ L ⊕ R)
  (c : (outside.composeRotationSystem (asOpen old) m).EdgeColoring Color)
  (hc : (outside.composeRotationSystem (asOpen old) m).IsTaitEdgeColoring c)

/-- Restrict the given physical colouring, replace only the inner witness,
and glue using the original complete exterior colouring. -/
def replaceClosedCol : Col (series (leftClosedPortTangle outside)
    (rightClosedPortTangle (asOpen new) m)) (Sum.elim PEmpty.elim PEmpty.elim) :=
  extendClosedColoring (leftClosedPortTangle outside)
    (rightClosedPortTangle (asOpen old) m) (rightClosedPortTangle (asOpen new) m)
    (innerSupport_mono old new hs m) (closedColOfPhysical outside (asOpen old) m c hc)

def replaceEdgeColoring : (outside.composeRotationSystem (asOpen new) m).EdgeColoring Color :=
  physicalEdgeColoring outside (asOpen new) m (replaceClosedCol old new hs outside m c hc)

theorem replaceEdgeColoring_isTait :
    (outside.composeRotationSystem (asOpen new) m).IsTaitEdgeColoring
      (replaceEdgeColoring old new hs outside m c hc) :=
  physicalEdgeColoring_isTait outside (asOpen new) m (replaceClosedCol old new hs outside m c hc)

/-- Pointwise preservation on actual edge orbits touching exterior darts,
including every edge sewn to an exterior port. -/
theorem replaceEdgeColoring_exterior (d : I ⊕ B) :
    replaceEdgeColoring old new hs outside m c hc
        ((compositeDarts outside (asOpen new) m).edgeOf (composeDartEquiv (.inl d))) =
      c ((compositeDarts outside (asOpen old) m).edgeOf (composeDartEquiv (.inl d))) := by
  change (compositeDarts outside (asOpen new) m).descendedEdgeColor
    (physicalDartColor outside (asOpen new) m (replaceClosedCol old new hs outside m c hc))
    ((compositeDarts outside (asOpen new) m).edgeOf (composeDartEquiv (.inl d))) = _
  rw [GoertzelV24RotationSpliceConstructor.RewiredDartSystem.descendedEdgeColor_edgeOf _ _
    (physicalDartColor_alpha outside (asOpen new) m (replaceClosedCol old new hs outside m c hc))]
  have h := extendClosedColoring_preserves_exterior (leftClosedPortTangle outside)
    (rightClosedPortTangle (asOpen old) m) (rightClosedPortTangle (asOpen new) m)
    (innerSupport_mono old new hs m) (closedColOfPhysical outside (asOpen old) m c hc)
  rcases d with i | b
  · exact congrArg (fun col => col.color (.inl i)) h
  · exact congrArg (fun col => col.color (.inr (.inr b))) h

end
end Mettapedia.GraphTheory.FourColor.OpenTangleClosedBoundary
