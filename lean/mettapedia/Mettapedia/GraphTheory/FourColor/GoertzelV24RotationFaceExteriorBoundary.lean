import Mettapedia.GraphTheory.FourColor.GoertzelV24DegreeTwoExteriorBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartGraph

/-!
# Exterior boundary of a regional face component

A regional face graph has degree at most two: from a dart, its only possible
neighbors are the face successor and predecessor.  Consequently, after a
finite interface is deleted, each connected strict-exterior component meets
that interface through at most two of its own darts.

This is the structural endpoint budget used by a rolling facial transfer.  It
does not enumerate a receipt carrier or depend on its chosen encoding.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationFaceExteriorBoundary

open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph

variable {V E Interface : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype Interface]

noncomputable section

/-- The regional graph of a face permutation has maximum degree two. -/
theorem faceRegionalDartGraph_neighborSet_ncard_le_two
    (RS : RotationSystem V E) (region : Finset E) (dart : RS.D) :
    ((faceRegionalDartGraph RS region).neighborSet dart).ncard ≤ 2 := by
  classical
  let direction :
      (faceRegionalDartGraph RS region).neighborSet dart → Bool :=
    fun neighbor => decide (neighbor.1 = RS.phi dart)
  have hpossible : ∀ neighbor :
      (faceRegionalDartGraph RS region).neighborSet dart,
      neighbor.1 = RS.phi dart ∨ neighbor.1 = RS.phi.symm dart := by
    intro neighbor
    rcases (faceRegionalDartGraph_adj RS region dart neighbor.1).1
        neighbor.2 with ⟨_hne, hstep, _hdartRegion, _hneighborRegion⟩
    rcases hstep with hforward | hbackward
    · exact Or.inl hforward
    · exact Or.inr (by
        calc
          neighbor.1 = RS.phi.symm (RS.phi neighbor.1) :=
            (RS.phi.symm_apply_apply neighbor.1).symm
          _ = RS.phi.symm dart :=
            congrArg RS.phi.symm hbackward.symm)
  have hinjective : Function.Injective direction := by
    intro first second heq
    apply Subtype.ext
    by_cases hfirst : first.1 = RS.phi dart
    · have hsecond : second.1 = RS.phi dart := by
        by_contra hsecond
        have hdirFirst : direction first = true := by
          change decide (first.1 = RS.phi dart) = true
          exact decide_eq_true hfirst
        have hdirSecond : direction second = false := by
          change decide (second.1 = RS.phi dart) = false
          exact decide_eq_false hsecond
        exact Bool.noConfusion
          (hdirFirst.symm.trans (heq.trans hdirSecond))
      exact hfirst.trans hsecond.symm
    · have hsecond : second.1 ≠ RS.phi dart := by
        intro hsecond
        have hdirFirst : direction first = false := by
          change decide (first.1 = RS.phi dart) = false
          exact decide_eq_false hfirst
        have hdirSecond : direction second = true := by
          change decide (second.1 = RS.phi dart) = true
          exact decide_eq_true hsecond
        exact Bool.noConfusion
          (hdirFirst.symm.trans (heq.trans hdirSecond))
      exact (hpossible first).resolve_left hfirst |>.trans
        ((hpossible second).resolve_left hsecond).symm
  have hcard := Fintype.card_le_of_injective direction hinjective
  calc
    ((faceRegionalDartGraph RS region).neighborSet dart).ncard =
        Fintype.card
          ((faceRegionalDartGraph RS region).neighborSet dart) :=
      (Set.fintypeCard_eq_ncard _).symm
    _ ≤ Fintype.card Bool := hcard
    _ = 2 := by decide

/-- One connected strict-exterior component of a regional face graph has at
most two exterior darts adjacent to the represented interface. -/
theorem card_faceRegionalExteriorComponentBoundaryVertices_le_two
    (RS : RotationSystem V E) (region : Finset E)
    (interfaceVertex : Interface → RS.D)
    (component :
      (exteriorGraph (faceRegionalDartGraph RS region) interfaceVertex
        ).ConnectedComponent)
    {root : RS.D} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface interfaceVertex root) :
    (exteriorComponentBoundaryVertices (faceRegionalDartGraph RS region)
      interfaceVertex component).card ≤ 2 := by
  classical
  exact card_exteriorComponentBoundaryVertices_le_two
    (faceRegionalDartGraph RS region) interfaceVertex component hroot
      hrootOutside
      (faceRegionalDartGraph_neighborSet_ncard_le_two RS region)

end

end GoertzelV24RotationFaceExteriorBoundary

end Mettapedia.GraphTheory.FourColor
