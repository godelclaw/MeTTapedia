import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelTransferObstruction
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTransferMonodromy
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceNetwork

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A cross edge carries the same three finite coordinates as a fusion edge:
route orientation followed by one cyclic arm turn at each endpoint. -/
def crossFaceSymbol
    (data : AdjacentPairData G) (graphData : Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) : FusionFaceSymbol where
  chirality := first.crossPairingBit second hab hac hbc site
  entryTurn := graphData.toRotationSystem.orientedEdgeArmTurn
    (ambientFirstCrossDart data first second hab hbc site)
    (ambientSecondCrossExitDart data first second hac hbc site)
  exitTurn := graphData.toRotationSystem.orientedEdgeArmTurn
    (graphData.toRotationSystem.alpha
      (ambientFirstCrossDart data first second hab hbc site))
    (ambientFirstCrossExitDart data first second hab hbc site)

@[simp] theorem crossFaceSymbol_chirality
    (data : AdjacentPairData G) (graphData : Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (crossFaceSymbol data graphData first second hab hac hbc site).chirality =
      first.crossPairingBit second hab hac hbc site :=
  rfl

@[simp] theorem crossFaceSymbol_entryTurn
    (data : AdjacentPairData G) (graphData : Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (crossFaceSymbol data graphData first second hab hac hbc site).entryTurn =
      graphData.toRotationSystem.orientedEdgeArmTurn
        (ambientFirstCrossDart data first second hab hbc site)
        (ambientSecondCrossExitDart data first second hac hbc site) :=
  rfl

@[simp] theorem crossFaceSymbol_exitTurn
    (data : AdjacentPairData G) (graphData : Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (crossFaceSymbol data graphData first second hab hac hbc site).exitTurn =
      graphData.toRotationSystem.orientedEdgeArmTurn
        (graphData.toRotationSystem.alpha
          (ambientFirstCrossDart data first second hab hbc site))
        (ambientFirstCrossExitDart data first second hab hbc site) :=
  rfl

/-- Rejection is exactly the negative-orientation, positive-twist symbol.
Thus the cross alphabet is literally the established fusion alphabet, not
merely an equinumerous encoding. -/
theorem crossExitFaceTransferBit_eq_false_iff_crossFaceSymbol_negative_twist
    (data : AdjacentPairData G) (graphData : Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    crossExitFaceTransferBit data graphData first second
        hab hac hbc site = false ↔
      (crossFaceSymbol data graphData first second
          hab hac hbc site).chirality = false ∧
        (crossFaceSymbol data graphData first second
          hab hac hbc site).twist = true := by
  rw [crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
    data graphData first second hab hac hbc site]
  simp only [crossFaceSymbol_chirality, FusionFaceSymbol.twist_eq_true_iff,
    crossFaceSymbol_entryTurn, crossFaceSymbol_exitTurn]

/-- A rejected cross symbol flips the signed endpoint coordinate and swaps
the two route labels. -/
theorem crossFaceSymbol_signedRouteTransfer_of_rejected
    (data : AdjacentPairData G) (graphData : Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second)
    (hfalse : crossExitFaceTransferBit data graphData first second
      hab hac hbc site = false)
    (endpoint route : Bool) :
    (fusionEndpointTransport
        (crossFaceSymbol data graphData first second
          hab hac hbc site).chirality endpoint,
      (crossFaceSymbol data graphData first second
        hab hac hbc site).routeTransfer route) =
      (!endpoint, !route) := by
  have hstate :=
    (crossExitFaceTransferBit_eq_false_iff_crossFaceSymbol_negative_twist
      data graphData first second hab hac hbc site).1 hfalse
  have hswap :
      (crossFaceSymbol data graphData first second
        hab hac hbc site).routeTransfer = Equiv.swap false true :=
    (FusionFaceSymbol.routeTransfer_eq_swap_iff _).2
      ((FusionFaceSymbol.twist_eq_true_iff _).1 hstate.2)
  rw [hstate.1, fusionEndpointTransport_false, hswap]
  cases route <;> rfl

/-- The canonical indexed face crossing has the same diagonal flip on a
rejected one-site cross symbol. -/
theorem indexedFusionFaceCrossing_crossFaceSymbol_of_rejected
    (data : AdjacentPairData G) (graphData : Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second)
    (hfalse : crossExitFaceTransferBit data graphData first second
      hab hac hbc site = false)
    (endpoint route : Bool) :
    indexedFusionFaceCrossing
        (fun _ : Unit ↦ crossFaceSymbol data graphData first second
          hab hac hbc site)
        (((), endpoint), route) =
      (((), !endpoint), !route) := by
  rw [indexedFusionFaceCrossing_apply]
  have hstate :=
    (crossExitFaceTransferBit_eq_false_iff_crossFaceSymbol_negative_twist
      data graphData first second hab hac hbc site).1 hfalse
  have hswap :
      (crossFaceSymbol data graphData first second
        hab hac hbc site).routeTransfer = Equiv.swap false true :=
    (FusionFaceSymbol.routeTransfer_eq_swap_iff _).2
      ((FusionFaceSymbol.twist_eq_true_iff _).1 hstate.2)
  rw [hswap]
  cases route <;> rfl

/-- The `bc` cross channel read in the common face-symbol alphabet. -/
def EvenKempeFusionLens.bcCrossFaceSymbol
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (graphData : Data G)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute) : FusionFaceSymbol :=
  crossFaceSymbol data graphData lens01.bRoute lens23.cRoute
    hab hac hbc site

/-- The complementary cross channel in the same alphabet. -/
def EvenKempeFusionLens.cbCrossFaceSymbol
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (graphData : Data G)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute) : FusionFaceSymbol :=
  crossFaceSymbol data graphData lens01.cRoute lens23.bRoute
    hac hab hbc.symm site

/-- A rejected `bc` bit is the negative transposition in the common symbol
alphabet. -/
theorem EvenKempeFusionLens.bcCrossFaceSymbol_negative_twist_of_rejected
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    (EvenKempeFusionLens.bcCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).chirality = false ∧
      (EvenKempeFusionLens.bcCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).twist = true ∧
      (EvenKempeFusionLens.bcCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).routeTransfer = Equiv.swap false true := by
  have hstate :=
    (crossExitFaceTransferBit_eq_false_iff_crossFaceSymbol_negative_twist
      data graphData lens01.bRoute lens23.cRoute hab hac hbc site).1
      (by simpa only [EvenKempeFusionLens.bcCrossExitFaceTransferBit] using
        hfalse)
  refine ⟨hstate.1, hstate.2, ?_⟩
  exact (FusionFaceSymbol.routeTransfer_eq_swap_iff _).2
    ((FusionFaceSymbol.twist_eq_true_iff _).1 hstate.2)

/-- The `cb` rejected bit has the same negative-transposition state. -/
theorem EvenKempeFusionLens.cbCrossFaceSymbol_negative_twist_of_rejected
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    (EvenKempeFusionLens.cbCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).chirality = false ∧
      (EvenKempeFusionLens.cbCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).twist = true ∧
      (EvenKempeFusionLens.cbCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).routeTransfer = Equiv.swap false true := by
  have hstate :=
    (crossExitFaceTransferBit_eq_false_iff_crossFaceSymbol_negative_twist
      data graphData lens01.cRoute lens23.bRoute hac hab hbc.symm site).1
      (by simpa only [EvenKempeFusionLens.cbCrossExitFaceTransferBit] using
        hfalse)
  refine ⟨hstate.1, hstate.2, ?_⟩
  exact (FusionFaceSymbol.routeTransfer_eq_swap_iff _).2
    ((FusionFaceSymbol.twist_eq_true_iff _).1 hstate.2)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
