import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicOrientedEdgeArmTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelLocalDarts

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
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

/-- The selected cross edge, oriented by the first route and lifted into
the ambient cubic graph. -/
def ambientFirstCrossDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) : G.Dart :=
  retainedDartToAmbientDart data
    (first.firstCrossDart second hab hbc site)

/-- The first route's outgoing arm at the selected cross edge, lifted to
the ambient graph. -/
def ambientFirstCrossExitDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) : G.Dart :=
  retainedDartToAmbientDart data
    (first.firstCrossExitDart second hab hbc site)

/-- The second route's outgoing arm at the selected cross edge, lifted to
the ambient graph. -/
def ambientSecondCrossExitDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) : G.Dart :=
  retainedDartToAmbientDart data
    (first.secondCrossExitDart second hac hbc site)

/-- The first ambient outgoing arm carries exactly the retained first
strict-tail edge. -/
@[simp] theorem toRotationSystem_edgeOf_ambientFirstCrossExitDart
    (graphData : Data G) (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    graphData.toRotationSystem.edgeOf
        (ambientFirstCrossExitDart data first second hab hbc site) =
      retainedEdgeToAmbientEdge data
        ((first.firstSuffixFromCrossSite second site).getVert 1) := by
  apply Subtype.ext
  simp [ambientFirstCrossExitDart]
  rfl

/-- The second ambient outgoing arm carries the retained second
strict-tail edge. -/
@[simp] theorem toRotationSystem_edgeOf_ambientSecondCrossExitDart
    (graphData : Data G) (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    graphData.toRotationSystem.edgeOf
        (ambientSecondCrossExitDart data first second hac hbc site) =
      retainedEdgeToAmbientEdge data
        ((first.secondSuffixFromCrossSite second site).getVert 1) := by
  apply Subtype.ext
  simp [ambientSecondCrossExitDart]
  rfl

/-- In the reversed endpoint-pairing branch, the remaining local facial
choice is the xor of the cyclic turns at the two ends of the cross edge. -/
def crossExitOppositeTransferBit
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
    (site : first.CrossSite second) : Bool :=
  graphData.toRotationSystem.oppositeArmTransferBit
    (ambientFirstCrossDart data first second hab hbc site)
    (ambientSecondCrossExitDart data first second hac hbc site)
    (ambientFirstCrossExitDart data first second hab hbc site)

/-- The complete local acceptance bit for joining the two outgoing arms
through a face avoiding their edges. Parallel endpoint pairing accepts
immediately; reversed pairing uses the two endpoint turns. -/
def crossExitFaceTransferBit
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
    (site : first.CrossSite second) : Bool :=
  Bool.or
    (first.crossPairingBit second hab hac hbc site)
    (crossExitOppositeTransferBit data graphData first second
      hab hac hbc site)

@[simp] theorem crossExitFaceTransferBit_eq_true_of_pairing_true
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
    (hpairing : first.crossPairingBit second hab hac hbc site = true) :
    crossExitFaceTransferBit data graphData first second
      hab hac hbc site = true := by
  rw [crossExitFaceTransferBit, hpairing]
  rfl

theorem crossExitFaceTransferBit_eq_opposite_of_pairing_false
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
    (hpairing : first.crossPairingBit second hab hac hbc site = false) :
    crossExitFaceTransferBit data graphData first second
        hab hac hbc site =
      crossExitOppositeTransferBit data graphData first second
        hab hac hbc site := by
  rw [crossExitFaceTransferBit, hpairing]
  rfl

/-- The rejected local state is exactly reversed endpoint pairing together
with equal cyclic turns at the two ends of the cross edge. -/
theorem crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
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
      first.crossPairingBit second hab hac hbc site = false ∧
        graphData.toRotationSystem.orientedEdgeArmTurn
            (ambientFirstCrossDart data first second hab hbc site)
            (ambientSecondCrossExitDart data first second hac hbc site) =
          graphData.toRotationSystem.orientedEdgeArmTurn
            (graphData.toRotationSystem.alpha
              (ambientFirstCrossDart data first second hab hbc site))
            (ambientFirstCrossExitDart data first second hab hbc site) := by
  simp [crossExitFaceTransferBit, crossExitOppositeTransferBit]

/-- If the local acceptance bit is true, exact-cut face labels on the two
outgoing cross arms agree whenever both arm edges avoid the cut. -/
theorem crossExitFaceLabels_eq_of_transferBit_eq_true
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
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (htransfer : crossExitFaceTransferBit data graphData first second
      hab hac hbc site = true)
    (hfirstNotCut : ¬cut (graphData.toRotationSystem.edgeOf
      (ambientFirstCrossExitDart data first second hab hbc site)))
    (hsecondNotCut : ¬cut (graphData.toRotationSystem.edgeOf
      (ambientSecondCrossExitDart data first second hac hbc site))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientFirstCrossExitDart data first second hab hbc site)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientSecondCrossExitDart data first second hac hbc site)) := by
  cases hpairing : first.crossPairingBit second hab hac hbc site with
  | true =>
      have hexits := (first.crossPairingBit_eq_true_iff
        second hab hac hbc site).1 hpairing
      apply graphData.toRotationSystem
        |>.labels_eq_of_distinct_dartsAt_of_edges_not_cut
          hcubic hrotation labels cut hexact
          (ambientFirstCrossExitDart data first second hab hbc site)
          (ambientSecondCrossExitDart data first second hac hbc site)
      · simpa only [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
          ambientFirstCrossExitDart, ambientSecondCrossExitDart,
          retainedDartToAmbientDart_fst] using
          congrArg Subtype.val hexits.symm
      · intro hdarts
        exact first.firstCrossExitDart_ne_secondCrossExitDart
          second hab hac hbc site
          (retainedDartToAmbientDart_injective data hdarts)
      · exact hfirstNotCut
      · exact hsecondNotCut
  | false =>
      have hopposite : crossExitOppositeTransferBit data graphData
          first second hab hac hbc site = true := by
        simpa only [crossExitFaceTransferBit, hpairing,
          Bool.false_or] using htransfer
      have hreversed :=
        first.secondCrossDart_eq_firstCrossDart_symm_of_pairing_false
          second hab hac hbc site hpairing
      have hentryBaseRetained :
          (first.secondCrossExitDart second hac hbc site).fst =
            (first.firstCrossDart second hab hbc site).fst := by
        calc
          (first.secondCrossExitDart second hac hbc site).fst =
              (first.secondCrossDart second hac hbc site).snd := rfl
          _ = ((first.firstCrossDart second hab hbc site).symm).snd :=
            congrArg (fun dart ↦ dart.snd) hreversed
          _ = (first.firstCrossDart second hab hbc site).fst := rfl
      have hlabels := graphData.toRotationSystem
        |>.labels_eq_of_oppositeArms_of_transferBit_eq_true
          hcubic hrotation labels cut hexact
          (ambientFirstCrossDart data first second hab hbc site)
          (ambientSecondCrossExitDart data first second hac hbc site)
          (ambientFirstCrossExitDart data first second hab hbc site)
          (by
            simpa only [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
              ambientFirstCrossDart, ambientSecondCrossExitDart,
              retainedDartToAmbientDart_fst] using
              congrArg Subtype.val hentryBaseRetained)
          (by
            simp only [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
              SimpleGraphDartRotation.Data.toRotationSystem_alpha,
              ambientFirstCrossDart, ambientFirstCrossExitDart,
              retainedDartToAmbientDart_fst]
            exact congrArg Subtype.val
              (first.firstCrossDart_snd second hab hbc site).symm)
          (by
            intro hdarts
            exact first.firstCrossDart_ne_secondCrossExitDart
              second hab hac hbc site
              (retainedDartToAmbientDart_injective data hdarts))
          (by
            intro hdarts
            apply first.firstCrossDart_symm_ne_firstCrossExitDart
              second hab hbc site
            apply retainedDartToAmbientDart_injective data
            change
              (retainedDartToAmbientDart data
                (first.firstCrossDart second hab hbc site)).symm =
              retainedDartToAmbientDart data
                (first.firstCrossExitDart second hab hbc site) at hdarts
            simpa only [ambientFirstCrossDart,
              ambientFirstCrossExitDart,
              SimpleGraphDartRotation.Data.toRotationSystem_alpha,
              retainedDartToAmbientDart_symm] using hdarts)
          hopposite hsecondNotCut hfirstNotCut
      exact hlabels.symm

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
