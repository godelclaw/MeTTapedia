import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTurns

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedHexCorridorTypes

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionFaceTurnGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance fusionFaceTurnRetainedVertexFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance fusionFaceTurnRetainedVertexDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- The dart selected by the entry-end turn away from the fusion edge. -/
def fusionEntryTurnDart (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  if fusionEntryTurn graphData data lens hab site = true then
    ambientBEntryNeighborDart data lens hab site
  else
    ambientCEntryCompanionDart data lens hab hac site

/-- The dart selected by the exit-end turn away from the fusion edge. -/
def fusionExitTurnDart (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  if fusionExitTurn graphData data lens hab site = true then
    ambientBExitNeighborDart data lens hab site
  else
    ambientCExitCompanionDart data lens hab hac site

/-- The entry turn dart is exactly the cyclic successor of the ambient
fusion dart. -/
theorem rho_ambientBFusionDart_eq_fusionEntryTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    graphData.toRotationSystem.rho
        (ambientBFusionDart data lens hab site) =
      fusionEntryTurnDart graphData data lens hab hac site := by
  by_cases hturn : fusionEntryTurn graphData data lens hab site = true
  · rw [fusionEntryTurnDart, if_pos hturn]
    exact (fusionEntryTurn_eq_true_iff
      graphData data lens hab site).1 hturn
  · have hfalse : fusionEntryTurn graphData data lens hab site = false :=
      Bool.eq_false_of_not_eq_true hturn
    rw [fusionEntryTurnDart, if_neg hturn]
    exact (fusionEntryTurn_eq_false_iff_companion
      graphData hcubic hrotation data lens hab hac hbc site).1 hfalse

/-- The exit turn dart is exactly the cyclic successor of the reversed
ambient fusion dart. -/
theorem rho_ambientBExitFusionDart_eq_fusionExitTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    graphData.toRotationSystem.rho
        (ambientBExitFusionDart data lens hab site) =
      fusionExitTurnDart graphData data lens hab hac site := by
  by_cases hturn : fusionExitTurn graphData data lens hab site = true
  · rw [fusionExitTurnDart, if_pos hturn]
    exact (fusionExitTurn_eq_true_iff
      graphData data lens hab site).1 hturn
  · have hfalse : fusionExitTurn graphData data lens hab site = false :=
      Bool.eq_false_of_not_eq_true hturn
    rw [fusionExitTurnDart, if_neg hturn]
    exact (fusionExitTurn_eq_false_iff_companion
      graphData hcubic hrotation data lens hab hac hbc site).1 hfalse

/-- On the entry side, the face permutation crosses the fusion edge and
then takes the entry turn. -/
theorem phi_alpha_ambientBFusionDart_eq_fusionEntryTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha
          (ambientBFusionDart data lens hab site)) =
      fusionEntryTurnDart graphData data lens hab hac site := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact rho_ambientBFusionDart_eq_fusionEntryTurnDart
    graphData hcubic hrotation data lens hab hac hbc site

/-- On the exit side, the face permutation crosses the fusion edge and
then takes the exit turn. -/
theorem phi_ambientBFusionDart_eq_fusionExitTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    graphData.toRotationSystem.phi
        (ambientBFusionDart data lens hab site) =
      fusionExitTurnDart graphData data lens hab hac site := by
  simpa only [RotationSystem.phi_apply,
    SimpleGraphDartRotation.Data.toRotationSystem_alpha,
    ambientBExitFusionDart_eq_symm] using
      rho_ambientBExitFusionDart_eq_fusionExitTurnDart
        graphData hcubic hrotation data lens hab hac hbc site

/-- In the positive-chirality state, the `c`-oriented fusion dart has
the same face successor as the `b`-oriented dart; in the negative state
its successor is the entry-side turn. -/
theorem phi_ambientCFusionDart_eq_chiralityTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    graphData.toRotationSystem.phi
        (ambientCFusionDart data lens hac site) =
      if lens.fusionChirality hab hac site = true then
        fusionExitTurnDart graphData data lens hab hac site
      else
        fusionEntryTurnDart graphData data lens hab hac site := by
  by_cases hchirality : lens.fusionChirality hab hac site = true
  · rw [if_pos hchirality,
      (fusionChirality_eq_true_iff_ambientCFusionDart_eq_ambientBFusionDart
        data lens hab hac site).1 hchirality]
    exact phi_ambientBFusionDart_eq_fusionExitTurnDart
      graphData hcubic hrotation data lens hab hac hbc site
  · have hfalse : lens.fusionChirality hab hac site = false :=
      Bool.eq_false_of_not_eq_true hchirality
    rw [if_neg hchirality,
      (fusionChirality_eq_false_iff_ambientCFusionDart_eq_alpha
        graphData data lens hab hac site).1 hfalse]
    exact phi_alpha_ambientBFusionDart_eq_fusionEntryTurnDart
      graphData hcubic hrotation data lens hab hac hbc site

/-- Reversing the `c`-oriented fusion dart exchanges the entry and exit
successors selected by chirality. -/
theorem phi_alpha_ambientCFusionDart_eq_chiralityTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha
          (ambientCFusionDart data lens hac site)) =
      if lens.fusionChirality hab hac site = true then
        fusionEntryTurnDart graphData data lens hab hac site
      else
        fusionExitTurnDart graphData data lens hab hac site := by
  by_cases hchirality : lens.fusionChirality hab hac site = true
  · rw [if_pos hchirality,
      (fusionChirality_eq_true_iff_ambientCFusionDart_eq_ambientBFusionDart
        data lens hab hac site).1 hchirality]
    exact phi_alpha_ambientBFusionDart_eq_fusionEntryTurnDart
      graphData hcubic hrotation data lens hab hac hbc site
  · have hfalse : lens.fusionChirality hab hac site = false :=
      Bool.eq_false_of_not_eq_true hchirality
    rw [if_neg hchirality,
      (fusionChirality_eq_false_iff_ambientCFusionDart_eq_alpha
        graphData data lens hab hac site).1 hfalse,
      graphData.toRotationSystem.alpha_involutive]
    exact phi_ambientBFusionDart_eq_fusionExitTurnDart
      graphData hcubic hrotation data lens hab hac hbc site

/-- Positive chirality preserves the exit/entry ordering of the two
face successors. -/
theorem fusionFaceTransitions_of_chirality_eq_true
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hchirality : lens.fusionChirality hab hac site = true) :
    graphData.toRotationSystem.phi
          (ambientCFusionDart data lens hac site) =
        fusionExitTurnDart graphData data lens hab hac site ∧
      graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha
            (ambientCFusionDart data lens hac site)) =
        fusionEntryTurnDart graphData data lens hab hac site := by
  constructor
  · simpa only [hchirality, if_true] using
      phi_ambientCFusionDart_eq_chiralityTurnDart
        graphData hcubic hrotation data lens hab hac hbc site
  · simpa only [hchirality, if_true] using
      phi_alpha_ambientCFusionDart_eq_chiralityTurnDart
        graphData hcubic hrotation data lens hab hac hbc site

/-- Negative chirality swaps the entry/exit ordering of the two face
successors. -/
theorem fusionFaceTransitions_of_chirality_eq_false
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hchirality : lens.fusionChirality hab hac site = false) :
    graphData.toRotationSystem.phi
          (ambientCFusionDart data lens hac site) =
        fusionEntryTurnDart graphData data lens hab hac site ∧
      graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha
            (ambientCFusionDart data lens hac site)) =
        fusionExitTurnDart graphData data lens hab hac site := by
  constructor
  · have htransition :=
      phi_ambientCFusionDart_eq_chiralityTurnDart
        graphData hcubic hrotation data lens hab hac hbc site
    rw [hchirality] at htransition
    simpa using htransition
  · have htransition :=
      phi_alpha_ambientCFusionDart_eq_chiralityTurnDart
        graphData hcubic hrotation data lens hab hac hbc site
    rw [hchirality] at htransition
    simpa using htransition

/-- The finite local state carried by a fusion edge in an embedded cubic
graph. -/
structure FusionFaceSymbol where
  chirality : Bool
  entryTurn : Bool
  exitTurn : Bool
deriving DecidableEq, Fintype

/-- There are exactly eight local fusion face symbols. -/
@[simp] theorem card_fusionFaceSymbol : Fintype.card FusionFaceSymbol = 8 := by
  decide

/-- Read the complete local face symbol at a fusion site. -/
def fusionFaceSymbol (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    FusionFaceSymbol where
  chirality := lens.fusionChirality hab hac site
  entryTurn := fusionEntryTurn graphData data lens hab site
  exitTurn := fusionExitTurn graphData data lens hab site

@[simp] theorem fusionFaceSymbol_chirality
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (fusionFaceSymbol graphData data lens hab hac site).chirality =
      lens.fusionChirality hab hac site :=
  rfl

@[simp] theorem fusionFaceSymbol_entryTurn
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (fusionFaceSymbol graphData data lens hab hac site).entryTurn =
      fusionEntryTurn graphData data lens hab site :=
  rfl

@[simp] theorem fusionFaceSymbol_exitTurn
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (fusionFaceSymbol graphData data lens hab hac site).exitTurn =
      fusionExitTurn graphData data lens hab site :=
  rfl

/-- Fusion face state read in `(a,b)` route order. -/
def bOrderedFusionFaceSymbol
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.bFusionSites.length) : FusionFaceSymbol :=
  fusionFaceSymbol graphData data lens hab hac
    (lens.bFusionSiteAt position)

/-- Fusion face state read in `(a,c)` route order. -/
def cOrderedFusionFaceSymbol
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.cFusionSites.length) : FusionFaceSymbol :=
  fusionFaceSymbol graphData data lens hab hac
    (lens.cFusionSiteAt position)

/-- The fusion-order equivalence preserves the complete local face
symbol, not merely its chirality coordinate. -/
theorem cOrderedFusionFaceSymbol_fusionOrderEquiv
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.bFusionSites.length) :
    cOrderedFusionFaceSymbol graphData data lens hab hac
        (lens.fusionOrderEquiv position) =
      bOrderedFusionFaceSymbol graphData data lens hab hac position := by
  simp only [cOrderedFusionFaceSymbol, bOrderedFusionFaceSymbol,
    lens.cFusionSiteAt_fusionOrderEquiv position]

/-- The finite word of face symbols in `(a,b)` route order. -/
def bFusionFaceWord
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : List FusionFaceSymbol :=
  List.ofFn (bOrderedFusionFaceSymbol graphData data lens hab hac)

/-- The same local states listed in `(a,c)` route order. -/
def cFusionFaceWord
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : List FusionFaceSymbol :=
  List.ofFn (cOrderedFusionFaceSymbol graphData data lens hab hac)

@[simp] theorem bFusionFaceWord_length
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    (bFusionFaceWord graphData data lens hab hac).length =
      lens.fusionSiteCount := by
  simp [bFusionFaceWord]

@[simp] theorem cFusionFaceWord_length
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    (cFusionFaceWord graphData data lens hab hac).length =
      lens.cFusionSites.length := by
  simp [cFusionFaceWord]

/-- The `c`-order face state transported to the common monodromy
carrier. -/
def cOrderedFusionFaceSymbolOnCount
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) : FusionFaceSymbol :=
  cOrderedFusionFaceSymbol graphData data lens hab hac
    (finCongr lens.fusionSites_length_eq position)

/-- Fusion monodromy preserves the complete eight-state face symbol
when its output is interpreted in the second route order. -/
theorem fusionMonodromy_preserves_faceSymbol
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    cOrderedFusionFaceSymbolOnCount graphData data lens hab hac
        (lens.fusionMonodromy position) =
      bOrderedFusionFaceSymbol graphData data lens hab hac position := by
  have hposition :
      finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy position) =
        lens.fusionOrderEquiv position := by
    apply Fin.ext
    rfl
  rw [cOrderedFusionFaceSymbolOnCount, hposition]
  exact cOrderedFusionFaceSymbol_fusionOrderEquiv
    graphData data lens hab hac position

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
