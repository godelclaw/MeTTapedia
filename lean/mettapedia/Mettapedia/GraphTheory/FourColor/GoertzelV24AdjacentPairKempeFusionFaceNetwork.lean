import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSignedMonodromy

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedHexCorridorTypes

/-- Two Boolean labels either agree or are complements. -/
theorem Bool.eq_or_eq_not (first second : Bool) :
    first = second ∨ first = !second := by
  cases first <;> cases second <;> simp

/-- Every two-state fusion-edge transfer is an involution. -/
@[simp] theorem GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol.routeTransfer_involutive
    (symbol : GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol)
    (route : Bool) :
    symbol.routeTransfer (symbol.routeTransfer route) = route := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;> cases route <;>
    simp [GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol.routeTransfer]

/-- Reindex one Boolean-labelled family by a permutation while leaving the
other family fixed.  Here `true` is the fixed `(a,b)` route and `false` is
the reindexed `(a,c)` route. -/
def routeLabelReindexing {α : Type*} (cReindexing : Equiv.Perm α) :
    Equiv.Perm (α × Bool) where
  toFun state :=
    if state.2 = true then state else (cReindexing state.1, false)
  invFun state :=
    if state.2 = true then state else (cReindexing.symm state.1, false)
  left_inv state := by
    rcases state with ⟨value, route⟩
    cases route <;> simp
  right_inv state := by
    rcases state with ⟨value, route⟩
    cases route <;> simp

@[simp] theorem routeLabelReindexing_apply_true {α : Type*}
    (cReindexing : Equiv.Perm α) (value : α) :
    routeLabelReindexing cReindexing (value, true) = (value, true) := by
  simp [routeLabelReindexing]

@[simp] theorem routeLabelReindexing_apply_false {α : Type*}
    (cReindexing : Equiv.Perm α) (value : α) :
    routeLabelReindexing cReindexing (value, false) =
      (cReindexing value, false) := by
  simp [routeLabelReindexing]

/-- The canonical local face crossing at a fusion edge.  It moves to the
opposite endpoint and applies that edge's two-route transfer. -/
def indexedFusionFaceCrossing {ι : Type*}
    (symbol : ι →
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol) :
    Equiv.Perm ((ι × Bool) × Bool) where
  toFun state :=
    ((state.1.1, !state.1.2),
      (symbol state.1.1).routeTransfer state.2)
  invFun state :=
    ((state.1.1, !state.1.2),
      (symbol state.1.1).routeTransfer state.2)
  left_inv state := by
    rcases state with ⟨⟨position, endpoint⟩, route⟩
    apply Prod.ext
    · apply Prod.ext <;> simp
    · simp
  right_inv state := by
    rcases state with ⟨⟨position, endpoint⟩, route⟩
    apply Prod.ext
    · apply Prod.ext <;> simp
    · simp

@[simp] theorem indexedFusionFaceCrossing_apply {ι : Type*}
    (symbol : ι →
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol)
    (position : ι) (endpoint route : Bool) :
    indexedFusionFaceCrossing symbol ((position, endpoint), route) =
      ((position, !endpoint), (symbol position).routeTransfer route) :=
  rfl

@[simp] theorem indexedFusionFaceCrossing_apply_fst_fst {ι : Type*}
    (symbol : ι →
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol)
    (state : (ι × Bool) × Bool) :
    (indexedFusionFaceCrossing symbol state).1.1 = state.1.1 :=
  rfl

@[simp] theorem indexedFusionFaceCrossing_apply_fst_snd {ι : Type*}
    (symbol : ι →
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol)
    (state : (ι × Bool) × Bool) :
    (indexedFusionFaceCrossing symbol state).1.2 = !state.1.2 :=
  rfl

@[simp] theorem indexedFusionFaceCrossing_apply_snd {ι : Type*}
    (symbol : ι →
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol)
    (state : (ι × Bool) × Bool) :
    (indexedFusionFaceCrossing symbol state).2 =
      (symbol state.1.1).routeTransfer state.2 :=
  rfl

/-- The canonical local crossing is itself an involution. -/
@[simp] theorem indexedFusionFaceCrossing_involutive {ι : Type*}
    (symbol : ι →
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.FusionFaceSymbol)
    (state : (ι × Bool) × Bool) :
    indexedFusionFaceCrossing symbol
        (indexedFusionFaceCrossing symbol state) = state :=
  (indexedFusionFaceCrossing symbol).left_inv state

/-- Conjugation preserves an involutive permutation. -/
theorem conjugatePermutation_involutive {α : Type*}
    (reindexing localPermutation : Equiv.Perm α)
    (hlocal : ∀ state : α,
      localPermutation (localPermutation state) = state)
    (state : α) :
    (reindexing.symm.trans (localPermutation.trans reindexing))
        ((reindexing.symm.trans
          (localPermutation.trans reindexing)) state) =
      state := by
  change reindexing
      (localPermutation (reindexing.symm
        (reindexing
          (localPermutation (reindexing.symm state))))) = state
  rw [reindexing.symm_apply_apply, hlocal,
    reindexing.apply_symm_apply]

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Reindex fusion arms from the common physical-site carrier into each
route's own order and orientation.  The `b` arms stay fixed; the `c` arms
are transported by signed fusion monodromy. -/
def EvenKempeFusionLens.fusionArmReindexing {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    Equiv.Perm ((Fin lens.fusionSiteCount × Bool) × Bool) :=
  routeLabelReindexing (lens.signedFusionMonodromy hab hac)

@[simp] theorem EvenKempeFusionLens.fusionArmReindexing_apply_b
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : Fin lens.fusionSiteCount × Bool) :
    lens.fusionArmReindexing hab hac (state, true) = (state, true) := by
  exact routeLabelReindexing_apply_true _ _

@[simp] theorem EvenKempeFusionLens.fusionArmReindexing_apply_c
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : Fin lens.fusionSiteCount × Bool) :
    lens.fusionArmReindexing hab hac (state, false) =
      (lens.signedFusionMonodromy hab hac state, false) := by
  exact routeLabelReindexing_apply_false _ _

end


end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionFaceNetworkGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance fusionFaceNetworkRetainedVertexFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance fusionFaceNetworkRetainedVertexDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- The route arm based at a chosen endpoint of one fusion edge.  The
endpoint bit is measured in the `b` orientation; the route bit is `true`
for the `b` route and `false` for its `c` companion. -/
def fusionRouteArmDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (endpoint route : Bool) : G.Dart :=
  if endpoint = true then
    if route = true then
      ambientBExitNeighborDart data lens hab site
    else
      ambientCExitCompanionDart data lens hab hac site
  else if route = true then
    ambientBEntryNeighborDart data lens hab site
  else
    ambientCEntryCompanionDart data lens hab hac site

@[simp] theorem fusionRouteArmDart_entry_b
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    fusionRouteArmDart data lens hab hac site false true =
      ambientBEntryNeighborDart data lens hab site := by
  simp [fusionRouteArmDart]

@[simp] theorem fusionRouteArmDart_entry_c
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    fusionRouteArmDart data lens hab hac site false false =
      ambientCEntryCompanionDart data lens hab hac site := by
  simp [fusionRouteArmDart]

@[simp] theorem fusionRouteArmDart_exit_b
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    fusionRouteArmDart data lens hab hac site true true =
      ambientBExitNeighborDart data lens hab site := by
  simp [fusionRouteArmDart]

@[simp] theorem fusionRouteArmDart_exit_c
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    fusionRouteArmDart data lens hab hac site true false =
      ambientCExitCompanionDart data lens hab hac site := by
  simp [fusionRouteArmDart]

@[simp] theorem fusionRouteArmDart_entry_turn
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    fusionRouteArmDart data lens hab hac site false
        (fusionEntryTurn graphData data lens hab site) =
      fusionEntryTurnDart graphData data lens hab hac site := by
  cases hturn : fusionEntryTurn graphData data lens hab site <;>
    simp [fusionRouteArmDart, fusionEntryTurnDart, hturn]

@[simp] theorem fusionRouteArmDart_entry_not_turn
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    fusionRouteArmDart data lens hab hac site false
        (!fusionEntryTurn graphData data lens hab site) =
      fusionEntryOtherDart graphData data lens hab hac site := by
  cases hturn : fusionEntryTurn graphData data lens hab site <;>
    simp [fusionRouteArmDart, fusionEntryOtherDart, hturn]

@[simp] theorem fusionRouteArmDart_exit_turn
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    fusionRouteArmDart data lens hab hac site true
        (fusionExitTurn graphData data lens hab site) =
      fusionExitTurnDart graphData data lens hab hac site := by
  cases hturn : fusionExitTurn graphData data lens hab site <;>
    simp [fusionRouteArmDart, fusionExitTurnDart, hturn]

@[simp] theorem fusionRouteArmDart_exit_not_turn
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    fusionRouteArmDart data lens hab hac site true
        (!fusionExitTurn graphData data lens hab site) =
      fusionExitOtherDart graphData data lens hab hac site := by
  cases hturn : fusionExitTurn graphData data lens hab site <;>
    simp [fusionRouteArmDart, fusionExitOtherDart, hturn]

/-- The abstract route transfer at one fusion site is exactly the pairing
of its two ambient face arcs.  Depending on which route arm is selected by
the entry rotation, one of the two displayed directions is the forward
two-step face equation. -/
theorem fusionRouteArmDart_facePairing
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
    (site : lens.FusionSite) (route : Bool) :
    let transferred :=
      (fusionFaceSymbol graphData data lens hab hac site).routeTransfer route
    graphData.toRotationSystem.phi
          (graphData.toRotationSystem.phi
            (graphData.toRotationSystem.alpha
              (fusionRouteArmDart data lens hab hac site false route))) =
        fusionRouteArmDart data lens hab hac site true transferred ∨
      graphData.toRotationSystem.phi
          (graphData.toRotationSystem.phi
            (graphData.toRotationSystem.alpha
              (fusionRouteArmDart data lens hab hac site true transferred))) =
        fusionRouteArmDart data lens hab hac site false route := by
  dsimp only
  have hselectedTransfer :
      (fusionFaceSymbol graphData data lens hab hac site).routeTransfer
          (fusionEntryTurn graphData data lens hab site) =
        !fusionExitTurn graphData data lens hab site := by
    simpa using FusionFaceSymbol.routeTransfer_entryTurn
      (fusionFaceSymbol graphData data lens hab hac site)
  have hotherTransfer :
      (fusionFaceSymbol graphData data lens hab hac site).routeTransfer
          (!fusionEntryTurn graphData data lens hab site) =
        fusionExitTurn graphData data lens hab site := by
    simpa using FusionFaceSymbol.routeTransfer_not_entryTurn
      (fusionFaceSymbol graphData data lens hab hac site)
  rcases Bool.eq_or_eq_not route
      (fusionEntryTurn graphData data lens hab site) with
    hselected | hother
  · right
    rw [hselected, hselectedTransfer,
      fusionRouteArmDart_exit_not_turn,
      fusionRouteArmDart_entry_turn]
    exact phi_sq_alpha_fusionExitOtherDart_eq_fusionEntryTurnDart
      graphData hcubic hrotation data lens hab hac hbc site
  · left
    rw [hother, hotherTransfer,
      fusionRouteArmDart_entry_not_turn,
      fusionRouteArmDart_exit_turn]
    exact phi_sq_alpha_fusionEntryOtherDart_eq_fusionExitTurnDart
      graphData hcubic hrotation data lens hab hac hbc site

/-- Interpret a canonical fusion-arm state as its actual ambient dart. -/
def bIndexedFusionArmDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : (Fin lens.fusionSiteCount × Bool) × Bool) : G.Dart :=
  fusionRouteArmDart data lens hab hac
    (lens.bFusionSiteAt state.1.1) state.1.2 state.2

/-- Every pair produced by the indexed crossing is exactly one of the two
verified ambient face arcs at its fusion site. -/
theorem indexedFusionFaceCrossing_facePairing
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
    (state : (Fin lens.fusionSiteCount × Bool) × Bool) :
    let crossing := indexedFusionFaceCrossing
      (bOrderedFusionFaceSymbol graphData data lens hab hac)
    graphData.toRotationSystem.phi
          (graphData.toRotationSystem.phi
            (graphData.toRotationSystem.alpha
              (bIndexedFusionArmDart data lens hab hac state))) =
        bIndexedFusionArmDart data lens hab hac (crossing state) ∨
      graphData.toRotationSystem.phi
          (graphData.toRotationSystem.phi
            (graphData.toRotationSystem.alpha
              (bIndexedFusionArmDart data lens hab hac
                (crossing state)))) =
        bIndexedFusionArmDart data lens hab hac state := by
  dsimp only
  rcases state with ⟨⟨position, endpoint⟩, route⟩
  cases endpoint
  · change
      graphData.toRotationSystem.phi
            (graphData.toRotationSystem.phi
              (graphData.toRotationSystem.alpha
                (fusionRouteArmDart data lens hab hac
                  (lens.bFusionSiteAt position) false route))) =
          fusionRouteArmDart data lens hab hac
            (lens.bFusionSiteAt position) true
            ((fusionFaceSymbol graphData data lens hab hac
              (lens.bFusionSiteAt position)).routeTransfer route) ∨
        graphData.toRotationSystem.phi
            (graphData.toRotationSystem.phi
              (graphData.toRotationSystem.alpha
                (fusionRouteArmDart data lens hab hac
                  (lens.bFusionSiteAt position) true
                  ((fusionFaceSymbol graphData data lens hab hac
                    (lens.bFusionSiteAt position)).routeTransfer route)))) =
          fusionRouteArmDart data lens hab hac
            (lens.bFusionSiteAt position) false route
    exact fusionRouteArmDart_facePairing graphData hcubic hrotation
      data lens hab hac hbc (lens.bFusionSiteAt position) route
  · have hpair := fusionRouteArmDart_facePairing
      graphData hcubic hrotation data lens hab hac hbc
      (lens.bFusionSiteAt position)
      ((bOrderedFusionFaceSymbol graphData data lens hab hac position).routeTransfer
        route)
    simp only [bOrderedFusionFaceSymbol] at hpair
    change
      graphData.toRotationSystem.phi
            (graphData.toRotationSystem.phi
              (graphData.toRotationSystem.alpha
                (fusionRouteArmDart data lens hab hac
                  (lens.bFusionSiteAt position) true route))) =
          fusionRouteArmDart data lens hab hac
            (lens.bFusionSiteAt position) false
            ((fusionFaceSymbol graphData data lens hab hac
              (lens.bFusionSiteAt position)).routeTransfer route) ∨
        graphData.toRotationSystem.phi
            (graphData.toRotationSystem.phi
              (graphData.toRotationSystem.alpha
                (fusionRouteArmDart data lens hab hac
                  (lens.bFusionSiteAt position) false
                  ((fusionFaceSymbol graphData data lens hab hac
                    (lens.bFusionSiteAt position)).routeTransfer route)))) =
          fusionRouteArmDart data lens hab hac
            (lens.bFusionSiteAt position) true route
    rw [FusionFaceSymbol.routeTransfer_involutive] at hpair
    exact hpair.symm

/-- The local fusion-face crossing written in the two separate route
orders.  It is the conjugate of the physical-site crossing by signed
fusion-arm reindexing. -/
def routeOrderedFusionFaceCrossing
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    Equiv.Perm ((Fin lens.fusionSiteCount × Bool) × Bool) :=
  (lens.fusionArmReindexing hab hac).symm.trans
    ((indexedFusionFaceCrossing
      (bOrderedFusionFaceSymbol graphData data lens hab hac)).trans
        (lens.fusionArmReindexing hab hac))

/-- Pulling a route-ordered crossing back through the arm reindexing
recovers the canonical indexed crossing. -/
theorem fusionArmReindexing_symm_routeOrderedFusionFaceCrossing
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : (Fin lens.fusionSiteCount × Bool) × Bool) :
    (lens.fusionArmReindexing hab hac).symm
        (routeOrderedFusionFaceCrossing
          graphData data lens hab hac state) =
      indexedFusionFaceCrossing
        (bOrderedFusionFaceSymbol graphData data lens hab hac)
        ((lens.fusionArmReindexing hab hac).symm state) := by
  change (lens.fusionArmReindexing hab hac).symm
      (lens.fusionArmReindexing hab hac
        (indexedFusionFaceCrossing
          (bOrderedFusionFaceSymbol graphData data lens hab hac)
          ((lens.fusionArmReindexing hab hac).symm state))) = _
  rw [(lens.fusionArmReindexing hab hac).symm_apply_apply]

/-- Interpret a state expressed in the separate route orders as its
ambient dart by transporting it back to the canonical physical-site
carrier. -/
def routeOrderedFusionArmDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : (Fin lens.fusionSiteCount × Bool) × Bool) : G.Dart :=
  bIndexedFusionArmDart data lens hab hac
    ((lens.fusionArmReindexing hab hac).symm state)

/-- The conjugated route-order crossing retains the exact ambient face
pairing semantics of the canonical crossing. -/
theorem routeOrderedFusionFaceCrossing_facePairing
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
    (state : (Fin lens.fusionSiteCount × Bool) × Bool) :
    graphData.toRotationSystem.phi
          (graphData.toRotationSystem.phi
            (graphData.toRotationSystem.alpha
              (routeOrderedFusionArmDart data lens hab hac state))) =
        routeOrderedFusionArmDart data lens hab hac
          (routeOrderedFusionFaceCrossing
            graphData data lens hab hac state) ∨
      graphData.toRotationSystem.phi
          (graphData.toRotationSystem.phi
            (graphData.toRotationSystem.alpha
              (routeOrderedFusionArmDart data lens hab hac
                (routeOrderedFusionFaceCrossing
                  graphData data lens hab hac state)))) =
        routeOrderedFusionArmDart data lens hab hac state := by
  have hpair := indexedFusionFaceCrossing_facePairing
    graphData hcubic hrotation data lens hab hac hbc
      ((lens.fusionArmReindexing hab hac).symm state)
  change
    graphData.toRotationSystem.phi
          (graphData.toRotationSystem.phi
            (graphData.toRotationSystem.alpha
              (bIndexedFusionArmDart data lens hab hac
                ((lens.fusionArmReindexing hab hac).symm state)))) =
        bIndexedFusionArmDart data lens hab hac
          ((lens.fusionArmReindexing hab hac).symm
            (routeOrderedFusionFaceCrossing
              graphData data lens hab hac state)) ∨
      graphData.toRotationSystem.phi
          (graphData.toRotationSystem.phi
            (graphData.toRotationSystem.alpha
              (bIndexedFusionArmDart data lens hab hac
                ((lens.fusionArmReindexing hab hac).symm
                  (routeOrderedFusionFaceCrossing
                    graphData data lens hab hac state))))) =
        bIndexedFusionArmDart data lens hab hac
          ((lens.fusionArmReindexing hab hac).symm state)
  rw [fusionArmReindexing_symm_routeOrderedFusionFaceCrossing]
  exact hpair

/-- Conjugating by signed route-order wiring preserves the involutive
nature of the local face crossing. -/
@[simp] theorem routeOrderedFusionFaceCrossing_involutive
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : (Fin lens.fusionSiteCount × Bool) × Bool) :
    routeOrderedFusionFaceCrossing graphData data lens hab hac
        (routeOrderedFusionFaceCrossing graphData data lens hab hac state) =
      state := by
  exact conjugatePermutation_involutive
    (lens.fusionArmReindexing hab hac)
    (indexedFusionFaceCrossing
      (bOrderedFusionFaceSymbol graphData data lens hab hac))
    (indexedFusionFaceCrossing_involutive
      (bOrderedFusionFaceSymbol graphData data lens hab hac)) state

end


end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
