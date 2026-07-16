import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceTurns

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedHexCorridorTypes

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Once the first step of a cyclic three-dart fiber is fixed, the
remaining two steps are forced. -/
theorem rho_three_cycle_of_eq_second
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {first second third : RS.D}
    (hsecondBase : RS.vertOf second = RS.vertOf first)
    (hthirdBase : RS.vertOf third = RS.vertOf first)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfirst : RS.rho first = second) :
    RS.rho second = third ∧ RS.rho third = first := by
  have hnext := rho_eq_second_or_third_of_cubic
    RS hcubic hrotation
    (first := second) (second := third) (third := first)
    (hthirdBase.trans hsecondBase.symm) hsecondBase.symm
    hsecondThird hfirstSecond.symm hfirstThird.symm
  rcases hnext with hsecond | hback
  · have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation first
    rw [hfirst, hsecond] at hcube
    exact ⟨hsecond, hcube⟩
  · have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation first
    rw [hfirst, hback, hfirst] at hcube
    exact False.elim (hfirstSecond hcube.symm)

end RotationSystem

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionFacePairingGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance fusionFacePairingRetainedVertexFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance fusionFacePairingRetainedVertexDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- The nonselected route-neighbor dart at the entry endpoint. -/
def fusionEntryOtherDart (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  if fusionEntryTurn graphData data lens hab site = true then
    ambientCEntryCompanionDart data lens hab hac site
  else
    ambientBEntryNeighborDart data lens hab site

/-- The nonselected route-neighbor dart at the exit endpoint. -/
def fusionExitOtherDart (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  if fusionExitTurn graphData data lens hab site = true then
    ambientCExitCompanionDart data lens hab hac site
  else
    ambientBExitNeighborDart data lens hab site

/-- The central, selected, and nonselected entry darts form the entire
cyclic three-dart fiber in that order. -/
theorem ambientFusionEntry_rotationCycle
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
        fusionEntryTurnDart graphData data lens hab hac site ∧
      graphData.toRotationSystem.rho
          (fusionEntryTurnDart graphData data lens hab hac site) =
        fusionEntryOtherDart graphData data lens hab hac site ∧
      graphData.toRotationSystem.rho
          (fusionEntryOtherDart graphData data lens hab hac site) =
        ambientBFusionDart data lens hab site := by
  let RS := graphData.toRotationSystem
  have hpairs := ambientEntryTurnDarts_pairwise_ne
    data lens hab hac hbc site
  by_cases hturn : fusionEntryTurn graphData data lens hab site = true
  · have hfirst := (fusionEntryTurn_eq_true_iff
      graphData data lens hab site).1 hturn
    have hcycle := RotationSystem.rho_three_cycle_of_eq_second
      RS hcubic hrotation
      (first := ambientBFusionDart data lens hab site)
      (second := ambientBEntryNeighborDart data lens hab site)
      (third := ambientCEntryCompanionDart data lens hab hac site)
      (hsecondBase := rfl) (hthirdBase := rfl)
      hpairs.1 hpairs.2.1 hpairs.2.2 hfirst
    rw [fusionEntryTurnDart, fusionEntryOtherDart,
      if_pos hturn, if_pos hturn]
    exact ⟨hfirst, hcycle⟩
  · have hfalse : fusionEntryTurn graphData data lens hab site = false :=
      Bool.eq_false_of_not_eq_true hturn
    have hfirst := (fusionEntryTurn_eq_false_iff_companion
      graphData hcubic hrotation data lens hab hac hbc site).1 hfalse
    have hcycle := RotationSystem.rho_three_cycle_of_eq_second
      RS hcubic hrotation
      (first := ambientBFusionDart data lens hab site)
      (second := ambientCEntryCompanionDart data lens hab hac site)
      (third := ambientBEntryNeighborDart data lens hab site)
      (hsecondBase := rfl) (hthirdBase := rfl)
      hpairs.2.1 hpairs.1 hpairs.2.2.symm hfirst
    rw [fusionEntryTurnDart, fusionEntryOtherDart,
      if_neg hturn, if_neg hturn]
    exact ⟨hfirst, hcycle⟩

/-- The analogous cyclic three-dart fiber at the exit endpoint. -/
theorem ambientFusionExit_rotationCycle
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
        fusionExitTurnDart graphData data lens hab hac site ∧
      graphData.toRotationSystem.rho
          (fusionExitTurnDart graphData data lens hab hac site) =
        fusionExitOtherDart graphData data lens hab hac site ∧
      graphData.toRotationSystem.rho
          (fusionExitOtherDart graphData data lens hab hac site) =
        ambientBExitFusionDart data lens hab site := by
  let RS := graphData.toRotationSystem
  have hpairs := ambientExitTurnDarts_pairwise_ne
    data lens hab hac hbc site
  by_cases hturn : fusionExitTurn graphData data lens hab site = true
  · have hfirst := (fusionExitTurn_eq_true_iff
      graphData data lens hab site).1 hturn
    have hcycle := RotationSystem.rho_three_cycle_of_eq_second
      RS hcubic hrotation
      (first := ambientBExitFusionDart data lens hab site)
      (second := ambientBExitNeighborDart data lens hab site)
      (third := ambientCExitCompanionDart data lens hab hac site)
      (hsecondBase := rfl) (hthirdBase := rfl)
      hpairs.1 hpairs.2.1 hpairs.2.2 hfirst
    rw [fusionExitTurnDart, fusionExitOtherDart,
      if_pos hturn, if_pos hturn]
    exact ⟨hfirst, hcycle⟩
  · have hfalse : fusionExitTurn graphData data lens hab site = false :=
      Bool.eq_false_of_not_eq_true hturn
    have hfirst := (fusionExitTurn_eq_false_iff_companion
      graphData hcubic hrotation data lens hab hac hbc site).1 hfalse
    have hcycle := RotationSystem.rho_three_cycle_of_eq_second
      RS hcubic hrotation
      (first := ambientBExitFusionDart data lens hab site)
      (second := ambientCExitCompanionDart data lens hab hac site)
      (third := ambientBExitNeighborDart data lens hab site)
      (hsecondBase := rfl) (hthirdBase := rfl)
      hpairs.2.1 hpairs.1 hpairs.2.2.symm hfirst
    rw [fusionExitTurnDart, fusionExitOtherDart,
      if_neg hturn, if_neg hturn]
    exact ⟨hfirst, hcycle⟩

/-- The nonselected entry neighbor is the face predecessor of the
forward fusion dart. -/
theorem phi_alpha_fusionEntryOtherDart_eq_ambientBFusionDart
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
          (fusionEntryOtherDart graphData data lens hab hac site)) =
      ambientBFusionDart data lens hab site := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact (ambientFusionEntry_rotationCycle
    graphData hcubic hrotation data lens hab hac hbc site).2.2

/-- The nonselected exit neighbor is the face predecessor of the
reversed fusion dart. -/
theorem phi_alpha_fusionExitOtherDart_eq_ambientBExitFusionDart
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
          (fusionExitOtherDart graphData data lens hab hac site)) =
      ambientBExitFusionDart data lens hab site := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact (ambientFusionExit_rotationCycle
    graphData hcubic hrotation data lens hab hac hbc site).2.2

/-- The face successor of the reversed `b`-fusion dart is the selected
entry turn. -/
theorem phi_ambientBExitFusionDart_eq_fusionEntryTurnDart
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
        (ambientBExitFusionDart data lens hab site) =
      fusionEntryTurnDart graphData data lens hab hac site := by
  rw [ambientBExitFusionDart_eq_symm,
    ← SimpleGraphDartRotation.Data.toRotationSystem_alpha]
  exact phi_alpha_ambientBFusionDart_eq_fusionEntryTurnDart
    graphData hcubic hrotation data lens hab hac hbc site

/-- One side of the shared edge pairs the nonselected entry neighbor
with the selected exit neighbor by two face steps. -/
theorem phi_sq_alpha_fusionEntryOtherDart_eq_fusionExitTurnDart
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
        (graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha
            (fusionEntryOtherDart graphData data lens hab hac site))) =
      fusionExitTurnDart graphData data lens hab hac site := by
  rw [phi_alpha_fusionEntryOtherDart_eq_ambientBFusionDart
    graphData hcubic hrotation data lens hab hac hbc site]
  exact phi_ambientBFusionDart_eq_fusionExitTurnDart
    graphData hcubic hrotation data lens hab hac hbc site

/-- The opposite side pairs the nonselected exit neighbor with the
selected entry neighbor. -/
theorem phi_sq_alpha_fusionExitOtherDart_eq_fusionEntryTurnDart
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
        (graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha
            (fusionExitOtherDart graphData data lens hab hac site))) =
      fusionEntryTurnDart graphData data lens hab hac site := by
  rw [phi_alpha_fusionExitOtherDart_eq_ambientBExitFusionDart
    graphData hcubic hrotation data lens hab hac hbc site]
  exact phi_ambientBExitFusionDart_eq_fusionEntryTurnDart
    graphData hcubic hrotation data lens hab hac hbc site

/-- The two-state route-label transfer induced by the two face arcs of
a fusion edge. Equal endpoint turns exchange `b` and `c`; unequal turns
preserve them. -/
def FusionFaceSymbol.routeTransfer
    (symbol : FusionFaceSymbol) : Equiv.Perm Bool :=
  if symbol.entryTurn = symbol.exitTurn then
    Equiv.swap false true
  else
    Equiv.refl Bool

/-- The route-transfer permutation monoid has exactly two elements. -/
theorem card_bool_route_permutation :
    Fintype.card (Equiv.Perm Bool) = 2 := by
  decide

/-- The nonselected entry route label is paired with the selected exit
label. -/
@[simp] theorem FusionFaceSymbol.routeTransfer_not_entryTurn
    (symbol : FusionFaceSymbol) :
    symbol.routeTransfer (!symbol.entryTurn) = symbol.exitTurn := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;>
    simp [FusionFaceSymbol.routeTransfer]

/-- The selected entry route label is paired with the nonselected exit
label. -/
@[simp] theorem FusionFaceSymbol.routeTransfer_entryTurn
    (symbol : FusionFaceSymbol) :
    symbol.routeTransfer symbol.entryTurn = !symbol.exitTurn := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;>
    simp [FusionFaceSymbol.routeTransfer]

/-- The local route transfer is the transposition exactly when the two
endpoint turns agree. -/
theorem FusionFaceSymbol.routeTransfer_eq_swap_iff
    (symbol : FusionFaceSymbol) :
    symbol.routeTransfer = Equiv.swap false true ↔
      symbol.entryTurn = symbol.exitTurn := by
  have hreflNeSwap : (Equiv.refl Bool : Equiv.Perm Bool) ≠
      Equiv.swap false true := by
    intro heq
    have hvalue := congrArg (fun permutation : Equiv.Perm Bool ↦
      permutation false) heq
    simp at hvalue
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;>
    simp [FusionFaceSymbol.routeTransfer, hreflNeSwap]

/-- The local route transfer is the identity exactly when the endpoint
turns differ. -/
theorem FusionFaceSymbol.routeTransfer_eq_refl_iff
    (symbol : FusionFaceSymbol) :
    symbol.routeTransfer = Equiv.refl Bool ↔
      symbol.entryTurn ≠ symbol.exitTurn := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;>
    simp [FusionFaceSymbol.routeTransfer]

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
