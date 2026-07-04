import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word0

namespace Mettapedia.GraphTheory.FourColor

/-!
# Closed-collar winding invariant

This module records the finite annular-collar winding test used for the
Section 9.2 ambient-execution diagnosis.  The radial cut is the cyclic
closing interface of the closed-collar model; a two-color component has
mod-2 winding class given by its crossing count with that cut.
-/

namespace GoertzelLemma818ClosedCollarWinding

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

structure ClosedCollarWindingCounts where
  winding0 : Nat
  winding1 : Nat
  deriving DecidableEq, BEq, Repr

def closedCollarRadialCutCrossingCount
    (orients : List TauOrient) (component : List ChainEdge) : Nat :=
  (component.filter fun ge => (closedCollarClosingEdges orients).contains ge).length

def closedCollarComponentWindingClass
    (orients : List TauOrient) (component : List ChainEdge) : Bool :=
  closedCollarRadialCutCrossingCount orients component % 2 == 1

def closedCollarComponentIsWinding
    (orients : List TauOrient) (component : List ChainEdge) : Bool :=
  closedCollarComponentWindingClass orients component

def closedCollarComponentIsConfined
    (orients : List TauOrient) (component : List ChainEdge) : Bool :=
  !closedCollarComponentWindingClass orients component

theorem closedCollarComponentWindingClass_perm
    {orients : List TauOrient} {component₁ component₂ : List ChainEdge}
    (hperm : component₁.Perm component₂) :
    closedCollarComponentWindingClass orients component₁ =
      closedCollarComponentWindingClass orients component₂ := by
  unfold closedCollarComponentWindingClass closedCollarRadialCutCrossingCount
  have hfilter :
      (component₁.filter fun ge => (closedCollarClosingEdges orients).contains ge).Perm
        (component₂.filter fun ge => (closedCollarClosingEdges orients).contains ge) :=
    hperm.filter _
  exact congrArg (fun n => n % 2 == 1) hfilter.length_eq

def closedCollarComponentSeedIsFirst
    (orients : List TauOrient) (component : List ChainEdge) (seed : ChainEdge) :
    Bool :=
  let earlier := (closedCollarEdges orients).takeWhile fun ge => !(ge == seed)
  !earlier.any (fun ge => component.contains ge)

def closedCollarPairComponents
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) : List (List ChainEdge) :=
  (closedCollarEdges orients).foldl
    (fun components seed =>
      let component := closedCollarComponent orients states a c seed
      if component.isEmpty then
        components
      else if closedCollarComponentSeedIsFirst orients component seed then
        components ++ [component]
      else
        components)
    []

def closedCollarPairWindingCounts
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) : ClosedCollarWindingCounts :=
  let components := closedCollarPairComponents orients states a c
  { winding0 :=
      (components.filter fun component =>
        !closedCollarComponentWindingClass orients component).length
    winding1 :=
      (components.filter fun component =>
        closedCollarComponentWindingClass orients component).length }

def closedCollarWindingProfile
    (orients : List TauOrient) (states : List TauState) :
    List ((LColor × LColor) × ClosedCollarWindingCounts) :=
  colorPairs.map fun pair =>
    (pair, closedCollarPairWindingCounts orients states pair.1 pair.2)

def closedCollarMoveWindingClass
    (orients : List TauOrient) (states : List TauState)
    (move : ChainMove) : Bool :=
  closedCollarComponentWindingClass orients
    (closedCollarComponent orients states move.a move.c move.seed)

def closedCollarAggregateCutParityForPair
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) : Bool :=
  ((closedCollarClosingEdges orients).filter fun ge =>
      colorInPair (chainEdgeColor states ge) a c).length % 2 == 1

def closedCollarAggregateCutParityProfile
    (orients : List TauOrient) (states : List TauState) :
    List ((LColor × LColor) × Bool) :=
  colorPairs.map fun pair =>
    (pair, closedCollarAggregateCutParityForPair orients states pair.1 pair.2)

def closedCollarWindingBoundaryDeterminedForWord
    (orients : List TauOrient) : Prop :=
  ∀ key, key ∈ colorAssignments4 →
    ∀ s t,
      s ∈ closedCollarFiber orients key →
      t ∈ closedCollarFiber orients key →
      closedCollarWindingProfile orients s =
        closedCollarWindingProfile orients t

def windingFreedomWord : List TauOrient :=
  GoertzelLemma818ClosedCollarS2Word0.word

def windingFreedomKey : List LColor :=
  [LColor.r, LColor.r, LColor.b, LColor.b]

def windingFreedomStateNoWinding : List TauState :=
  listGetD GoertzelLemma818ClosedCollarS2Word0.fiber4 0 []

def windingFreedomStateWithWinding : List TauState :=
  listGetD GoertzelLemma818ClosedCollarS2Word0.fiber4 4 []

def windingFreedomProfileNoWinding :
    List ((LColor × LColor) × ClosedCollarWindingCounts) :=
  [ ((LColor.r, LColor.b), { winding0 := 2, winding1 := 0 })
  , ((LColor.r, LColor.p), { winding0 := 2, winding1 := 0 })
  , ((LColor.b, LColor.p), { winding0 := 2, winding1 := 0 })
  ]

def windingFreedomProfileWithWinding :
    List ((LColor × LColor) × ClosedCollarWindingCounts) :=
  [ ((LColor.r, LColor.b), { winding0 := 2, winding1 := 2 })
  , ((LColor.r, LColor.p), { winding0 := 2, winding1 := 0 })
  , ((LColor.b, LColor.p), { winding0 := 2, winding1 := 0 })
  ]

def windingFreedomAggregateParity :
    List ((LColor × LColor) × Bool) :=
  [ ((LColor.r, LColor.b), false)
  , ((LColor.r, LColor.p), false)
  , ((LColor.b, LColor.p), false)
  ]

theorem windingFreedom_stateNoWinding_mem :
    windingFreedomStateNoWinding ∈
      closedCollarFiber windingFreedomWord windingFreedomKey := by
  decide

theorem windingFreedom_stateWithWinding_mem :
    windingFreedomStateWithWinding ∈
      closedCollarFiber windingFreedomWord windingFreedomKey := by
  decide

theorem windingFreedom_profiles :
    closedCollarWindingProfile windingFreedomWord
        windingFreedomStateNoWinding =
          windingFreedomProfileNoWinding ∧
      closedCollarWindingProfile windingFreedomWord
        windingFreedomStateWithWinding =
          windingFreedomProfileWithWinding := by
  decide

theorem windingFreedom_profiles_differ :
    closedCollarWindingProfile windingFreedomWord
        windingFreedomStateNoWinding ≠
      closedCollarWindingProfile windingFreedomWord
        windingFreedomStateWithWinding := by
  intro hsame
  have hbad : windingFreedomProfileNoWinding ≠
      windingFreedomProfileWithWinding := by
    decide
  exact hbad (by
    simpa [windingFreedom_profiles.1, windingFreedom_profiles.2] using hsame)

theorem windingFreedom_aggregateParity_same :
    closedCollarAggregateCutParityProfile windingFreedomWord
        windingFreedomStateNoWinding =
          windingFreedomAggregateParity ∧
      closedCollarAggregateCutParityProfile windingFreedomWord
        windingFreedomStateWithWinding =
          windingFreedomAggregateParity := by
  decide

theorem not_closedCollarWindingBoundaryDetermined_tauTau :
    ¬ closedCollarWindingBoundaryDeterminedForWord windingFreedomWord := by
  intro hdet
  have hkey : windingFreedomKey ∈ colorAssignments4 := by decide
  have hsame :=
    hdet windingFreedomKey hkey
      windingFreedomStateNoWinding windingFreedomStateWithWinding
      windingFreedom_stateNoWinding_mem windingFreedom_stateWithWinding_mem
  exact windingFreedom_profiles_differ hsame

def ClosedCollarWindingFreedomTheorem : Prop :=
  ∃ orients key s t,
    orients ∈ closedCollarL1Words ∧
      key ∈ colorAssignments4 ∧
      s ∈ closedCollarFiber orients key ∧
      t ∈ closedCollarFiber orients key ∧
      closedCollarAggregateCutParityProfile orients s =
        closedCollarAggregateCutParityProfile orients t ∧
      closedCollarWindingProfile orients s ≠
        closedCollarWindingProfile orients t

theorem closedCollarWindingFreedomTheorem :
    ClosedCollarWindingFreedomTheorem := by
  refine
    ⟨windingFreedomWord, windingFreedomKey,
      windingFreedomStateNoWinding, windingFreedomStateWithWinding,
      ?_, ?_, windingFreedom_stateNoWinding_mem,
      windingFreedom_stateWithWinding_mem, ?_, windingFreedom_profiles_differ⟩
  · decide
  · decide
  · exact
      windingFreedom_aggregateParity_same.1.trans
        windingFreedom_aggregateParity_same.2.symm

def windingZeroProfileChangingMove : ChainMove :=
  GoertzelLemma818ClosedCollarS2Word0.cert4_move_1_4

theorem windingZeroProfileChangingMove_is_step :
    closedCollarSpecifiedKempeStep windingFreedomWord
      (listGetD GoertzelLemma818ClosedCollarS2Word0.fiber4 1 [])
      windingFreedomStateWithWinding
      windingZeroProfileChangingMove = true := by
  decide

theorem windingZeroProfileChangingMove_winding0 :
    closedCollarMoveWindingClass windingFreedomWord
      (listGetD GoertzelLemma818ClosedCollarS2Word0.fiber4 1 [])
      windingZeroProfileChangingMove = false := by
  decide

theorem windingZeroProfileChangingMove_source_profile :
    closedCollarWindingProfile windingFreedomWord
        (listGetD GoertzelLemma818ClosedCollarS2Word0.fiber4 1 []) =
      windingFreedomProfileNoWinding := by
  decide

theorem windingZeroProfileChangingMove_changes_profile :
    closedCollarWindingProfile windingFreedomWord
        (listGetD GoertzelLemma818ClosedCollarS2Word0.fiber4 1 []) ≠
      closedCollarWindingProfile windingFreedomWord
        windingFreedomStateWithWinding := by
  intro hsame
  have hbad : windingFreedomProfileNoWinding ≠
      windingFreedomProfileWithWinding := by
    decide
  exact hbad (by
    simpa [windingZeroProfileChangingMove_source_profile,
      windingFreedom_profiles.2] using hsame)

def ClosedCollarWindingZeroSwitchChangesProfile : Prop :=
  ∃ s t move,
    s ∈ closedCollarFiber windingFreedomWord windingFreedomKey ∧
      t ∈ closedCollarFiber windingFreedomWord windingFreedomKey ∧
      closedCollarSpecifiedKempeStep windingFreedomWord s t move = true ∧
      closedCollarMoveWindingClass windingFreedomWord s move = false ∧
      closedCollarWindingProfile windingFreedomWord s ≠
        closedCollarWindingProfile windingFreedomWord t

theorem closedCollarWindingZeroSwitchChangesProfile :
    ClosedCollarWindingZeroSwitchChangesProfile := by
  refine
    ⟨listGetD GoertzelLemma818ClosedCollarS2Word0.fiber4 1 [],
      windingFreedomStateWithWinding,
      windingZeroProfileChangingMove, ?_, windingFreedom_stateWithWinding_mem,
      windingZeroProfileChangingMove_is_step,
      windingZeroProfileChangingMove_winding0,
      windingZeroProfileChangingMove_changes_profile⟩
  decide

end GoertzelLemma818ClosedCollarWinding

end Mettapedia.GraphTheory.FourColor
