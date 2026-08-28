import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationTaitPotential
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarDualStructure

/-!
# The stellar Tait reduction

This is the consumer-facing form of the source's reverse Tait implication.
The stellar subdivision triangulates every orbit face without collapsing
parallel spokes.  A Tait colouring of its literal facial dual integrates to a
four-colouring of the stellar primal map.  Restricting that colouring to the
old vertices gives a four-colouring of the original simple graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24StellarTaitReduction

open GoertzelV24FaceDualConnectedness
open GoertzelV24RotationTaitPotential
open GoertzelV24SphericalGraphPresentation
open GoertzelV24StellarDualStructure
open GoertzelV24StellarSubdivision
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The Tait hypothesis in the rotation-system vocabulary used by the
compositional route. -/
def EveryBridgelessSphericalCubicTaitColorable : Prop :=
  ∀ {V E : Type u} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E),
    BridgelessSphericalCubicMapData RS → RotationSystemTaitColorable RS

/-- The old vertices embed as a subgraph of the stellar primal graph. -/
theorem stellar_adj_of_adj
    (presentation : ConnectedSphericalGraphPresentation G)
    {left right : V} (hadj : G.Adj left right) :
    (rotationPrimalGraph (StellarRS presentation)).Adj
      (Sum.inl left) (Sum.inl right) := by
  let dart : G.Dart := ⟨(left, right), hadj⟩
  apply (rotationPrimalGraph_adj_iff (StellarRS presentation)).2
  refine ⟨old dart, ?_, ?_⟩
  · rfl
  · rfl

/-- Restrict any four-colouring of the stellar primal graph to the old
vertices. -/
theorem colorable_four_of_stellar_colorable
    (presentation : ConnectedSphericalGraphPresentation G)
    (hstellar : (rotationPrimalGraph (StellarRS presentation)).Colorable 4) :
    G.Colorable 4 := by
  let stellarColouring :
      (rotationPrimalGraph (StellarRS presentation)).Coloring (Fin 4) :=
    hstellar.some
  refine ⟨SimpleGraph.Coloring.mk
    (fun vertex => stellarColouring (Sum.inl vertex)) ?_⟩
  intro left right hadj
  exact stellarColouring.valid (stellar_adj_of_adj presentation hadj)

/-- A Tait colouring of the stellar facial dual produces a four-colouring of
the original graph.  The only size hypothesis is the one used to ensure that
the connected original presentation has a dart over every displayed vertex. -/
theorem colorable_four_of_stellarDual_taitColorable
    (presentation : ConnectedSphericalGraphPresentation G)
    (hcard : 3 ≤ Fintype.card V)
    (hTait : RotationSystemTaitColorable (StellarDualRS presentation)) :
    G.Colorable 4 := by
  obtain ⟨colouring, hcolouring⟩ := hTait
  have hstellar : (rotationPrimalGraph (StellarRS presentation)).Colorable 4 :=
    colorable_four_of_dualTaitColoring
      (StellarRS presentation)
      (GoertzelV24StellarRotationSystem.orbitFacesTwoSided
        presentation.graphData.toRotationSystem)
      (stellarDual_primalConnected presentation)
      (stellar_primalConnected presentation hcard)
      (stellar_euler_semantic presentation hcard)
      (stellarDual_orbitSphericalCubicMapData presentation hcard).cubic
      colouring hcolouring
  exact colorable_four_of_stellar_colorable presentation hstellar

/-- The source-facing reverse Tait implication for genuine connected
spherical graph presentations.  Abstract planar graphs enter only through
the separate plane-embedding representation theorem. -/
theorem connectedSphericalFourColorStatement_of_tait
    (hTait : EveryBridgelessSphericalCubicTaitColorable.{u}) :
    ConnectedSphericalFourColorStatement.{u} := by
  intro V _ _ G _ hcard
  rintro ⟨presentation⟩
  apply colorable_four_of_stellarDual_taitColorable presentation hcard
  exact hTait (StellarDualRS presentation)
    (stellarDual_bridgelessSphericalCubicMapData presentation hcard)

/-- Tait colourability of every bridgeless spherical cubic rotation map
implies the componentwise spherical Four-Colour statement. -/
theorem sphericalFourColorStatement_of_tait
    (hTait : EveryBridgelessSphericalCubicTaitColorable.{u}) :
    SphericalFourColorStatement.{u} :=
  sphericalFourColorStatement_of_connected
    (connectedSphericalFourColorStatement_of_tait hTait)

end

end GoertzelV24StellarTaitReduction

end Mettapedia.GraphTheory.FourColor
