import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularBoundaryIsoTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapSequentialOpening

/-!
# L1: ordered boundary data for the sequential two-cap opening

The supplied two-cap laboratory may be formed in Addendum-V order: open the
outer cap to obtain a frontier, then open the transported inner cap.  The
preceding module proves that this sequential graph is exactly the simultaneous
two-cap opening.  Here that equality is packaged as the identity vertex
isomorphism and the complete ordered boundary datum is transported through it.

The result preserves all five inner and outer coordinates.  It is a comparison
for a supplied cap pair, not a construction of a closed antecedent for every
abstract frontier and not a source crosscut constructor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapSequentialBoundary

open GoertzelV24AnnularBoundaryIsoTransport
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24PentagonCapOpening
open GoertzelV24TwoPentagonCapFrontierFactorization
open GoertzelV24TwoPentagonCapFrontierFactorization.PentagonCapPair
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24TwoPentagonCapSequentialOpening.PentagonCapPair
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace PentagonCapPair

local instance outerOpenGraphDecidableRel (caps : PentagonCapPair G) :
    DecidableRel caps.outer.openGraph.Adj :=
  Classical.decRel _

/-- The boundary datum obtained by opening the outer cap first and then the
transported inner cap. -/
def sequentialBoundaryData (caps : PentagonCapPair G)
    (hregular : G.IsRegularOfDegree 3) :
    AnnularBoundaryData (innerInOuterOpenGraph caps).openGraph 5 :=
  FrontierBoundaryData.openingBoundaryData
    (frontier := outerFrontier caps)
    (cap := innerInOuterOpenGraph caps)
    (hinterior := innerInOuterOpenGraph_interior caps)
    (outerFrontier_wellFormed_of_isRegularOfDegree_three caps hregular)

/-- The graph equality between sequential and simultaneous openings, viewed
as the identity map on the unchanged ambient vertex type. -/
def sequentialOpenGraphIso (caps : PentagonCapPair G) :
    (innerInOuterOpenGraph caps).openGraph ≃g caps.openGraph where
  toEquiv := Equiv.refl V
  map_rel_iff' := by
    intro left right
    rw [sequentialOpenGraph_eq_openGraph caps]
    simp

/-- Move the complete source-ordered boundary datum to the simultaneous
two-cap carrier. -/
def transportedSequentialBoundaryData (caps : PentagonCapPair G)
    (hregular : G.IsRegularOfDegree 3) : AnnularBoundaryData caps.openGraph 5 :=
  transport (sequentialOpenGraphIso caps) (sequentialBoundaryData caps hregular)

/-- The sequential construction preserves the five inner stub coordinates. -/
@[simp] theorem transportedSequentialBoundaryData_innerStub
    (caps : PentagonCapPair G) (hregular : G.IsRegularOfDegree 3)
    (step : Fin 5) :
    (transportedSequentialBoundaryData caps hregular).innerStub step =
      caps.boundaryData.innerStub step :=
  rfl

/-- The sequential construction preserves the five outer stub coordinates. -/
@[simp] theorem transportedSequentialBoundaryData_outerStub
    (caps : PentagonCapPair G) (hregular : G.IsRegularOfDegree 3)
    (step : Fin 5) :
    (transportedSequentialBoundaryData caps hregular).outerStub step =
      caps.boundaryData.outerStub step :=
  rfl

/-- The transported inner boundary edge has the same underlying primal edge
as the simultaneous inner opening spoke. -/
@[simp] theorem transportedSequentialBoundaryData_innerBoundaryEdge_val
    (caps : PentagonCapPair G) (hregular : G.IsRegularOfDegree 3)
    (step : Fin 5) :
    ((transportedSequentialBoundaryData caps hregular).innerBoundaryEdge step).1 =
      (caps.boundaryData.innerBoundaryEdge step).1 := by
  simp [transportedSequentialBoundaryData, sequentialBoundaryData,
    transport, sequentialOpenGraphIso,
    FrontierBoundaryData.openingBoundaryData,
    PentagonCap.openSpokeEmbedding, PentagonCapPair.boundaryData,
    PentagonCapPair.innerOpenSpokeEmbedding]
  rw [PentagonCap.openSpokeEdge_val,
    innerInOuterOpenGraph_spokeEdge_val]

/-- The transported outer boundary edge has the same underlying primal edge
as the simultaneous outer opening spoke. -/
@[simp] theorem transportedSequentialBoundaryData_outerBoundaryEdge_val
    (caps : PentagonCapPair G) (hregular : G.IsRegularOfDegree 3)
    (step : Fin 5) :
    ((transportedSequentialBoundaryData caps hregular).outerBoundaryEdge step).1 =
      (caps.boundaryData.outerBoundaryEdge step).1 := by
  simp [transportedSequentialBoundaryData, sequentialBoundaryData,
    transport, sequentialOpenGraphIso,
    FrontierBoundaryData.openingBoundaryData,
    FrontierBoundaryData.openOuterBoundaryEdgeEmbedding,
    PentagonCapPair.boundaryData,
    PentagonCapPair.outerOpenSpokeEmbedding,
    outerFrontier]
  exact caps.outer.openSpokeEdge_val step

/-- The complete ordered annular boundary package obtained sequentially is
the simultaneous two-cap package.  In particular no hidden permutation of
the five inner or outer coordinates occurs. -/
theorem transportedSequentialBoundaryData_eq_boundaryData
    (caps : PentagonCapPair G) (hregular : G.IsRegularOfDegree 3) :
    transportedSequentialBoundaryData caps hregular = caps.boundaryData := by
  rw [AnnularBoundaryData.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply DFunLike.ext _ _
    intro step
    exact transportedSequentialBoundaryData_innerStub caps hregular step
  · apply DFunLike.ext _ _
    intro step
    exact transportedSequentialBoundaryData_outerStub caps hregular step
  · apply DFunLike.ext _ _
    intro step
    apply Subtype.ext
    exact transportedSequentialBoundaryData_innerBoundaryEdge_val
      caps hregular step
  · apply DFunLike.ext _ _
    intro step
    apply Subtype.ext
    exact transportedSequentialBoundaryData_outerBoundaryEdge_val
      caps hregular step

end PentagonCapPair

end

end GoertzelV24TwoPentagonCapSequentialBoundary

end Mettapedia.GraphTheory.FourColor
