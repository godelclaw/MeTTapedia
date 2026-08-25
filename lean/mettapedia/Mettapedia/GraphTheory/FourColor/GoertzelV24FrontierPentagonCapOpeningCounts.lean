import Mathlib.Data.Fintype.Card
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison

/-!
# Exact carrier counts for Addendum V's one-cap opening

Addendum V opens one interior pentagon of a frontier tangle which already has
its outer boundary.  In the toolchain presentation the five cap vertices stay
as degree-one stubs and exactly the five cap-cycle edges are deleted.  The
manuscript-side open-region presentation deletes those vertices and replaces
the five spokes by fresh boundary ports.  The proved ordered graph isomorphism
identifies the two presentations.

This module records the resulting vertex and edge counts on both carriers.
Together with `GoertzelV24FrontierPentagonCapOpenEuler`, they show that the
one-cap operation preserves Euler characteristic.  They do not prove the
ambient frontier's Euler equation, construct its cellulation, or select that
frontier from a minimal counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapOpeningCounts

open SimpleGraph
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FrontierPentagonCapOpenRegionComparison
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening


variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  G.fintypeEdgeSet

namespace PentagonCap

local instance openGraphDecidableRel (cap : PentagonCap G) :
    DecidableRel cap.openGraph.Adj :=
  Classical.decRel _

local instance openGraphEdgeSetFintype (cap : PentagonCap G) :
    Fintype cap.openGraph.edgeSet :=
  cap.openGraph.fintypeEdgeSet

/-- A literal pentagon cap has exactly five cycle edges.  The name is kept
one-cap-specific so this module can coexist with the earlier two-cap count
laboratory without duplicating a global declaration. -/
@[simp] theorem one_cycleSupport_card (cap : PentagonCap G) :
    cap.cycleSupport.card = 5 := by
  simp [GoertzelV24PentagonCapOpening.PentagonCap.cycleSupport]

/-- Edges of the literal one-cap opening are exactly the ambient edges outside
the five named cap-cycle edges. -/
def openEdgeEquivComplement (cap : PentagonCap G) :
    cap.openGraph.edgeSet ≃ {edge : G.edgeSet // edge ∉ cap.cycleSupport} where
  toFun := fun edge =>
    ⟨⟨edge.1, cap.openGraph_edgeSet_subset edge.2⟩, by
      intro hremoved
      have hvalue : edge.1 ∈ edgeFinsetValueSet cap.cycleSupport :=
        (mem_edgeFinsetValueSet_iff cap.cycleSupport edge.1).mpr
          ⟨⟨edge.1, cap.openGraph_edgeSet_subset edge.2⟩, hremoved, rfl⟩
      exact ((cap.mem_openGraph_edgeSet_iff edge.1
        (cap.openGraph_edgeSet_subset edge.2)).mp edge.2) hvalue⟩
  invFun := fun edge =>
    ⟨edge.1.1, (cap.mem_openGraph_edgeSet_iff edge.1.1 edge.1.2).mpr (by
      intro hvalue
      rcases (mem_edgeFinsetValueSet_iff cap.cycleSupport edge.1.1).mp hvalue with
        ⟨removed, hremoved, hremovedValue⟩
      exact edge.2 (by
        have hremovedEq : removed = edge.1 := Subtype.ext hremovedValue
        simpa [← hremovedEq] using hremoved))⟩
  left_inv := by
    intro edge
    apply Subtype.ext
    rfl
  right_inv := by
    intro edge
    apply Subtype.ext
    rfl

/-- Exact one-cap edge deletion before changing presentations. -/
theorem card_openGraph_edgeSet_add_cycleSupport (cap : PentagonCap G) :
    Fintype.card cap.openGraph.edgeSet + cap.cycleSupport.card =
      Fintype.card G.edgeSet := by
  classical
  have hcomplement :
      Fintype.card {edge : G.edgeSet // edge ∉ cap.cycleSupport} =
        Fintype.card G.edgeSet -
          Fintype.card {edge : G.edgeSet // edge ∈ cap.cycleSupport} :=
    Fintype.card_subtype_compl (fun edge : G.edgeSet =>
      edge ∈ cap.cycleSupport)
  have hremoved :
      Fintype.card {edge : G.edgeSet // edge ∈ cap.cycleSupport} =
        cap.cycleSupport.card := by
    simpa using Fintype.card_subtype
      (fun edge : G.edgeSet => edge ∈ cap.cycleSupport)
  have hsurviving : Fintype.card cap.openGraph.edgeSet =
      Fintype.card G.edgeSet - cap.cycleSupport.card := by
    rw [Fintype.card_congr (openEdgeEquivComplement cap),
      hcomplement, hremoved]
  have hle : cap.cycleSupport.card ≤ Fintype.card G.edgeSet := by
    simpa using Finset.card_le_univ cap.cycleSupport
  omega

/-- Numerical form: one cap opening removes exactly five edges. -/
theorem card_openGraph_edgeSet_add_five (cap : PentagonCap G) :
    Fintype.card cap.openGraph.edgeSet + 5 = Fintype.card G.edgeSet := by
  simpa using card_openGraph_edgeSet_add_cycleSupport cap

/-- The graph-backed manuscript opening has the same vertex count as the
ambient frontier: five deleted cap vertices are replaced by five fresh stubs. -/
theorem card_openPrimalGraph_vertices
    (data : SimpleGraphDartRotation.Data G) (cap : PentagonCap G)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep cap.vertexSupport)) :
    Fintype.card
        (GoertzelV24OpenRegionRotation.Vertex data.toRotationSystem
          (keep cap.vertexSupport)) =
      Fintype.card V := by
  exact Fintype.card_congr
    (_root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison.PentagonCap.openingGraphIsoOpenPrimalGraph
      data cap root).toEquiv.symm

/-- The exact five-edge loss transported to the graph-backed manuscript
opening. -/
theorem card_openPrimalGraph_edgeSet_add_five
    (data : SimpleGraphDartRotation.Data G) (cap : PentagonCap G)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep cap.vertexSupport)) :
    Fintype.card
        (PrimalGraph data.toRotationSystem
          (keep cap.vertexSupport) root).edgeSet + 5 =
      Fintype.card G.edgeSet := by
  rw [← Fintype.card_congr
    (_root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison.PentagonCap.openingGraphIsoOpenPrimalGraph
      data cap root).mapEdgeSet]
  exact card_openGraph_edgeSet_add_five cap

end PentagonCap

end

end GoertzelV24FrontierPentagonCapOpeningCounts

end Mettapedia.GraphTheory.FourColor
