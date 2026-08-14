import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionGraphBacking
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount

/-!
# Face transport to the simple-graph backing of an open region

The literal open-region rotation is first constructed on a sum of retained
darts and fresh boundary darts.  Its computed `PrimalGraph` carries the same
rotation through `primalDartEquiv`.  This module records the resulting
equivalence of quotient face carriers and its action on named dart faces.

This is generic carrier transport.  It proves no Euler equation, connectedness,
annular cellulation, or source-specific identification of hole faces.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionGraphFaceTransport

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionRotation
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceFaceCount

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/- The open-region and retained-splice layers provide extensionally identical
subtype instances under distinct names.  Use Lean's ordinary subtype instances
for this carrier-comparison calculation. -/
attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance openPrimalGraphDecidableRel
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : Dart data.toRotationSystem keep) :
    DecidableRel (PrimalGraph data.toRotationSystem keep outer).Adj :=
  Classical.decRel _

/-- The graph-backed face permutation is the conjugate of the literal
open-region face permutation under the canonical dart equivalence. -/
theorem graphData_phi_eq_permCongr
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : Dart data.toRotationSystem keep) :
    (graphData data keep outer).toRotationSystem.phi =
      (primalDartEquiv data keep outer).permCongr
        (rotationSystem data.toRotationSystem keep outer).phi := by
  apply Equiv.ext
  intro dart
  change (graphData data keep outer).vertexRotation dart.symm =
    primalDartEquiv data keep outer
      ((rotationSystem data.toRotationSystem keep outer).phi
        ((primalDartEquiv data keep outer).symm dart))
  convert (primalDartEquiv_phi data keep outer
    ((primalDartEquiv data keep outer).symm dart)).symm using 1
  · simp
  · apply SimpleGraph.Dart.ext
    rfl

/-- Quotient facial cycles of the literal open rotation are canonically the
facial cycles of its computed simple-graph backing. -/
def graphFaceEquiv
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : Dart data.toRotationSystem keep) :
    OrbitFace (rotationSystem data.toRotationSystem keep outer) ≃
      OrbitFace (graphData data keep outer).toRotationSystem :=
  Quotient.congr (primalDartEquiv data keep outer) (fun first second => by
    rw [graphData_phi_eq_permCongr data keep outer]
    exact (permCongr_sameCycle_iff (primalDartEquiv data keep outer)
      (rotationSystem data.toRotationSystem keep outer).phi first second).symm)

/-- The face equivalence sends the face named by a literal open dart to the
graph-backed face named by the corresponding simple-graph dart. -/
theorem graphFaceEquiv_dartOrbitFace
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer dart : Dart data.toRotationSystem keep) :
    graphFaceEquiv data keep outer
        (dartOrbitFace (rotationSystem data.toRotationSystem keep outer) dart) =
      dartOrbitFace (graphData data keep outer).toRotationSystem
        (primalDartEquiv data keep outer dart) := by
  rfl

/-- In particular, distinct literal opened faces remain distinct in the
simple-graph presentation consumed by `FramedAnnularCellulation`. -/
theorem graphFaceEquiv_ne
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : SimpleGraphDartRotation.Data G) (keep : V → Prop)
    (outer : Dart data.toRotationSystem keep)
    {left right : OrbitFace (rotationSystem data.toRotationSystem keep outer)}
    (hne : left ≠ right) :
    graphFaceEquiv data keep outer left ≠ graphFaceEquiv data keep outer right :=
  (graphFaceEquiv data keep outer).injective.ne hne

end

end GoertzelV24OpenRegionGraphFaceTransport

end Mettapedia.GraphTheory.FourColor
