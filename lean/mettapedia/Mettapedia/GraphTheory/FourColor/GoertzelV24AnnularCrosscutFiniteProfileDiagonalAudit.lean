import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutFiniteSeamAudit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutProfileDiagonalLift

/-!
# Finite full-profile diagonal audit for a source crosscut

The existing finite seam audit compares the color-word projections of two
generated profile matrices.  The reductive pumping step needs a narrower
polarity but a stronger witness: every word accepted by the shortened
retained context must be realized by a positive *diagonal entry* of the
removed region's complete profile matrix.

The diagonal repeats one whole profile, so cut colors, tracked connectivity,
face continuation, fragment incidence, and capped face progress agree at the
two interfaces.  This file packages that exact obligation as containment of
two generated finite word supports and proves it equivalent to
`SourceCrosscutProfileDiagonalLift`.  It does not identify profiles computed
on the retained and removed regional carriers.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- Boundary words carried by positive diagonal entries of the removed
region's complete five-field profile matrix. -/
noncomputable def sourceCrosscutComplementDiagonalProfileWords
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hcubic : data.toRotationSystem.IsCubic) :
    Finset (Fin pair.left.walk.length → Color) := by
  classical
  exact Finset.univ.filter fun word =>
    ∃ profile : pair.SourceCrosscutComplementInterfaceProfile data boundary,
      pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
          data boundary profile = word ∧
        0 < pair.sourceCrosscutComplementLiteralOpenProfileCount
          data boundary hcubic profile profile

/-- Membership exposes the full-profile diagonal witness rather than only a
positive color-projected seam count. -/
theorem mem_sourceCrosscutComplementDiagonalProfileWords_iff
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hcubic : data.toRotationSystem.IsCubic)
    (word : Fin pair.left.walk.length → Color) :
    word ∈ pair.sourceCrosscutComplementDiagonalProfileWords
        data boundary hcubic ↔
      ∃ profile : pair.SourceCrosscutComplementInterfaceProfile data boundary,
        pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
            data boundary profile = word ∧
          0 < pair.sourceCrosscutComplementLiteralOpenProfileCount
            data boundary hcubic profile profile := by
  classical
  simp [sourceCrosscutComplementDiagonalProfileWords]

/-- The exact finite audit needed by reductive reverse completion.  It is
one-way because extra diagonal colorings of the removed corridor cannot
obstruct preservation of a counterexample. -/
def SourceCrosscutFiniteProfileDiagonalAudit
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hcubic : data.toRotationSystem.IsCubic) : Prop :=
  pair.sourceCrosscutLiteralOpenSeamProfileWords data boundary ⊆
    pair.sourceCrosscutComplementDiagonalProfileWords data boundary hcubic

/-- The finite containment audit is exactly the previously named semantic
full-profile diagonal lift. -/
theorem sourceCrosscutProfileDiagonalLift_iff_finiteProfileDiagonalAudit
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hcubic : data.toRotationSystem.IsCubic) :
    pair.SourceCrosscutProfileDiagonalLift data boundary hcubic ↔
      pair.SourceCrosscutFiniteProfileDiagonalAudit data boundary hcubic := by
  constructor
  · intro hlift word hword
    apply (pair.mem_sourceCrosscutComplementDiagonalProfileWords_iff
      data boundary hcubic word).2
    apply hlift word
    exact (pair.mem_sourceCrosscutLiteralOpenSeamProfileWords_iff
      data boundary word).1 hword
  · intro haudit word hword
    apply (pair.mem_sourceCrosscutComplementDiagonalProfileWords_iff
      data boundary hcubic word).1
    apply haudit
    exact (pair.mem_sourceCrosscutLiteralOpenSeamProfileWords_iff
      data boundary word).2 hword

/-- A successful full-profile audit supplies the one-way generated seam
support implication consumed by literal gluing. -/
theorem sourceCrosscutSeamSupportLift_ofFiniteProfileDiagonalAudit
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hcubic : data.toRotationSystem.IsCubic)
    (haudit : pair.SourceCrosscutFiniteProfileDiagonalAudit
      data boundary hcubic) :
    pair.SourceCrosscutSeamSupportLift data boundary hcubic :=
  pair.sourceCrosscutSeamSupportLift_ofProfileDiagonalLift
    data boundary hcubic
    ((pair.sourceCrosscutProfileDiagonalLift_iff_finiteProfileDiagonalAudit
      data boundary hcubic).2 haudit)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
