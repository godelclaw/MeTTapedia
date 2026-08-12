import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileEnclosedMovingProfile

/-!
# Literal `Count` fibers on the moving interfaces of an enclosed aligned slab

The physical aligned slab has a six-port local boundary, but the transfer
engine observes its two transverse ends as separate width-two moving profiles.
This file gives that observation its literal nonnegative counting semantics:
an entry counts Tait colorings of the *enclosed* open slab which compute the
specified input and output profiles.

The construction deliberately does not assert that adjacent enclosed slabs
already glue in the ambient graph.  That remains the geometric realization
obligation.  Here the point is narrower: a supported profile pair carries
the multiplicity of its actual coloring fiber, rather than merely a Boolean
realizability witness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the open-region coloring carrier on the same ordinary edge-set
decidable equality as the literal-profile modules it extends. -/
local instance framedCorridorAlignedTwoTileEnclosedMovingCountEdgeSetFintype :
    Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance framedCorridorAlignedTwoTileEnclosedMovingCountEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Tait colorings of one literal enclosed aligned slab.  Keeping the
coloring and its Tait proof together makes the following fibers realizable by
construction. -/
abbrev SourceTwoTileAlignedEnclosedMovingTaitColoring
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :=
  { coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color //
    (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic hrotation
      htwoSided hunique offset).IsTaitEdgeColoring coloring }

/-- The literal coloring fiber over one pair of width-two moving profiles.
This is the correct carrier for a `Count` entry: different Tait colorings
with the same two profiles remain distinct elements of the fiber. -/
noncomputable def sourceTwoTileAlignedEnclosedMovingProfileFiber
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (input output : AlignedTwoTileEnclosedMovingProfile) :=
  { coloring : SourceTwoTileAlignedEnclosedMovingTaitColoring realization hcubic
      hrotation htwoSided hunique offset //
    sourceTwoTileAlignedEnclosedLiteralMovingInputProfile realization hcubic
        hrotation htwoSided hunique offset coloring.1 coloring.2 = input ∧
      sourceTwoTileAlignedEnclosedLiteralMovingOutputProfile realization hcubic
        hrotation htwoSided hunique offset coloring.1 coloring.2 = output }

/-- The nonnegative `Count` entry of the literal enclosed slab on its two
moving interfaces. -/
noncomputable def sourceTwoTileAlignedEnclosedMovingProfileCount
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (input output : AlignedTwoTileEnclosedMovingProfile) : Nat :=
  Nat.card (sourceTwoTileAlignedEnclosedMovingProfileFiber realization hcubic
    hrotation htwoSided hunique offset input output)

/-- Nonemptiness of a literal `Count` fiber is exactly the existing
realizability support relation. -/
theorem sourceTwoTileAlignedEnclosedMovingProfileFiber_nonempty_iff
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (input output : AlignedTwoTileEnclosedMovingProfile) :
    Nonempty (sourceTwoTileAlignedEnclosedMovingProfileFiber realization hcubic
      hrotation htwoSided hunique offset input output) ↔
      sourceTwoTileAlignedEnclosedMovingProfileSupport realization hcubic
        hrotation htwoSided hunique offset input output := by
  constructor
  · rintro ⟨coloring⟩
    exact ⟨coloring.1, coloring.2.1, coloring.2.2⟩
  · rintro ⟨coloring, hinput, houtput⟩
    exact ⟨⟨coloring, hinput, houtput⟩⟩

/-- Positivity of the literal moving-profile `Count` is precisely the
existence of a literal enclosed-slab Tait coloring with those endpoint
profiles. -/
theorem sourceTwoTileAlignedEnclosedMovingProfileCount_pos_iff
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (input output : AlignedTwoTileEnclosedMovingProfile) :
    0 < sourceTwoTileAlignedEnclosedMovingProfileCount realization hcubic
      hrotation htwoSided hunique offset input output ↔
      sourceTwoTileAlignedEnclosedMovingProfileSupport realization hcubic
        hrotation htwoSided hunique offset input output := by
  rw [sourceTwoTileAlignedEnclosedMovingProfileCount, Nat.card_pos_iff]
  constructor
  · rintro ⟨hnonempty, _⟩
    exact (sourceTwoTileAlignedEnclosedMovingProfileFiber_nonempty_iff realization
      hcubic hrotation htwoSided hunique offset input output).mp hnonempty
  · intro hsupport
    exact ⟨(sourceTwoTileAlignedEnclosedMovingProfileFiber_nonempty_iff realization
      hcubic hrotation htwoSided hunique offset input output).mpr hsupport,
      Finite.of_injective (fun fiber => fiber.1) Subtype.val_injective⟩

/-- Each literal enclosed-slab Tait coloring makes its own moving-profile
`Count` entry positive. -/
theorem sourceTwoTileAlignedEnclosedLiteralMovingProfileCount_pos
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (coloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).EdgeColoring Color)
    (hcoloring : (sourceTwoTileAlignedEnclosedOpenRegion realization hcubic
      hrotation htwoSided hunique offset).IsTaitEdgeColoring coloring) :
    0 < sourceTwoTileAlignedEnclosedMovingProfileCount realization hcubic
      hrotation htwoSided hunique offset
      (sourceTwoTileAlignedEnclosedLiteralMovingInputProfile realization hcubic
        hrotation htwoSided hunique offset coloring hcoloring)
      (sourceTwoTileAlignedEnclosedLiteralMovingOutputProfile realization hcubic
        hrotation htwoSided hunique offset coloring hcoloring) := by
  rw [sourceTwoTileAlignedEnclosedMovingProfileCount_pos_iff]
  exact sourceTwoTileAlignedEnclosedLiteralMovingProfiles_supported realization
    hcubic hrotation htwoSided hunique offset coloring hcoloring

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
