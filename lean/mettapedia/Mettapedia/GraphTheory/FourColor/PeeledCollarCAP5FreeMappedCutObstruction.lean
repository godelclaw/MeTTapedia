import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeMappedCutFoundationIndex

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelLemma818ClosedCollarWindingRealization

/-!
Obstruction interface for the CAP5-free mapped-cut face-route foundation.

The next planar-normal-form theorem may be proved contrapositive-style: rule
out a carrier cut with two off-carrier attachments for which no selected
face-route avoids the mapped carrier cut.  This module packages that exact
obstruction and proves it equivalent to the mapped-cut face-route foundation.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
The witness body inside the per-cut mapped-cut face-route target: the two
attachments are placed on selected boundary edges of one face, and the
selected-boundary walk on that face avoids the mapped carrier cut.
-/
def CutOffCarrierAttachmentMappedCutAvoidingFaceRouteWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet))
    (_root : V)
    (a b : BoundaryEdgeSetEndpointVertex
        (G := G)
        source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet) :
    Prop :=
  ∃ f : AmbientFace emb.faces,
  ∃ e₁ e₂ : G.edgeSet,
  ∃ _ : e₁ ∈ emb.faceBoundary f.1,
  ∃ _ : e₂ ∈ emb.faceBoundary f.1,
  ∃ _ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
  ∃ _ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
    (a : V) ∈ (e₁ : Sym2 V) ∧
      (b : V) ∈ (e₂ : Sym2 V) ∧
        BoundaryComponentWalkOnFace (emb := emb) f ∧
          ∀ g : PlanarBoundaryEdgeVertex emb,
            g.1 ∈ emb.faceBoundary f.1 →
              (source.toPlanarBoundaryAnnulusBoundaryData
                |>.toBoundaryEdgeSetEdgeVertex g).1 ∉
                cut.edgeCut.map
                  (boundaryEdgeSetInducedGraphEmbedding
                    (G := G)
                    (source.toPlanarBoundaryAnnulusBoundaryData
                      |>.ambientBoundaryEdgeSet)).mapEdgeSet

/--
The original per-cut target is exactly the assertion that every attached pair
has a mapped-cut face-route witness.
-/
theorem cutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget_iff_witness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)) :
    source.CutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget cut ↔
      ∀ root : V,
      ∀ a b : BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet,
        BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet root a →
        BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet root b →
          source.CutOffCarrierAttachmentMappedCutAvoidingFaceRouteWitness
            cut root a b :=
  Iff.rfl

/--
Per-cut obstruction: one off-carrier component attaches to two carrier
vertices, but that attachment pair has no selected face-route avoiding the
mapped carrier cut.
-/
def CutOffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)) :
    Prop :=
  ∃ root : V,
  ∃ a b : BoundaryEdgeSetEndpointVertex
      (G := G)
      source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet,
    BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
      (G := G)
      source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet root a ∧
    BoundaryEdgeSetInducedOffCarrierComponentAttachesToCarrierVertex
      (G := G)
      source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet root b ∧
    ¬ source.CutOffCarrierAttachmentMappedCutAvoidingFaceRouteWitness
        cut root a b

/--
The per-cut mapped-cut face-route target is equivalent to absence of the
per-cut obstruction.
-/
theorem cutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget_iff_no_obstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)) :
    source.CutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget cut ↔
      ¬ source.CutOffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction cut := by
  classical
  rw [source.cutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget_iff_witness]
  constructor
  · intro h hobs
    rcases hobs with ⟨root, a, b, hrootA, hrootB, hno⟩
    exact hno (h root a b hrootA hrootB)
  · intro hno root a b hrootA hrootB
    by_contra hnot
    exact hno ⟨root, a, b, hrootA, hrootB, hnot⟩

/-- All-cuts obstruction for the mapped-cut face-route target. -/
def OffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    Prop :=
  ∃ cut :
      SmallCyclicEdgeCut
        (BoundaryEdgeSetInducedGraph
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet),
    source.CutOffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction cut

/--
The all-cuts mapped-cut face-route target is equivalent to absence of the
all-cuts obstruction.
-/
theorem offCarrierAttachmentMappedCutAvoidingFaceRouteTarget_iff_no_obstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    source.OffCarrierAttachmentMappedCutAvoidingFaceRouteTarget ↔
      ¬ source.OffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction := by
  classical
  constructor
  · intro h hobs
    rcases hobs with ⟨cut, hcutObs⟩
    exact
      (source.cutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget_iff_no_obstruction
        cut).1 (h cut) hcutObs
  · intro hno cut
    refine
      (source.cutOffCarrierAttachmentMappedCutAvoidingFaceRouteTarget_iff_no_obstruction
        cut).2 ?_
    intro hcutObs
    exact hno ⟨cut, hcutObs⟩

end PlanarBoundaryClosedWalkAnnulusBoundarySource

/--
Closed-walk CAP5-free no-obstruction foundation target.  This is the
contrapositive form of the remaining mapped-cut face-route foundation: the
CAP5-free regime rules out every mapped-cut face-route obstruction.
-/
def CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget :
    Prop :=
  ∀ {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb),
      MinimalCounterexamplePeeledCollarRegime G
        (BoundaryEdgeSetEndpointVertex
          (G := G)
          source.toPlanarBoundaryAnnulusBoundaryData.ambientBoundaryEdgeSet)
        source.toPlanarBoundaryAnnulusBoundaryData.inducedBoundaryGraph →
      ¬ source.OffCarrierAttachmentMappedCutAvoidingFaceRouteObstruction

/--
The mapped-cut face-route foundation supplies the no-obstruction foundation.
-/
theorem
    cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget := by
  intro V _ G emb source regime
  exact
    (source.offCarrierAttachmentMappedCutAvoidingFaceRouteTarget_iff_no_obstruction).1
      (hfoundation source regime)

/--
The no-obstruction foundation supplies the mapped-cut face-route foundation.
-/
theorem
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_noMappedCutFaceRouteObstructionFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget := by
  intro V _ G emb source regime
  exact
    (source.offCarrierAttachmentMappedCutAvoidingFaceRouteTarget_iff_no_obstruction).2
      (hfoundation source regime)

/--
The mapped-cut face-route foundation and the no-obstruction foundation are
equivalent.
-/
theorem
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_iff_noMappedCutFaceRouteObstructionFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarMappedCutAvoidingFaceRouteFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget :=
  ⟨cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget,
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_noMappedCutFaceRouteObstructionFoundationTarget⟩

/--
No-obstruction variant of the public CAP5-free peeled-collar foundation index.
-/
def CAP5FreePeeledCollarNoMappedCutFaceRouteObstructionFoundationTargetIndex :
    Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget

/-- The mapped-cut public foundation index supplies the no-obstruction index. -/
theorem
    cap5FreePeeledCollarNoMappedCutFaceRouteObstructionFoundationTargetIndex_of_mappedCutFoundationTargetIndex
    (hindex : CAP5FreePeeledCollarMappedCutFoundationTargetIndex) :
    CAP5FreePeeledCollarNoMappedCutFaceRouteObstructionFoundationTargetIndex :=
  ⟨hindex.1, hindex.2.1,
    cap5FreeClosedWalkNoMappedCutFaceRouteObstructionFoundationTarget_of_mappedCutAvoidingFaceRouteFoundationTarget
      hindex.2.2⟩

/-- The no-obstruction public foundation index supplies the mapped-cut index. -/
theorem
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_noMappedCutFaceRouteObstructionFoundationTargetIndex
    (hindex :
      CAP5FreePeeledCollarNoMappedCutFaceRouteObstructionFoundationTargetIndex) :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex :=
  ⟨hindex.1, hindex.2.1,
    cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_noMappedCutFaceRouteObstructionFoundationTarget
      hindex.2.2⟩

/--
The mapped-cut public foundation index and the no-obstruction public index are
equivalent.
-/
theorem
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_iff_noMappedCutFaceRouteObstructionFoundationTargetIndex :
    CAP5FreePeeledCollarMappedCutFoundationTargetIndex ↔
      CAP5FreePeeledCollarNoMappedCutFaceRouteObstructionFoundationTargetIndex :=
  ⟨cap5FreePeeledCollarNoMappedCutFaceRouteObstructionFoundationTargetIndex_of_mappedCutFoundationTargetIndex,
    cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_noMappedCutFaceRouteObstructionFoundationTargetIndex⟩

/--
The no-obstruction foundation target feeds the closed-walk mapped-cut route
index.
-/
theorem
    section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget_of_noMappedCutFaceRouteObstructionFoundationTarget
    (hfoundation :
      CAP5FreeClosedWalkPeeledCollarNoMappedCutFaceRouteObstructionFoundationTarget) :
    Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :=
  section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget
    (cap5FreeClosedWalkMappedCutAvoidingFaceRouteFoundationTarget_of_noMappedCutFaceRouteObstructionFoundationTarget
      hfoundation)

/--
The no-obstruction public index supplies the three mapped-cut downstream route
indices.
-/
theorem
    cap5FreePeeledCollarNoMappedCutFaceRouteObstructionFoundationTargetIndex_routeIndexTargets
    (hindex :
      CAP5FreePeeledCollarNoMappedCutFaceRouteObstructionFoundationTargetIndex) :
    Section92Step4CanonicalAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4RepairedAnnulusCAP5FreeSeparationFoundationRouteIndexTarget ∧
      Section92Step4ClosedWalkCAP5FreeMappedCutFoundationRouteIndexTarget :=
  cap5FreePeeledCollarMappedCutFoundationTargetIndex_routeIndexTargets
    (cap5FreePeeledCollarMappedCutFoundationTargetIndex_of_noMappedCutFaceRouteObstructionFoundationTargetIndex
      hindex)

end Mettapedia.GraphTheory.FourColor
