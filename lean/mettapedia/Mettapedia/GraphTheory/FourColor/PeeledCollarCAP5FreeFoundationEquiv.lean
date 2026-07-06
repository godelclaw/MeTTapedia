import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeOffBoundarySourceData

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

/-!
Equivalent CAP5-free foundation interfaces for the peeled-collar regime route.

The source-data and face-source foundation targets package the same
normal-form obligation at different levels of detail.  This module exposes the
conversion at the CAP5-free theorem-interface level, so downstream route
modules may consume either statement without changing the graph consequence.
-/

variable {V : Type} [DecidableEq V]

namespace PlanarBoundaryAnnulusCollarGeometry

/-- Canonical noncrossing face-source data supplies canonical source data. -/
theorem
    regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    (h : data.RegimeNoncrossingFaceSourceFoundationTarget) :
    data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  planarBoundaryAnnulusPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_noncrossingFaceSourceTarget
    h

/--
Canonical aligned face-source and source-data foundation targets are
equivalent.
-/
theorem
    regimeNoncrossingFaceSourceFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    data.RegimeNoncrossingFaceSourceFoundationTarget ↔
      data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  ⟨fun h =>
      data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
        h,
    fun h =>
      data.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
        h⟩

end PlanarBoundaryAnnulusCollarGeometry

namespace PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/-- Repaired noncrossing face-source data supplies repaired source data. -/
theorem
    regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    (h : data.RegimeNoncrossingFaceSourceFoundationTarget) :
    data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  planarBoundaryPreviousBoundaryPeeledCollarOffCarrierAttachmentFaceSourceDataTarget_of_noncrossingFaceSourceTarget
    h

/--
Repaired aligned face-source and source-data foundation targets are
equivalent.
-/
theorem
    regimeNoncrossingFaceSourceFoundationTarget_iff_regimeAttachmentFaceSourceDataFoundationTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    data.RegimeNoncrossingFaceSourceFoundationTarget ↔
      data.RegimeAttachmentFaceSourceDataFoundationTarget :=
  ⟨fun h =>
      data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
        h,
    fun h =>
      data.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
        h⟩

end PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry

/--
The closed-walk CAP5-free face-source target supplies the closed-walk
source-data target.
-/
theorem cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_faceSourceFoundationTarget
    (hfoundation : CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget) :
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget := by
  intro V _ G emb source regime
  exact
    source.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      (hfoundation source regime)

/--
Closed-walk CAP5-free face-source and source-data foundation targets are
equivalent.
-/
theorem cap5FreeClosedWalkFaceSourceFoundationTarget_iff_attachmentFaceSourceDataFoundationTarget :
    CAP5FreeClosedWalkPeeledCollarFaceSourceFoundationTarget ↔
      CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
  ⟨cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_faceSourceFoundationTarget,
    cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget⟩

/--
The canonical CAP5-free face-source target supplies the canonical source-data
target.
-/
theorem cap5FreeCanonicalAnnulusAttachmentFaceSourceDataFoundationTarget_of_faceSourceFoundationTarget
    (hfoundation : CAP5FreeCanonicalAnnulusPeeledCollarFaceSourceFoundationTarget) :
    CAP5FreeCanonicalAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      (hfoundation data source hboundary regime)

/--
The canonical CAP5-free source-data target supplies the canonical face-source
target.
-/
theorem cap5FreeCanonicalAnnulusFaceSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget
    (hfoundation :
      CAP5FreeCanonicalAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    CAP5FreeCanonicalAnnulusPeeledCollarFaceSourceFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      (hfoundation data source hboundary regime)

/--
Canonical CAP5-free face-source and source-data foundation targets are
equivalent.
-/
theorem cap5FreeCanonicalAnnulusFaceSourceFoundationTarget_iff_attachmentFaceSourceDataFoundationTarget :
    CAP5FreeCanonicalAnnulusPeeledCollarFaceSourceFoundationTarget ↔
      CAP5FreeCanonicalAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
  ⟨cap5FreeCanonicalAnnulusAttachmentFaceSourceDataFoundationTarget_of_faceSourceFoundationTarget,
    cap5FreeCanonicalAnnulusFaceSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget⟩

/--
The repaired CAP5-free face-source target supplies the repaired source-data
target.
-/
theorem cap5FreeRepairedAnnulusAttachmentFaceSourceDataFoundationTarget_of_faceSourceFoundationTarget
    (hfoundation : CAP5FreeRepairedAnnulusPeeledCollarFaceSourceFoundationTarget) :
    CAP5FreeRepairedAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeAttachmentFaceSourceDataFoundationTarget_of_regimeNoncrossingFaceSourceFoundationTarget
      (hfoundation data source hboundary regime)

/--
The repaired CAP5-free source-data target supplies the repaired face-source
target.
-/
theorem cap5FreeRepairedAnnulusFaceSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget
    (hfoundation :
      CAP5FreeRepairedAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget) :
    CAP5FreeRepairedAnnulusPeeledCollarFaceSourceFoundationTarget := by
  intro V _ G emb data source hboundary regime
  exact
    data.regimeNoncrossingFaceSourceFoundationTarget_of_regimeAttachmentFaceSourceDataFoundationTarget
      (hfoundation data source hboundary regime)

/--
Repaired CAP5-free face-source and source-data foundation targets are
equivalent.
-/
theorem cap5FreeRepairedAnnulusFaceSourceFoundationTarget_iff_attachmentFaceSourceDataFoundationTarget :
    CAP5FreeRepairedAnnulusPeeledCollarFaceSourceFoundationTarget ↔
      CAP5FreeRepairedAnnulusPeeledCollarAttachmentFaceSourceDataFoundationTarget :=
  ⟨cap5FreeRepairedAnnulusAttachmentFaceSourceDataFoundationTarget_of_faceSourceFoundationTarget,
    cap5FreeRepairedAnnulusFaceSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget⟩

/--
Source-data variant of the public CAP5-free peeled-collar foundation index.
-/
def CAP5FreePeeledCollarSourceDataFoundationTargetIndex : Prop :=
  CAP5FreeCanonicalAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeRepairedAnnulusPeeledCollarSeparationFoundationTarget ∧
    CAP5FreeClosedWalkPeeledCollarAttachmentFaceSourceDataFoundationTarget

/--
The public face-source foundation index and its source-data variant are
equivalent.
-/
theorem cap5FreePeeledCollarFoundationTargetIndex_iff_sourceDataFoundationTargetIndex :
    CAP5FreePeeledCollarFoundationTargetIndex ↔
      CAP5FreePeeledCollarSourceDataFoundationTargetIndex := by
  constructor
  · rintro ⟨hcanonical, hrepaired, hface⟩
    exact
      ⟨hcanonical,
        hrepaired,
        cap5FreeClosedWalkAttachmentFaceSourceDataFoundationTarget_of_faceSourceFoundationTarget
          hface⟩
  · rintro ⟨hcanonical, hrepaired, hsourceData⟩
    exact
      ⟨hcanonical,
        hrepaired,
        cap5FreeClosedWalkFaceSourceFoundationTarget_of_attachmentFaceSourceDataFoundationTarget
          hsourceData⟩

end Mettapedia.GraphTheory.FourColor

