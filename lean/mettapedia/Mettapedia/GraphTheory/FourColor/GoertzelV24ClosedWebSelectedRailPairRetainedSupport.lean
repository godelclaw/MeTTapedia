import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairRetainedCrossAppend

/-!
# L1: support provenance for retained selected-rail bypasses

Loop erasure may shorten either composed rail, but it cannot introduce a
face which was absent from the two input assemblies.  This module records
that elementary containment for both endpoint orders and carries it through
the retained-collision classifiers.

The result is support provenance only.  It neither eliminates a retained
cross collision nor constructs the rolling corridor transition or either
end cap.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A support uses only faces already present in one of two input rail
assemblies. -/
def SupportContainedInAssemblyPair
    {firstStart secondStart middleFirst middleSecond newFirstStart newSecondStart
      firstFinish secondFinish : SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      newFirstStart newSecondStart firstFinish secondFinish)
    (support : List (SelectedFace (web := web))) : Prop :=
  ∀ face ∈ support,
    face ∈ oldAssembly.firstRail.support ∨
    face ∈ oldAssembly.secondRail.support ∨
    face ∈ newAssembly.firstRail.support ∨
    face ∈ newAssembly.secondRail.support

/-- Both rails of an output assembly use only the two input supports. -/
def AssemblySupportContainedInAssemblyPair
    {firstStart secondStart middleFirst middleSecond newFirstStart newSecondStart
      firstFinish secondFinish outputFirst outputSecond : SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      newFirstStart newSecondStart firstFinish secondFinish)
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart outputFirst outputSecond) : Prop :=
  SupportContainedInAssemblyPair oldAssembly newAssembly
      assembly.firstRail.support ∧
    SupportContainedInAssemblyPair oldAssembly newAssembly
      assembly.secondRail.support

private theorem bypass_append_support_contained
    {start middle finish : SelectedFace (web := web)}
    (oldWalk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk start middle)
    (newWalk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk middle finish) :
    ∀ face ∈ (oldWalk.append newWalk).bypass.support,
      face ∈ oldWalk.support ∨ face ∈ newWalk.support := by
  intro face hface
  have hraw := (oldWalk.append newWalk).support_bypass_subset_support hface
  rw [SimpleGraph.Walk.support_append] at hraw
  rcases List.mem_append.mp hraw with hold | hnew
  · exact .inl hold
  · exact .inr (List.mem_of_mem_tail hnew)

/-- The first ordered retained-bypass candidate introduces no new support. -/
theorem orderedBypassedPair_firstSupportContained
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    SupportContainedInAssemblyPair oldAssembly newAssembly
      (orderedBypassedPair oldAssembly newAssembly).firstRail.support := by
  intro face hface
  rcases bypass_append_support_contained oldAssembly.firstRail
      newAssembly.firstRail face hface with hold | hnew
  · exact .inl hold
  · exact .inr (.inr (.inl hnew))

/-- The second ordered retained-bypass candidate introduces no new support. -/
theorem orderedBypassedPair_secondSupportContained
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    SupportContainedInAssemblyPair oldAssembly newAssembly
      (orderedBypassedPair oldAssembly newAssembly).secondRail.support := by
  intro face hface
  rcases bypass_append_support_contained oldAssembly.secondRail
      newAssembly.secondRail face hface with hold | hnew
  · exact .inr (.inl hold)
  · exact .inr (.inr (.inr hnew))

/-- The first crossed retained-bypass candidate also introduces no new
support; only the suffix track used by the first output is exchanged. -/
theorem crossedBypassedPair_firstSupportContained
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    SupportContainedInAssemblyPair oldAssembly newAssembly
      (crossedBypassedPair oldAssembly newAssembly).firstRail.support := by
  intro face hface
  rcases bypass_append_support_contained oldAssembly.firstRail
      newAssembly.secondRail face hface with hold | hnew
  · exact .inl hold
  · exact .inr (.inr (.inr hnew))

/-- The second crossed retained-bypass candidate introduces no new support. -/
theorem crossedBypassedPair_secondSupportContained
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    SupportContainedInAssemblyPair oldAssembly newAssembly
      (crossedBypassedPair oldAssembly newAssembly).secondRail.support := by
  intro face hface
  rcases bypass_append_support_contained oldAssembly.secondRail
      newAssembly.firstRail face hface with hold | hnew
  · exact .inr (.inl hold)
  · exact .inr (.inr (.inl hnew))

/-- A support uses one named old track and one named new track.  This is the
track-sensitive refinement of `SupportContainedInAssemblyPair`. -/
def SupportContainedInTrackPair
    (oldSupport newSupport support : List (SelectedFace (web := web))) : Prop :=
  ∀ face ∈ support, face ∈ oldSupport ∨ face ∈ newSupport

/-- Ordered composition preserves first-to-first and second-to-second track
provenance after loop erasure. -/
def AssemblySupportContainedInOrderedTrackPairs
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (firstSupport secondSupport : List (SelectedFace (web := web))) : Prop :=
  SupportContainedInTrackPair oldAssembly.firstRail.support
      newAssembly.firstRail.support firstSupport ∧
    SupportContainedInTrackPair oldAssembly.secondRail.support
      newAssembly.secondRail.support secondSupport

/-- Crossed composition preserves first-to-second and second-to-first track
provenance after loop erasure. -/
def AssemblySupportContainedInCrossedTrackPairs
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (firstSupport secondSupport : List (SelectedFace (web := web))) : Prop :=
  SupportContainedInTrackPair oldAssembly.firstRail.support
      newAssembly.secondRail.support firstSupport ∧
    SupportContainedInTrackPair oldAssembly.secondRail.support
      newAssembly.firstRail.support secondSupport

/-- Both ordered bypassed rails retain their individual track pairs. -/
theorem orderedBypassedPair_supportContainedInOrderedTrackPairs
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    AssemblySupportContainedInOrderedTrackPairs oldAssembly newAssembly
      (orderedBypassedPair oldAssembly newAssembly).firstRail.support
      (orderedBypassedPair oldAssembly newAssembly).secondRail.support := by
  constructor
  · intro face hface
    exact bypass_append_support_contained oldAssembly.firstRail
      newAssembly.firstRail face hface
  · intro face hface
    exact bypass_append_support_contained oldAssembly.secondRail
      newAssembly.secondRail face hface

/-- Both crossed bypassed rails retain their individual track pairs. -/
theorem crossedBypassedPair_supportContainedInCrossedTrackPairs
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    AssemblySupportContainedInCrossedTrackPairs oldAssembly newAssembly
      (crossedBypassedPair oldAssembly newAssembly).firstRail.support
      (crossedBypassedPair oldAssembly newAssembly).secondRail.support := by
  constructor
  · intro face hface
    exact bypass_append_support_contained oldAssembly.firstRail
      newAssembly.secondRail face hface
  · intro face hface
    exact bypass_append_support_contained oldAssembly.secondRail
      newAssembly.firstRail face hface

/-- An output edge uses one named old track or one named new track.  This is
the edge-level analogue of `SupportContainedInTrackPair`. -/
def EdgeContainedInTrackPair
    (oldEdges newEdges edges : List (Sym2 (SelectedFace (web := web)))) : Prop :=
  ∀ edge ∈ edges, edge ∈ oldEdges ∨ edge ∈ newEdges

/-- Ordered composition preserves the edge provenance of both output rails. -/
def AssemblyEdgesContainedInOrderedTrackPairs
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (firstEdges secondEdges : List (Sym2 (SelectedFace (web := web)))) : Prop :=
  EdgeContainedInTrackPair oldAssembly.firstRail.edges
      newAssembly.firstRail.edges firstEdges ∧
    EdgeContainedInTrackPair oldAssembly.secondRail.edges
      newAssembly.secondRail.edges secondEdges

/-- Crossed composition preserves the corresponding crossed edge pairing. -/
def AssemblyEdgesContainedInCrossedTrackPairs
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (firstEdges secondEdges : List (Sym2 (SelectedFace (web := web)))) : Prop :=
  EdgeContainedInTrackPair oldAssembly.firstRail.edges
      newAssembly.secondRail.edges firstEdges ∧
    EdgeContainedInTrackPair oldAssembly.secondRail.edges
      newAssembly.firstRail.edges secondEdges

private theorem bypass_append_edges_contained
    {start middle finish : SelectedFace (web := web)}
    (oldWalk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk start middle)
    (newWalk : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk middle finish) :
    EdgeContainedInTrackPair oldWalk.edges newWalk.edges
      (oldWalk.append newWalk).bypass.edges := by
  intro edge hedge
  have hraw := (oldWalk.append newWalk).edges_bypass_subset_edges hedge
  rw [SimpleGraph.Walk.edges_append] at hraw
  exact List.mem_append.mp hraw

/-- Both ordered bypassed rails retain the edge lists of their named track
pairs; loop erasure deletes edges but creates none. -/
theorem orderedBypassedPair_edgesContainedInOrderedTrackPairs
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    AssemblyEdgesContainedInOrderedTrackPairs oldAssembly newAssembly
      (orderedBypassedPair oldAssembly newAssembly).firstRail.edges
      (orderedBypassedPair oldAssembly newAssembly).secondRail.edges := by
  exact ⟨bypass_append_edges_contained oldAssembly.firstRail
      newAssembly.firstRail,
    bypass_append_edges_contained oldAssembly.secondRail newAssembly.secondRail⟩

/-- Both crossed bypassed rails retain the corresponding crossed track-edge
pairs. -/
theorem crossedBypassedPair_edgesContainedInCrossedTrackPairs
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    AssemblyEdgesContainedInCrossedTrackPairs oldAssembly newAssembly
      (crossedBypassedPair oldAssembly newAssembly).firstRail.edges
      (crossedBypassedPair oldAssembly newAssembly).secondRail.edges := by
  exact ⟨bypass_append_edges_contained oldAssembly.firstRail
      newAssembly.secondRail,
    bypass_append_edges_contained oldAssembly.secondRail newAssembly.firstRail⟩

/-- Track-sensitive provenance predicate on the ordered retained classifier.
Collision branches already retain their exact cross origin. -/
def ClassifiedRetainedBypassAppendOutcome.HasTrackProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish}
    (outcome : ClassifiedRetainedBypassAppendOutcome oldAssembly newAssembly) : Prop :=
  match outcome with
  | .assembled assembly =>
      AssemblySupportContainedInOrderedTrackPairs oldAssembly newAssembly
        assembly.firstRail.support assembly.secondRail.support
  | .collision _ => True

/-- The canonical ordered retained classifier preserves the named track
pairs, not merely their four-way union. -/
theorem classifyRetainedBypassAppend_hasTrackProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    (classifyRetainedBypassAppend oldAssembly newAssembly).HasTrackProvenance := by
  classical
  unfold classifyRetainedBypassAppend
  dsimp
  split
  · exact orderedBypassedPair_supportContainedInOrderedTrackPairs
      oldAssembly newAssembly
  · trivial

/-- Track-sensitive provenance predicate on the crossed retained classifier. -/
def ClassifiedCrossedRetainedBypassAppendOutcome.HasTrackProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish}
    (outcome : ClassifiedCrossedRetainedBypassAppendOutcome
      oldAssembly newAssembly) : Prop :=
  match outcome with
  | .assembled assembly =>
      AssemblySupportContainedInCrossedTrackPairs oldAssembly newAssembly
        assembly.firstRail.support assembly.secondRail.support
  | .collision _ => True

/-- The canonical crossed retained classifier preserves the named track
pairs, not merely their four-way union. -/
theorem classifyCrossedRetainedBypassAppend_hasTrackProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    (classifyCrossedRetainedBypassAppend oldAssembly newAssembly
      |>.HasTrackProvenance) := by
  classical
  unfold classifyCrossedRetainedBypassAppend
  dsimp
  split
  · exact crossedBypassedPair_supportContainedInCrossedTrackPairs
      oldAssembly newAssembly
  · trivial

/-- Edge-sensitive provenance predicate on the ordered retained classifier. -/
def ClassifiedRetainedBypassAppendOutcome.HasTrackEdgeProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish}
    (outcome : ClassifiedRetainedBypassAppendOutcome oldAssembly newAssembly) : Prop :=
  match outcome with
  | .assembled assembly =>
      AssemblyEdgesContainedInOrderedTrackPairs oldAssembly newAssembly
        assembly.firstRail.edges assembly.secondRail.edges
  | .collision _ => True

/-- The ordered classifier preserves edge-level track provenance. -/
theorem classifyRetainedBypassAppend_hasTrackEdgeProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    (classifyRetainedBypassAppend oldAssembly newAssembly
      |>.HasTrackEdgeProvenance) := by
  classical
  unfold classifyRetainedBypassAppend
  dsimp
  split
  · exact orderedBypassedPair_edgesContainedInOrderedTrackPairs
      oldAssembly newAssembly
  · trivial

/-- Edge-sensitive provenance predicate on the crossed retained classifier. -/
def ClassifiedCrossedRetainedBypassAppendOutcome.HasTrackEdgeProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish}
    (outcome : ClassifiedCrossedRetainedBypassAppendOutcome
      oldAssembly newAssembly) : Prop :=
  match outcome with
  | .assembled assembly =>
      AssemblyEdgesContainedInCrossedTrackPairs oldAssembly newAssembly
        assembly.firstRail.edges assembly.secondRail.edges
  | .collision _ => True

/-- The crossed classifier preserves edge-level track provenance. -/
theorem classifyCrossedRetainedBypassAppend_hasTrackEdgeProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    (classifyCrossedRetainedBypassAppend oldAssembly newAssembly
      |>.HasTrackEdgeProvenance) := by
  classical
  unfold classifyCrossedRetainedBypassAppend
  dsimp
  split
  · exact crossedBypassedPair_edgesContainedInCrossedTrackPairs
      oldAssembly newAssembly
  · trivial

/-- Provenance predicate on the ordered retained classifier.  Collision
branches already carry their exact cross origin, while successful branches
must retain support containment. -/
def ClassifiedRetainedBypassAppendOutcome.HasSupportProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish}
    (outcome : ClassifiedRetainedBypassAppendOutcome oldAssembly newAssembly) : Prop :=
  match outcome with
  | .assembled assembly =>
      AssemblySupportContainedInAssemblyPair oldAssembly newAssembly assembly
  | .collision _ => True

/-- The canonical ordered retained classifier preserves support provenance. -/
theorem classifyRetainedBypassAppend_hasSupportProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    (classifyRetainedBypassAppend oldAssembly newAssembly).HasSupportProvenance := by
  classical
  unfold classifyRetainedBypassAppend
  dsimp
  split
  · exact ⟨orderedBypassedPair_firstSupportContained oldAssembly newAssembly,
      orderedBypassedPair_secondSupportContained oldAssembly newAssembly⟩
  · trivial

/-- Provenance predicate on the crossed retained classifier. -/
def ClassifiedCrossedRetainedBypassAppendOutcome.HasSupportProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish}
    (outcome : ClassifiedCrossedRetainedBypassAppendOutcome oldAssembly newAssembly) : Prop :=
  match outcome with
  | .assembled assembly =>
      AssemblySupportContainedInAssemblyPair oldAssembly newAssembly assembly
  | .collision _ => True

/-- The canonical crossed retained classifier preserves support provenance. -/
theorem classifyCrossedRetainedBypassAppend_hasSupportProvenance
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    (classifyCrossedRetainedBypassAppend oldAssembly newAssembly).HasSupportProvenance := by
  classical
  unfold classifyCrossedRetainedBypassAppend
  dsimp
  split
  · exact ⟨crossedBypassedPair_firstSupportContained oldAssembly newAssembly,
      crossedBypassedPair_secondSupportContained oldAssembly newAssembly⟩
  · trivial

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
