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
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
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
