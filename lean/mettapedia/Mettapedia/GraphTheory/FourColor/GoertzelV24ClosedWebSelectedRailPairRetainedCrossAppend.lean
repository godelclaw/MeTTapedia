import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairBypassAppend

/-!
# L1: classify only cross collisions retained after loop erasure

The raw cross-support test is conservative: its common face may itself be
deleted by loop erasure.  Here both same-track concatenations are bypassed
first, and disjointness is decided on the two final simple paths.  A bad branch
therefore carries a face retained by both output candidates.  Its raw origins
are necessarily cross-track because the two input pairs are internally
disjoint.

This is still an alternative, not a collision repair or L1 closure.
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

/-- The two endpoint-correct simple candidate paths obtained before testing
their mutual separation. -/
structure BypassedSelectedRailPair
    (firstStart secondStart firstFinish secondFinish : SelectedFace (web := web))
    where
  firstRail :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
      firstStart firstFinish
  secondRail :
    (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Walk
      secondStart secondFinish
  firstRail_isPath : firstRail.IsPath
  secondRail_isPath : secondRail.IsPath

/-- Ordered bypass candidate, with no mutual-disjointness premise. -/
noncomputable def orderedBypassedPair
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    BypassedSelectedRailPair (web := web)
      firstStart secondStart firstFinish secondFinish where
  firstRail := (oldAssembly.firstRail.append newAssembly.firstRail).bypass
  secondRail := (oldAssembly.secondRail.append newAssembly.secondRail).bypass
  firstRail_isPath :=
    (oldAssembly.firstRail.append newAssembly.firstRail).bypass_isPath
  secondRail_isPath :=
    (oldAssembly.secondRail.append newAssembly.secondRail).bypass_isPath

/-- Crossed-order bypass candidate. -/
noncomputable def crossedBypassedPair
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    BypassedSelectedRailPair (web := web)
      firstStart secondStart secondFinish firstFinish where
  firstRail := (oldAssembly.firstRail.append newAssembly.secondRail).bypass
  secondRail := (oldAssembly.secondRail.append newAssembly.firstRail).bypass
  firstRail_isPath :=
    (oldAssembly.firstRail.append newAssembly.secondRail).bypass_isPath
  secondRail_isPath :=
    (oldAssembly.secondRail.append newAssembly.firstRail).bypass_isPath

/-- Exact cross-track raw origin of a collision retained by both bypassed
candidates. -/
inductive RetainedCrossOrigin
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (face : SelectedFace (web := web)) : Type (u + 1)
  | firstSecond
      (hold : face ∈ oldAssembly.firstRail.support)
      (hnew : face ∈ newAssembly.secondRail.support.tail)
  | secondFirst
      (hold : face ∈ oldAssembly.secondRail.support)
      (hnew : face ∈ newAssembly.firstRail.support.tail)

/-- A collision retained after loop erasure, together with its cross origin. -/
structure RetainedBypassCrossCollision
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) where
  face : SelectedFace (web := web)
  mem_first : face ∈ (orderedBypassedPair oldAssembly newAssembly).firstRail.support
  mem_second : face ∈ (orderedBypassedPair oldAssembly newAssembly).secondRail.support
  origin : RetainedCrossOrigin oldAssembly newAssembly face

private theorem path_start_not_mem_support_tail
    {F : Type*} {H : SimpleGraph F} {start finish : F}
    (walk : H.Walk start finish) (hpath : walk.IsPath) :
    start ∉ walk.support.tail := by
  have hnodup := hpath.support_nodup
  rw [← walk.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

/-- A retained ordered collision is distinct from the first suffix start. -/
theorem RetainedBypassCrossCollision.face_ne_newFirstStart
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish}
    (collision : RetainedBypassCrossCollision oldAssembly newAssembly) :
    collision.face ≠ middleFirst := by
  intro hface
  cases collision.origin with
  | firstSecond hold hnew =>
      have hfirst : collision.face ∈ newAssembly.firstRail.support := by
        simpa [hface] using newAssembly.firstRail.start_mem_support
      exact (List.disjoint_left.mp
        newAssembly.firstRail_support_disjoint_secondRail hfirst)
          (List.mem_of_mem_tail hnew)
  | secondFirst hold hnew =>
      exact path_start_not_mem_support_tail newAssembly.firstRail
        newAssembly.firstRail_isPath (by simpa [hface] using hnew)

/-- A retained ordered collision is distinct from the second suffix start. -/
theorem RetainedBypassCrossCollision.face_ne_newSecondStart
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish}
    (collision : RetainedBypassCrossCollision oldAssembly newAssembly) :
    collision.face ≠ middleSecond := by
  intro hface
  cases collision.origin with
  | firstSecond hold hnew =>
      exact path_start_not_mem_support_tail newAssembly.secondRail
        newAssembly.secondRail_isPath (by simpa [hface] using hnew)
  | secondFirst hold hnew =>
      have hsecond : collision.face ∈ newAssembly.secondRail.support := by
        simpa [hface] using newAssembly.secondRail.start_mem_support
      exact (List.disjoint_left.mp
        newAssembly.firstRail_support_disjoint_secondRail
          (List.mem_of_mem_tail hnew)) hsecond

/-- Forget survival through bypass and retain the exact raw cross-support
witness consumed by the source-local geometry. -/
def RetainedBypassCrossCollision.toRawCrossCollision
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish}
    (collision : RetainedBypassCrossCollision oldAssembly newAssembly) :
    SelectedRailPairCrossCollision (web := web)
      oldAssembly.firstRail.support oldAssembly.secondRail.support
      newAssembly.firstRail.support newAssembly.secondRail.support :=
  match collision.origin with
  | .firstSecond hold hnew =>
      .firstSecond ⟨collision.face, hold, hnew⟩
  | .secondFirst hold hnew =>
      .secondFirst ⟨collision.face, hold, hnew⟩

@[simp] theorem RetainedBypassCrossCollision.toRawCrossCollision_face
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish}
    (collision : RetainedBypassCrossCollision oldAssembly newAssembly) :
    collision.toRawCrossCollision.face = collision.face := by
  cases collision with
  | mk face memFirst memSecond origin => cases origin <;> rfl

/-- Any actual collision of the two ordered bypass candidates has a
cross-track raw origin. -/
noncomputable def retainedCrossOrigin_of_orderedBypassCollision
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    {face : SelectedFace (web := web)}
    (hfirst : face ∈ (orderedBypassedPair oldAssembly newAssembly).firstRail.support)
    (hsecond : face ∈ (orderedBypassedPair oldAssembly newAssembly).secondRail.support) :
    RetainedCrossOrigin oldAssembly newAssembly face := by
  classical
  have hfirstRaw :=
    (oldAssembly.firstRail.append newAssembly.firstRail
      |>.support_bypass_subset_support) hfirst
  have hsecondRaw :=
    (oldAssembly.secondRail.append newAssembly.secondRail
      |>.support_bypass_subset_support) hsecond
  rw [SimpleGraph.Walk.support_append] at hfirstRaw hsecondRaw
  by_cases hfirstOld : face ∈ oldAssembly.firstRail.support
  · by_cases hsecondOld : face ∈ oldAssembly.secondRail.support
    · exact False.elim ((List.disjoint_left.mp
        oldAssembly.firstRail_support_disjoint_secondRail hfirstOld) hsecondOld)
    · exact .firstSecond hfirstOld
        ((List.mem_append.mp hsecondRaw).resolve_left hsecondOld)
  · have hfirstNew : face ∈ newAssembly.firstRail.support.tail :=
      (List.mem_append.mp hfirstRaw).resolve_left hfirstOld
    by_cases hsecondOld : face ∈ oldAssembly.secondRail.support
    · exact .secondFirst hsecondOld hfirstNew
    · have hsecondNew : face ∈ newAssembly.secondRail.support.tail :=
        (List.mem_append.mp hsecondRaw).resolve_left hsecondOld
      have hfirstFull : face ∈ newAssembly.firstRail.support :=
        List.mem_of_mem_tail hfirstNew
      have hsecondFull : face ∈ newAssembly.secondRail.support :=
        List.mem_of_mem_tail hsecondNew
      exact False.elim ((List.disjoint_left.mp
        newAssembly.firstRail_support_disjoint_secondRail hfirstFull) hsecondFull)

/-- Final ordered outcome after testing the supports which actually survive
loop erasure. -/
inductive ClassifiedRetainedBypassAppendOutcome
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) : Type (u + 1)
  | assembled
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart firstFinish secondFinish)
  | collision (witness : RetainedBypassCrossCollision oldAssembly newAssembly)

/-- **L1 retained-collision classifier.** The bad branch contains only a face
which survives in both final simple paths. -/
noncomputable def classifyRetainedBypassAppend
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    ClassifiedRetainedBypassAppendOutcome oldAssembly newAssembly := by
  classical
  let pair := orderedBypassedPair oldAssembly newAssembly
  by_cases hdisjoint : pair.firstRail.support.Disjoint pair.secondRail.support
  · exact .assembled
      { firstRail := pair.firstRail
        secondRail := pair.secondRail
        firstRail_isPath := pair.firstRail_isPath
        secondRail_isPath := pair.secondRail_isPath
        firstRail_support_disjoint_secondRail := hdisjoint }
  · let collision : SelectedRailSupportCollision (web := web)
        pair.firstRail.support pair.secondRail.support :=
      SelectedRailSupportCollision.of_not_disjoint hdisjoint
    exact .collision
      { face := collision.face
        mem_first := collision.mem_old
        mem_second := collision.mem_new
        origin := retainedCrossOrigin_of_orderedBypassCollision
          oldAssembly newAssembly collision.mem_old collision.mem_new }

/-- Raw cross origin in the exchanged-middle endpoint order.  The first
candidate follows the new second rail and the second candidate follows the
new first rail, so the surviving cross terms are old-first/new-first and
old-second/new-second. -/
inductive CrossedRetainedCrossOrigin
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (face : SelectedFace (web := web)) : Type (u + 1)
  | firstFirst
      (hold : face ∈ oldAssembly.firstRail.support)
      (hnew : face ∈ newAssembly.firstRail.support.tail)
  | secondSecond
      (hold : face ∈ oldAssembly.secondRail.support)
      (hnew : face ∈ newAssembly.secondRail.support.tail)

/-- A collision retained by both crossed-order bypass candidates. -/
structure CrossedRetainedBypassCrossCollision
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) where
  face : SelectedFace (web := web)
  mem_first : face ∈ (crossedBypassedPair oldAssembly newAssembly).firstRail.support
  mem_second : face ∈ (crossedBypassedPair oldAssembly newAssembly).secondRail.support
  origin : CrossedRetainedCrossOrigin oldAssembly newAssembly face

/-- A retained crossed-order collision is distinct from the first suffix
rail's start (`middleSecond` in exchanged endpoint order). -/
theorem CrossedRetainedBypassCrossCollision.face_ne_newFirstStart
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish}
    (collision : CrossedRetainedBypassCrossCollision oldAssembly newAssembly) :
    collision.face ≠ middleSecond := by
  intro hface
  cases collision.origin with
  | firstFirst hold hnew =>
      exact path_start_not_mem_support_tail newAssembly.firstRail
        newAssembly.firstRail_isPath (by simpa [hface] using hnew)
  | secondSecond hold hnew =>
      have hfirst : collision.face ∈ newAssembly.firstRail.support := by
        rw [hface]
        exact newAssembly.firstRail.start_mem_support
      exact (List.disjoint_left.mp
        newAssembly.firstRail_support_disjoint_secondRail hfirst)
          (List.mem_of_mem_tail hnew)

/-- A retained crossed-order collision is also distinct from the second
suffix rail's start (`middleFirst`). -/
theorem CrossedRetainedBypassCrossCollision.face_ne_newSecondStart
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish}
    (collision : CrossedRetainedBypassCrossCollision oldAssembly newAssembly) :
    collision.face ≠ middleFirst := by
  intro hface
  cases collision.origin with
  | firstFirst hold hnew =>
      have hfirst : collision.face ∈ newAssembly.firstRail.support :=
        List.mem_of_mem_tail hnew
      have hsecond : collision.face ∈ newAssembly.secondRail.support := by
        simpa [hface] using newAssembly.secondRail.start_mem_support
      exact (List.disjoint_left.mp
        newAssembly.firstRail_support_disjoint_secondRail hfirst) hsecond
  | secondSecond hold hnew =>
      exact path_start_not_mem_support_tail newAssembly.secondRail
        newAssembly.secondRail_isPath (by simpa [hface] using hnew)

/-- Crossed-order retained collisions likewise project to the generic raw
cross witness after the suffix pair is viewed in continuation order. -/
def CrossedRetainedBypassCrossCollision.toRawCrossCollision
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish}
    (collision : CrossedRetainedBypassCrossCollision oldAssembly newAssembly) :
    SelectedRailPairCrossCollision (web := web)
      oldAssembly.firstRail.support oldAssembly.secondRail.support
      newAssembly.secondRail.support newAssembly.firstRail.support :=
  match collision.origin with
  | .firstFirst hold hnew =>
      .firstSecond ⟨collision.face, hold, hnew⟩
  | .secondSecond hold hnew =>
      .secondFirst ⟨collision.face, hold, hnew⟩

@[simp] theorem CrossedRetainedBypassCrossCollision.toRawCrossCollision_face
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    {oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond}
    {newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish}
    (collision : CrossedRetainedBypassCrossCollision oldAssembly newAssembly) :
    collision.toRawCrossCollision.face = collision.face := by
  cases collision with
  | mk face memFirst memSecond origin => cases origin <;> rfl

/-- A retained crossed-order collision has one of the two exact cross raw
origins. -/
noncomputable def crossedRetainedCrossOrigin_of_bypassCollision
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    {face : SelectedFace (web := web)}
    (hfirst : face ∈ (crossedBypassedPair oldAssembly newAssembly).firstRail.support)
    (hsecond : face ∈ (crossedBypassedPair oldAssembly newAssembly).secondRail.support) :
    CrossedRetainedCrossOrigin oldAssembly newAssembly face := by
  classical
  have hfirstRaw :=
    (oldAssembly.firstRail.append newAssembly.secondRail
      |>.support_bypass_subset_support) hfirst
  have hsecondRaw :=
    (oldAssembly.secondRail.append newAssembly.firstRail
      |>.support_bypass_subset_support) hsecond
  rw [SimpleGraph.Walk.support_append] at hfirstRaw hsecondRaw
  by_cases hfirstOld : face ∈ oldAssembly.firstRail.support
  · by_cases hsecondOld : face ∈ oldAssembly.secondRail.support
    · exact False.elim ((List.disjoint_left.mp
        oldAssembly.firstRail_support_disjoint_secondRail hfirstOld) hsecondOld)
    · exact .firstFirst hfirstOld
        ((List.mem_append.mp hsecondRaw).resolve_left hsecondOld)
  · have hsecondNew : face ∈ newAssembly.secondRail.support.tail :=
      (List.mem_append.mp hfirstRaw).resolve_left hfirstOld
    by_cases hsecondOld : face ∈ oldAssembly.secondRail.support
    · exact .secondSecond hsecondOld hsecondNew
    · have hfirstNew : face ∈ newAssembly.firstRail.support.tail :=
        (List.mem_append.mp hsecondRaw).resolve_left hsecondOld
      have hfirstFull : face ∈ newAssembly.firstRail.support :=
        List.mem_of_mem_tail hfirstNew
      have hsecondFull : face ∈ newAssembly.secondRail.support :=
        List.mem_of_mem_tail hsecondNew
      exact False.elim ((List.disjoint_left.mp
        newAssembly.firstRail_support_disjoint_secondRail hfirstFull) hsecondFull)

/-- Final crossed-order outcome after testing the retained supports. -/
inductive ClassifiedCrossedRetainedBypassAppendOutcome
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) : Type (u + 1)
  | assembled
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart secondFinish firstFinish)
  | collision
      (witness : CrossedRetainedBypassCrossCollision oldAssembly newAssembly)

/-- Crossed-order retained-collision classifier. -/
noncomputable def classifyCrossedRetainedBypassAppend
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    ClassifiedCrossedRetainedBypassAppendOutcome oldAssembly newAssembly := by
  classical
  let pair := crossedBypassedPair oldAssembly newAssembly
  by_cases hdisjoint : pair.firstRail.support.Disjoint pair.secondRail.support
  · exact .assembled
      { firstRail := pair.firstRail
        secondRail := pair.secondRail
        firstRail_isPath := pair.firstRail_isPath
        secondRail_isPath := pair.secondRail_isPath
        firstRail_support_disjoint_secondRail := hdisjoint }
  · let collision : SelectedRailSupportCollision (web := web)
        pair.firstRail.support pair.secondRail.support :=
      SelectedRailSupportCollision.of_not_disjoint hdisjoint
    exact .collision
      { face := collision.face
        mem_first := collision.mem_old
        mem_second := collision.mem_new
        origin := crossedRetainedCrossOrigin_of_bypassCollision
          oldAssembly newAssembly collision.mem_old collision.mem_new }

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
