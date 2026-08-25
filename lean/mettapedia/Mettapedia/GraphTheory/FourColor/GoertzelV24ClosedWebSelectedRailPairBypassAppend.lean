import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAssemblyAppend
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedRailPairAppendClassification

/-!
# L1: loop-erased composition of two selected rail-pair assemblies

Ordinary assembly append tests four old/new support interactions.  Two are
same-track tests used only to prove that the raw concatenations are paths.
Loop erasure discharges those two tests constructively for arbitrary input
assemblies.  The exact alternative below therefore returns either a composed
pair or one of the two genuine cross-track collisions.

This is generic walk algebra.  It does not show that the remaining cross-track
collisions are absent in a source corridor, iterate a terminal window, attach
an annular end cap, or close Fable flag L1.
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

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A genuine cross-track collision between two ordered rail pairs. -/
inductive SelectedRailPairCrossCollision
    (oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))) : Type (u + 1)
  | firstSecond
      (collision : SelectedRailSupportCollision (web := web)
        oldFirst newSecond.tail)
  | secondFirst
      (collision : SelectedRailSupportCollision (web := web)
        oldSecond newFirst.tail)

/-- The literal common face of a cross-track collision. -/
def SelectedRailPairCrossCollision.face
    {oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))}
    (collision : SelectedRailPairCrossCollision
      oldFirst oldSecond newFirst newSecond) : SelectedFace (web := web) :=
  match collision with
  | .firstSecond witness => witness.face
  | .secondFirst witness => witness.face

/-- The collision face belongs to one old rail. -/
theorem SelectedRailPairCrossCollision.face_mem_old
    {oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))}
    (collision : SelectedRailPairCrossCollision
      oldFirst oldSecond newFirst newSecond) :
    collision.face ∈ oldFirst ∨ collision.face ∈ oldSecond := by
  cases collision with
  | firstSecond witness => exact Or.inl witness.mem_old
  | secondFirst witness => exact Or.inr witness.mem_old

/-- The collision face belongs to the opposite complete new rail. -/
theorem SelectedRailPairCrossCollision.face_mem_new
    {oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))}
    (collision : SelectedRailPairCrossCollision
      oldFirst oldSecond newFirst newSecond) :
    collision.face ∈ newFirst ∨ collision.face ∈ newSecond := by
  cases collision with
  | firstSecond witness =>
      exact Or.inr (List.mem_of_mem_tail witness.mem_new)
  | secondFirst witness =>
      exact Or.inl (List.mem_of_mem_tail witness.mem_new)

/-- A two-way cross collision is the corresponding branch of the earlier
four-way append classifier. -/
def SelectedRailPairCrossCollision.toAppendCollision
    {oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))}
    (collision : SelectedRailPairCrossCollision
      oldFirst oldSecond newFirst newSecond) :
    SelectedRailPairAppendCollision (web := web)
      oldFirst oldSecond newFirst newSecond :=
  match collision with
  | .firstSecond witness => .firstSecondCollision witness
  | .secondFirst witness => .secondFirstCollision witness

namespace SelectedSourceLocalRailAssembly

/-- Append ordered rail pairs and erase every same-track revisit.  The two
remaining premises are exactly mutual cross-track separation. -/
noncomputable def appendAssemblyBypass
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (hfirstSecond : oldAssembly.firstRail.support.Disjoint
      newAssembly.secondRail.support.tail)
    (hsecondFirst : oldAssembly.secondRail.support.Disjoint
      newAssembly.firstRail.support.tail) :
    SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish where
  firstRail := (oldAssembly.firstRail.append newAssembly.firstRail).bypass
  secondRail := (oldAssembly.secondRail.append newAssembly.secondRail).bypass
  firstRail_isPath :=
    (oldAssembly.firstRail.append newAssembly.firstRail).bypass_isPath
  secondRail_isPath :=
    (oldAssembly.secondRail.append newAssembly.secondRail).bypass_isPath
  firstRail_support_disjoint_secondRail := by
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hfirstRaw :=
      (oldAssembly.firstRail.append newAssembly.firstRail
        |>.support_bypass_subset_support) hfirst
    have hsecondRaw :=
      (oldAssembly.secondRail.append newAssembly.secondRail
        |>.support_bypass_subset_support) hsecond
    rw [SimpleGraph.Walk.support_append] at hfirstRaw hsecondRaw
    rcases List.mem_append.mp hfirstRaw with hfirstOld | hfirstNew
    · rcases List.mem_append.mp hsecondRaw with hsecondOld | hsecondNew
      · exact (List.disjoint_left.mp
          oldAssembly.firstRail_support_disjoint_secondRail hfirstOld) hsecondOld
      · exact (List.disjoint_left.mp hfirstSecond hfirstOld) hsecondNew
    · rcases List.mem_append.mp hsecondRaw with hsecondOld | hsecondNew
      · exact (List.disjoint_left.mp hsecondFirst hsecondOld) hfirstNew
      · have hfirstFull : face ∈ newAssembly.firstRail.support :=
          List.mem_of_mem_tail hfirstNew
        have hsecondFull : face ∈ newAssembly.secondRail.support :=
          List.mem_of_mem_tail hsecondNew
        exact (List.disjoint_left.mp
          newAssembly.firstRail_support_disjoint_secondRail hfirstFull) hsecondFull

/-- Outcome of the ordered loop-erased append. -/
inductive ClassifiedBypassAppendOutcome
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) : Type (u + 1)
  | assembled
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart firstFinish secondFinish)
  | collision
      (witness : SelectedRailPairCrossCollision (web := web)
        oldAssembly.firstRail.support oldAssembly.secondRail.support
        newAssembly.firstRail.support newAssembly.secondRail.support)

/-- **L1 generic loop-erased transition.** Same-track collisions are always
removed; failure retains an actual cross-track common face. -/
noncomputable def classifyAndAppendBypass
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    ClassifiedBypassAppendOutcome oldAssembly newAssembly := by
  classical
  by_cases hfirstSecond : oldAssembly.firstRail.support.Disjoint
      newAssembly.secondRail.support.tail
  · by_cases hsecondFirst : oldAssembly.secondRail.support.Disjoint
        newAssembly.firstRail.support.tail
    · exact .assembled (appendAssemblyBypass oldAssembly newAssembly
        hfirstSecond hsecondFirst)
    · exact .collision (.secondFirst
        (SelectedRailSupportCollision.of_not_disjoint hsecondFirst))
  · exact .collision (.firstSecond
      (SelectedRailSupportCollision.of_not_disjoint hfirstSecond))

/-- Append across exchanged middle endpoint order and erase same-track
revisits. -/
noncomputable def appendAssemblyCrossedBypass
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (hfirstSecond : oldAssembly.firstRail.support.Disjoint
      newAssembly.firstRail.support.tail)
    (hsecondFirst : oldAssembly.secondRail.support.Disjoint
      newAssembly.secondRail.support.tail) :
    SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart secondFinish firstFinish where
  firstRail := (oldAssembly.firstRail.append newAssembly.secondRail).bypass
  secondRail := (oldAssembly.secondRail.append newAssembly.firstRail).bypass
  firstRail_isPath :=
    (oldAssembly.firstRail.append newAssembly.secondRail).bypass_isPath
  secondRail_isPath :=
    (oldAssembly.secondRail.append newAssembly.firstRail).bypass_isPath
  firstRail_support_disjoint_secondRail := by
    rw [List.disjoint_left]
    intro face hfirst hsecond
    have hfirstRaw :=
      (oldAssembly.firstRail.append newAssembly.secondRail
        |>.support_bypass_subset_support) hfirst
    have hsecondRaw :=
      (oldAssembly.secondRail.append newAssembly.firstRail
        |>.support_bypass_subset_support) hsecond
    rw [SimpleGraph.Walk.support_append] at hfirstRaw hsecondRaw
    rcases List.mem_append.mp hfirstRaw with hfirstOld | hsecondNew
    · rcases List.mem_append.mp hsecondRaw with hsecondOld | hfirstNew
      · exact (List.disjoint_left.mp
          oldAssembly.firstRail_support_disjoint_secondRail hfirstOld) hsecondOld
      · exact (List.disjoint_left.mp hfirstSecond hfirstOld) hfirstNew
    · rcases List.mem_append.mp hsecondRaw with hsecondOld | hfirstNew
      · exact (List.disjoint_left.mp hsecondFirst hsecondOld) hsecondNew
      · have hfirstFull : face ∈ newAssembly.firstRail.support :=
          List.mem_of_mem_tail hfirstNew
        have hsecondFull : face ∈ newAssembly.secondRail.support :=
          List.mem_of_mem_tail hsecondNew
        exact (List.disjoint_left.mp
          newAssembly.firstRail_support_disjoint_secondRail hfirstFull) hsecondFull

/-- Outcome of the crossed loop-erased append. -/
inductive ClassifiedCrossedBypassAppendOutcome
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
      (witness : SelectedRailPairCrossCollision (web := web)
        oldAssembly.firstRail.support oldAssembly.secondRail.support
        newAssembly.secondRail.support newAssembly.firstRail.support)

/-- Crossed counterpart of `classifyAndAppendBypass`. -/
noncomputable def classifyAndAppendCrossedBypass
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (oldAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (newAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    ClassifiedCrossedBypassAppendOutcome oldAssembly newAssembly := by
  classical
  by_cases hfirstSecond : oldAssembly.firstRail.support.Disjoint
      newAssembly.firstRail.support.tail
  · by_cases hsecondFirst : oldAssembly.secondRail.support.Disjoint
        newAssembly.secondRail.support.tail
    · exact .assembled (appendAssemblyCrossedBypass oldAssembly newAssembly
        hfirstSecond hsecondFirst)
    · exact .collision (.secondFirst
        (SelectedRailSupportCollision.of_not_disjoint hsecondFirst))
  · exact .collision (.firstSecond
      (SelectedRailSupportCollision.of_not_disjoint hfirstSecond))

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
