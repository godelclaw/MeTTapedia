import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailSuccessorCompatibility

/-!
# L1: finite four-way support classifier for appending a rail pair

Appending two ordered rail pairs has exactly four old/new support tests: two
same-track path tests and two cross-track separation tests.  This module
classifies them without losing a failed test behind negation.  Either all four
disjointness proofs are returned, or an actual common face is exhibited for
one failed interaction.

The classifier is generic list algebra.  It does not claim that neighbouring
Cell-3 windows pass the tests, repair a returned collision, construct an
arbitrary-length pair, or close Fable flag L1.
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

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- The four positive support facts needed to append two ordered rail pairs. -/
structure SelectedRailPairAppendCompatibility
    (oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))) : Prop where
  firstPath : oldFirst.Disjoint newFirst.tail
  secondPath : oldSecond.Disjoint newSecond.tail
  firstSecond : oldFirst.Disjoint newSecond.tail
  secondFirst : oldSecond.Disjoint newFirst.tail

/-- A failed old/new rail interaction, carrying its actual common face. -/
inductive SelectedRailPairAppendCollision
    (oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))) : Type (u + 1)
  | firstPathCollision
      (collision : SelectedRailSupportCollision (web := web)
        oldFirst newFirst.tail)
  | secondPathCollision
      (collision : SelectedRailSupportCollision (web := web)
        oldSecond newSecond.tail)
  | firstSecondCollision
      (collision : SelectedRailSupportCollision (web := web)
        oldFirst newSecond.tail)
  | secondFirstCollision
      (collision : SelectedRailSupportCollision (web := web)
        oldSecond newFirst.tail)

/-- Exhaustive positive result of testing the four old/new rail interactions. -/
inductive SelectedRailPairAppendClassification
    (oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))) : Type (u + 1)
  | compatible
      (certificate : SelectedRailPairAppendCompatibility
        oldFirst oldSecond newFirst newSecond)
  | collision
      (witness : SelectedRailPairAppendCollision
        oldFirst oldSecond newFirst newSecond)

/-- Decide the four support tests, returning either their complete positive
certificate or the exact face witnessing the first failed test. -/
noncomputable def classifySelectedRailPairAppend
    (oldFirst oldSecond newFirst newSecond :
      List (SelectedFace (web := web))) :
    SelectedRailPairAppendClassification oldFirst oldSecond newFirst newSecond := by
  classical
  by_cases hfirstPath : oldFirst.Disjoint newFirst.tail
  · by_cases hsecondPath : oldSecond.Disjoint newSecond.tail
    · by_cases hfirstSecond : oldFirst.Disjoint newSecond.tail
      · by_cases hsecondFirst : oldSecond.Disjoint newFirst.tail
        · exact .compatible
            ⟨hfirstPath, hsecondPath, hfirstSecond, hsecondFirst⟩
        · exact .collision (.secondFirstCollision
            (SelectedRailSupportCollision.of_not_disjoint hsecondFirst))
      · exact .collision (.firstSecondCollision
          (SelectedRailSupportCollision.of_not_disjoint hfirstSecond))
    · exact .collision (.secondPathCollision
        (SelectedRailSupportCollision.of_not_disjoint hsecondPath))
  · exact .collision (.firstPathCollision
      (SelectedRailSupportCollision.of_not_disjoint hfirstPath))

namespace SelectedSourceLocalRailAssembly

/-- Ordered assembly append, or the exact failed old/new support interaction. -/
inductive ClassifiedAppendOutcome
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (old : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (new : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) : Type (u + 1)
  | assembled
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart firstFinish secondFinish)
  | collision
      (witness : SelectedRailPairAppendCollision (web := web)
        old.firstRail.support old.secondRail.support
        new.firstRail.support new.secondRail.support)

/-- Test and, exactly in the compatible branch, append two ordered assemblies. -/
noncomputable def classifyAndAppend
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (old : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (new : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish) :
    ClassifiedAppendOutcome old new :=
  match classifySelectedRailPairAppend old.firstRail.support old.secondRail.support
      new.firstRail.support new.secondRail.support with
  | .compatible certificate =>
      .assembled (appendAssembly old new certificate.firstPath certificate.secondPath
        certificate.firstSecond certificate.secondFirst)
  | .collision witness => .collision witness

/-- Crossed-order assembly append, or the exact failed interaction after the
new pair is reordered to follow the old labels. -/
inductive ClassifiedCrossedAppendOutcome
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (old : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (new : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) : Type (u + 1)
  | assembled
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart secondFinish firstFinish)
  | collision
      (witness : SelectedRailPairAppendCollision (web := web)
        old.firstRail.support old.secondRail.support
        new.secondRail.support new.firstRail.support)

/-- Test and, exactly in the compatible branch, append across an exchanged
middle endpoint order. -/
noncomputable def classifyAndAppendCrossed
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (old : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (new : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish) :
    ClassifiedCrossedAppendOutcome old new :=
  match classifySelectedRailPairAppend old.firstRail.support old.secondRail.support
      new.secondRail.support new.firstRail.support with
  | .compatible certificate =>
      .assembled (appendAssemblyCrossed old new certificate.firstPath
        certificate.secondPath certificate.firstSecond certificate.secondFirst)
  | .collision witness => .collision witness

end SelectedSourceLocalRailAssembly

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
