import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailTerminalWindow

/-!
# L1: append two certified selected-rail assemblies

The mutable-window induction needs to separate two jobs.  Local Cell-3
geometry constructs or repairs the terminal window; this file supplies the
pure path algebra which attaches a frozen prefix to whichever repaired pair
the local classifier returns.

All four old/new support conditions stay explicit.  The theorem therefore
does not assert that an arbitrary prefix is compatible with a terminal
window, nor does it construct the finite transition which will discharge
those conditions.  It is the permutation-neutral glue used after that
geometry has been proved, not an arbitrary-length rail or Fable flag L1
closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType

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

/-- Change only the names of an assembly's two starting faces.

Both walks are copied across the supplied equalities; their supports and all
path/separation certificates are unchanged. -/
noncomputable def rebaseAssemblyStart
    {oldFirstStart oldSecondStart newFirstStart newSecondStart
      firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      oldFirstStart oldSecondStart firstFinish secondFinish)
    (hfirst : oldFirstStart = newFirstStart)
    (hsecond : oldSecondStart = newSecondStart) :
    SelectedSourceLocalRailAssembly (web := web)
      newFirstStart newSecondStart firstFinish secondFinish where
  firstRail := assembly.firstRail.copy hfirst rfl
  secondRail := assembly.secondRail.copy hsecond rfl
  firstRail_isPath := by simpa using assembly.firstRail_isPath
  secondRail_isPath := by simpa using assembly.secondRail_isPath
  firstRail_support_disjoint_secondRail := by
    simpa using assembly.firstRail_support_disjoint_secondRail

@[simp] theorem rebaseAssemblyStart_firstRail_support
    {oldFirstStart oldSecondStart newFirstStart newSecondStart
      firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      oldFirstStart oldSecondStart firstFinish secondFinish)
    (hfirst : oldFirstStart = newFirstStart)
    (hsecond : oldSecondStart = newSecondStart) :
    (rebaseAssemblyStart assembly hfirst hsecond).firstRail.support =
      assembly.firstRail.support := by simp [rebaseAssemblyStart]

@[simp] theorem rebaseAssemblyStart_secondRail_support
    {oldFirstStart oldSecondStart newFirstStart newSecondStart
      firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      oldFirstStart oldSecondStart firstFinish secondFinish)
    (hfirst : oldFirstStart = newFirstStart)
    (hsecond : oldSecondStart = newSecondStart) :
    (rebaseAssemblyStart assembly hfirst hsecond).secondRail.support =
      assembly.secondRail.support := by simp [rebaseAssemblyStart]

/-- Rebasing the first starting face changes only endpoint typing, not the
literal first-rail edge list. -/
@[simp] theorem rebaseAssemblyStart_firstRail_edges
    {oldFirstStart oldSecondStart newFirstStart newSecondStart
      firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      oldFirstStart oldSecondStart firstFinish secondFinish)
    (hfirst : oldFirstStart = newFirstStart)
    (hsecond : oldSecondStart = newSecondStart) :
    (rebaseAssemblyStart assembly hfirst hsecond).firstRail.edges =
      assembly.firstRail.edges := by simp [rebaseAssemblyStart]

/-- Rebasing the second starting face likewise preserves the literal
second-rail edge list. -/
@[simp] theorem rebaseAssemblyStart_secondRail_edges
    {oldFirstStart oldSecondStart newFirstStart newSecondStart
      firstFinish secondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      oldFirstStart oldSecondStart firstFinish secondFinish)
    (hfirst : oldFirstStart = newFirstStart)
    (hsecond : oldSecondStart = newSecondStart) :
    (rebaseAssemblyStart assembly hfirst hsecond).secondRail.edges =
      assembly.secondRail.edges := by simp [rebaseAssemblyStart]

/-- Change only the names of an assembly's two finishing faces.

This is the endpoint-symmetric companion of `rebaseAssemblyStart`.  Both
walks are copied across the supplied face equalities; their supports and all
path/separation certificates are unchanged. -/
noncomputable def rebaseAssemblyFinish
    {firstStart secondStart oldFirstFinish oldSecondFinish
      newFirstFinish newSecondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart oldFirstFinish oldSecondFinish)
    (hfirst : oldFirstFinish = newFirstFinish)
    (hsecond : oldSecondFinish = newSecondFinish) :
    SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart newFirstFinish newSecondFinish where
  firstRail := assembly.firstRail.copy rfl hfirst
  secondRail := assembly.secondRail.copy rfl hsecond
  firstRail_isPath := by simpa using assembly.firstRail_isPath
  secondRail_isPath := by simpa using assembly.secondRail_isPath
  firstRail_support_disjoint_secondRail := by
    simpa using assembly.firstRail_support_disjoint_secondRail

@[simp] theorem rebaseAssemblyFinish_firstRail_support
    {firstStart secondStart oldFirstFinish oldSecondFinish
      newFirstFinish newSecondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart oldFirstFinish oldSecondFinish)
    (hfirst : oldFirstFinish = newFirstFinish)
    (hsecond : oldSecondFinish = newSecondFinish) :
    (rebaseAssemblyFinish assembly hfirst hsecond).firstRail.support =
      assembly.firstRail.support := by simp [rebaseAssemblyFinish]

@[simp] theorem rebaseAssemblyFinish_secondRail_support
    {firstStart secondStart oldFirstFinish oldSecondFinish
      newFirstFinish newSecondFinish : SelectedFace (web := web)}
    (assembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart oldFirstFinish oldSecondFinish)
    (hfirst : oldFirstFinish = newFirstFinish)
    (hsecond : oldSecondFinish = newSecondFinish) :
    (rebaseAssemblyFinish assembly hfirst hsecond).secondRail.support =
      assembly.secondRail.support := by simp [rebaseAssemblyFinish]

/-- Append two ordered pairs of selected facial-dual rails.

The same-track premises are exactly the path conditions for the two appended
walks.  The crossed premises, together with the separation already stored in
the two inputs, prove separation of the two complete outputs. -/
noncomputable def appendAssembly
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail) :
    SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart firstFinish secondFinish where
  firstRail := prefixAssembly.firstRail.append suffixAssembly.firstRail
  secondRail := prefixAssembly.secondRail.append suffixAssembly.secondRail
  firstRail_isPath :=
    GoertzelV24DualPathTransversal.walk_append_isPath_of_support_disjoint
      prefixAssembly.firstRail suffixAssembly.firstRail
      prefixAssembly.firstRail_isPath suffixAssembly.firstRail_isPath hfirstPath
  secondRail_isPath :=
    GoertzelV24DualPathTransversal.walk_append_isPath_of_support_disjoint
      prefixAssembly.secondRail suffixAssembly.secondRail
      prefixAssembly.secondRail_isPath suffixAssembly.secondRail_isPath hsecondPath
  firstRail_support_disjoint_secondRail := by
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
      List.disjoint_left]
    intro face hfirst hsecond
    rcases List.mem_append.mp hfirst with hfirstPrefix | hfirstSuffix
    · rcases List.mem_append.mp hsecond with hsecondPrefix | hsecondSuffix
      · exact (List.disjoint_left.mp
          prefixAssembly.firstRail_support_disjoint_secondRail hfirstPrefix)
            hsecondPrefix
      · exact (List.disjoint_left.mp hfirstSecond hfirstPrefix) hsecondSuffix
    · rcases List.mem_append.mp hsecond with hsecondPrefix | hsecondSuffix
      · exact (List.disjoint_left.mp hsecondFirst hsecondPrefix) hfirstSuffix
      · have hfirstFull : face ∈ suffixAssembly.firstRail.support :=
          List.mem_of_mem_tail hfirstSuffix
        have hsecondFull : face ∈ suffixAssembly.secondRail.support :=
          List.mem_of_mem_tail hsecondSuffix
        exact (List.disjoint_left.mp
          suffixAssembly.firstRail_support_disjoint_secondRail hfirstFull) hsecondFull

@[simp] theorem appendAssembly_firstRail
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail) :
    (appendAssembly prefixAssembly suffixAssembly hfirstPath hsecondPath hfirstSecond
      hsecondFirst).firstRail =
      prefixAssembly.firstRail.append suffixAssembly.firstRail := rfl

@[simp] theorem appendAssembly_secondRail
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleFirst middleSecond firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail) :
    (appendAssembly prefixAssembly suffixAssembly hfirstPath hsecondPath hfirstSecond
      hsecondFirst).secondRail =
      prefixAssembly.secondRail.append suffixAssembly.secondRail := rfl

/-- Append two rail assemblies when the middle endpoint order is exchanged.

The first prefix rail continues along the second suffix rail and conversely;
the returned endpoint order is therefore exchanged as well. -/
noncomputable def appendAssemblyCrossed
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail) :
    SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart secondFinish firstFinish where
  firstRail := prefixAssembly.firstRail.append suffixAssembly.secondRail
  secondRail := prefixAssembly.secondRail.append suffixAssembly.firstRail
  firstRail_isPath :=
    GoertzelV24DualPathTransversal.walk_append_isPath_of_support_disjoint
      prefixAssembly.firstRail suffixAssembly.secondRail
      prefixAssembly.firstRail_isPath suffixAssembly.secondRail_isPath hfirstPath
  secondRail_isPath :=
    GoertzelV24DualPathTransversal.walk_append_isPath_of_support_disjoint
      prefixAssembly.secondRail suffixAssembly.firstRail
      prefixAssembly.secondRail_isPath suffixAssembly.firstRail_isPath hsecondPath
  firstRail_support_disjoint_secondRail := by
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
      List.disjoint_left]
    intro face hfirst hsecond
    rcases List.mem_append.mp hfirst with hfirstPrefix | hsecondSuffix
    · rcases List.mem_append.mp hsecond with hsecondPrefix | hfirstSuffix
      · exact (List.disjoint_left.mp
          prefixAssembly.firstRail_support_disjoint_secondRail hfirstPrefix)
            hsecondPrefix
      · exact (List.disjoint_left.mp hfirstSecond hfirstPrefix) hfirstSuffix
    · rcases List.mem_append.mp hsecond with hsecondPrefix | hfirstSuffix
      · exact (List.disjoint_left.mp hsecondFirst hsecondPrefix) hsecondSuffix
      · have hfirstFull : face ∈ suffixAssembly.firstRail.support :=
          List.mem_of_mem_tail hfirstSuffix
        have hsecondFull : face ∈ suffixAssembly.secondRail.support :=
          List.mem_of_mem_tail hsecondSuffix
        exact (List.disjoint_left.mp
          suffixAssembly.firstRail_support_disjoint_secondRail hfirstFull)
            hsecondFull

@[simp] theorem appendAssemblyCrossed_firstRail
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail) :
    (appendAssemblyCrossed prefixAssembly suffixAssembly hfirstPath hsecondPath
      hfirstSecond hsecondFirst).firstRail =
      prefixAssembly.firstRail.append suffixAssembly.secondRail := rfl

@[simp] theorem appendAssemblyCrossed_secondRail
    {firstStart secondStart middleFirst middleSecond firstFinish secondFinish :
      SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart middleFirst middleSecond)
    (suffixAssembly : SelectedSourceLocalRailAssembly (web := web)
      middleSecond middleFirst firstFinish secondFinish)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.secondRail.support.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      suffixAssembly.firstRail.support.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      suffixAssembly.secondRail.support.tail) :
    (appendAssemblyCrossed prefixAssembly suffixAssembly hfirstPath hsecondPath
      hfirstSecond hsecondFirst).secondRail =
      prefixAssembly.secondRail.append suffixAssembly.firstRail := rfl

variable
    {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {leftIncomingBefore leftIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions leftPlacement}}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}
    {left : SeparatedSelectedSourceLocalRailPaths leftPlacement
      leftIncomingBefore leftIncomingAfter successor.frame.leftBefore
      successor.frame.leftAfter}

/-- The two possible endpoint orders after a frozen prefix is attached to a
certified terminal window. -/
inductive CertifiedSelectedLocalRailTerminalWindow.PrependOutcome
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left) : Type (u + 1)
  | straight
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter))
  | swapped
      (assembly : SelectedSourceLocalRailAssembly (web := web)
        firstStart secondStart
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingAfter)
        (selectedPlacementSideFace rightPlacement successor.rightOutgoingBefore))

/-- Attach a frozen prefix to a certified terminal window while retaining the
terminal window's endpoint permutation.

The four premises are intentionally explicit: a later finite-state transition
must prove them from the frozen-prefix and mutable-window invariants. -/
noncomputable def CertifiedSelectedLocalRailTerminalWindow.prepend
    {firstStart secondStart : SelectedFace (web := web)}
    (prefixAssembly : SelectedSourceLocalRailAssembly (web := web)
      firstStart secondStart
      (selectedPlacementSideFace leftPlacement leftIncomingBefore)
      (selectedPlacementSideFace leftPlacement leftIncomingAfter))
    (window : CertifiedSelectedLocalRailTerminalWindow successor left)
    (hfirstPath : prefixAssembly.firstRail.support.Disjoint
      window.firstSupport.tail)
    (hsecondPath : prefixAssembly.secondRail.support.Disjoint
      window.secondSupport.tail)
    (hfirstSecond : prefixAssembly.firstRail.support.Disjoint
      window.secondSupport.tail)
    (hsecondFirst : prefixAssembly.secondRail.support.Disjoint
      window.firstSupport.tail) :
    window.PrependOutcome prefixAssembly :=
  match hresult : window.outcome with
  | .straight terminalAssembly =>
      .straight (appendAssembly prefixAssembly terminalAssembly
        (by simpa [CertifiedSelectedLocalRailTerminalWindow.firstSupport,
          hresult] using hfirstPath)
        (by simpa [CertifiedSelectedLocalRailTerminalWindow.secondSupport,
          hresult] using hsecondPath)
        (by simpa [CertifiedSelectedLocalRailTerminalWindow.secondSupport,
          hresult] using hfirstSecond)
        (by simpa [CertifiedSelectedLocalRailTerminalWindow.firstSupport,
          hresult] using hsecondFirst))
  | .swapped terminalAssembly =>
      .swapped (appendAssembly prefixAssembly terminalAssembly
        (by simpa [CertifiedSelectedLocalRailTerminalWindow.firstSupport,
          hresult] using hfirstPath)
        (by simpa [CertifiedSelectedLocalRailTerminalWindow.secondSupport,
          hresult] using hsecondPath)
        (by simpa [CertifiedSelectedLocalRailTerminalWindow.secondSupport,
          hresult] using hfirstSecond)
        (by simpa [CertifiedSelectedLocalRailTerminalWindow.firstSupport,
          hresult] using hsecondFirst))

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
