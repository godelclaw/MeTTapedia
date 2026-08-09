import Mettapedia.GraphTheory.FourColor.GoertzelV24ReductiveSpine
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedVertexTaitSplice

/-!
# The source-faithful splice interface

The corridor profile is the finite transfer state used by the reductive
argument: it records boundary colors, tracked connectivity, and capped face
progress.  This file does not replace that state by an unproved semantic
surrogate.  Instead it packages the concrete retained-vertex splice and
separates the three logically different obligations:

* profile identity gives the forward Tait coloring of the shortened object;
* deleting a genuinely absent vertex gives strict size decrease;
* reverse completion is the remaining descent premise, stated explicitly.

Keeping the last item as a field prevents the reduction interface from
silently turning a one-way coloring transport into counterexample
preservation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SpliceUnification

open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RetainedVertexTaitSplice
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The target predicate used by the reductive spine at a fixed rotation
system. -/
abbrev TaitColorable (RS : RotationSystem V E) : Prop :=
  ∃ C : RS.EdgeColoring Color, RS.IsTaitEdgeColoring C

/-! ## Concrete splice data -/

structure OrderedCutSpliceData
    (RS : RotationSystem V E)
    (n terminalCount faceFragmentCount : Nat) where
  keep : V → Prop
  left : GraphCorridorCutData RS n terminalCount faceFragmentCount
  right : GraphCorridorCutData RS n terminalCount faceFragmentCount
  leftCrosses : ∀ step, ∃ dart : RS.D,
    RS.edgeOf dart = left.crossingEdge step ∧
    keep (RS.vertOf dart) ∧
    ¬ keep (RS.vertOf (RS.alpha dart))
  rightCrosses : ∀ step, ∃ dart : RS.D,
    RS.edgeOf dart = right.crossingEdge step ∧
    keep (RS.vertOf dart) ∧
    ¬ keep (RS.vertOf (RS.alpha dart))
  leftInjective : Function.Injective left.crossingEdge
  rightInjective : Function.Injective right.crossingEdge
  cover : ∀ dart : BoundaryDart RS keep,
    RS.edgeOf dart.1.1 ∈ orderedCut left.crossingEdge ∨
      RS.edgeOf dart.1.1 ∈ orderedCut right.crossingEdge
  disjoint : Disjoint (orderedCut left.crossingEdge)
    (orderedCut right.crossingEdge)
  outer_kept : keep (RS.vertOf RS.outer)
  seamEndpoints : ∀ step,
    RS.vertOf
        (orderedBoundaryDart RS keep left.crossingEdge
          leftCrosses step).1.1.1 ≠
      RS.vertOf
        (orderedBoundaryDart RS keep right.crossingEdge
          rightCrosses step).1.1.1
  removed : V
  removed_not_kept : ¬ keep removed

namespace OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The concrete shortened rotation system.  Every proof argument is retained
in the definition, so later statements cannot accidentally use a different
seam than the one certified by the data. -/
def output (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    RotationSystem (RetainedVertex data.keep)
      (orderedCutRetainedVertexRewiredDartSystem RS data.keep
        data.left.crossingEdge data.right.crossingEdge
        data.leftCrosses data.rightCrosses data.leftInjective
        data.rightInjective data.cover data.disjoint data.outer_kept
        data.seamEndpoints).Edge :=
  orderedCutRetainedVertexRotationSystem RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept
    data.seamEndpoints

/-- The size used for this local reduction is the retained vertex carrier. -/
def outputSize (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    Nat := Fintype.card (RetainedVertex data.keep)

theorem outputSize_lt (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    data.outputSize < Fintype.card V := by
  exact card_retainedVertex_lt data.keep data.removed data.removed_not_kept

/-! ## Profile identity and the forward coloring direction -/

structure EqualProfile
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) where
  coloring : RS.EdgeColoring Color
  coloring_isTait : RS.IsTaitEdgeColoring coloring
  profile_eq : data.left.profile coloring coloring_isTait =
    data.right.profile coloring coloring_isTait

/-- The profile state is the exact finite datum consumed by the existing
ordered-cut coloring theorem; no extra boundary-color equality is hidden. -/
theorem profile_boundary_color_eq
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile) (step : Fin n) :
    profile.coloring (data.left.crossingEdge step) =
      profile.coloring (data.right.crossingEdge step) := by
  exact crossingEdge_color_eq_of_profiles_eq data.left data.right
    profile.coloring profile.coloring profile.coloring_isTait
    profile.coloring_isTait profile.profile_eq step

def splicedColoring
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile) : data.output.EdgeColoring Color :=
  orderedCutRetainedVertexSplicedColoring RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept
    data.seamEndpoints profile.coloring
    (fun step => profile_boundary_color_eq data profile step)

theorem splicedColoring_isTait
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile) :
    data.output.IsTaitEdgeColoring (data.splicedColoring profile) := by
  exact orderedCutRetainedVertexSplicedColoring_isTait_of_profiles_eq
    RS data.keep data.left data.right data.leftCrosses data.rightCrosses
    data.leftInjective data.rightInjective data.cover data.disjoint
    data.outer_kept data.seamEndpoints profile.coloring
    profile.coloring_isTait profile.profile_eq

theorem output_taitColorable_of_equalProfile
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (profile : data.EqualProfile) :
    TaitColorable data.output :=
  ⟨data.splicedColoring profile, data.splicedColoring_isTait profile⟩

/-! ## The reverse direction is deliberately explicit -/

/-- The semantic descent obligation: every Tait coloring of the shortened
object can be completed back to a Tait coloring of the original object.  This
is the exact missing half of a counterexample-preserving splice; profile
identity alone must not be mistaken for this theorem. -/
def ReverseCompletion
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ coloring : data.output.EdgeColoring Color,
    data.output.IsTaitEdgeColoring coloring →
      TaitColorable (RS := RS)

theorem not_taitColorable_output_of_not_taitColorable
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hcompletion : data.ReverseCompletion)
    (hbad : ¬ TaitColorable (RS := RS)) :
    ¬ TaitColorable data.output := by
  intro houtput
  rcases houtput with ⟨coloring, hcoloring⟩
  exact hbad (hcompletion coloring hcoloring)

/-- A completed splice step has exactly the two reductive facts needed by the
spine: strict descent and preservation of counterexamples.  The theorem is
kept at the fixed-rotation-system level because the eventual object family
must still choose a uniform carrier for varying vertex and edge types. -/
structure CompletedStep
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) where
  reverse_completion : data.ReverseCompletion

theorem completedStep_strict_size
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (_step : data.CompletedStep) :
    data.outputSize < Fintype.card V :=
  data.outputSize_lt

theorem completedStep_counterexample_preserved
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (step : data.CompletedStep)
    (hbad : ¬ TaitColorable (RS := RS)) :
    ¬ TaitColorable data.output :=
  data.not_taitColorable_output_of_not_taitColorable
    step.reverse_completion hbad

end OrderedCutSpliceData

end

end GoertzelV24SpliceUnification

end Mettapedia.GraphTheory.FourColor
