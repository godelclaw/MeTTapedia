import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarColorSymmetry
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarColorTranslationParity

/-!
# Affine color monodromy at an intrinsic collar

Local Tait-color transport may combine an additive color translation with a
permutation of the three nonzero color names.  The sign of such an affine
step is exactly the sign of its color-name part.  Consequently, a finite
word whose net color-name action is literal identity is even.  It cannot
realize the odd singleton-collar monodromy, in any four-state coordinates.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

namespace IntrinsicShortTargetEscapeCollar

/-- The canonical equivalence between a Boolean bit and `ᵓd₂`. -/
def boolF2Equiv : Bool ≃ F2 :=
  Equiv.ofBijective (fun bit => if bit then 1 else 0) (by decide)

/-- Coordinatewise identification of the four Boolean states with the four
Tait colors. -/
def boolColorEquiv : Bool × Bool ≃ Color :=
  boolF2Equiv.prodCongr boolF2Equiv

/-- Translation by a Tait color, transported from the canonical Boolean
four-state translation action. -/
def colorTranslationPermutation (translation : Color) :
    Equiv.Perm Color :=
  boolColorEquiv.permCongr
    (signedRoutePermutation
      (boolColorEquiv.symm translation).1
      (boolColorEquiv.symm translation).2)

/-- Every additive translation of the four Tait colors is even. -/
theorem colorTranslationPermutation_sign_eq_one
    (translation : Color) :
    Equiv.Perm.sign (colorTranslationPermutation translation) = 1 := by
  rw [colorTranslationPermutation, Equiv.Perm.sign_permCongr]
  exact signedRoutePermutation_sign_eq_one _ _

/-- An affine color step consists of a translation followed by a zero-fixing
permutation of the three nonzero color names. -/
def colorAffinePermutation
    (translation : Color) (linear : ColorNameSymmetry) :
    Equiv.Perm Color :=
  colorTranslationPermutation translation * linear.1

/-- Translation contributes no sign, so an affine color step has exactly the
sign of its linear color-name action. -/
theorem colorAffinePermutation_sign
    (translation : Color) (linear : ColorNameSymmetry) :
    Equiv.Perm.sign (colorAffinePermutation translation linear) =
      Equiv.Perm.sign linear.1 := by
  rw [colorAffinePermutation, Equiv.Perm.sign_mul,
    colorTranslationPermutation_sign_eq_one, one_mul]

/-- Composite affine color action in traversal order. -/
def colorAffineWordTransfer :
    List (Color × ColorNameSymmetry) → Equiv.Perm Color
  | [] => Equiv.refl Color
  | step :: rest =>
      colorAffineWordTransfer rest *
        colorAffinePermutation step.1 step.2

/-- Net linear color-name action of an affine transfer word. -/
def colorAffineWordLinear :
    List (Color × ColorNameSymmetry) → ColorNameSymmetry
  | [] => 1
  | step :: rest => colorAffineWordLinear rest * step.2

/-- Linear holonomy is composed in traversal order: the second word acts
after the first. -/
theorem colorAffineWordLinear_append
    (first second : List (Color × ColorNameSymmetry)) :
    colorAffineWordLinear (first ++ second) =
      colorAffineWordLinear second * colorAffineWordLinear first := by
  induction first with
  | nil => simp [colorAffineWordLinear]
  | cons step rest ih =>
      simp only [List.cons_append, colorAffineWordLinear, ih]
      rw [mul_assoc]

/-- The sign of a composite affine transfer is exactly the sign of its net
linear color-name action. -/
theorem colorAffineWordTransfer_sign
    (word : List (Color × ColorNameSymmetry)) :
    Equiv.Perm.sign (colorAffineWordTransfer word) =
      Equiv.Perm.sign (colorAffineWordLinear word).1 := by
  induction word with
  | nil =>
      simp [colorAffineWordTransfer, colorAffineWordLinear]
  | cons step rest ih =>
      rw [colorAffineWordTransfer, colorAffineWordLinear,
        Equiv.Perm.sign_mul, colorAffinePermutation_sign, ih]
      change
        Equiv.Perm.sign (colorAffineWordLinear rest).1 *
            Equiv.Perm.sign step.2.1 =
          Equiv.Perm.sign
            ((colorAffineWordLinear rest).1 * step.2.1)
      rw [Equiv.Perm.sign_mul]

/-- Literal return of the color names forces every affine transfer word to
be even, independently of its accumulated translation. -/
theorem colorAffineWordTransfer_sign_eq_one_of_linear_eq_one
    {word : List (Color × ColorNameSymmetry)}
    (hlinear : colorAffineWordLinear word = 1) :
    Equiv.Perm.sign (colorAffineWordTransfer word) = 1 := by
  rw [colorAffineWordTransfer_sign, hlinear]
  rfl

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}
  {rebaseCircuit :
    CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
  {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace ScalarSupportCrossingState

variable (state : ScalarSupportCrossingState collar sourceEscape)

/-- No affine color-transport word with literal net color-name identity can
represent singleton geometric monodromy, in any four-state coordinates. -/
theorem targetRootedSignedMonodromy_ne_closedAffineColorWordConjugate_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile)
    (coordinates :
      Color ≃ Fin state.targetRootedSupportOrder.length × Bool)
    (word : List (Color × ColorNameSymmetry))
    (hlinear : colorAffineWordLinear word = 1) :
    state.targetRootedSignedMonodromy ≠
      coordinates.permCongr (colorAffineWordTransfer word) := by
  intro heq
  have hsign := congrArg Equiv.Perm.sign heq
  rw [state.targetRootedSignedMonodromy_sign_eq_neg_one_of_singletonPrimalCutProfile
      profile,
    Equiv.Perm.sign_permCongr,
    colorAffineWordTransfer_sign_eq_one_of_linear_eq_one hlinear] at hsign
  norm_num at hsign

/-- Equivalently, singleton geometry admits no closed affine-color
realization with literal return of the color names. -/
theorem not_exists_closedAffineColorWordConjugacy_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    ¬ ∃ coordinates :
          Color ≃ Fin state.targetRootedSupportOrder.length × Bool,
        ∃ word : List (Color × ColorNameSymmetry),
          colorAffineWordLinear word = 1 ∧
            state.targetRootedSignedMonodromy =
              coordinates.permCongr (colorAffineWordTransfer word) := by
  rintro ⟨coordinates, word, hlinear, htransport⟩
  exact
    state.targetRootedSignedMonodromy_ne_closedAffineColorWordConjugate_of_singletonPrimalCutProfile
      profile coordinates word hlinear htransport

end ScalarSupportCrossingState

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

/-! Publication-facing alias for the singleton affine-monodromy obstruction. -/

alias GoertzelV24AllFaceIntrinsicCollarAffineColorMonodromy.targetRootedSignedMonodromy_ne_closedAffineColorWordConjugate_of_singletonPrimalCutProfile :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle.IntrinsicShortTargetEscapeCollar.ScalarSupportCrossingState.targetRootedSignedMonodromy_ne_closedAffineColorWordConjugate_of_singletonPrimalCutProfile

end Mettapedia.GraphTheory.FourColor
