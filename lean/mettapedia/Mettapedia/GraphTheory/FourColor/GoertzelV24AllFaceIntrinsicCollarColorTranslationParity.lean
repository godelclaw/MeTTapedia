import Mathlib.GroupTheory.Perm.Sign
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSignedTransferMonoid
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarSignedSupportParity

/-!
# Color-translation parity at an intrinsic collar

The canonical color state has two Boolean coordinates.  Translation in this
four-state space is always even: a nontrivial translation is a product of two
disjoint transpositions.  By contrast, singleton-collar geometry produces one
endpoint transposition.  Thus no change of four-state coordinates can identify
the geometric monodromy with a color translation.
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

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- A coordinatewise Boolean translation factors into its independent
second- and first-coordinate actions. -/
theorem signedRoutePermutation_eq_prodCongrRight_mul_prodCongrLeft
    (endpointFlip routeFlip : Bool) :
    signedRoutePermutation endpointFlip routeFlip =
      Equiv.prodCongrRight
          (fun _ : Bool => boolRoutePermutation routeFlip) *
        Equiv.prodCongrLeft
          (fun _ : Bool => boolRoutePermutation endpointFlip) := by
  ext state <;>
    rcases state with ⟨endpoint, route⟩ <;>
      simp only [signedRoutePermutation_apply, Equiv.Perm.mul_apply,
        Equiv.prodCongrLeft_apply, Equiv.prodCongrRight_apply]

/-- Every translation of the four color-coordinate states is even. -/
theorem signedRoutePermutation_sign_eq_one
    (endpointFlip routeFlip : Bool) :
    Equiv.Perm.sign (signedRoutePermutation endpointFlip routeFlip) = 1 := by
  rw [signedRoutePermutation_eq_prodCongrRight_mul_prodCongrLeft,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_prodCongrRight,
    Equiv.Perm.sign_prodCongrLeft]
  simp

/-- Every finite fusion-face transfer word is even.  Thus enlarging from a
single coordinate translation to the full finite transfer monoid does not
alter the parity obstruction. -/
theorem fusionFaceWordSignedRouteTransfer_sign_eq_one
    (word : List FusionFaceSymbol) :
    Equiv.Perm.sign (fusionFaceWordSignedRouteTransfer word) = 1 := by
  rw [fusionFaceWordSignedRouteTransfer_eq_signedRoutePermutation]
  exact signedRoutePermutation_sign_eq_one _ _

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}

namespace ScalarSupportCrossingState

variable (state : ScalarSupportCrossingState collar sourceEscape)

/-- Singleton geometric monodromy cannot be a color-coordinate translation,
even after an arbitrary relabeling of its four endpoint states. -/
theorem targetRootedSignedMonodromy_ne_translationConjugate_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile)
    (coordinates :
      Bool × Bool ≃ Fin state.targetRootedSupportOrder.length × Bool)
    (endpointFlip routeFlip : Bool) :
    state.targetRootedSignedMonodromy ≠
      coordinates.permCongr
        (signedRoutePermutation endpointFlip routeFlip) := by
  intro heq
  have hsign := congrArg Equiv.Perm.sign heq
  rw [state.targetRootedSignedMonodromy_sign_eq_neg_one_of_singletonPrimalCutProfile
      profile,
    Equiv.Perm.sign_permCongr,
    signedRoutePermutation_sign_eq_one] at hsign
  norm_num at hsign

/-- There is no four-state coordinate system in which singleton geometric
monodromy is any color-coordinate translation. -/
theorem not_exists_translationConjugacy_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    ¬ ∃ coordinates :
          Bool × Bool ≃ Fin state.targetRootedSupportOrder.length × Bool,
        ∃ endpointFlip routeFlip : Bool,
          state.targetRootedSignedMonodromy =
            coordinates.permCongr
              (signedRoutePermutation endpointFlip routeFlip) := by
  rintro ⟨coordinates, endpointFlip, routeFlip, htransport⟩
  exact
    state.targetRootedSignedMonodromy_ne_translationConjugate_of_singletonPrimalCutProfile
      profile coordinates endpointFlip routeFlip htransport

/-- Singleton geometric monodromy cannot be represented by any finite word
in the fusion-face transfer monoid, in any four-state coordinate system. -/
theorem targetRootedSignedMonodromy_ne_fusionFaceWordConjugate_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile)
    (coordinates :
      Bool × Bool ≃ Fin state.targetRootedSupportOrder.length × Bool)
    (word : List FusionFaceSymbol) :
    state.targetRootedSignedMonodromy ≠
      coordinates.permCongr (fusionFaceWordSignedRouteTransfer word) := by
  intro heq
  have hsign := congrArg Equiv.Perm.sign heq
  rw [state.targetRootedSignedMonodromy_sign_eq_neg_one_of_singletonPrimalCutProfile
      profile,
    Equiv.Perm.sign_permCongr,
    fusionFaceWordSignedRouteTransfer_sign_eq_one] at hsign
  norm_num at hsign

/-- There are no coordinates and no finite fusion-face transfer word whose
action realizes singleton geometric monodromy. -/
theorem not_exists_fusionFaceWordConjugacy_of_singletonPrimalCutProfile
    (profile : cycle.SingletonPrimalCutProfile) :
    ¬ ∃ coordinates :
          Bool × Bool ≃ Fin state.targetRootedSupportOrder.length × Bool,
        ∃ word : List FusionFaceSymbol,
          state.targetRootedSignedMonodromy =
            coordinates.permCongr
              (fusionFaceWordSignedRouteTransfer word) := by
  rintro ⟨coordinates, word, htransport⟩
  exact
    state.targetRootedSignedMonodromy_ne_fusionFaceWordConjugate_of_singletonPrimalCutProfile
      profile coordinates word htransport

end ScalarSupportCrossingState
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
