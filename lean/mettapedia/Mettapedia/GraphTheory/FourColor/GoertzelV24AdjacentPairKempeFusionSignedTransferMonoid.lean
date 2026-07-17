import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelFaceSymbol
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionReturnCircuit

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open SimpleGraph

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

/-- The endpoint coordinate of a face symbol flips exactly at negative
chirality. -/
def FusionFaceSymbol.endpointFlip (symbol : FusionFaceSymbol) : Bool :=
  !symbol.chirality

/-- The canonical four-state transfer. The first coordinate records the
oriented endpoint of the shared edge and the second records the Kempe route. -/
def signedRoutePermutation (endpointFlip routeFlip : Bool) :
    Equiv.Perm (Bool × Bool) :=
  (boolRoutePermutation endpointFlip).prodCongr
    (boolRoutePermutation routeFlip)

@[simp] theorem signedRoutePermutation_apply
    (endpointFlip routeFlip endpoint route : Bool) :
    signedRoutePermutation endpointFlip routeFlip (endpoint, route) =
      (boolRoutePermutation endpointFlip endpoint,
        boolRoutePermutation routeFlip route) :=
  rfl

/-- Coordinatewise XOR is composition in the four-state transfer group. -/
theorem signedRoutePermutation_xor
    (firstEndpoint secondEndpoint firstRoute secondRoute : Bool) :
    signedRoutePermutation
        (Bool.xor firstEndpoint secondEndpoint)
        (Bool.xor firstRoute secondRoute) =
      signedRoutePermutation secondEndpoint secondRoute *
        signedRoutePermutation firstEndpoint firstRoute := by
  cases firstEndpoint <;> cases secondEndpoint <;>
    cases firstRoute <;> cases secondRoute <;>
    ext state <;> rcases state with ⟨endpoint, route⟩ <;>
      cases endpoint <;> cases route <;>
      simp [signedRoutePermutation, boolRoutePermutation,
        Equiv.Perm.mul_apply]

/-- Endpoint transport is the Boolean transposition represented by the
negative-chirality bit. -/
theorem fusionEndpointTransport_eq_boolRoutePermutation_endpointFlip
    (chirality endpoint : Bool) :
    fusionEndpointTransport chirality endpoint =
      boolRoutePermutation (!chirality) endpoint := by
  cases chirality <;> cases endpoint <;> rfl

/-- A local fusion symbol acts simultaneously on oriented endpoint and route
coordinates. -/
def FusionFaceSymbol.signedRouteTransfer (symbol : FusionFaceSymbol) :
    Equiv.Perm (Bool × Bool) :=
  signedRoutePermutation symbol.endpointFlip symbol.twist

@[simp] theorem FusionFaceSymbol.signedRouteTransfer_apply
    (symbol : FusionFaceSymbol) (endpoint route : Bool) :
    symbol.signedRouteTransfer (endpoint, route) =
      (fusionEndpointTransport symbol.chirality endpoint,
        symbol.routeTransfer route) := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases chirality <;> cases entryTurn <;> cases exitTurn <;>
    cases endpoint <;> cases route <;>
    simp [FusionFaceSymbol.signedRouteTransfer, signedRoutePermutation,
      FusionFaceSymbol.endpointFlip, FusionFaceSymbol.twist,
      FusionFaceSymbol.routeTransfer, boolRoutePermutation,
      fusionEndpointTransport]

/-- XOR of the negative-chirality bits in a face-symbol word. -/
def fusionFaceWordEndpointFlip : List FusionFaceSymbol → Bool
  | [] => false
  | symbol :: word =>
      Bool.xor symbol.endpointFlip (fusionFaceWordEndpointFlip word)

@[simp] theorem fusionFaceWordEndpointFlip_nil :
    fusionFaceWordEndpointFlip [] = false :=
  rfl

@[simp] theorem fusionFaceWordEndpointFlip_cons
    (symbol : FusionFaceSymbol) (word : List FusionFaceSymbol) :
    fusionFaceWordEndpointFlip (symbol :: word) =
      Bool.xor symbol.endpointFlip (fusionFaceWordEndpointFlip word) :=
  rfl

/-- Composite four-state transfer in word order. -/
def fusionFaceWordSignedRouteTransfer :
    List FusionFaceSymbol → Equiv.Perm (Bool × Bool)
  | [] => Equiv.refl (Bool × Bool)
  | symbol :: word =>
      fusionFaceWordSignedRouteTransfer word * symbol.signedRouteTransfer

@[simp] theorem fusionFaceWordSignedRouteTransfer_nil :
    fusionFaceWordSignedRouteTransfer [] = Equiv.refl (Bool × Bool) :=
  rfl

@[simp] theorem fusionFaceWordSignedRouteTransfer_cons
    (symbol : FusionFaceSymbol) (word : List FusionFaceSymbol) :
    fusionFaceWordSignedRouteTransfer (symbol :: word) =
      fusionFaceWordSignedRouteTransfer word * symbol.signedRouteTransfer :=
  rfl

/-- The four-state transfer of a word is completely determined by the two
XOR parities: negative chirality and route twist. -/
theorem fusionFaceWordSignedRouteTransfer_eq_signedRoutePermutation
    (word : List FusionFaceSymbol) :
    fusionFaceWordSignedRouteTransfer word =
      signedRoutePermutation
        (fusionFaceWordEndpointFlip word)
        (fusionFaceWordTwist word) := by
  induction word with
  | nil => rfl
  | cons symbol word inductionHypothesis =>
      rw [fusionFaceWordSignedRouteTransfer_cons, inductionHypothesis,
        FusionFaceSymbol.signedRouteTransfer,
        fusionFaceWordEndpointFlip_cons, fusionFaceWordTwist_cons,
        signedRoutePermutation_xor]

/-- A word containing only positive-chirality symbols has no net endpoint
flip. -/
theorem fusionFaceWordEndpointFlip_eq_false_of_forall_chirality_eq_true
    (word : List FusionFaceSymbol)
    (hpositive : ∀ symbol ∈ word, symbol.chirality = true) :
    fusionFaceWordEndpointFlip word = false := by
  induction word with
  | nil => rfl
  | cons symbol word inductionHypothesis =>
      have hsymbol : symbol.chirality = true :=
        hpositive symbol (by simp)
      have htail : ∀ tailSymbol ∈ word, tailSymbol.chirality = true := by
        intro tailSymbol hmem
        exact hpositive tailSymbol (by simp [hmem])
      rw [fusionFaceWordEndpointFlip_cons, inductionHypothesis htail]
      simp [FusionFaceSymbol.endpointFlip, hsymbol]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The total endpoint-flip parity of one fusion lens. -/
def bFusionTotalEndpointFlip
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : Bool :=
  fusionFaceWordEndpointFlip
    (bFusionFaceWord graphData data lens hab hac)

/-- The total four-state transfer of one fusion lens. -/
def bFusionTotalSignedRouteTransfer
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : Equiv.Perm (Bool × Bool) :=
  fusionFaceWordSignedRouteTransfer
    (bFusionFaceWord graphData data lens hab hac)

/-- Trivial signed fusion monodromy makes every symbol in the first-route
word positively oriented, hence kills the total endpoint-flip parity. -/
theorem bFusionTotalEndpointFlip_eq_false_of_signedMonodromy_eq_refl
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    bFusionTotalEndpointFlip graphData data lens hab hac = false := by
  have hpositive : ∀ position : Fin lens.fusionSiteCount,
      lens.bOrderedFusionChirality hab hac position = true :=
    ((lens.signedFusionMonodromy_eq_refl_iff hab hac).1 hsigned).2
  apply fusionFaceWordEndpointFlip_eq_false_of_forall_chirality_eq_true
  rw [bFusionFaceWord, List.forall_mem_ofFn_iff]
  intro position
  simpa [bOrderedFusionFaceSymbol,
    EvenKempeFusionLens.bOrderedFusionChirality] using hpositive position

/-- In the trivial-signed branch a lens can only act on the route
coordinate; its endpoint coordinate is fixed. -/
theorem bFusionTotalSignedRouteTransfer_eq_routeOnly_of_signedMonodromy_eq_refl
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    bFusionTotalSignedRouteTransfer graphData data lens hab hac =
      signedRoutePermutation false
        (bFusionTotalTwist graphData data lens hab hac) := by
  rw [bFusionTotalSignedRouteTransfer,
    fusionFaceWordSignedRouteTransfer_eq_signedRoutePermutation]
  rw [show fusionFaceWordEndpointFlip
      (bFusionFaceWord graphData data lens hab hac) = false from
    bFusionTotalEndpointFlip_eq_false_of_signedMonodromy_eq_refl
      graphData data lens hab hac hsigned]
  rfl

/-- A rejected cross is exactly the diagonal element of the four-state
transfer group. -/
theorem crossFaceSymbol_signedRouteTransfer_eq_diagonal_of_rejected
    (data : AdjacentPairData G)
    (graphData : SimpleGraphDartRotation.Data G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second)
    (hfalse : crossExitFaceTransferBit data graphData first second
      hab hac hbc site = false) :
    (crossFaceSymbol data graphData first second
      hab hac hbc site).signedRouteTransfer =
        signedRoutePermutation true true := by
  have hstate :=
    (crossExitFaceTransferBit_eq_false_iff_crossFaceSymbol_negative_twist
      data graphData first second hab hac hbc site).1 hfalse
  rw [FusionFaceSymbol.signedRouteTransfer,
    FusionFaceSymbol.endpointFlip, hstate.1, hstate.2]
  rfl

/-- Route-only transfers on either side of a diagonal flip still reverse
the endpoint coordinate. -/
theorem routeOnly_mul_diagonal_mul_routeOnly_apply_fst
    (firstRoute secondRoute endpoint route : Bool) :
    (((signedRoutePermutation false secondRoute *
          signedRoutePermutation true true) *
        signedRoutePermutation false firstRoute) (endpoint, route)).1 =
      !endpoint := by
  cases firstRoute <;> cases secondRoute <;>
    cases endpoint <;> cases route <;>
    simp [signedRoutePermutation, boolRoutePermutation,
      Equiv.Perm.mul_apply]

/-- Consequently a diagonal cross bracketed by arbitrary route-only lens
transfers is never the identity. -/
theorem routeOnly_mul_diagonal_mul_routeOnly_ne_refl
    (firstRoute secondRoute : Bool) :
    (signedRoutePermutation false secondRoute *
          signedRoutePermutation true true) *
        signedRoutePermutation false firstRoute ≠
      Equiv.refl (Bool × Bool) := by
  intro hidentity
  have hvalue := congrArg
    (fun transfer : Equiv.Perm (Bool × Bool) ↦ transfer (false, false))
    hidentity
  have hfirst := congrArg Prod.fst hvalue
  rw [routeOnly_mul_diagonal_mul_routeOnly_apply_fst] at hfirst
  simp at hfirst

/-- Total four-state transfer around a `bc` cross bracketed by its two
fusion lenses. -/
def EvenKempeFusionLens.bcCombinedSignedTransfer
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (graphData : SimpleGraphDartRotation.Data G)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute) :
    Equiv.Perm (Bool × Bool) :=
  (bFusionTotalSignedRouteTransfer graphData data lens23 hab hac *
      (EvenKempeFusionLens.bcCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).signedRouteTransfer) *
    bFusionTotalSignedRouteTransfer graphData data lens01 hab hac

/-- Total four-state transfer in the complementary `cb` orientation. -/
def EvenKempeFusionLens.cbCombinedSignedTransfer
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (graphData : SimpleGraphDartRotation.Data G)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute) :
    Equiv.Perm (Bool × Bool) :=
  (bFusionTotalSignedRouteTransfer graphData data lens23 hab hac *
      (EvenKempeFusionLens.cbCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).signedRouteTransfer) *
    bFusionTotalSignedRouteTransfer graphData data lens01 hab hac

/-- The exact finite obstruction supplied by a rejected `bc` cross: if the
signed monodromies of both adjacent lenses are trivial, their two total
transfers cannot absorb the cross. The composite four-state monodromy remains
nonidentity because it reverses the endpoint coordinate. -/
theorem EvenKempeFusionLens.bcCombinedSignedTransfer_ne_refl_of_rejected_of_lensMonodromies_eq_refl
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hmono01 : lens01.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens01.fusionSiteCount × Bool))
    (hmono23 : lens23.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens23.fusionSiteCount × Bool)) :
    EvenKempeFusionLens.bcCombinedSignedTransfer lens01 graphData lens23
        hab hac hbc site ≠
      Equiv.refl (Bool × Bool) := by
  rw [EvenKempeFusionLens.bcCombinedSignedTransfer]
  rw [bFusionTotalSignedRouteTransfer_eq_routeOnly_of_signedMonodromy_eq_refl
      graphData data lens01 hab hac hmono01,
    bFusionTotalSignedRouteTransfer_eq_routeOnly_of_signedMonodromy_eq_refl
      graphData data lens23 hab hac hmono23]
  have hcross :
      (EvenKempeFusionLens.bcCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).signedRouteTransfer =
          signedRoutePermutation true true := by
    apply crossFaceSymbol_signedRouteTransfer_eq_diagonal_of_rejected
    simpa only [EvenKempeFusionLens.bcCrossExitFaceTransferBit] using hfalse
  rw [hcross]
  exact routeOnly_mul_diagonal_mul_routeOnly_ne_refl _ _

/-- The complementary `cb` channel has the identical diagonal obstruction. -/
theorem EvenKempeFusionLens.cbCombinedSignedTransfer_ne_refl_of_rejected_of_lensMonodromies_eq_refl
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hmono01 : lens01.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens01.fusionSiteCount × Bool))
    (hmono23 : lens23.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens23.fusionSiteCount × Bool)) :
    EvenKempeFusionLens.cbCombinedSignedTransfer lens01 graphData lens23
        hab hac hbc site ≠
      Equiv.refl (Bool × Bool) := by
  rw [EvenKempeFusionLens.cbCombinedSignedTransfer]
  rw [bFusionTotalSignedRouteTransfer_eq_routeOnly_of_signedMonodromy_eq_refl
      graphData data lens01 hab hac hmono01,
    bFusionTotalSignedRouteTransfer_eq_routeOnly_of_signedMonodromy_eq_refl
      graphData data lens23 hab hac hmono23]
  have hcross :
      (EvenKempeFusionLens.cbCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).signedRouteTransfer =
          signedRoutePermutation true true := by
    apply crossFaceSymbol_signedRouteTransfer_eq_diagonal_of_rejected
    simpa only [EvenKempeFusionLens.cbCrossExitFaceTransferBit] using hfalse
  rw [hcross]
  exact routeOnly_mul_diagonal_mul_routeOnly_ne_refl _ _

/-- Rejection in the `bc` channel is now absorbed by the established
shortening layer unless the combined four-state transfer itself is
nonidentity. Thus the cross obstruction has no residual algebraic branch. -/
theorem EvenKempeFusionLens.bcRejectedCross_shortens_or_combinedSignedTransfer_ne_refl
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
        (circuit : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk start start),
        circuit.IsCircuit ∧ circuit.length < lens01.closedWalk.length) ∨
      (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
          (circuit : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk start start),
          circuit.IsCircuit ∧ circuit.length < lens23.closedWalk.length) ∨
        EvenKempeFusionLens.bcCombinedSignedTransfer lens01 graphData lens23
            hab hac hbc site ≠
          Equiv.refl (Bool × Bool) := by
  by_cases hmono01 : lens01.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens01.fusionSiteCount × Bool)
  · by_cases hmono23 : lens23.signedFusionMonodromy hab hac =
        Equiv.refl (Fin lens23.fusionSiteCount × Bool)
    · exact Or.inr (Or.inr
        (EvenKempeFusionLens.bcCombinedSignedTransfer_ne_refl_of_rejected_of_lensMonodromies_eq_refl
          graphData data lens01 lens23 hab hac hbc site hfalse hmono01 hmono23))
    · exact Or.inr (Or.inl
        (lens23.exists_shorter_primalCircuit_of_signedMonodromy_ne_refl
          hdata hab hac hmono23))
  · exact Or.inl
      (lens01.exists_shorter_primalCircuit_of_signedMonodromy_ne_refl
        hdata hab hac hmono01)

/-- The same branch-free shortening/transfer dichotomy for a rejected `cb`
cross. -/
theorem EvenKempeFusionLens.cbRejectedCross_shortens_or_combinedSignedTransfer_ne_refl
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
        (circuit : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk start start),
        circuit.IsCircuit ∧ circuit.length < lens01.closedWalk.length) ∨
      (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
          (circuit : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk start start),
          circuit.IsCircuit ∧ circuit.length < lens23.closedWalk.length) ∨
        EvenKempeFusionLens.cbCombinedSignedTransfer lens01 graphData lens23
            hab hac hbc site ≠
          Equiv.refl (Bool × Bool) := by
  by_cases hmono01 : lens01.signedFusionMonodromy hab hac =
      Equiv.refl (Fin lens01.fusionSiteCount × Bool)
  · by_cases hmono23 : lens23.signedFusionMonodromy hab hac =
        Equiv.refl (Fin lens23.fusionSiteCount × Bool)
    · exact Or.inr (Or.inr
        (EvenKempeFusionLens.cbCombinedSignedTransfer_ne_refl_of_rejected_of_lensMonodromies_eq_refl
          graphData data lens01 lens23 hab hac hbc site hfalse hmono01 hmono23))
    · exact Or.inr (Or.inl
        (lens23.exists_shorter_primalCircuit_of_signedMonodromy_ne_refl
          hdata hab hac hmono23))
  · exact Or.inl
      (lens01.exists_shorter_primalCircuit_of_signedMonodromy_ne_refl
        hdata hab hac hmono01)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
