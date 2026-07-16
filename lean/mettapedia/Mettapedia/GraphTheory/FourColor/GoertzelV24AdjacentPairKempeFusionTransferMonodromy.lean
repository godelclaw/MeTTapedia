import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFacePairing

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

/-- The local transfer parity: `true` exactly when the fusion face
pairing transposes the two route labels. -/
def FusionFaceSymbol.twist (symbol : FusionFaceSymbol) : Bool :=
  decide (symbol.entryTurn = symbol.exitTurn)

@[simp] theorem FusionFaceSymbol.twist_eq_true_iff
    (symbol : FusionFaceSymbol) :
    symbol.twist = true ↔ symbol.entryTurn = symbol.exitTurn := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;>
    simp [FusionFaceSymbol.twist]

@[simp] theorem FusionFaceSymbol.twist_eq_false_iff
    (symbol : FusionFaceSymbol) :
    symbol.twist = false ↔ symbol.entryTurn ≠ symbol.exitTurn := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;>
    simp [FusionFaceSymbol.twist]

/-- The canonical representation of a Boolean parity as a route-label
permutation. -/
def boolRoutePermutation : Bool → Equiv.Perm Bool
  | false => Equiv.refl Bool
  | true => Equiv.swap false true

@[simp] theorem boolRoutePermutation_false :
    boolRoutePermutation false = Equiv.refl Bool :=
  rfl

@[simp] theorem boolRoutePermutation_true :
    boolRoutePermutation true = Equiv.swap false true :=
  rfl

/-- Boolean XOR is composition in the two-element route-transfer
group. -/
theorem boolRoutePermutation_xor (first second : Bool) :
    boolRoutePermutation (Bool.xor first second) =
      boolRoutePermutation second * boolRoutePermutation first := by
  cases first <;> cases second <;>
    ext label <;> cases label <;>
      simp [boolRoutePermutation, Equiv.Perm.mul_apply]

/-- The geometric route transfer is represented exactly by its twist
bit. -/
theorem FusionFaceSymbol.routeTransfer_eq_boolRoutePermutation_twist
    (symbol : FusionFaceSymbol) :
    symbol.routeTransfer = boolRoutePermutation symbol.twist := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;>
    simp [FusionFaceSymbol.routeTransfer, FusionFaceSymbol.twist,
      boolRoutePermutation]

/-- XOR parity of a finite word of fusion face symbols. -/
def fusionFaceWordTwist : List FusionFaceSymbol → Bool
  | [] => false
  | symbol :: word => Bool.xor symbol.twist (fusionFaceWordTwist word)

@[simp] theorem fusionFaceWordTwist_nil :
    fusionFaceWordTwist [] = false :=
  rfl

@[simp] theorem fusionFaceWordTwist_cons
    (symbol : FusionFaceSymbol) (word : List FusionFaceSymbol) :
    fusionFaceWordTwist (symbol :: word) =
      Bool.xor symbol.twist (fusionFaceWordTwist word) :=
  rfl

/-- Compose the local route transfers in word order. -/
def fusionFaceWordTransfer : List FusionFaceSymbol → Equiv.Perm Bool
  | [] => Equiv.refl Bool
  | symbol :: word =>
      fusionFaceWordTransfer word * symbol.routeTransfer

@[simp] theorem fusionFaceWordTransfer_nil :
    fusionFaceWordTransfer [] = Equiv.refl Bool :=
  rfl

@[simp] theorem fusionFaceWordTransfer_cons
    (symbol : FusionFaceSymbol) (word : List FusionFaceSymbol) :
    fusionFaceWordTransfer (symbol :: word) =
      fusionFaceWordTransfer word * symbol.routeTransfer :=
  rfl

/-- A word transfer is completely determined by the XOR of its local
twist bits. -/
theorem fusionFaceWordTransfer_eq_boolRoutePermutation_twist
    (word : List FusionFaceSymbol) :
    fusionFaceWordTransfer word =
      boolRoutePermutation (fusionFaceWordTwist word) := by
  induction word with
  | nil => rfl
  | cons symbol word inductionHypothesis =>
      rw [fusionFaceWordTransfer_cons, inductionHypothesis,
        symbol.routeTransfer_eq_boolRoutePermutation_twist,
        fusionFaceWordTwist_cons,
        boolRoutePermutation_xor]

/-- XOR twist is invariant under reordering a finite word. -/
theorem fusionFaceWordTwist_eq_of_perm
    {first second : List FusionFaceSymbol} (hperm : first.Perm second) :
    fusionFaceWordTwist first = fusionFaceWordTwist second := by
  induction hperm with
  | nil => rfl
  | cons symbol hperm inductionHypothesis =>
      simp only [fusionFaceWordTwist_cons, inductionHypothesis]
  | swap first second word =>
      simp only [fusionFaceWordTwist_cons]
      rw [← Bool.xor_assoc,
        Bool.xor_comm second.twist first.twist, Bool.xor_assoc]
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-- Consequently the composed route transfer is independent of word
order. -/
theorem fusionFaceWordTransfer_eq_of_perm
    {first second : List FusionFaceSymbol} (hperm : first.Perm second) :
    fusionFaceWordTransfer first = fusionFaceWordTransfer second := by
  rw [fusionFaceWordTransfer_eq_boolRoutePermutation_twist,
    fusionFaceWordTransfer_eq_boolRoutePermutation_twist,
    fusionFaceWordTwist_eq_of_perm hperm]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionTransferGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance fusionTransferRetainedVertexFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance fusionTransferRetainedVertexDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- The `c`-ordered face word transported to the common fusion-count
carrier. -/
def cFusionFaceWordOnCount
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : List FusionFaceSymbol :=
  List.ofFn
    (cOrderedFusionFaceSymbolOnCount graphData data lens hab hac)

@[simp] theorem cFusionFaceWordOnCount_length
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    (cFusionFaceWordOnCount graphData data lens hab hac).length =
      lens.fusionSiteCount := by
  simp [cFusionFaceWordOnCount]

/-- The finite fusion monodromy is a concrete permutation certificate
between the complete face-symbol words in the two route orders. -/
theorem bFusionFaceWord_perm_cFusionFaceWordOnCount
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    (bFusionFaceWord graphData data lens hab hac).Perm
      (cFusionFaceWordOnCount graphData data lens hab hac) := by
  let bState : Fin lens.fusionSiteCount → FusionFaceSymbol :=
    bOrderedFusionFaceSymbol graphData data lens hab hac
  let cState : Fin lens.fusionSiteCount → FusionFaceSymbol :=
    cOrderedFusionFaceSymbolOnCount graphData data lens hab hac
  have hstate : cState ∘ lens.fusionMonodromy = bState := by
    funext position
    exact fusionMonodromy_preserves_faceSymbol
      graphData data lens hab hac position
  have hperm := lens.fusionMonodromy.ofFn_comp_perm cState
  rw [hstate] at hperm
  change (List.ofFn bState).Perm (List.ofFn cState)
  exact hperm

/-- Total transfer parity in `(a,b)` route order. -/
def bFusionTotalTwist
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : Bool :=
  fusionFaceWordTwist (bFusionFaceWord graphData data lens hab hac)

/-- Total transfer parity in transported `(a,c)` route order. -/
def cFusionTotalTwistOnCount
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : Bool :=
  fusionFaceWordTwist
    (cFusionFaceWordOnCount graphData data lens hab hac)

/-- Total fusion-transfer parity is invariant under changing between the
two route orders. -/
theorem bFusionTotalTwist_eq_cFusionTotalTwistOnCount
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    bFusionTotalTwist graphData data lens hab hac =
      cFusionTotalTwistOnCount graphData data lens hab hac := by
  exact fusionFaceWordTwist_eq_of_perm
    (bFusionFaceWord_perm_cFusionFaceWordOnCount
      graphData data lens hab hac)

/-- Composite route transfer in `(a,b)` route order. -/
def bFusionTotalTransfer
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : Equiv.Perm Bool :=
  fusionFaceWordTransfer (bFusionFaceWord graphData data lens hab hac)

/-- Composite route transfer in transported `(a,c)` route order. -/
def cFusionTotalTransferOnCount
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : Equiv.Perm Bool :=
  fusionFaceWordTransfer
    (cFusionFaceWordOnCount graphData data lens hab hac)

/-- The two route-order computations give the same composite transfer. -/
theorem bFusionTotalTransfer_eq_cFusionTotalTransferOnCount
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    bFusionTotalTransfer graphData data lens hab hac =
      cFusionTotalTransferOnCount graphData data lens hab hac := by
  exact fusionFaceWordTransfer_eq_of_perm
    (bFusionFaceWord_perm_cFusionFaceWordOnCount
      graphData data lens hab hac)

/-- The total transfer is exactly the Boolean permutation represented by
the total twist parity. -/
theorem bFusionTotalTransfer_eq_boolRoutePermutation_totalTwist
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    bFusionTotalTransfer graphData data lens hab hac =
      boolRoutePermutation
        (bFusionTotalTwist graphData data lens hab hac) :=
  fusionFaceWordTransfer_eq_boolRoutePermutation_twist _

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
