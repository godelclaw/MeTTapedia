import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalTurns

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary

/-- Transport an oriented endpoint through a local fusion edge.  Positive
chirality preserves the endpoint and negative chirality reverses it. -/
def fusionEndpointTransport (chirality endpoint : Bool) : Bool :=
  if chirality = true then endpoint else !endpoint

@[simp] theorem fusionEndpointTransport_true (endpoint : Bool) :
    fusionEndpointTransport true endpoint = endpoint := by
  simp [fusionEndpointTransport]

@[simp] theorem fusionEndpointTransport_false (endpoint : Bool) :
    fusionEndpointTransport false endpoint = !endpoint := by
  simp [fusionEndpointTransport]

/-- Endpoint transport is an involution for either chirality. -/
@[simp] theorem fusionEndpointTransport_involutive
    (chirality endpoint : Bool) :
    fusionEndpointTransport chirality
        (fusionEndpointTransport chirality endpoint) = endpoint := by
  cases chirality <;> cases endpoint <;>
    rfl

/-- Lift a finite position permutation to oriented positions, reversing
the endpoint bit precisely at the negatively signed positions. -/
def signedIndexPermutation {ι : Type*}
    (permutation : Equiv.Perm ι) (chirality : ι → Bool) :
    Equiv.Perm (ι × Bool) where
  toFun state :=
    (permutation state.1,
      fusionEndpointTransport (chirality state.1) state.2)
  invFun state :=
    (permutation.symm state.1,
      fusionEndpointTransport
        (chirality (permutation.symm state.1)) state.2)
  left_inv state := by
    rcases state with ⟨position, endpoint⟩
    apply Prod.ext
    · simp
    · simp
  right_inv state := by
    rcases state with ⟨position, endpoint⟩
    apply Prod.ext
    · simp
    · simp

@[simp] theorem signedIndexPermutation_apply_fst {ι : Type*}
    (permutation : Equiv.Perm ι) (chirality : ι → Bool)
    (state : ι × Bool) :
    (signedIndexPermutation permutation chirality state).1 =
      permutation state.1 :=
  rfl

@[simp] theorem signedIndexPermutation_apply_snd {ι : Type*}
    (permutation : Equiv.Perm ι) (chirality : ι → Bool)
    (state : ι × Bool) :
    (signedIndexPermutation permutation chirality state).2 =
      fusionEndpointTransport (chirality state.1) state.2 :=
  rfl

/-- A signed position permutation is trivial exactly when its underlying
position permutation is trivial and every local sign preserves endpoints. -/
theorem signedIndexPermutation_eq_refl_iff {ι : Type*}
    (permutation : Equiv.Perm ι) (chirality : ι → Bool) :
    signedIndexPermutation permutation chirality =
        Equiv.refl (ι × Bool) ↔
      permutation = Equiv.refl ι ∧
        ∀ position : ι, chirality position = true := by
  constructor
  · intro hsigned
    constructor
    · apply Equiv.ext
      intro position
      have hstate := congrArg
        (fun signed : Equiv.Perm (ι × Bool) ↦ signed (position, false))
        hsigned
      have hfst := congrArg Prod.fst hstate
      simpa using hfst
    · intro position
      have hstate := congrArg
        (fun signed : Equiv.Perm (ι × Bool) ↦ signed (position, false))
        hsigned
      have hsnd := congrArg Prod.snd hstate
      change fusionEndpointTransport (chirality position) false = false
        at hsnd
      cases hchirality : chirality position with
      | false => simp [hchirality] at hsnd
      | true => rfl
  · rintro ⟨hpermutation, hchirality⟩
    apply Equiv.ext
    rintro ⟨position, endpoint⟩
    apply Prod.ext
    · simp [signedIndexPermutation, hpermutation]
    · simp [signedIndexPermutation, hchirality position]

/-- Select the dart based at one of the two endpoints of an oriented edge.
`false` denotes its source and `true` its target. -/
def fusionEndpointDart {V : Type*} {G : SimpleGraph V}
    (dart : G.Dart) (endpoint : Bool) : G.Dart :=
  if endpoint = true then dart.symm else dart

@[simp] theorem fusionEndpointDart_false
    {V : Type*} {G : SimpleGraph V} (dart : G.Dart) :
    fusionEndpointDart dart false = dart := by
  simp [fusionEndpointDart]

@[simp] theorem fusionEndpointDart_true
    {V : Type*} {G : SimpleGraph V} (dart : G.Dart) :
    fusionEndpointDart dart true = dart.symm := by
  simp [fusionEndpointDart]

/-- Reversing an oriented edge and reversing its endpoint bit names the
same based dart. -/
@[simp] theorem fusionEndpointDart_symm_not
    {V : Type*} {G : SimpleGraph V}
    (dart : G.Dart) (endpoint : Bool) :
    fusionEndpointDart dart.symm (!endpoint) =
      fusionEndpointDart dart endpoint := by
  cases endpoint <;>
    simp [fusionEndpointDart]

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The signed fusion monodromy acts on a fusion position together with
one of its two oriented endpoints. -/
def EvenKempeFusionLens.signedFusionMonodromy {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    Equiv.Perm (Fin lens.fusionSiteCount × Bool) :=
  signedIndexPermutation lens.fusionMonodromy
    (lens.bOrderedFusionChirality hab hac)

@[simp] theorem EvenKempeFusionLens.signedFusionMonodromy_apply_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : Fin lens.fusionSiteCount × Bool) :
    (lens.signedFusionMonodromy hab hac state).1 =
      lens.fusionMonodromy state.1 :=
  rfl

@[simp] theorem EvenKempeFusionLens.signedFusionMonodromy_apply_snd
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : Fin lens.fusionSiteCount × Bool) :
    (lens.signedFusionMonodromy hab hac state).2 =
      fusionEndpointTransport
        (lens.bOrderedFusionChirality hab hac state.1) state.2 :=
  rfl

/-- The signed fusion monodromy is trivial exactly when the fusion sites
occur in the same order on both routes and every shared edge is traversed
with positive chirality. -/
theorem EvenKempeFusionLens.signedFusionMonodromy_eq_refl_iff
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.signedFusionMonodromy hab hac =
        Equiv.refl (Fin lens.fusionSiteCount × Bool) ↔
      lens.fusionMonodromy =
          Equiv.refl (Fin lens.fusionSiteCount) ∧
        ∀ position : Fin lens.fusionSiteCount,
          lens.bOrderedFusionChirality hab hac position = true :=
  signedIndexPermutation_eq_refl_iff _ _

/-- A single negatively chiral fusion edge makes the signed monodromy
nontrivial, even when the unsigned position order happens to close. -/
theorem EvenKempeFusionLens.signedFusionMonodromy_ne_refl_of_chirality_eq_false
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount)
    (hchirality :
      lens.bOrderedFusionChirality hab hac position = false) :
    lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool) := by
  intro htrivial
  have hpositive :=
    (lens.signedFusionMonodromy_eq_refl_iff hab hac).1 htrivial |>.2
      position
  rw [hchirality] at hpositive
  contradiction

/-- Nontrivial fusion-site order already forces nontrivial signed
monodromy. -/
theorem EvenKempeFusionLens.signedFusionMonodromy_ne_refl_of_monodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hmonodromy : lens.fusionMonodromy ≠
      Equiv.refl (Fin lens.fusionSiteCount)) :
    lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool) := by
  intro htrivial
  exact hmonodromy
    ((lens.signedFusionMonodromy_eq_refl_iff hab hac).1 htrivial).1

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance signedFusionGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance signedFusionRetainedVertexFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance signedFusionRetainedVertexDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- Interpret a signed state in `(a,b)` route order as its actual ambient
dart based at the selected endpoint of the fusion edge. -/
def bFusionEndpointDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b)
    (state : Fin lens.fusionSiteCount × Bool) : G.Dart :=
  fusionEndpointDart
    (ambientBFusionDart data lens hab
      (lens.bFusionSiteAt state.1)) state.2

/-- Interpret a signed state in the transported `(a,c)` route order. -/
def cFusionEndpointDartOnCount
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hac : a ≠ c)
    (state : Fin lens.fusionSiteCount × Bool) : G.Dart :=
  fusionEndpointDart
    (ambientCFusionDart data lens hac
      (lens.cFusionSiteAt
        (finCongr lens.fusionSites_length_eq state.1))) state.2

/-- Transporting a position by fusion monodromy identifies the same
underlying fusion site in the second route order. -/
theorem cFusionSiteAtOnCount_fusionMonodromy
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    lens.cFusionSiteAt
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy position)) =
      lens.bFusionSiteAt position := by
  have hposition :
      finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy position) =
        lens.fusionOrderEquiv position := by
    apply Fin.ext
    rfl
  rw [hposition, lens.cFusionSiteAt_fusionOrderEquiv]

/-- Signed monodromy preserves the actual based ambient dart.  Its
endpoint reversal is therefore exactly the geometric effect of negative
fusion chirality. -/
theorem cFusionEndpointDartOnCount_signedFusionMonodromy
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : Fin lens.fusionSiteCount × Bool) :
    cFusionEndpointDartOnCount data lens hac
        (lens.signedFusionMonodromy hab hac state) =
      bFusionEndpointDart data lens hab state := by
  rcases state with ⟨position, endpoint⟩
  change fusionEndpointDart
      (ambientCFusionDart data lens hac
        (lens.cFusionSiteAt
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy position))))
      (fusionEndpointTransport
        (lens.bOrderedFusionChirality hab hac position) endpoint) =
    fusionEndpointDart
      (ambientBFusionDart data lens hab
        (lens.bFusionSiteAt position)) endpoint
  rw [cFusionSiteAtOnCount_fusionMonodromy data lens position]
  by_cases hchirality :
      lens.fusionChirality hab hac
        (lens.bFusionSiteAt position) = true
  · rw [(fusionChirality_eq_true_iff_ambientCFusionDart_eq_ambientBFusionDart
      data lens hab hac (lens.bFusionSiteAt position)).1 hchirality]
    have hordered :
        lens.bOrderedFusionChirality hab hac position = true :=
      hchirality
    rw [hordered]
    rfl
  · have hfalse : lens.fusionChirality hab hac
        (lens.bFusionSiteAt position) = false :=
      Bool.eq_false_of_not_eq_true hchirality
    rw [(fusionChirality_eq_false_iff_ambientCFusionDart_eq_ambientBFusionDart_symm
      data lens hab hac (lens.bFusionSiteAt position)).1 hfalse]
    have hordered :
        lens.bOrderedFusionChirality hab hac position = false :=
      hfalse
    rw [hordered]
    exact fusionEndpointDart_symm_not _ _

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
