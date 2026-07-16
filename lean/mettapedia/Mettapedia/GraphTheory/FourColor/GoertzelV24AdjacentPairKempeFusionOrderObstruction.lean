import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceNetwork

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

/-- A strictly increasing permutation of a finite linear order is the
identity. -/
theorem finPermutation_eq_refl_of_strictMono {n : Nat}
    (permutation : Equiv.Perm (Fin n))
    (hmono : StrictMono permutation) :
    permutation = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro position
  exact le_antisymm hmono.apply_le hmono.le_apply

/-- Every nonidentity permutation of a finite linear order has an
inversion. -/
theorem finPermutation_exists_inversion_of_ne_refl {n : Nat}
    (permutation : Equiv.Perm (Fin n))
    (hne : permutation ≠ Equiv.refl (Fin n)) :
    ∃ first second : Fin n,
      first < second ∧ permutation second < permutation first := by
  by_contra hnoInversion
  apply hne
  apply finPermutation_eq_refl_of_strictMono permutation
  intro first second hfirstSecond
  by_contra hnotIncreasing
  have hle : permutation second ≤ permutation first :=
    le_of_not_gt hnotIncreasing
  have hneImage : permutation second ≠ permutation first := by
    intro heq
    exact hfirstSecond.ne
      (permutation.injective heq).symm
  exact hnoInversion
    ⟨first, second, hfirstSecond, lt_of_le_of_ne hle hneImage⟩

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Filtering the first route support to fusion sites preserves their
order as a sublist. -/
theorem EvenKempeFusionLens.bFusionSites_sublist_ambientPath_support
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.bFusionSites.Sublist lens.bRoute.ambientPath.support := by
  exact List.filter_sublist

/-- The analogous ordered inclusion into the second route support. -/
theorem EvenKempeFusionLens.cFusionSites_sublist_ambientPath_support
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.cFusionSites.Sublist lens.cRoute.ambientPath.support := by
  exact List.filter_sublist

/-- The canonical order embedding of fusion positions into positions of
the first route support. -/
def EvenKempeFusionLens.bFusionSupportOrderEmbedding
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    Fin lens.bFusionSites.length ↪o
      Fin lens.bRoute.ambientPath.support.length :=
  Classical.choose
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      lens.bFusionSites_sublist_ambientPath_support)

/-- The selected support position carries the same fusion edge. -/
theorem EvenKempeFusionLens.bFusionSupportOrderEmbedding_preserves_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.bFusionSites.length) :
    lens.bFusionSites.get position =
      lens.bRoute.ambientPath.support.get
        (lens.bFusionSupportOrderEmbedding position) :=
  Classical.choose_spec
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      lens.bFusionSites_sublist_ambientPath_support) position

/-- The canonical order embedding of fusion positions into positions of
the second route support. -/
def EvenKempeFusionLens.cFusionSupportOrderEmbedding
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    Fin lens.cFusionSites.length ↪o
      Fin lens.cRoute.ambientPath.support.length :=
  Classical.choose
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      lens.cFusionSites_sublist_ambientPath_support)

/-- The second support embedding likewise preserves the underlying edge. -/
theorem EvenKempeFusionLens.cFusionSupportOrderEmbedding_preserves_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.cFusionSites.length) :
    lens.cFusionSites.get position =
      lens.cRoute.ambientPath.support.get
        (lens.cFusionSupportOrderEmbedding position) :=
  Classical.choose_spec
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      lens.cFusionSites_sublist_ambientPath_support) position

/-- A fusion position and its monodromy image select the same graph edge
in the two ambient route supports. -/
theorem EvenKempeFusionLens.support_get_fusionMonodromy_eq
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    lens.bRoute.ambientPath.support.get
        (lens.bFusionSupportOrderEmbedding position) =
      lens.cRoute.ambientPath.support.get
        (lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy position))) := by
  have hposition :
      finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy position) =
        lens.fusionOrderEquiv position := by
    apply Fin.ext
    rfl
  calc
    lens.bRoute.ambientPath.support.get
          (lens.bFusionSupportOrderEmbedding position) =
        lens.bFusionSites.get position :=
      (lens.bFusionSupportOrderEmbedding_preserves_edge position).symm
    _ = lens.cFusionSites.get (lens.fusionOrderEquiv position) :=
      (lens.fusionOrderEquiv_preserves_edge position).symm
    _ = lens.cRoute.ambientPath.support.get
          (lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy position))) := by
      rw [hposition]
      exact lens.cFusionSupportOrderEmbedding_preserves_edge _

/-- Nontrivial fusion-site order produces two shared edges encountered in
opposite orders by the two Kempe routes. -/
theorem EvenKempeFusionLens.exists_fusionOrderInversion_of_monodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hmonodromy : lens.fusionMonodromy ≠
      Equiv.refl (Fin lens.fusionSiteCount)) :
    ∃ first second : Fin lens.fusionSiteCount,
      first < second ∧
        lens.fusionMonodromy second < lens.fusionMonodromy first :=
  finPermutation_exists_inversion_of_ne_refl
    lens.fusionMonodromy hmonodromy

/-- The abstract inversion is realized by two actual common edges whose
positions increase along the first ambient route and decrease along the
second. -/
theorem EvenKempeFusionLens.exists_ambientSupportOrderInversion_of_monodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hmonodromy : lens.fusionMonodromy ≠
      Equiv.refl (Fin lens.fusionSiteCount)) :
    ∃ first second : Fin lens.fusionSiteCount,
      lens.bFusionSupportOrderEmbedding first <
          lens.bFusionSupportOrderEmbedding second ∧
        lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy second)) <
          lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy first)) ∧
        lens.bRoute.ambientPath.support.get
            (lens.bFusionSupportOrderEmbedding first) =
          lens.cRoute.ambientPath.support.get
            (lens.cFusionSupportOrderEmbedding
              (finCongr lens.fusionSites_length_eq
                (lens.fusionMonodromy first))) ∧
        lens.bRoute.ambientPath.support.get
            (lens.bFusionSupportOrderEmbedding second) =
          lens.cRoute.ambientPath.support.get
            (lens.cFusionSupportOrderEmbedding
              (finCongr lens.fusionSites_length_eq
                (lens.fusionMonodromy second))) := by
  rcases lens.exists_fusionOrderInversion_of_monodromy_ne_refl
    hmonodromy with ⟨first, second, hfirstSecond, hreverse⟩
  refine ⟨first, second,
    (lens.bFusionSupportOrderEmbedding.lt_iff_lt).2 hfirstSecond,
    ?_, lens.support_get_fusionMonodromy_eq first,
    lens.support_get_fusionMonodromy_eq second⟩
  apply (lens.cFusionSupportOrderEmbedding.lt_iff_lt).2
  exact hreverse

/-- A nontrivial signed fusion monodromy has exactly the two kinds of
geometric obstruction needed for shortening: either an order inversion,
or a shared edge traversed with negative chirality. -/
theorem EvenKempeFusionLens.exists_orderInversion_or_negativeChirality_of_signedMonodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    (∃ first second : Fin lens.fusionSiteCount,
        first < second ∧
          lens.fusionMonodromy second < lens.fusionMonodromy first) ∨
      ∃ position : Fin lens.fusionSiteCount,
        lens.bOrderedFusionChirality hab hac position = false := by
  by_cases hmonodromy : lens.fusionMonodromy =
      Equiv.refl (Fin lens.fusionSiteCount)
  · right
    by_contra hnoNegative
    have hpositive : ∀ position : Fin lens.fusionSiteCount,
        lens.bOrderedFusionChirality hab hac position = true := by
      intro position
      cases hchirality : lens.bOrderedFusionChirality hab hac position
      · exact False.elim (hnoNegative ⟨position, hchirality⟩)
      · rfl
    exact hsigned
      ((lens.signedFusionMonodromy_eq_refl_iff hab hac).2
        ⟨hmonodromy, hpositive⟩)
  · left
    exact lens.exists_fusionOrderInversion_of_monodromy_ne_refl
      hmonodromy

/-- Conversely, either shortening witness makes the signed monodromy
nontrivial. -/
theorem EvenKempeFusionLens.signedFusionMonodromy_ne_refl_of_orderInversion_or_negativeChirality
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hobstruction :
      (∃ first second : Fin lens.fusionSiteCount,
          first < second ∧
            lens.fusionMonodromy second < lens.fusionMonodromy first) ∨
        ∃ position : Fin lens.fusionSiteCount,
          lens.bOrderedFusionChirality hab hac position = false) :
    lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool) := by
  rcases hobstruction with hinversion | hnegative
  · rcases hinversion with ⟨first, second, hfirstSecond, hreverse⟩
    apply lens.signedFusionMonodromy_ne_refl_of_monodromy_ne_refl
      hab hac
    intro htrivial
    rw [htrivial] at hreverse
    exact (lt_asymm hfirstSecond hreverse)
  · rcases hnegative with ⟨position, hchirality⟩
    exact lens.signedFusionMonodromy_ne_refl_of_chirality_eq_false
      hab hac position hchirality

/-- Hence nontrivial signed fusion monodromy is equivalent to the explicit
finite disjunction of an order inversion and a negative-chirality site. -/
theorem EvenKempeFusionLens.signedFusionMonodromy_ne_refl_iff_exists_obstruction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.signedFusionMonodromy hab hac ≠
        Equiv.refl (Fin lens.fusionSiteCount × Bool) ↔
      (∃ first second : Fin lens.fusionSiteCount,
          first < second ∧
            lens.fusionMonodromy second < lens.fusionMonodromy first) ∨
        ∃ position : Fin lens.fusionSiteCount,
          lens.bOrderedFusionChirality hab hac position = false := by
  exact ⟨lens.exists_orderInversion_or_negativeChirality_of_signedMonodromy_ne_refl
      hab hac,
    lens.signedFusionMonodromy_ne_refl_of_orderInversion_or_negativeChirality
      hab hac⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionOrderObstructionGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance fusionOrderObstructionRetainedVertexFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance fusionOrderObstructionRetainedVertexDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- The signed obstruction dichotomy in ambient geometric form: either
two actual common edges occur in opposite support orders, or one common
edge is traversed by the two routes with opposite ambient darts. -/
theorem exists_ambientOrderInversion_or_reversedFusionDart_of_signedMonodromy_ne_refl
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    (∃ first second : Fin lens.fusionSiteCount,
        lens.bFusionSupportOrderEmbedding first <
            lens.bFusionSupportOrderEmbedding second ∧
          lens.cFusionSupportOrderEmbedding
              (finCongr lens.fusionSites_length_eq
                (lens.fusionMonodromy second)) <
            lens.cFusionSupportOrderEmbedding
              (finCongr lens.fusionSites_length_eq
                (lens.fusionMonodromy first))) ∨
      ∃ position : Fin lens.fusionSiteCount,
        ambientCFusionDart data lens hac (lens.bFusionSiteAt position) =
          (ambientBFusionDart data lens hab
            (lens.bFusionSiteAt position)).symm := by
  rcases
      lens.exists_orderInversion_or_negativeChirality_of_signedMonodromy_ne_refl
        hab hac hsigned with hinversion | hnegative
  · left
    rcases hinversion with ⟨first, second, hfirstSecond, hreverse⟩
    exact ⟨first, second,
      (lens.bFusionSupportOrderEmbedding.lt_iff_lt).2 hfirstSecond,
      (lens.cFusionSupportOrderEmbedding.lt_iff_lt).2 hreverse⟩
  · right
    rcases hnegative with ⟨position, hchirality⟩
    refine ⟨position,
      (fusionChirality_eq_false_iff_ambientCFusionDart_eq_ambientBFusionDart_symm
        data lens hab hac (lens.bFusionSiteAt position)).1 ?_⟩
    exact hchirality

/-- Conversely, either ambient shortening configuration forces signed
monodromy to be nontrivial. -/
theorem signedMonodromy_ne_refl_of_ambientOrderInversion_or_reversedFusionDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hobstruction :
      (∃ first second : Fin lens.fusionSiteCount,
          lens.bFusionSupportOrderEmbedding first <
              lens.bFusionSupportOrderEmbedding second ∧
            lens.cFusionSupportOrderEmbedding
                (finCongr lens.fusionSites_length_eq
                  (lens.fusionMonodromy second)) <
              lens.cFusionSupportOrderEmbedding
                (finCongr lens.fusionSites_length_eq
                  (lens.fusionMonodromy first))) ∨
        ∃ position : Fin lens.fusionSiteCount,
          ambientCFusionDart data lens hac (lens.bFusionSiteAt position) =
            (ambientBFusionDart data lens hab
              (lens.bFusionSiteAt position)).symm) :
    lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool) := by
  rcases hobstruction with hinversion | hreverse
  · rcases hinversion with ⟨first, second, hfirstSecond, hsecondFirst⟩
    apply lens.signedFusionMonodromy_ne_refl_of_monodromy_ne_refl hab hac
    intro htrivial
    rw [htrivial] at hsecondFirst
    have hfirstSecond' : first < second :=
      (lens.bFusionSupportOrderEmbedding.lt_iff_lt).1 hfirstSecond
    have hsecondFirst' : second < first :=
      (lens.cFusionSupportOrderEmbedding.lt_iff_lt).1 hsecondFirst
    exact lt_asymm hfirstSecond' hsecondFirst'
  · rcases hreverse with ⟨position, hreverse⟩
    apply lens.signedFusionMonodromy_ne_refl_of_chirality_eq_false
      hab hac position
    exact
      (fusionChirality_eq_false_iff_ambientCFusionDart_eq_ambientBFusionDart_symm
        data lens hab hac (lens.bFusionSiteAt position)).2 hreverse

/-- Nontrivial signed monodromy is therefore equivalent to the explicit
ambient shortening dichotomy. -/
theorem signedMonodromy_ne_refl_iff_exists_ambient_obstruction
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.signedFusionMonodromy hab hac ≠
        Equiv.refl (Fin lens.fusionSiteCount × Bool) ↔
      (∃ first second : Fin lens.fusionSiteCount,
          lens.bFusionSupportOrderEmbedding first <
              lens.bFusionSupportOrderEmbedding second ∧
            lens.cFusionSupportOrderEmbedding
                (finCongr lens.fusionSites_length_eq
                  (lens.fusionMonodromy second)) <
              lens.cFusionSupportOrderEmbedding
                (finCongr lens.fusionSites_length_eq
                  (lens.fusionMonodromy first))) ∨
        ∃ position : Fin lens.fusionSiteCount,
          ambientCFusionDart data lens hac (lens.bFusionSiteAt position) =
            (ambientBFusionDart data lens hab
              (lens.bFusionSiteAt position)).symm := by
  exact ⟨exists_ambientOrderInversion_or_reversedFusionDart_of_signedMonodromy_ne_refl
      data lens hab hac,
    signedMonodromy_ne_refl_of_ambientOrderInversion_or_reversedFusionDart
      data lens hab hac⟩

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
