import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSharedSiteCycle

namespace Mettapedia.GraphTheory.FourColor

/-- Every nonidentity permutation of a finite linear order has a descent at
two consecutive positions. -/
theorem finPermutation_exists_adjacent_inversion_of_ne_refl {n : Nat}
    (permutation : Equiv.Perm (Fin n))
    (hne : permutation ≠ Equiv.refl (Fin n)) :
    ∃ first second : Fin n,
      first.val + 1 = second.val ∧
        permutation second < permutation first := by
  have hnotMono : ¬StrictMono permutation := by
    intro hmono
    exact hne (finPermutation_eq_refl_of_strictMono permutation hmono)
  cases n with
  | zero =>
      exact False.elim (hnotMono fun first ↦ Fin.elim0 first)
  | succ n =>
      rw [Fin.strictMono_iff_lt_succ] at hnotMono
      push Not at hnotMono
      rcases hnotMono with ⟨position, hnotIncreasing⟩
      have hle : permutation position.succ ≤
          permutation position.castSucc := hnotIncreasing
      have hneImage : permutation position.succ ≠
          permutation position.castSucc := by
        intro heq
        exact (show position.castSucc < position.succ from
          Fin.castSucc_lt_succ).ne
          (permutation.injective heq).symm
      exact ⟨position.castSucc, position.succ, by simp,
        lt_of_le_of_ne hle hneImage⟩

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- At a common route edge, both through-splice orientations are coherent:
entering along either route and leaving along the other uses different
endpoints of the shared edge. -/
def EvenKempeFusionLens.ThroughSpliceCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : Prop :=
  lens.cEntryVertex hac site ≠ lens.bExitVertex hab site ∧
    lens.bEntryVertex hab site ≠ lens.cExitVertex hac site

/-- A return splice joins the two route prefixes at their common terminal
edge. It is coherent when the two incoming incidences use opposite endpoints
of that edge. -/
def EvenKempeFusionLens.ReturnSpliceCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : Prop :=
  lens.bEntryVertex hab site ≠ lens.cEntryVertex hac site

/-- Positive chirality is exactly coherence of the through-splice. -/
theorem EvenKempeFusionLens.throughSpliceCoherent_iff_chirality_eq_true
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.ThroughSpliceCoherent hab hac site ↔
      lens.fusionChirality hab hac site = true := by
  constructor
  · intro hcoherent
    cases hchirality : lens.fusionChirality hab hac site
    · have hreverse :=
        (lens.fusionChirality_eq_false_iff_endpoints_reverse
          hab hac site).1 hchirality
      exact False.elim (hcoherent.1 hreverse.1)
    · rfl
  · intro hpositive
    have hagree :=
      (lens.fusionChirality_eq_true_iff_endpoints_agree
        hab hac site).1 hpositive
    rw [EvenKempeFusionLens.ThroughSpliceCoherent, hagree.1, hagree.2]
    exact ⟨lens.bEntryVertex_ne_bExitVertex hab site,
      lens.bEntryVertex_ne_bExitVertex hab site⟩

/-- Negative chirality is exactly coherence of the prefix-return splice. -/
theorem EvenKempeFusionLens.returnSpliceCoherent_iff_chirality_eq_false
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.ReturnSpliceCoherent hab hac site ↔
      lens.fusionChirality hab hac site = false := by
  constructor
  · intro hcoherent
    cases hchirality : lens.fusionChirality hab hac site
    · rfl
    · have hagree :=
        (lens.fusionChirality_eq_true_iff_endpoints_agree
          hab hac site).1 hchirality
      exact False.elim (hcoherent hagree.1.symm)
  · intro hnegative
    have hreverse :=
      (lens.fusionChirality_eq_false_iff_endpoints_reverse
        hab hac site).1 hnegative
    rw [EvenKempeFusionLens.ReturnSpliceCoherent, hreverse.1]
    exact lens.bEntryVertex_ne_bExitVertex hab site

/-- The explicit line-graph loop obtained by following the first inversion
interval and returning along the second. -/
def EvenKempeFusionLens.fusionOrderInversionLoop
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    G.lineGraph.Walk (lens.fusionSupportEdgeAt first)
      (lens.fusionSupportEdgeAt first) :=
  (lens.bFusionOrderInterval first second hbOrder).append
    (lens.cFusionOrderInterval first second hcOrder).reverse

/-- The explicit return loop obtained from the two left-to-site prefixes. -/
def EvenKempeFusionLens.fusionSiteLeftReturnLoop
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    G.lineGraph.Walk lens.bRoute.leftEdge.1 lens.bRoute.leftEdge.1 :=
  (lens.bAmbientPrefixToFusion site).append
    (lens.cLeftConnectedPrefixToFusion site).reverse

theorem EvenKempeFusionLens.fusionOrderInversionLoop_length_lt_closedWalk
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.fusionOrderInversionLoop first second hbOrder hcOrder).length <
      lens.closedWalk.length := by
  rw [EvenKempeFusionLens.fusionOrderInversionLoop,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    lens.closedWalk_length]
  have hb := lens.bFusionOrderInterval_length_le_ambientPath
    first second hbOrder
  have hc := lens.cFusionOrderInterval_length_le_ambientPath
    first second hcOrder
  simp only [EvenKempePortPath.ambientPath_length] at hb hc
  omega

theorem EvenKempeFusionLens.fusionSiteLeftReturnLoop_length_lt_closedWalk
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.fusionSiteLeftReturnLoop site).length <
      lens.closedWalk.length := by
  rw [EvenKempeFusionLens.fusionSiteLeftReturnLoop,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    lens.cLeftConnectedPrefixToFusion_length site,
    lens.closedWalk_length]
  have hb := lens.bAmbientPrefixToFusion_length_lt_ambientPath
    hab hac site
  have hc := lens.cAmbientPrefixToFusion_length_lt_ambientPath
    hab hac site
  simp only [EvenKempePortPath.ambientPath_length] at hb hc
  omega

/-- Signed nontriviality has a no-bounce refinement: either there is an
adjacent order inversion with coherent through-splices at both ends, or
there is a coherent return splice at one fusion site. -/
theorem EvenKempeFusionLens.exists_positiveAdjacentInversion_or_coherentReturn_of_signedMonodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    (∃ first second : Fin lens.fusionSiteCount,
        first.val + 1 = second.val ∧
        lens.bFusionSupportOrderEmbedding first <
          lens.bFusionSupportOrderEmbedding second ∧
        lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy second)) <
          lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy first)) ∧
        lens.ThroughSpliceCoherent hab hac
          (lens.bFusionSiteAt first) ∧
        lens.ThroughSpliceCoherent hab hac
          (lens.bFusionSiteAt second)) ∨
      ∃ position : Fin lens.fusionSiteCount,
        lens.ReturnSpliceCoherent hab hac
          (lens.bFusionSiteAt position) := by
  by_cases hmonodromy : lens.fusionMonodromy =
      Equiv.refl (Fin lens.fusionSiteCount)
  · right
    rcases lens.exists_orderInversion_or_negativeChirality_of_signedMonodromy_ne_refl
      hab hac hsigned with hinversion | ⟨position, hnegative⟩
    · rcases hinversion with ⟨first, second, hfirstSecond, hsecondFirst⟩
      rw [hmonodromy] at hsecondFirst
      exact False.elim (lt_asymm hfirstSecond hsecondFirst)
    · exact ⟨position,
        (lens.returnSpliceCoherent_iff_chirality_eq_false
          hab hac (lens.bFusionSiteAt position)).2 hnegative⟩
  · rcases finPermutation_exists_adjacent_inversion_of_ne_refl
      lens.fusionMonodromy hmonodromy with
      ⟨first, second, hadjacent, hreverse⟩
    have hfirstSecond : first < second := by
      rw [Fin.lt_def]
      omega
    have hbOrder : lens.bFusionSupportOrderEmbedding first <
        lens.bFusionSupportOrderEmbedding second :=
      (lens.bFusionSupportOrderEmbedding.lt_iff_lt).2 hfirstSecond
    have hcOrder : lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy second)) <
        lens.cFusionSupportOrderEmbedding
          (finCongr lens.fusionSites_length_eq
            (lens.fusionMonodromy first)) := by
      apply (lens.cFusionSupportOrderEmbedding.lt_iff_lt).2
      exact hreverse
    cases hfirstChirality : lens.bOrderedFusionChirality hab hac first
    · right
      refine ⟨first, ?_⟩
      apply (lens.returnSpliceCoherent_iff_chirality_eq_false
        hab hac (lens.bFusionSiteAt first)).2
      exact hfirstChirality
    · cases hsecondChirality : lens.bOrderedFusionChirality hab hac second
      · right
        refine ⟨second, ?_⟩
        apply (lens.returnSpliceCoherent_iff_chirality_eq_false
          hab hac (lens.bFusionSiteAt second)).2
        exact hsecondChirality
      · left
        refine ⟨first, second, hadjacent, hbOrder, hcOrder, ?_, ?_⟩
        · apply (lens.throughSpliceCoherent_iff_chirality_eq_true
            hab hac (lens.bFusionSiteAt first)).2
          exact hfirstChirality
        · apply (lens.throughSpliceCoherent_iff_chirality_eq_true
            hab hac (lens.bFusionSiteAt second)).2
          exact hsecondChirality

/-- Consequently, every nontrivial signed monodromy produces one of two
explicit shorter line-graph loops together with the local coherence facts
needed to lift its fusion junctions to primal traversal. -/
theorem EvenKempeFusionLens.exists_coherent_shorterLoop_of_signedMonodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    (∃ first second : Fin lens.fusionSiteCount,
        first.val + 1 = second.val ∧
        ∃ hbOrder : lens.bFusionSupportOrderEmbedding first <
          lens.bFusionSupportOrderEmbedding second,
        ∃ hcOrder : lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy second)) <
          lens.cFusionSupportOrderEmbedding
            (finCongr lens.fusionSites_length_eq
              (lens.fusionMonodromy first)),
          (lens.fusionOrderInversionLoop first second
              hbOrder hcOrder).length < lens.closedWalk.length ∧
          lens.ThroughSpliceCoherent hab hac
            (lens.bFusionSiteAt first) ∧
          lens.ThroughSpliceCoherent hab hac
            (lens.bFusionSiteAt second)) ∨
      ∃ position : Fin lens.fusionSiteCount,
        (lens.fusionSiteLeftReturnLoop
            (lens.bFusionSiteAt position)).length <
          lens.closedWalk.length ∧
        lens.ReturnSpliceCoherent hab hac
          (lens.bFusionSiteAt position) := by
  rcases lens.exists_positiveAdjacentInversion_or_coherentReturn_of_signedMonodromy_ne_refl
    hab hac hsigned with hinversion | hreturn
  · rcases hinversion with
      ⟨first, second, hadjacent, hbOrder, hcOrder,
        hfirstCoherent, hsecondCoherent⟩
    exact Or.inl ⟨first, second, hadjacent, hbOrder, hcOrder,
      lens.fusionOrderInversionLoop_length_lt_closedWalk
        first second hbOrder hcOrder,
      hfirstCoherent, hsecondCoherent⟩
  · rcases hreturn with ⟨position, hcoherent⟩
    exact Or.inr ⟨position,
      lens.fusionSiteLeftReturnLoop_length_lt_closedWalk
        hab hac (lens.bFusionSiteAt position), hcoherent⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
