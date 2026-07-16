import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionDisjointCircuit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A nonempty fusion list has a site that is encountered first along the
first Kempe route.  No other common route edge occurs in its prefix. -/
theorem EvenKempeFusionLens.exists_leftmostFusionSite
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hcount : 0 < lens.fusionSiteCount) :
    ∃ site : lens.FusionSite,
      ∀ edge : G.edgeSet,
        edge ∈ (lens.bAmbientPrefixToFusion site).support →
        edge ∈ lens.cRoute.ambientPath.support →
        edge = site.1 := by
  have hlistNonempty : lens.bFusionSites ≠ [] := by
    intro hnil
    have : lens.fusionSiteCount = 0 := by
      simp only [EvenKempeFusionLens.fusionSiteCount, hnil, List.length_nil]
    omega
  obtain ⟨edge, hedge⟩ :=
    List.exists_mem_of_ne_nil lens.bFusionSites hlistNonempty
  rcases lens.bRoute.ambientPath.exists_mem_support_forall_mem_support_imp_eq
      lens.bFusionSites.toFinset (by
        refine ⟨edge, ?_⟩
        simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨hedge, ((lens.mem_bFusionSites_iff edge).1 hedge).1⟩) with
    ⟨siteEdge, hsiteFinset, hsiteSupport, hfirst⟩
  have hsiteList : siteEdge ∈ lens.bFusionSites := by
    simpa only [List.mem_toFinset] using hsiteFinset
  let site : lens.FusionSite := ⟨siteEdge, hsiteList⟩
  refine ⟨site, ?_⟩
  intro candidate hprefix hcSupport
  have hbSupport : candidate ∈ lens.bRoute.ambientPath.support :=
    lens.bAmbientPrefixToFusion_support_subset site hprefix
  have hcandidateList : candidate ∈ lens.bFusionSites :=
    (lens.mem_bFusionSites_iff candidate).2 ⟨hbSupport, hcSupport⟩
  have hcandidateFinset : candidate ∈ lens.bFusionSites.toFinset := by
    simpa only [List.mem_toFinset]
  have hprefix' : candidate ∈
      (lens.bRoute.ambientPath.takeUntil siteEdge hsiteSupport).support := by
    simpa only [site, EvenKempeFusionLens.bAmbientPrefixToFusion] using hprefix
  simpa only [site] using
    hfirst candidate hcandidateFinset hprefix'

/-- At a leftmost fusion site, the two left prefixes form a simple cycle:
their only common route edge is the selected endpoint. -/
theorem EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop_isCycle_of_leftmost
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (site : lens.FusionSite)
    (hleftmost : ∀ edge : G.edgeSet,
      edge ∈ (lens.bAmbientPrefixToFusion site).support →
      edge ∈ lens.cRoute.ambientPath.support →
      edge = site.1) :
    (lens.fusionSiteLeftReturnOppositeLoop site).IsCycle := by
  let cPrefix := lens.cLeftConnectedPrefixToFusion site
  let bReverse := (lens.bAmbientPrefixToFusion site).reverse
  have hcPath : cPrefix.IsPath := by
    dsimp only [cPrefix]
    exact lens.cLeftConnectedPrefixToFusion_isPath hab hac site
  have hbPath : bReverse.IsPath := by
    dsimp only [bReverse]
    exact (lens.bAmbientPrefixToFusion site).isPath_reverse_iff.mpr
      (lens.bAmbientPrefixToFusion_isPath site)
  have hsiteNotMemBReverseTail : site.1 ∉ bReverse.support.tail := by
    have hnodup := hbPath.support_nodup
    rw [← bReverse.cons_tail_support] at hnodup
    have hstartNotMem := (List.nodup_cons.mp hnodup).1
    simpa only [bReverse, SimpleGraph.Walk.support_reverse,
      List.head_reverse, SimpleGraph.Walk.getVert_length] using hstartNotMem
  have hdisjoint : cPrefix.support.tail.Disjoint bReverse.support.tail := by
    rw [List.disjoint_left]
    intro edge hcTail hbTail
    have hcAmbientPrefix :
        edge ∈ (lens.cAmbientPrefixToFusion site).support := by
      simpa only [cPrefix,
        EvenKempeFusionLens.cLeftConnectedPrefixToFusion,
        SimpleGraph.Walk.support_cons, List.tail_cons] using hcTail
    have hcAmbient : edge ∈ lens.cRoute.ambientPath.support :=
      lens.cAmbientPrefixToFusion_support_subset site hcAmbientPrefix
    have hbReverseSupport : edge ∈ bReverse.support :=
      List.mem_of_mem_tail hbTail
    have hbPrefix : edge ∈
        (lens.bAmbientPrefixToFusion site).support := by
      simpa only [bReverse, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hbReverseSupport
    have hedge : edge = site.1 := hleftmost edge hbPrefix hcAmbient
    exact hsiteNotMemBReverseTail (hedge ▸ hbTail)
  have hcLong : 1 < cPrefix.length := by
    dsimp only [cPrefix]
    rw [lens.cLeftConnectedPrefixToFusion_length site]
    have hcPositive := lens.cAmbientPrefixToFusion_length_pos hab hac site
    omega
  rw [EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop]
  exact hcPath.isCycle_append hbPath hdisjoint (Or.inl hcLong)

/-- In the positive-chirality branch, contracting the selected shared edge
preserves that simple cycle. -/
theorem EvenKempeFusionLens.positiveFusionBounceShortcut_isCycle_of_leftmost
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hleftmost : ∀ edge : G.edgeSet,
      edge ∈ (lens.bAmbientPrefixToFusion site).support →
      edge ∈ lens.cRoute.ambientPath.support →
      edge = site.1)
    (hpositive : lens.fusionChirality hab hac site = true) :
    (lens.positiveFusionBounceShortcut
      hab hac hbc site hpositive).IsCycle := by
  let cPrefix := lens.cLeftConnectedPrefixToFusion site
  let bReverse := (lens.bAmbientPrefixToFusion site).reverse
  let shortcutAdj : G.lineGraph.Adj cPrefix.penultimate bReverse.snd := by
    simpa only [cPrefix, bReverse, SimpleGraph.Walk.snd_reverse,
      lens.cLeftConnectedPrefixToFusion_getVert_penultimate hab hac site,
      lens.bAmbientPrefixToFusion_getVert_penultimate hab site] using
        lens.positiveFusionShortcutAdj hab hac hbc site hpositive
  let bShortcut := SimpleGraph.Walk.cons shortcutAdj bReverse.tail
  let cDrop := cPrefix.dropLast
  have hcPath : cPrefix.IsPath := by
    dsimp only [cPrefix]
    exact lens.cLeftConnectedPrefixToFusion_isPath hab hac site
  have hbPath : bReverse.IsPath := by
    dsimp only [bReverse]
    exact (lens.bAmbientPrefixToFusion site).isPath_reverse_iff.mpr
      (lens.bAmbientPrefixToFusion_isPath site)
  have hcNotNil : ¬cPrefix.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact lens.cLeftConnectedPrefixToFusion_length_pos site
  have hbNotNil : ¬bReverse.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    dsimp only [bReverse]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens.bAmbientPrefixToFusion_length_pos hab hac site
  have hcTwo : 2 ≤ cPrefix.length := by
    dsimp only [cPrefix]
    rw [lens.cLeftConnectedPrefixToFusion_length site]
    have hcPositive := lens.cAmbientPrefixToFusion_length_pos hab hac site
    omega
  have hprefixDisjoint :
      cPrefix.support.tail.Disjoint bReverse.support.tail := by
    rw [List.disjoint_left]
    intro edge hcTail hbTail
    have hcAmbientPrefix :
        edge ∈ (lens.cAmbientPrefixToFusion site).support := by
      simpa only [cPrefix,
        EvenKempeFusionLens.cLeftConnectedPrefixToFusion,
        SimpleGraph.Walk.support_cons, List.tail_cons] using hcTail
    have hcAmbient : edge ∈ lens.cRoute.ambientPath.support :=
      lens.cAmbientPrefixToFusion_support_subset site hcAmbientPrefix
    have hbReverseSupport : edge ∈ bReverse.support :=
      List.mem_of_mem_tail hbTail
    have hbPrefix : edge ∈
        (lens.bAmbientPrefixToFusion site).support := by
      simpa only [bReverse, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using hbReverseSupport
    have hedge : edge = site.1 := hleftmost edge hbPrefix hcAmbient
    have hsiteNotMem : site.1 ∉ bReverse.support.tail := by
      have hnodup := hbPath.support_nodup
      rw [← bReverse.cons_tail_support] at hnodup
      have hstartNotMem := (List.nodup_cons.mp hnodup).1
      simpa only [bReverse, SimpleGraph.Walk.support_reverse,
        List.head_reverse, SimpleGraph.Walk.getVert_length] using hstartNotMem
    exact hsiteNotMem (hedge ▸ hbTail)
  have hshortcutStartMemC : cPrefix.penultimate ∈ cPrefix.support.tail := by
    exact cPrefix.getVert_mem_tail_support hcNotNil (by omega)
  have hshortcutStartNotMemB :
      cPrefix.penultimate ∉ bReverse.tail.support := by
    intro hmem
    have hmem' : cPrefix.penultimate ∈ bReverse.support.tail := by
      simpa only [bReverse.support_tail_of_not_nil hbNotNil] using hmem
    exact (List.disjoint_left.mp hprefixDisjoint)
      hshortcutStartMemC hmem'
  have hbShortcutPath : bShortcut.IsPath := by
    dsimp only [bShortcut]
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hbPath.tail, hshortcutStartNotMemB⟩
  have hcDropPath : cDrop.IsPath := by
    dsimp only [cDrop]
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_rfl cPrefix).dropLast hcPath
  have hcDropNotNil : ¬cDrop.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    dsimp only [cDrop]
    rw [SimpleGraph.Walk.length_dropLast]
    omega
  have hdisjoint : cDrop.support.tail.Disjoint bShortcut.support.tail := by
    rw [List.disjoint_left]
    intro edge hcTail hbTail
    have hcDropSupport : edge ∈ cDrop.support :=
      List.mem_of_mem_tail hcTail
    have hcPrefixSupport : edge ∈ cPrefix.support :=
      (SimpleGraph.Walk.isSubwalk_rfl cPrefix).dropLast.support_subset
        hcDropSupport
    have hcStartNotMem : lens.bRoute.leftEdge.1 ∉
        cDrop.support.tail := by
      have hnodup := hcDropPath.support_nodup
      rw [← cDrop.cons_tail_support] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    have hcPrefixTail : edge ∈ cPrefix.support.tail := by
      rw [← cPrefix.cons_tail_support] at hcPrefixSupport
      simp only [List.mem_cons] at hcPrefixSupport
      rcases hcPrefixSupport with hstart | htail
      · exact False.elim (hcStartNotMem (by
          simpa only [hstart] using hcTail))
      · exact htail
    have hbReverseTail : edge ∈ bReverse.support.tail := by
      have hbTailSupport : edge ∈ bReverse.tail.support := by
        simpa only [bShortcut, SimpleGraph.Walk.support_cons,
          List.tail_cons] using hbTail
      simpa only [bReverse.support_tail_of_not_nil hbNotNil] using
        hbTailSupport
    exact (List.disjoint_left.mp hprefixDisjoint)
      hcPrefixTail hbReverseTail
  have hshortcutPositive :
      0 < (lens.positiveFusionBounceShortcut
        hab hac hbc site hpositive).length :=
    lens.positiveFusionBounceShortcut_length_pos
      hab hac hbc site hpositive
  have hshortcutCoherent :=
    lens.positiveFusionBounceShortcut_isPrimalCoherentClosed
      hdata hab hac hbc site hpositive
  rcases (lens.positiveFusionBounceShortcut
      hab hac hbc site hpositive).exists_primal_isCycle_length_le_of_primalCoherentClosed
      hshortcutPositive hshortcutCoherent with
    ⟨_start, extracted, hextracted, hextractedLength⟩
  have hshortcutThree : 3 ≤
      (lens.positiveFusionBounceShortcut
        hab hac hbc site hpositive).length :=
    le_trans hextracted.three_le_length hextractedLength
  have hlong : 1 < cDrop.length ∨ 1 < bShortcut.length := by
    change 3 ≤ (cDrop.append bShortcut).length at hshortcutThree
    rw [SimpleGraph.Walk.length_append] at hshortcutThree
    omega
  change (cDrop.append bShortcut).IsCycle
  exact hcDropPath.isCycle_append hbShortcutPath hdisjoint hlong

/-- The reverse return loop begins at the left boundary connector. -/
theorem EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite)
    (hloopPositive :
      0 < (lens.fusionSiteLeftReturnOppositeLoop site).length) :
    (lens.fusionSiteLeftReturnOppositeLoop site).lineGraphJunctionAt
        ⟨0, hloopPositive⟩ = data.defectVertex left := by
  let cPrefix := lens.cLeftConnectedPrefixToFusion site
  let bReverse := (lens.bAmbientPrefixToFusion site).reverse
  have hcPositive : 0 < cPrefix.length := by
    dsimp only [cPrefix]
    exact lens.cLeftConnectedPrefixToFusion_length_pos site
  have happend := cPrefix.lineGraphJunctionAt_append_zero_of_left_pos
    bReverse hcPositive
  have hfirst := lens.cLeftConnectedPrefixToFusion_firstJunction site
  change (cPrefix.append bReverse).lineGraphJunctionAt
      ⟨0, hloopPositive⟩ = data.defectVertex left
  exact happend.trans (hfirst.trans lens.leftConnectorVertex_eq_defectVertex)

/-- The positive bounce also begins at the unchanged left boundary
connector; the contraction occurs only at the remote fusion site. -/
theorem EvenKempeFusionLens.positiveFusionBounceShortcut_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hpositive : lens.fusionChirality hab hac site = true)
    (hshortcutPositive : 0 < (lens.positiveFusionBounceShortcut
      hab hac hbc site hpositive).length) :
    (lens.positiveFusionBounceShortcut
        hab hac hbc site hpositive).lineGraphJunctionAt
          ⟨0, hshortcutPositive⟩ = data.defectVertex left := by
  let cPrefix := lens.cLeftConnectedPrefixToFusion site
  let bReverse := (lens.bAmbientPrefixToFusion site).reverse
  let shortcutAdj : G.lineGraph.Adj cPrefix.penultimate bReverse.snd := by
    simpa only [cPrefix, bReverse, SimpleGraph.Walk.snd_reverse,
      lens.cLeftConnectedPrefixToFusion_getVert_penultimate hab hac site,
      lens.bAmbientPrefixToFusion_getVert_penultimate hab site] using
        lens.positiveFusionShortcutAdj hab hac hbc site hpositive
  let bShortcut := SimpleGraph.Walk.cons shortcutAdj bReverse.tail
  have hcTwo : 2 ≤ cPrefix.length := by
    dsimp only [cPrefix]
    rw [lens.cLeftConnectedPrefixToFusion_length site]
    have hcPositive := lens.cAmbientPrefixToFusion_length_pos hab hac site
    omega
  have hcDropPositive : 0 < cPrefix.dropLast.length := by
    rw [SimpleGraph.Walk.length_dropLast]
    omega
  have happend := cPrefix.dropLast.lineGraphJunctionAt_append_zero_of_left_pos
    bShortcut hcDropPositive
  have hdrop := cPrefix.lineGraphJunctionAt_dropLast
    ⟨0, hcDropPositive⟩
  have hfirst := lens.cLeftConnectedPrefixToFusion_firstJunction site
  change (cPrefix.dropLast.append bShortcut).lineGraphJunctionAt
      ⟨0, hshortcutPositive⟩ = data.defectVertex left
  exact happend.trans
    (hdrop.trans (hfirst.trans lens.leftConnectorVertex_eq_defectVertex))

/-- Negative chirality at a leftmost fusion site yields the explicit
shorter primal circuit while retaining the left boundary defect. -/
theorem EvenKempeFusionLens.exists_leftDefect_shorterPrimalCircuit_of_leftmost_of_chirality_eq_false
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c)
    (site : lens.FusionSite)
    (hleftmost : ∀ edge : G.edgeSet,
      edge ∈ (lens.bAmbientPrefixToFusion site).support →
      edge ∈ lens.cRoute.ambientPath.support →
      edge = site.1)
    (hnegative : lens.fusionChirality hab hac site = false) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
      circuit.length < lens.closedWalk.length ∧
      data.defectVertex left ∈ circuit.support := by
  let loop := lens.fusionSiteLeftReturnOppositeLoop site
  have hcycle : loop.IsCycle := by
    dsimp only [loop]
    exact lens.fusionSiteLeftReturnOppositeLoop_isCycle_of_leftmost
      hab hac site hleftmost
  have hloopPositive : 0 < loop.length := by
    have hthree := hcycle.three_le_length
    omega
  have hreturn : lens.ReturnSpliceCoherent hab hac site :=
    (lens.returnSpliceCoherent_iff_chirality_eq_false
      hab hac site).2 hnegative
  have hcoherent : loop.IsPrimalCoherentClosed := by
    dsimp only [loop]
    exact lens.fusionSiteLeftReturnOppositeLoop_isPrimalCoherentClosed
      hdata hab hac site hreturn
  let circuit := loop.primalLift hloopPositive hcoherent
  have hdefect : data.defectVertex left ∈ circuit.support := by
    have hjunction := loop.lineGraphJunctionAt_mem_primalLift_support
      hloopPositive hcoherent ⟨0, hloopPositive⟩
    have hfirst := lens.fusionSiteLeftReturnOppositeLoop_firstJunction
      site hloopPositive
    exact hfirst ▸ hjunction
  refine ⟨loop.lineGraphJunctionAt ⟨0, hloopPositive⟩,
    circuit,
    loop.primalLift_isCircuit_of_isCycle
      hloopPositive hcoherent hcycle,
    ?_, hdefect⟩
  rw [loop.primalLift_length hloopPositive hcoherent]
  exact lens.fusionSiteLeftReturnOppositeLoop_length_lt_closedWalk
    hab hac site

/-- Positive chirality at a leftmost fusion site yields the contracted
shorter primal circuit, again retaining the left boundary defect. -/
theorem EvenKempeFusionLens.exists_leftDefect_shorterPrimalCircuit_of_leftmost_of_chirality_eq_true
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite)
    (hleftmost : ∀ edge : G.edgeSet,
      edge ∈ (lens.bAmbientPrefixToFusion site).support →
      edge ∈ lens.cRoute.ambientPath.support →
      edge = site.1)
    (hpositive : lens.fusionChirality hab hac site = true) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
      circuit.length < lens.closedWalk.length ∧
      data.defectVertex left ∈ circuit.support := by
  let shortcut :=
    lens.positiveFusionBounceShortcut hab hac hbc site hpositive
  have hcycle : shortcut.IsCycle := by
    dsimp only [shortcut]
    exact lens.positiveFusionBounceShortcut_isCycle_of_leftmost
      hdata hab hac hbc site hleftmost hpositive
  have hshortcutPositive : 0 < shortcut.length := by
    dsimp only [shortcut]
    exact lens.positiveFusionBounceShortcut_length_pos
      hab hac hbc site hpositive
  have hcoherent : shortcut.IsPrimalCoherentClosed := by
    dsimp only [shortcut]
    exact lens.positiveFusionBounceShortcut_isPrimalCoherentClosed
      hdata hab hac hbc site hpositive
  let circuit := shortcut.primalLift hshortcutPositive hcoherent
  have hdefect : data.defectVertex left ∈ circuit.support := by
    have hjunction := shortcut.lineGraphJunctionAt_mem_primalLift_support
      hshortcutPositive hcoherent ⟨0, hshortcutPositive⟩
    have hfirst := lens.positiveFusionBounceShortcut_firstJunction
      hab hac hbc site hpositive hshortcutPositive
    exact hfirst ▸ hjunction
  refine ⟨shortcut.lineGraphJunctionAt ⟨0, hshortcutPositive⟩,
    circuit,
    shortcut.primalLift_isCircuit_of_isCycle
      hshortcutPositive hcoherent hcycle,
    ?_, hdefect⟩
  rw [shortcut.primalLift_length hshortcutPositive hcoherent]
  have hcontracted := lens.positiveFusionBounceShortcut_length
    hab hac hbc site hpositive
  have hreturnShorter :=
    lens.fusionSiteLeftReturnOppositeLoop_length_lt_closedWalk
      hab hac site
  dsimp only [shortcut] at hcontracted ⊢
  omega

/-- Every nonempty fusion chain has a strictly shorter primal circuit
through its left boundary defect, independently of chirality. -/
theorem EvenKempeFusionLens.exists_leftDefect_shorterPrimalCircuit_of_fusionSiteCount_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : 0 < lens.fusionSiteCount) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧
      circuit.length < lens.closedWalk.length ∧
      data.defectVertex left ∈ circuit.support := by
  rcases lens.exists_leftmostFusionSite hcount with
    ⟨site, hleftmost⟩
  by_cases hpositive : lens.fusionChirality hab hac site = true
  · exact lens.exists_leftDefect_shorterPrimalCircuit_of_leftmost_of_chirality_eq_true
      hdata hab hac hbc site hleftmost hpositive
  · have hnegative : lens.fusionChirality hab hac site = false :=
      Bool.eq_false_of_not_eq_true hpositive
    exact lens.exists_leftDefect_shorterPrimalCircuit_of_leftmost_of_chirality_eq_false
      hdata hab hac site hleftmost hnegative

/-- Boundary-sensitive exhaustive fusion descent.  The zero-fusion branch
is the equal-length circuit through both ports; the positive branch is a
strictly shorter circuit that still passes through the designated left
port. -/
theorem EvenKempeFusionLens.fusionChain_portSpanningCircuit_or_leftDefectShorterCircuit
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hleftRight : left ≠ right) :
    (lens.fusionSiteCount = 0 ∧
      ∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧
        circuit.length = lens.closedWalk.length ∧
        circuit.edges = lens.closedWalk.support.tail.map Subtype.val ∧
        data.defectVertex left ∈ circuit.support ∧
        data.defectVertex right ∈ circuit.support) ∨
    (0 < lens.fusionSiteCount ∧
      ∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧
        circuit.length < lens.closedWalk.length ∧
        data.defectVertex left ∈ circuit.support) := by
  by_cases hzero : lens.fusionSiteCount = 0
  · exact Or.inl ⟨hzero,
      lens.exists_portSpanning_primalCircuit_of_fusionSiteCount_eq_zero
        hdata hab hac hleftRight hzero⟩
  · have hpositive : 0 < lens.fusionSiteCount := Nat.pos_of_ne_zero hzero
    exact Or.inr ⟨hpositive,
      lens.exists_leftDefect_shorterPrimalCircuit_of_fusionSiteCount_pos
        hdata hab hac hbc hpositive⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
