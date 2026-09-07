import Mettapedia.GraphTheory.FourColor.KempeEmbeddingFusion

/-!
# Target-directed failure of a Kempe lift

A lifted prefix records each common-core switch and its exact ambient lift.
An obstruction retains this prefix, the first switch not lifted by that
construction, and a remaining common-core sequence to the specified target.
An arbitrary boundary encounter, unrelated to the repair, cannot fill these
fields.  The obstruction concerns single same-pair component switches; it
does not rule out other ambient repair sequences.

An existential suffix may undo its first switch.  Productive repair is
therefore handled below by disagreement minima and correct-edge blockers,
not inferred from the suffix alone.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeTargetFusion

open SimpleGraph GoertzelV24KempeComponentEmbeddingBoundary
open GoertzelV24LocalSwapKempeGeneration KempeEmbeddingFusion

universe u v
variable {A : Type u} {B : Type v} {G : SimpleGraph A} {H : SimpleGraph B}

/-- A finite prefix lifted one component at a time, with exact restriction
at every step and a distinct nonzero colour pair throughout. -/
inductive LiftedPrefix (embedding : G ↪g H) (base : H.EdgeColoring Color) :
    H.EdgeColoring Color → Prop
  | refl : LiftedPrefix embedding base base
  | step {current : H.EdgeColoring Color}
      (hpref : LiftedPrefix embedding base current)
      (first second : Color) (valid : ValidColorPair first second)
      (K : ((current.pullbackEmbedding embedding).bicoloredSubgraph
        first second).ConnectedComponent)
      (L : (current.bicoloredSubgraph first second).ConnectedComponent)
      (restricts : EdgeColoring.pullbackEmbedding
        (current.swapOnKempeComponent first second L) embedding =
          (current.pullbackEmbedding embedding).swapOnKempeComponent first second K) :
      LiftedPrefix embedding base (current.swapOnKempeComponent first second L)

theorem LiftedPrefix.reachable {embedding : G ↪g H} {base current : H.EdgeColoring Color}
    (p : LiftedPrefix embedding base current) : TaitKempeReachable base current := by
  induction p with
  | refl => exact .refl
  | step _ first second valid _ L _ ih =>
      exact ih.tail ⟨first, second, valid, L, rfl⟩

theorem LiftedPrefix.restriction_reachable {embedding : G ↪g H}
    {base current : H.EdgeColoring Color} (p : LiftedPrefix embedding base current) :
    TaitKempeReachable (base.pullbackEmbedding embedding)
      (current.pullbackEmbedding embedding) := by
  induction p with
  | refl => exact .refl
  | step _ first second valid K _ restricts ih =>
      exact ih.tail ⟨first, second, valid, K, restricts⟩

theorem LiftedPrefix.isTait {embedding : G ↪g H} {base current : H.EdgeColoring Color}
    (p : LiftedPrefix embedding base current) (hbase : IsTaitEdgeColoring H base) :
    IsTaitEdgeColoring H current :=
  isTaitEdgeColoring_of_taitKempeReachable hbase p.reachable

/-- The failure retains the successfully lifted prefix and a suffix to the
actual target, rather than only an unrooted boundary event. -/
def TargetFusion (base : H.EdgeColoring Color) (embedding : G ↪g H)
    (target : G.EdgeColoring Color) : Prop :=
  ∃ current : H.EdgeColoring Color, LiftedPrefix embedding base current ∧
    ∃ first second : Color, ValidColorPair first second ∧
      ∃ K : ((current.pullbackEmbedding embedding).bicoloredSubgraph
        first second).ConnectedComponent,
        ComponentFuses current embedding first second K ∧
        TaitKempeReachable
          ((current.pullbackEmbedding embedding).swapOnKempeComponent first second K) target

theorem TargetFusion.tail {base : H.EdgeColoring Color} {embedding : G ↪g H}
    {target next : G.EdgeColoring Color} (h : TargetFusion base embedding target)
    (step : TaitKempeStep target next) : TargetFusion base embedding next := by
  obtain ⟨current, hpref, first, second, valid, K, fusion, suffix⟩ := h
  exact ⟨current, hpref, first, second, valid, K, fusion, suffix.tail step⟩

/-- A target-reaching common-core sequence either lifts step by step or has
a genuinely fusing step between a lifted prefix and a target-reaching suffix. -/
theorem targetFusion_or_lifted
    (base : H.EdgeColoring Color) (embedding : G ↪g H) (target : G.EdgeColoring Color)
    (h : TaitKempeReachable (base.pullbackEmbedding embedding) target) :
    TargetFusion base embedding target ∨
      ∃ current : H.EdgeColoring Color, LiftedPrefix embedding base current ∧
        current.pullbackEmbedding embedding = target := by
  induction h with
  | refl => exact Or.inr ⟨base, .refl, rfl⟩
  | tail _ step ih =>
      rcases ih with fusion | ⟨current, hpref, restricts⟩
      · exact Or.inl (fusion.tail step)
      · rcases step with ⟨first, second, valid, K, rfl⟩
        subst restricts
        by_cases fusion : ComponentFuses current embedding first second K
        · exact Or.inl ⟨current, hpref, first, second, valid, K, fusion, .refl⟩
        · let L := K.map (bicoloredSubgraphEmbedding current embedding first second).toHom
          have restricts := lifted_switch_of_not_fuses current embedding first second K fusion
          exact Or.inr ⟨_, hpref.step first second valid K L restricts, restricts⟩

/-- The recorded fusing step really has no single same-pair lift.  This does
not assert that its target is unreachable by a different ambient route. -/
theorem TargetFusion.exists_failed_step
    {base : H.EdgeColoring Color} {embedding : G ↪g H} {target : G.EdgeColoring Color}
    (h : TargetFusion base embedding target) :
    ∃ current : H.EdgeColoring Color, LiftedPrefix embedding base current ∧
      ∃ first second : Color, ValidColorPair first second ∧
        ∃ K : ((current.pullbackEmbedding embedding).bicoloredSubgraph
          first second).ConnectedComponent,
          (¬ ∃ L : (current.bicoloredSubgraph first second).ConnectedComponent,
            EdgeColoring.pullbackEmbedding (current.swapOnKempeComponent first second L) embedding =
              (current.pullbackEmbedding embedding).swapOnKempeComponent first second K) ∧
          TaitKempeReachable
            ((current.pullbackEmbedding embedding).swapOnKempeComponent first second K) target := by
  obtain ⟨current, hpref, first, second, valid, K, fusion, suffix⟩ := h
  refine ⟨current, hpref, first, second, valid, K, ?_, suffix⟩
  intro lifts
  exact (exists_lifted_switch_iff_not_fuses current embedding valid.2.2 K).mp lifts fusion

end Mettapedia.GraphTheory.FourColor.KempeTargetFusion

/-! ## Disagreement-minimal representatives

A suffix may undo a switch.  The following stronger construction does not
rely on the existence of a suffix: it minimizes literal disagreement with the
target and roots the obstruction at an edge which must actually be repaired.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeTargetFusion

open SimpleGraph GoertzelV24LocalSwapKempeGeneration
open GoertzelV24KempeComponentEmbeddingBoundary KempeEmbeddingFusion

universe u v
variable {A : Type u} {B : Type v} [Fintype A]
  {G : SimpleGraph A} [DecidableRel G.Adj] {H : SimpleGraph B}

def MinimumAt (base : H.EdgeColoring Color) (embedding : G ↪g H)
    (target : G.EdgeColoring Color) (current : H.EdgeColoring Color) : Prop :=
  TaitKempeReachable base current ∧
    ∀ next : H.EdgeColoring Color, TaitKempeReachable base next →
      (disagreementEdges (current.pullbackEmbedding embedding) target).card ≤
        (disagreementEdges (next.pullbackEmbedding embedding) target).card

/-- The representative is constructed by minimizing a natural-valued measure
on the nonempty Kempe orbit; no minimum certificate is an input. -/
theorem exists_minimum (base : H.EdgeColoring Color) (embedding : G ↪g H)
    (target : G.EdgeColoring Color) : ∃ current, MinimumAt base embedding target current := by
  classical
  let P : Nat → Prop := fun n => ∃ current : H.EdgeColoring Color,
    TaitKempeReachable base current ∧
      (disagreementEdges (current.pullbackEmbedding embedding) target).card = n
  have hp : ∃ n, P n := ⟨_, base, .refl, rfl⟩
  obtain ⟨current, hcurrent, hmeasure⟩ := Nat.find_spec hp
  refine ⟨current, hcurrent, fun next hnext => ?_⟩
  rw [hmeasure]
  exact Nat.find_min' hp ⟨next, hnext, rfl⟩

/-- At a minimum, the ambient component switch which repairs a chosen wrong
edge must spoil an edge which currently agrees with the target.  Thus its
obstruction has both a wrong-edge root and a correct-edge blocker. -/
theorem blocking_edge_of_minimum
    (base current : H.EdgeColoring Color) (embedding : G ↪g H)
    (target : G.EdgeColoring Color)
    (hbase : IsTaitEdgeColoring H base) (htarget : IsTaitEdgeColoring G target)
    (hmin : MinimumAt base embedding target current)
    (seed : G.edgeSet) (hseed : current.pullbackEmbedding embedding seed ≠ target seed) :
    let first := current.pullbackEmbedding embedding seed
    let second := target seed
    let L := (current.bicoloredSubgraph first second).connectedComponentMk
      ⟨embedding.mapEdgeSet seed, Or.inl rfl⟩
    ∃ edge : G.edgeSet, current.pullbackEmbedding embedding edge = target edge ∧
      embedding.mapEdgeSet edge ∈ current.kempeComponentSet first second L := by
  classical
  dsimp only
  let small := current.pullbackEmbedding embedding
  let L := (current.bicoloredSubgraph (small seed) (target seed)).connectedComponentMk
    ⟨embedding.mapEdgeSet seed, Or.inl rfl⟩
  let next : H.EdgeColoring Color := current.swapOnKempeComponent (small seed) (target seed) L
  let nextSmall := next.pullbackEmbedding embedding
  have hcurrent := isTaitEdgeColoring_of_taitKempeReachable hbase hmin.1
  have hpair : ValidColorPair (small seed) (target seed) :=
    ⟨hcurrent (embedding.mapEdgeSet seed), htarget seed, hseed⟩
  have hnext : TaitKempeReachable base next := hmin.1.tail ⟨_, _, hpair, L, rfl⟩
  have hfixed : nextSmall seed = target seed := by
    change current.swapOnKempeComponent _ _ L (embedding.mapEdgeSet seed) = target seed
    have hm : embedding.mapEdgeSet seed ∈ current.kempeComponentSet (small seed) (target seed) L :=
      ⟨Or.inl rfl, rfl⟩
    rw [current.swapOnKempeComponent_apply_of_mem hm]
    exact Equiv.swap_apply_left _ _
  have hnotSubset : ¬ disagreementEdges nextSmall target ⊆ disagreementEdges small target := by
    intro hsubset
    have hne : disagreementEdges nextSmall target ≠ disagreementEdges small target := by
      intro heq
      have hs : seed ∈ disagreementEdges nextSmall target :=
        heq.symm ▸ (mem_disagreementEdges small target seed).mpr hseed
      exact (mem_disagreementEdges nextSmall target seed).mp hs hfixed
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩)
    exact (not_lt_of_ge (hmin.2 next hnext)) hlt
  obtain ⟨edge, hnew, hold⟩ := Finset.not_subset.mp hnotSubset
  have hagrees : small edge = target edge := by
    simpa only [mem_disagreementEdges, not_not] using hold
  refine ⟨edge, hagrees, ?_⟩
  by_contra hout
  have hunchanged : nextSmall edge = small edge := by
    exact current.swapOnKempeComponent_apply_of_not_mem hout
  exact (mem_disagreementEdges nextSmall target edge).mp hnew (hunchanged.trans hagrees)

/-- If the common-core discrepancy is locally a transposition, every wrong
edge at a minimum seeds a genuinely fusing component.  Its isolated switch
would strictly decrease disagreement and would create no new errors. -/
theorem seed_fuses_of_minimum_of_local
    (base current : H.EdgeColoring Color) (embedding : G ↪g H)
    (target : G.EdgeColoring Color)
    (hbase : IsTaitEdgeColoring H base) (htarget : IsTaitEdgeColoring G target)
    (hmin : MinimumAt base embedding target current)
    (hlocal : LocallySwapRelated (current.pullbackEmbedding embedding) target)
    (seed : G.edgeSet) (hseed : current.pullbackEmbedding embedding seed ≠ target seed) :
    ComponentFuses current embedding (current.pullbackEmbedding embedding seed) (target seed)
      (((current.pullbackEmbedding embedding).bicoloredSubgraph
        (current.pullbackEmbedding embedding seed) (target seed)).connectedComponentMk
          ⟨seed, Or.inl rfl⟩) := by
  classical
  let small := current.pullbackEmbedding embedding
  let K := (small.bicoloredSubgraph (small seed) (target seed)).connectedComponentMk
    ⟨seed, Or.inl rfl⟩
  let f := bicoloredSubgraphEmbedding current embedding (small seed) (target seed)
  by_contra hn
  have hlift := lifted_switch_of_not_fuses current embedding (small seed) (target seed) K hn
  let next : H.EdgeColoring Color := current.swapOnKempeComponent
    (small seed) (target seed) (K.map f.toHom)
  have hcurrent := isTaitEdgeColoring_of_taitKempeReachable hbase hmin.1
  have hpair : ValidColorPair (small seed) (target seed) :=
    ⟨hcurrent (embedding.mapEdgeSet seed), htarget seed, hseed⟩
  have hnext : TaitKempeReachable base next := hmin.1.tail ⟨_, _, hpair, _, rfl⟩
  have hle := hmin.2 next hnext
  change (disagreementEdges small target).card ≤
    (disagreementEdges (EdgeColoring.pullbackEmbedding
      (current.swapOnKempeComponent (small seed) (target seed) (K.map f.toHom)) embedding) target).card
      at hle
  rw [hlift] at hle
  exact (not_lt_of_ge hle) (disagreementEdges_card_after_seed_switch_lt hlocal seed hseed)

/-- The discrepancy-rooted component connects upstairs to a currently correct
common-core edge in a different small component. -/
def SeedBlockingFusion (current : H.EdgeColoring Color) (embedding : G ↪g H)
    (target : G.EdgeColoring Color) (seed : G.edgeSet) : Prop :=
  let small := current.pullbackEmbedding embedding
  let first := small seed
  let second := target seed
  let x : small.bicoloredSet first second := ⟨seed, Or.inl rfl⟩
  let K := (small.bicoloredSubgraph first second).connectedComponentMk x
  let f := bicoloredSubgraphEmbedding current embedding first second
  ∃ y : small.bicoloredSet first second, small y.val = target y.val ∧ y ∉ K ∧
    (current.bicoloredSubgraph first second).Reachable (f x) (f y)

/-- The blocker can be chosen to be an actually correct edge, not merely an
arbitrary member of a second component sharing the same ambient image. -/
theorem seedBlockingFusion_of_minimum_of_local
    (base current : H.EdgeColoring Color) (embedding : G ↪g H)
    (target : G.EdgeColoring Color)
    (hbase : IsTaitEdgeColoring H base) (htarget : IsTaitEdgeColoring G target)
    (hmin : MinimumAt base embedding target current)
    (hlocal : LocallySwapRelated (current.pullbackEmbedding embedding) target)
    (seed : G.edgeSet) (hseed : current.pullbackEmbedding embedding seed ≠ target seed) :
    SeedBlockingFusion current embedding target seed := by
  obtain ⟨edge, hagrees, hmem⟩ :=
    blocking_edge_of_minimum base current embedding target hbase htarget hmin seed hseed
  dsimp only [SeedBlockingFusion]
  refine ⟨⟨edge, hmem.choose⟩, hagrees, ?_, ConnectedComponent.exact hmem.choose_spec.symm⟩
  intro hK
  have hswap := swap_relation_on_seed_component hlocal seed hseed edge ⟨hmem.choose, hK⟩
  rw [← hagrees] at hswap
  exact (Equiv.swap_apply_ne_self_iff.mpr ⟨hseed, hmem.choose⟩) hswap.symm

theorem disagreementEdges_symm (left right : G.EdgeColoring Color) :
    disagreementEdges left right = disagreementEdges right left := by
  ext edge
  simp only [mem_disagreementEdges, ne_comm]

omit [Fintype A] [DecidableRel G.Adj] in
theorem locallySwapRelated_symm {left right : G.EdgeColoring Color}
    (h : LocallySwapRelated left right) : LocallySwapRelated right left := by
  intro vertex
  obtain ⟨first, second, hv⟩ := h vertex
  refine ⟨first, second, fun edge he => ?_⟩
  rw [hv edge he]
  simp

/-- Minimize disagreement over both deletion orbits simultaneously.  Holding
either representative fixed then gives the minimum needed by the rooted
blocking theorem on the other side. -/
theorem exists_joint_minimum {D : Type*} {J : SimpleGraph D}
    (leftBase : H.EdgeColoring Color) (rightBase : J.EdgeColoring Color)
    (leftEmbedding : G ↪g H) (rightEmbedding : G ↪g J) :
    ∃ left : H.EdgeColoring Color, ∃ right : J.EdgeColoring Color,
      MinimumAt leftBase leftEmbedding (right.pullbackEmbedding rightEmbedding) left ∧
      MinimumAt rightBase rightEmbedding (left.pullbackEmbedding leftEmbedding) right := by
  classical
  let P : Nat → Prop := fun n => ∃ left : H.EdgeColoring Color, ∃ right : J.EdgeColoring Color,
    TaitKempeReachable leftBase left ∧ TaitKempeReachable rightBase right ∧
      (disagreementEdges (left.pullbackEmbedding leftEmbedding)
        (right.pullbackEmbedding rightEmbedding)).card = n
  have hp : ∃ n, P n := ⟨_, leftBase, rightBase, .refl, .refl, rfl⟩
  obtain ⟨left, right, hl, hr, hmeasure⟩ := Nat.find_spec hp
  refine ⟨left, right, ⟨hl, fun next hn => ?_⟩, hr, fun next hn => ?_⟩
  · rw [hmeasure]
    exact Nat.find_min' hp ⟨next, right, hn, hr, rfl⟩
  · rw [disagreementEdges_symm (right.pullbackEmbedding rightEmbedding),
      disagreementEdges_symm (next.pullbackEmbedding rightEmbedding), hmeasure]
    exact Nat.find_min' hp ⟨left, next, hl, hn, rfl⟩

end Mettapedia.GraphTheory.FourColor.KempeTargetFusion
