import Mettapedia.GraphTheory.EdgeColoring

/-!
# Local colour swaps generate Kempe reachability

Two proper edge colourings can be compared without choosing paths or a cycle
decomposition.  Say that they are *locally swap related* when, at every graph
vertex, one transposition of the colour set carries the first colouring to the
second on every incident edge.

The main theorem proves that this local condition is already sufficient for
global Kempe reachability.  Starting from any disagreeing edge, its local
transposition propagates across the whole corresponding bicoloured component.
Switching that component removes every disagreement on it and creates none;
finite induction finishes.

For three-edge-colourings, the contrapositive isolates the only possible local
obstruction to Kempe generation: some vertex is not governed by one
transposition.  At an interior cubic vertex this is precisely the three-cycle,
or branching, sector of the relative colour permutation.  No planarity or
Four-Colour conclusion is used here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24LocalSwapKempeGeneration

open SimpleGraph

universe u v

variable {V : Type u} {ColorType : Type v}
  [Fintype V] [DecidableEq V] [DecidableEq ColorType]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At every graph vertex, one colour transposition carries `source` to
`target` on all incident edges.  The transposition may be the identity. -/
def LocallySwapRelated
    (source target : G.EdgeColoring ColorType) : Prop :=
  ∀ vertex : V, ∃ first second : ColorType,
    ∀ edge : G.edgeSet, vertex ∈ (edge.1 : Sym2 V) →
      target edge = Equiv.swap first second (source edge)

/-- A nontrivial value of a transposition determines the transposition. -/
theorem swap_eq_of_apply_eq_of_ne
    {first second input output : ColorType}
    (happly : output = Equiv.swap first second input)
    (hne : input ≠ output) :
    Equiv.swap first second = Equiv.swap input output := by
  have hmoved : Equiv.swap first second input ≠ input := by
    rw [← happly]
    exact hne.symm
  rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hinput | hinput
  · subst first
    have houtput : output = second := by
      simpa using happly
    subst second
    rfl
  · subst second
    have houtput : output = first := by
      simpa using happly
    subst first
    exact Equiv.swap_comm output input

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Once a nontrivial swap is known on one edge, local swap relatedness
propagates that same swap across every adjacent edge. -/
theorem swap_relation_of_lineGraph_adj
    {source target : G.EdgeColoring ColorType}
    (hlocal : LocallySwapRelated source target)
    {first second : ColorType} (hne : first ≠ second)
    {edge next : G.edgeSet}
    (hedgeColor : source edge = first ∨ source edge = second)
    (hedge : target edge = Equiv.swap first second (source edge))
    (hadj : G.lineGraph.Adj edge next) :
    target next = Equiv.swap first second (source next) := by
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with
    ⟨_, vertex, hedgeIncident, hnextIncident⟩
  rcases hlocal vertex with ⟨localFirst, localSecond, hvertex⟩
  have hedgeNe : source edge ≠ target edge := by
    rw [hedge]
    exact ((Equiv.swap_apply_ne_self_iff).2 ⟨hne, hedgeColor⟩).symm
  have hswap : Equiv.swap localFirst localSecond =
      Equiv.swap first second := by
    calc
      Equiv.swap localFirst localSecond =
          Equiv.swap (source edge) (target edge) :=
        swap_eq_of_apply_eq_of_ne (hvertex edge hedgeIncident) hedgeNe
      _ = Equiv.swap first second :=
        (swap_eq_of_apply_eq_of_ne hedge hedgeNe).symm
  rw [hvertex next hnextIncident, hswap]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A local swap relation propagates along a walk in the selected bicoloured
subgraph. -/
theorem swap_relation_of_bicolored_walk
    {source target : G.EdgeColoring ColorType}
    (hlocal : LocallySwapRelated source target)
    {first second : ColorType} (hne : first ≠ second)
    {start finish : source.bicoloredSet first second}
    (walk : (source.bicoloredSubgraph first second).Walk start finish)
    (hstart : target start.1 = Equiv.swap first second (source start.1)) :
    target finish.1 = Equiv.swap first second (source finish.1) := by
  induction walk with
  | nil => exact hstart
  | @cons current next finish hadj tail ih =>
      apply ih
      exact swap_relation_of_lineGraph_adj hlocal hne current.2 hstart hadj

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The transposition witnessed by one disagreeing edge governs its entire
bicoloured Kempe component. -/
theorem swap_relation_on_seed_component
    {source target : G.EdgeColoring ColorType}
    (hlocal : LocallySwapRelated source target)
    (seed : G.edgeSet) (hseed : source seed ≠ target seed) :
    let first := source seed
    let second := target seed
    let seedSelected : seed ∈ source.bicoloredSet first second := Or.inl rfl
    let component :=
      (source.bicoloredSubgraph first second).connectedComponentMk
        ⟨seed, seedSelected⟩
    ∀ edge : G.edgeSet,
      edge ∈ source.kempeComponentSet first second component →
        target edge = Equiv.swap first second (source edge) := by
  dsimp only
  intro edge hedge
  rcases hedge with ⟨hedgeSelected, hedgeComponent⟩
  have hreachable :
      (source.bicoloredSubgraph (source seed) (target seed)).Reachable
        ⟨seed, Or.inl rfl⟩ ⟨edge, hedgeSelected⟩ :=
    SimpleGraph.ConnectedComponent.exact hedgeComponent.symm
  rcases hreachable with ⟨walk⟩
  apply swap_relation_of_bicolored_walk hlocal hseed walk
  simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Edges on the selected component agree with the target after switching. -/
theorem swapOnKempeComponent_eq_target_of_mem
    {source target : G.EdgeColoring ColorType}
    (hlocal : LocallySwapRelated source target)
    (seed : G.edgeSet) (hseed : source seed ≠ target seed)
    (edge : G.edgeSet)
    (hedge : edge ∈ source.kempeComponentSet
      (source seed) (target seed)
      ((source.bicoloredSubgraph (source seed) (target seed)).connectedComponentMk
        ⟨seed, Or.inl rfl⟩)) :
    source.swapOnKempeComponent (source seed) (target seed)
        ((source.bicoloredSubgraph (source seed) (target seed)).connectedComponentMk
          ⟨seed, Or.inl rfl⟩) edge = target edge := by
  rw [source.swapOnKempeComponent_apply_of_mem hedge]
  exact (swap_relation_on_seed_component hlocal seed hseed edge hedge).symm

/-- Switching the component selected by one disagreement leaves a local swap
relation to the target.  At vertices touched by the component the two
colourings now agree; elsewhere the old local transposition remains. -/
theorem locallySwapRelated_after_seed_switch
    {source target : G.EdgeColoring ColorType}
    (hlocal : LocallySwapRelated source target)
    (seed : G.edgeSet) (hseed : source seed ≠ target seed) :
    LocallySwapRelated
      (source.swapOnKempeComponent (source seed) (target seed)
        ((source.bicoloredSubgraph (source seed) (target seed)).connectedComponentMk
          ⟨seed, Or.inl rfl⟩))
      target := by
  let first := source seed
  let second := target seed
  let component :=
    (source.bicoloredSubgraph first second).connectedComponentMk
      ⟨seed, Or.inl rfl⟩
  let switched := source.swapOnKempeComponent first second component
  intro vertex
  by_cases htouched : ∃ edge : G.edgeSet,
      vertex ∈ (edge.1 : Sym2 V) ∧
        edge ∈ source.kempeComponentSet first second component
  · refine ⟨first, first, ?_⟩
    intro edge hedgeIncident
    simp only [Equiv.swap_self, Equiv.refl_apply]
    rcases htouched with ⟨witness, hwitnessIncident, hwitnessComponent⟩
    have hwitnessMap := swap_relation_on_seed_component
      hlocal seed hseed witness hwitnessComponent
    have hwitnessSelected :=
      source.mem_bicoloredSet_of_mem_kempeComponentSet hwitnessComponent
    rcases hlocal vertex with ⟨localFirst, localSecond, hvertex⟩
    have hwitnessNe : source witness ≠ target witness := by
      rw [hwitnessMap]
      exact ((Equiv.swap_apply_ne_self_iff).2
        ⟨hseed, hwitnessSelected⟩).symm
    have hlocalSwap : Equiv.swap localFirst localSecond =
        Equiv.swap first second := by
      calc
        Equiv.swap localFirst localSecond =
            Equiv.swap (source witness) (target witness) :=
          swap_eq_of_apply_eq_of_ne
            (hvertex witness hwitnessIncident) hwitnessNe
        _ = Equiv.swap first second :=
          (swap_eq_of_apply_eq_of_ne hwitnessMap hwitnessNe).symm
    by_cases hedgeSelected : edge ∈ source.bicoloredSet first second
    · have hedgeComponent :
          edge ∈ source.kempeComponentSet first second component := by
        by_cases heq : edge = witness
        · simpa [heq] using hwitnessComponent
        · exact source.mem_kempeComponentSet_of_adj hwitnessComponent
            (G.lineGraph_adj_of_edgeSet_common_vertex
              (Ne.symm heq) hwitnessIncident hedgeIncident)
            hedgeSelected
      exact (swapOnKempeComponent_eq_target_of_mem
        hlocal seed hseed edge hedgeComponent).symm
    · have hedgeNotComponent :
          edge ∉ source.kempeComponentSet first second component := by
        intro hmember
        exact hedgeSelected
          (source.mem_bicoloredSet_of_mem_kempeComponentSet hmember)
      rw [source.swapOnKempeComponent_apply_of_not_mem hedgeNotComponent]
      symm
      calc
        source edge = Equiv.swap first second (source edge) := by
            symm
            apply Equiv.swap_apply_of_ne_of_ne
            · intro heq
              exact hedgeSelected (Or.inl heq)
            · intro heq
              exact hedgeSelected (Or.inr heq)
        _ = Equiv.swap localFirst localSecond (source edge) := by
            rw [hlocalSwap]
        _ = target edge := (hvertex edge hedgeIncident).symm
  · rcases hlocal vertex with ⟨first, second, hvertex⟩
    refine ⟨first, second, ?_⟩
    intro edge hedgeIncident
    have hedgeNotComponent :
        edge ∉ source.kempeComponentSet (source seed) (target seed)
          ((source.bicoloredSubgraph (source seed) (target seed)).connectedComponentMk
            ⟨seed, Or.inl rfl⟩) := by
      intro hmember
      exact htouched ⟨edge, hedgeIncident, hmember⟩
    rw [source.swapOnKempeComponent_apply_of_not_mem hedgeNotComponent]
    exact hvertex edge hedgeIncident

/-- The finite set of edges on which two colourings disagree. -/
def disagreementEdges
    (source target : G.EdgeColoring ColorType) : Finset G.edgeSet :=
  Finset.univ.filter fun edge => source edge ≠ target edge

omit [DecidableEq V] in
@[simp]
theorem mem_disagreementEdges
    (source target : G.EdgeColoring ColorType) (edge : G.edgeSet) :
    edge ∈ disagreementEdges source target ↔ source edge ≠ target edge := by
  simp [disagreementEdges]

omit [DecidableEq V] in
/-- One component switch selected by a disagreement strictly decreases the
number of disagreeing edges. -/
theorem disagreementEdges_card_after_seed_switch_lt
    {source target : G.EdgeColoring ColorType}
    (hlocal : LocallySwapRelated source target)
    (seed : G.edgeSet) (hseed : source seed ≠ target seed) :
    (disagreementEdges
      (source.swapOnKempeComponent (source seed) (target seed)
        ((source.bicoloredSubgraph (source seed) (target seed)).connectedComponentMk
          ⟨seed, Or.inl rfl⟩))
      target).card < (disagreementEdges source target).card := by
  let component :=
    (source.bicoloredSubgraph (source seed) (target seed)).connectedComponentMk
      ⟨seed, Or.inl rfl⟩
  let switched := source.swapOnKempeComponent (source seed) (target seed) component
  have hsubset : disagreementEdges switched target ⊆
      disagreementEdges source target := by
    intro edge hedge
    rw [mem_disagreementEdges] at hedge ⊢
    by_cases hcomponent : edge ∈ source.kempeComponentSet
        (source seed) (target seed) component
    · exact False.elim (hedge (swapOnKempeComponent_eq_target_of_mem
        hlocal seed hseed edge hcomponent))
    · rw [source.swapOnKempeComponent_apply_of_not_mem hcomponent] at hedge
      exact hedge
  have hstrict : disagreementEdges switched target ≠
      disagreementEdges source target := by
    intro heq
    have hseedOld : seed ∈ disagreementEdges source target :=
      (mem_disagreementEdges source target seed).2 hseed
    have hseedComponent : seed ∈ source.kempeComponentSet
        (source seed) (target seed) component := by
      exact ⟨Or.inl rfl, rfl⟩
    have hseedNew : seed ∉ disagreementEdges switched target := by
      rw [mem_disagreementEdges]
      exact not_ne_iff.mpr
        (swapOnKempeComponent_eq_target_of_mem
          hlocal seed hseed seed hseedComponent)
    exact hseedNew (heq ▸ hseedOld)
  exact Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hstrict⟩)

/-- **Local swaps generate global Kempe reachability.** -/
theorem mem_edgeKempeClosure_of_locallySwapRelated
    (source target : G.EdgeColoring ColorType)
    (hlocal : LocallySwapRelated source target) :
    target ∈ G.EdgeKempeClosure source := by
  classical
  generalize hmeasure : (disagreementEdges source target).card = measure
  induction measure using Nat.strong_induction_on generalizing source with
  | h measure ih =>
      by_cases heq : source = target
      · subst target
        exact G.mem_edgeKempeClosure_self source
      · have hnonempty : (disagreementEdges source target).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          apply heq
          apply DFunLike.ext _ _
          intro edge
          by_contra hedge
          have : edge ∈ disagreementEdges source target :=
            (mem_disagreementEdges source target edge).2 hedge
          simp [hempty] at this
        let seed := Classical.choose hnonempty
        have hseedMem : seed ∈ disagreementEdges source target :=
          Classical.choose_spec hnonempty
        have hseed : source seed ≠ target seed :=
          (mem_disagreementEdges source target seed).1 hseedMem
        let component :=
          (source.bicoloredSubgraph (source seed) (target seed)).connectedComponentMk
            ⟨seed, Or.inl rfl⟩
        let switched := source.swapOnKempeComponent
          (source seed) (target seed) component
        have hsmaller : (disagreementEdges switched target).card < measure := by
          rw [← hmeasure]
          exact disagreementEdges_card_after_seed_switch_lt
            hlocal seed hseed
        have hlocal' : LocallySwapRelated switched target :=
          locallySwapRelated_after_seed_switch hlocal seed hseed
        have htarget : target ∈ G.EdgeKempeClosure switched :=
          ih _ hsmaller switched hlocal' rfl
        have hswitched : switched ∈ G.EdgeKempeClosure source := by
          exact G.mem_edgeKempeClosure_of_mem_of_step
            (G.mem_edgeKempeClosure_self source)
            (source seed) (target seed) component
        exact G.edgeKempeClosure_subset_of_mem hswitched htarget

/-- If two colourings are not Kempe equivalent, some vertex has a genuine
non-transposition local discrepancy. -/
theorem exists_not_locallySwapRelated_of_not_mem_edgeKempeClosure
    (source target : G.EdgeColoring ColorType)
    (hnot : target ∉ G.EdgeKempeClosure source) :
    ∃ vertex : V, ¬ ∃ first second : ColorType,
      ∀ edge : G.edgeSet, vertex ∈ (edge.1 : Sym2 V) →
        target edge = Equiv.swap first second (source edge) := by
  by_contra hnone
  push Not at hnone
  exact hnot (mem_edgeKempeClosure_of_locallySwapRelated source target hnone)

end GoertzelV24LocalSwapKempeGeneration

end Mettapedia.GraphTheory.FourColor
