import Mettapedia.GraphTheory.Kempe.Restriction
import Mettapedia.GraphTheory.Kempe.TauGadget
import Mettapedia.Combinatorics.Reconfiguration.TauTauLifting

/-!
# Two gadgets in series: step lifting fails on the actual graph

Two canonical three-cell gadgets glued in series along
`X.B4..X.B7 = Y.B0..Y.B3`.  Gluing identifies stubs, and the two stubs `B5,B6`
of the upstream vertex `F5` are glued to the two stubs `B1,B2` of the
downstream vertex `F1`, so the composite has a pair of parallel edges.  Its line
graph `seriesLineGraph` is simple: its vertices are the twenty-two edges and
adjacency is sharing an internal vertex of either gadget.

With the upstream edges as the near side and the four upstream input stubs as
the input, this is the setting of `SimpleGraph.fibreConnected_of_restriction`.
The theorem `not_liftsSteps` shows, on this graph, that step lifting for every
input-avoiding upstream switch fails: the composite colouring made of upstream
state `6` and downstream state `176` has an upstream `{r,b}`-switch (the one of
`GoertzelLemma814.lemma818_pointwise_lift_preparation_obstruction`) after which
the upstream colouring extends to no colouring of the composite.  Consequently
the manuscript's preparation hypothesis `PairingPreparable` fails for this
composite (`not_pairingPreparable`), and the composition theorem in the form
that assumes it cannot be applied to two gadgets in series.  The form with
lifting asked only of moves into extendable colourings is not refuted.
-/

namespace Mettapedia.GraphTheory.Kempe.TauSeries

open SimpleGraph Relation
open Mettapedia.Combinatorics.Reconfiguration
open Mettapedia.GraphTheory.FourColor
open GoertzelLemma814 GoertzelLemma814GraphFidelity
open Mettapedia.GraphTheory.Kempe.TauGadget

/-- Edges of two gadgets in series: the thirteen upstream edges, and the nine
downstream edges that are not glued to upstream stubs. -/
inductive SeriesEdge
  | up (e : TauEdge)
  | dF1F0 | dF0F2 | dF2F3 | dF2F4 | dF4F5 | dB4 | dB5 | dB6 | dB7
  deriving DecidableEq, Fintype

/-- The downstream gadget's edges inside the composite: its input stubs are the
upstream output stubs. -/
def yEdge : TauEdge → SeriesEdge
  | .F1F0 => .dF1F0 | .F0F2 => .dF0F2 | .F2F3 => .dF2F3 | .F2F4 => .dF2F4
  | .F4F5 => .dF4F5
  | .B0 => .up .B4 | .B1 => .up .B5 | .B2 => .up .B6 | .B3 => .up .B7
  | .B4 => .dB4 | .B5 => .dB5 | .B6 => .dB6 | .B7 => .dB7

/-- Edges at an internal vertex of the upstream (`false`) or downstream (`true`)
gadget. -/
def seriesIncident : Bool → TauVertex → List SeriesEdge
  | false, v => (incidentEdges v).map .up
  | true, v => (incidentEdges v).map yEdge

def seriesShare (e f : SeriesEdge) : Bool :=
  e != f && [false, true].any fun side => tauVertices.any fun v =>
    (seriesIncident side v).contains e && (seriesIncident side v).contains f

/-- The line graph of the composite. -/
def seriesLineGraph : SimpleGraph SeriesEdge where
  Adj e f := seriesShare e f = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel seriesLineGraph.Adj := fun e f =>
  inferInstanceAs (Decidable (seriesShare e f = true))

/-- The near side: the upstream edges. -/
def upSet : Set SeriesEdge := Set.range SeriesEdge.up

/-- The input: the upstream input stubs. -/
def upInputs : Set SeriesEdge := {.up .B0, .up .B1, .up .B2, .up .B3}

theorem upInputs_subset : upInputs ⊆ upSet := by
  rintro e (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- A composite colour function from an upstream and a downstream state. -/
def seriesColor (x y : TauState) : SeriesEdge → LColor
  | .up e => x.color e
  | .dF1F0 => y.color .F1F0 | .dF0F2 => y.color .F0F2 | .dF2F3 => y.color .F2F3
  | .dF2F4 => y.color .F2F4 | .dF4F5 => y.color .F4F5 | .dB4 => y.color .B4
  | .dB5 => y.color .B5 | .dB6 => y.color .B6 | .dB7 => y.color .B7

set_option maxRecDepth 8192 in
/-- The obstruction's composite colouring: upstream state `6`, downstream state
`176`. -/
def obstructionColoring : seriesLineGraph.Coloring LColor :=
  Coloring.mk (seriesColor (stateAt 6) (stateAt 176)) (by intro e f; revert e f; decide)

/-- Its restriction to the upstream edges. -/
def obstructionRestriction : (seriesLineGraph.induce upSet).Coloring LColor :=
  obstructionColoring.restrictInduce upSet

theorem mem_upSet (e : TauEdge) : SeriesEdge.up e ∈ upSet := ⟨e, rfl⟩

theorem restriction_apply (e : TauEdge) :
    obstructionRestriction ⟨.up e, mem_upSet e⟩ = (stateAt 6).color e :=
  rfl

theorem seed_mem :
    (⟨.up .B5, mem_upSet _⟩ : upSet) ∈ obstructionRestriction.bicoloredSet LColor.r LColor.b :=
  Or.inl (by decide)

/-- The upstream `{r,b}`-component of the stub `B5`. -/
def obstructionComponent :
    (obstructionRestriction.bicoloredSubgraph LColor.r LColor.b).ConnectedComponent :=
  (obstructionRestriction.bicoloredSubgraph LColor.r LColor.b).connectedComponentMk
    ⟨⟨.up .B5, mem_upSet _⟩, seed_mem⟩

/-- The component `{B5, F4F5, B7}` is closed. -/
theorem component_closed_check :
    ([TauEdge.B5, TauEdge.B7, TauEdge.F4F5].all fun s => tauEdges.all fun t =>
      !seriesShare (.up s) (.up t) ||
        !(colorInPair ((stateAt 6).color t) LColor.r LColor.b) ||
        [TauEdge.B5, TauEdge.B7, TauEdge.F4F5].contains t) = true := by
  decide

theorem component_subset :
    obstructionRestriction.kempeComponentSet LColor.r LColor.b obstructionComponent ⊆
      {v | v.1 = .up .B5 ∨ v.1 = .up .B7 ∨ v.1 = .up .F4F5} := by
  apply obstructionRestriction.kempeComponentSet_subset_of_closed seed_mem (Or.inl rfl)
  rintro ⟨u, hu⟩ ⟨w, ⟨t, rfl⟩⟩ hT hadj hw
  obtain ⟨s, rfl⟩ := hu
  have hadj' : seriesShare (.up s) (.up t) = true := hadj
  have hw' : (stateAt 6).color t = LColor.r ∨ (stateAt 6).color t = LColor.b := hw
  have hs : s ∈ [TauEdge.B5, TauEdge.B7, TauEdge.F4F5] := by
    simp only [Set.mem_setOf_eq, SeriesEdge.up.injEq] at hT
    rcases hT with rfl | rfl | rfl <;> simp
  have hcheck := List.all_eq_true.1 (List.all_eq_true.1 component_closed_check s hs) t
    (mem_tauEdges t)
  have hpair : colorInPair ((stateAt 6).color t) LColor.r LColor.b = true := by
    unfold colorInPair
    rcases hw' with h | h <;> rw [h] <;> decide
  rw [hadj', hpair] at hcheck
  simp only [Bool.not_true, Bool.false_or, List.contains_iff_mem, List.mem_cons,
    List.not_mem_nil, or_false] at hcheck
  simp only [Set.mem_setOf_eq, SeriesEdge.up.injEq]
  exact hcheck

theorem B7_mem_component :
    (⟨.up .B7, mem_upSet _⟩ : upSet) ∈
      obstructionRestriction.kempeComponentSet LColor.r LColor.b obstructionComponent := by
  have h5 := obstructionRestriction.mem_kempeComponentSet_self seed_mem
  have h45 := obstructionRestriction.mem_kempeComponentSet_of_adj h5
    (v := ⟨.up .F4F5, mem_upSet _⟩) (by decide) (Or.inr (by decide))
  exact obstructionRestriction.mem_kempeComponentSet_of_adj h45
    (v := ⟨.up .B7, mem_upSet _⟩) (by decide) (Or.inl (by decide))

theorem B5_mem_component :
    (⟨.up .B5, mem_upSet _⟩ : upSet) ∈
      obstructionRestriction.kempeComponentSet LColor.r LColor.b obstructionComponent :=
  obstructionRestriction.mem_kempeComponentSet_self seed_mem

theorem B4_not_mem_component :
    (⟨.up .B4, mem_upSet _⟩ : upSet) ∉
      obstructionRestriction.kempeComponentSet LColor.r LColor.b obstructionComponent := by
  intro h
  have := component_subset h
  simp at this

theorem B6_not_mem_component :
    (⟨.up .B6, mem_upSet _⟩ : upSet) ∉
      obstructionRestriction.kempeComponentSet LColor.r LColor.b obstructionComponent := by
  intro h
  have := component_subset h
  simp at this

/-- The upstream switch avoids the input stubs. -/
theorem obstruction_nearStep :
    nearStep seriesLineGraph upSet upInputs obstructionRestriction
      (obstructionRestriction.swapOnKempeComponent LColor.r LColor.b obstructionComponent) := by
  refine ⟨LColor.r, LColor.b, obstructionComponent, ?_, rfl⟩
  rw [Set.disjoint_left]
  intro v hv hB
  have hT := component_subset hv
  simp only [Set.mem_preimage, upInputs, Set.mem_insert_iff, Set.mem_singleton_iff] at hB
  rcases hT with h | h | h <;> rw [h] at hB <;> simp at hB

/-- The downstream part of a composite colouring is a gadget colouring. -/
theorem downstream_check (D : seriesLineGraph.Coloring LColor) :
    tauIncidenceProperColoringCheck (fun e => D (yEdge e)) = true := by
  unfold tauIncidenceProperColoringCheck
  rw [List.all_eq_true]
  intro v _
  cases v <;> simp only [incidentEdges] <;> rw [pairwiseDistinct3_iff] <;>
    exact ⟨D.valid (by decide), D.valid (by decide), D.valid (by decide)⟩

/-- **Step lifting fails for two gadgets in series, on the actual graph.** -/
theorem not_liftsSteps :
    ¬ LiftsSteps (seriesLineGraph.KempeStepAvoiding (α := LColor) upInputs)
      (nearStep seriesLineGraph upSet upInputs) (nearProj (G := seriesLineGraph) upSet) := by
  intro hlift
  obtain ⟨D, hD, -⟩ := hlift obstructionColoring _ obstruction_nearStep
  have hval (e : TauEdge) : D (.up e) =
      (obstructionRestriction.swapOnKempeComponent LColor.r LColor.b obstructionComponent)
        ⟨.up e, mem_upSet e⟩ :=
    congrArg (fun E : (seriesLineGraph.induce upSet).Coloring LColor => E ⟨.up e, mem_upSet e⟩) hD
  have h4 : D (.up .B4) = (stateAt 4).color .B4 := by
    rw [hval, Coloring.swapOnKempeComponent_apply_of_not_mem _ B4_not_mem_component,
      restriction_apply]
    decide
  have h5 : D (.up .B5) = (stateAt 4).color .B5 := by
    rw [hval, Coloring.swapOnKempeComponent_apply_of_mem _ B5_mem_component, restriction_apply]
    decide
  have h6 : D (.up .B6) = (stateAt 4).color .B6 := by
    rw [hval, Coloring.swapOnKempeComponent_apply_of_not_mem _ B6_not_mem_component,
      restriction_apply]
    decide
  have h7 : D (.up .B7) = (stateAt 4).color .B7 := by
    rw [hval, Coloring.swapOnKempeComponent_apply_of_mem _ B7_mem_component, restriction_apply]
    decide
  obtain ⟨t, ht, htcol⟩ := List.mem_map.1
    (tauIncidenceProperColoring_mem_enumeratedTauColorings _ (downstream_check D))
  have hagree : tauInterfaceColorAgrees (stateAt 4) t = true := by
    unfold tauInterfaceColorAgrees
    simp only [Bool.and_eq_true, colorEq_eq_true_iff]
    have hcol (e : TauEdge) : t.color e = D (yEdge e) := congrFun htcol e
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hcol]; exact h4.symm
    · rw [hcol]; exact h5.symm
    · rw [hcol]; exact h6.symm
    · rw [hcol]; exact h7.symm
  have hno := List.all_eq_true.1 TauTauLifting.obstruction_target_has_no_extension t ht
  rw [hagree] at hno
  exact Bool.false_ne_true hno

/-- **The manuscript's preparation hypothesis fails for two gadgets in
series.** -/
theorem not_pairingPreparable :
    ¬ seriesLineGraph.PairingPreparable LColor upSet upInputs :=
  fun h => not_liftsSteps (liftsSteps_nearProj_of_preparable upInputs_subset h)

end Mettapedia.GraphTheory.Kempe.TauSeries
