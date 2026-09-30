import Mettapedia.GraphTheory.FourColor.CyclicFiveBoundary
import Mettapedia.GraphTheory.CoupledThreeColouring

/-!
# Two-vertex deletion from cyclically four-edge-connected cubic graphs

The source condition of coupled colouring is derived from actual cuts. Two
different components after deleting two vertices have at most six outgoing
darts in total. One therefore has at most three. Cubic degree counting forces
cycles on both sides of its exact boundary, contradicting cyclic connectivity.

The argument concerns finite simple graphs. It neither supplies spherical
geometry nor recognizes an inverse dual-and-truncate representation.
-/

namespace Mettapedia.GraphTheory.FourColor.CubicPairDeletionConnectivity

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : _root_.SimpleGraph V) [DecidableRel G.Adj] [G.LocallyFinite]

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem two_le_side_card (side : V → Prop) {x y : V}
    (hx : side x) (hy : side y) (hne : x ≠ y) :
    2 ≤ Nat.card {v : V // side v} := by
  have hsubset : ({x, y} : Finset V) ⊆ Finset.univ.filter side := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [hx, hy]
  have hcard := Finset.card_le_card hsubset
  rw [Nat.card_eq_fintype_card]
  simpa [hne, Fintype.card_subtype] using hcard

/-- At least two cubic vertices behind at most three outgoing darts force a
cycle. The existing forest boundary law supplies the counting argument. -/
theorem hasCycleOnSide_of_two_le_card_of_crossing_le_three
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (htwo : 2 ≤ Nat.card {v : V // side v})
    (hcross : Fintype.card (CrossingSideDart G side) ≤ 3) :
    HasCycleOnSide G side := by
  have htwo' : 2 ≤ Fintype.card {v : V // side v} := by
    simpa only [Nat.card_eq_fintype_card] using htwo
  exact CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
    (G := G) (fun v =>
      (GoertzelV24CubicSmallBoundaryCycle.degree_instance_independent v _ _).trans (hregular v))
    side (Fintype.card_pos_iff.mp (by omega)) (by omega)

abbrev retained (a b : V) := G.induce {v | v ≠ a ∧ v ≠ b}

/-- A retained component viewed on the ambient source carrier. -/
def componentSide (a b : V) (c : (retained G a b).ConnectedComponent) (v : V) : Prop :=
  ∃ hv : v ≠ a ∧ v ≠ b, (⟨v, hv⟩ : CoupledThreeColouring.Retained a b) ∈ c.supp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem componentSide_avoids {a b : V}
    (c : (retained G a b).ConnectedComponent) {v : V}
    (hv : componentSide G a b c v) : v ≠ a ∧ v ≠ b := hv.choose

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem componentSide_of_adj {a b : V}
    (c : (retained G a b).ConnectedComponent) {v w : V}
    (hv : componentSide G a b c v) (hw : w ≠ a ∧ w ≠ b)
    (hadj : G.Adj v w) : componentSide G a b c w := by
  obtain ⟨hv', hmem⟩ := hv
  exact ⟨hw, c.mem_supp_of_adj_mem_supp hmem hadj⟩

/-- Every outgoing component dart ends at one of the two deleted vertices. -/
theorem crossing_ends_deleted {a b : V}
    (c : (retained G a b).ConnectedComponent)
    (d : CrossingSideDart G (componentSide G a b c)) :
    d.1.snd = a ∨ d.1.snd = b := by
  by_contra h
  have hw : d.1.snd ≠ a ∧ d.1.snd ≠ b := by simpa using h
  exact d.2.2 (componentSide_of_adj G c d.2.1 hw d.1.adj)

/-- Reversing the outgoing dart gives a genuine dart starting at a deleted
vertex. This is the finite interface used to count all boundary influence. -/
def reverseCrossing {a b : V} (c : (retained G a b).ConnectedComponent)
    (d : CrossingSideDart G (componentSide G a b c)) :
    SideDart G (fun v => v = a ∨ v = b) :=
  ⟨d.1.symm, crossing_ends_deleted G c d⟩

theorem reverseCrossing_injective {a b : V}
    (c : (retained G a b).ConnectedComponent) :
    Function.Injective (reverseCrossing G c) := by
  intro d e he
  apply Subtype.ext
  have h := congrArg (fun x => x.1.symm) he
  simpa [reverseCrossing] using h

/-- Distinct retained components use disjoint outgoing darts. -/
theorem reverseCrossing_ne {a b : V}
    {c e : (retained G a b).ConnectedComponent} (hne : c ≠ e)
    (d : CrossingSideDart G (componentSide G a b c))
    (f : CrossingSideDart G (componentSide G a b e)) :
    reverseCrossing G c d ≠ reverseCrossing G e f := by
  intro he
  have hv : d.1.fst = f.1.fst := congrArg (fun x => x.1.snd) he
  obtain ⟨hd, hdm⟩ := d.2.1
  obtain ⟨hf, hfm⟩ := f.2.1
  apply hne
  exact ConnectedComponent.eq_of_common_vertex hdm (by simpa [hv] using hfm)

/-- The two deleted cubic vertices provide six possible outgoing source
darts; two different retained components cannot spend the same dart twice. -/
theorem two_component_crossing_card_le_six
    (hregular : G.IsRegularOfDegree 3) {a b : V} (hab : a ≠ b)
    {c e : (retained G a b).ConnectedComponent} (hne : c ≠ e) :
    Fintype.card (CrossingSideDart G (componentSide G a b c)) +
      Fintype.card (CrossingSideDart G (componentSide G a b e)) ≤ 6 := by
  have hinj := (reverseCrossing_injective G c).sumElim
    (reverseCrossing_injective G e) (reverseCrossing_ne G hne)
  have hbound := Fintype.card_le_of_injective
    (Sum.elim (reverseCrossing G c) (reverseCrossing G e)) hinj
  have hdeleted : Fintype.card {v : V // v = a ∨ v = b} = 2 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun v => v = a ∨ v = b) = {a, b} := by
      ext v
      simp
    rw [heq]
    simp [hab]
  rw [Fintype.card_sum, card_sideDart_eq_three_mul hregular, hdeleted] at hbound
  exact hbound

omit [Fintype V] [DecidableRel G.Adj] in
private theorem exists_retained_neighbour
    (hregular : G.IsRegularOfDegree 3) (a b v : V) :
    ∃ w, G.Adj v w ∧ w ≠ a ∧ w ≠ b := by
  have hnot : ¬ G.neighborFinset v ⊆ ({a, b} : Finset V) := by
    intro hs
    have hcard := Finset.card_le_card hs
    have hpair : ({a, b} : Finset V).card ≤ 2 := by
      by_cases he : a = b <;> simp [he]
    rw [card_neighborFinset_eq_degree, hregular.degree_eq] at hcard
    omega
  obtain ⟨w, hw, hnot⟩ := Finset.not_subset.mp hnot
  exact ⟨w, (mem_neighborFinset G v w).mp hw, by simpa using hnot⟩

/-- A retained component contains at least two vertices: a simple cubic
vertex cannot have all three neighbours among two deleted vertices. -/
theorem componentSide_card_two_le
    (hregular : G.IsRegularOfDegree 3) {a b : V}
    (c : (retained G a b).ConnectedComponent) :
    2 ≤ Nat.card {v : V // componentSide G a b c v} := by
  obtain ⟨v, hv⟩ := c.nonempty_supp
  have hside : componentSide G a b c v.1 := ⟨v.2, hv⟩
  obtain ⟨w, hadj, hw⟩ := exists_retained_neighbour G hregular a b v.1
  exact two_le_side_card (componentSide G a b c) hside
    (componentSide_of_adj G c hside hw hadj) hadj.ne

/-- Deleting any two distinct vertices of a finite simple cubic graph with
cyclic edge-connectivity at least four leaves a connected graph. -/
theorem pairDeletion_connected
    (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (a b : V) (hab : a ≠ b) : (retained G a b).Connected := by
  obtain ⟨v, _, hv⟩ := exists_retained_neighbour G hregular a b a
  let : Nonempty ↑({v | v ≠ a ∧ v ≠ b} : Set V) := ⟨⟨v, hv⟩⟩
  by_contra hconn
  have hnot : ¬ (retained G a b).Preconnected := fun hp =>
    hconn { preconnected := hp }
  simp only [Preconnected, not_forall] at hnot
  obtain ⟨x, y, hxy⟩ := hnot
  let c := (retained G a b).connectedComponentMk x
  let e := (retained G a b).connectedComponentMk y
  have hne : c ≠ e := fun he => hxy (ConnectedComponent.exact he)
  have hbound := two_component_crossing_card_le_six G hregular hab hne
  have hsmall :
      Fintype.card (CrossingSideDart G (componentSide G a b c)) ≤ 3 ∨
      Fintype.card (CrossingSideDart G (componentSide G a b e)) ≤ 3 := by omega
  have exclude : ∀ z : (retained G a b).ConnectedComponent,
      Fintype.card (CrossingSideDart G (componentSide G a b z)) ≤ 3 → False := by
    intro z hz
    let side := componentSide G a b z
    change Fintype.card (CrossingSideDart G side) ≤ 3 at hz
    have hcycle := hasCycleOnSide_of_two_le_card_of_crossing_le_three G hregular side
      (componentSide_card_two_le G hregular z) hz
    have hcomplTwo : 2 ≤ Nat.card {v : V // ¬ side v} := by
      exact two_le_side_card (fun v => ¬ side v)
        (fun ha => (componentSide_avoids G z ha).1 rfl)
        (fun hb => (componentSide_avoids G z hb).2 rfl) hab
    have hcomplCount : Fintype.card (CrossingSideDart G (fun v => ¬ side v)) =
        Fintype.card (CrossingSideDart G side) := by
      refine Fintype.card_congr ?_
      exact
        { toFun := fun d => ⟨d.1.symm, by simpa using d.2.2, d.2.1⟩
          invFun := fun d => ⟨d.1.symm, d.2.2, by simpa using d.2.1⟩
          left_inv := fun d => by apply Subtype.ext; simp
          right_inv := fun d => by apply Subtype.ext; simp }
    have hcomplCycle := hasCycleOnSide_of_two_le_card_of_crossing_le_three G hregular
      (fun v => ¬ side v) hcomplTwo
      (hcomplCount.trans_le hz)
    let cut : SmallCyclicEdgeCut G :=
      { edgeCut := crossingEdgeFinset G side
        side := side
        hcut_eq := mem_crossingEdgeFinset_iff side
        hcard_le_four := by
          rw [card_crossingEdgeFinset_eq_card_crossingSideDart]
          exact hz.trans (by decide)
        hinside_cycle := hcycle
        houtside_cycle := hcomplCycle }
    have hlarge := hcyclic cut
    have hcard : cut.edgeCut.card ≤ 3 := by
      change (crossingEdgeFinset G side).card ≤ 3
      rwa [card_crossingEdgeFinset_eq_card_crossingSideDart]
    omega
  exact hsmall.elim (exclude c) (exclude e)

/-- The geometric cut condition discharges the source-colouring supplier's
entire two-vertex-deletion hypothesis. -/
theorem colourable_three_of_cyclic_connectivity
    (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (hconn : G.Connected)
    (hnot : ¬∀ x y : V, x ≠ y → G.Adj x y) : G.Colorable 3 := by
  exact CoupledThreeColouring.colourable_of_pairDeletionConnected G
    (fun v =>
      (GoertzelV24CubicSmallBoundaryCycle.degree_instance_independent (G := G) v _ _).trans_le
        (le_of_eq (hregular.degree_eq v))) hconn hnot
    (pairDeletion_connected G hregular hcyclic)

end
end Mettapedia.GraphTheory.FourColor.CubicPairDeletionConnectivity
