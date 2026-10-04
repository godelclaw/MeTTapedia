import MettapediaFourColor.CoreProfileSwitchObstruction

/-! # A source boundary which no single two-colour change can repair -/

namespace FourColor.CorePairChangeObstruction

open SimpleGraph FiveTriangleCollapseObstruction CoreProfileSwitchObstruction

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Each position is kept or swapped using the same colour pair. No
connectivity assumption is imposed on the selected positions. -/
def PairChange (a b : Palette) (w w' : Boundary) : Prop :=
  ∀ j, w' j = w j ∨ w' j = Equiv.swap a b (w j)

abbrev sourceWord (K : upper.graph.Coloring Palette) : Boundary :=
  fun j => K (j.castAdd 7)

/-- The source incidences consumed by the six triangle arguments. They
are decoded and checked once, then shared by all uses. -/
private def requiredEdges : List (Fin 18 × Fin 18) :=
  [(1,15), (2,3), (2,15), (3,4), (3,12), (3,15), (4,5), (4,12), (5,6), (5,12), (5,13), (6,7), (6,13), (7,8), (7,13), (7,14), (8,14), (11,8), (11,12), (11,14), (11,15), (11,16), (11,17), (12,3), (12,4), (12,5), (12,13), (12,14), (13,5), (13,6), (13,7), (13,14), (14,7), (14,8), (14,12), (15,1), (15,2), (15,12), (15,17), (16,8), (16,10), (16,17), (17,0), (17,1), (17,15)]

private theorem edges_checked : requiredEdges.all
    (fun e => decide (upper.graph.Adj e.1 e.2)) = true := by decide +kernel

private theorem edge (K : upper.graph.Coloring Palette) (u v : Fin 18)
    (h : (u,v) ∈ requiredEdges) : K u ≠ K v :=
  K.valid (of_decide_eq_true (List.all_eq_true.mp edges_checked (u,v) h))

/-- The other two colours after excluding a specified pair. -/
private theorem remaining (a b c d : Palette)
    (cover : ∀ x : Palette, x = a ∨ x = b ∨ x = c ∨ x = d)
    {x : Palette} (ha : x ≠ a) (hb : x ≠ b) : x = c ∨ x = d := by
  exact ((cover x).resolve_left ha).resolve_left hb

/-- Two adjacent vertices using one pair force their common neighbour
outside that pair. This argument works for any palette. -/
private theorem third_outside {α : Type*} {a b x y z : α}
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) : z ≠ a ∧ z ≠ b := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact False.elim (xy rfl)
  · exact ⟨xz.symm, yz.symm⟩
  · exact ⟨yz.symm, xz.symm⟩
  · exact False.elim (xy rfl)

private theorem triangle_not_two {α : Type*} {a b x y z : α}
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) (hz : z = a ∨ z = b) : False := by
  have h := third_outside xy xz yz hx hy
  exact hz.elim h.1 h.2

/-- The core triangle 12/13/14 is restricted to colours 0 and 1. -/
private theorem no_change01 (K : upper.graph.Coloring Palette)
    (h : PairChange 0 1 (word true) (sourceWord K)) : False := by
  have b3 : K 3 = 2 := (h 3).elim id id
  have b5 : K 5 = 3 := (h 5).elim id id
  have b7 : K 7 = 2 := (h 7).elim id id
  have b8 : K 8 = 3 := (h 8).elim id id
  have e12_3 := edge K 12 3 (by decide +kernel)
  have e12_5 := edge K 12 5 (by decide +kernel)
  have e13_5 := edge K 13 5 (by decide +kernel)
  have e13_7 := edge K 13 7 (by decide +kernel)
  have e14_7 := edge K 14 7 (by decide +kernel)
  have e14_8 := edge K 14 8 (by decide +kernel)
  have e12_13 := edge K 12 13 (by decide +kernel)
  have e12_14 := edge K 12 14 (by decide +kernel)
  have e13_14 := edge K 13 14 (by decide +kernel)
  have p12 := remaining 2 3 0 1 (by decide +kernel) (b3 ▸ e12_3) (b5 ▸ e12_5)
  have p13 := remaining 2 3 0 1 (by decide +kernel) (b7 ▸ e13_7) (b5 ▸ e13_5)
  have p14 := remaining 2 3 0 1 (by decide +kernel) (b7 ▸ e14_7) (b8 ▸ e14_8)
  exact triangle_not_two e12_13 e12_14 e13_14 p12 p13 p14

/-- Two triangular constraints force colours 3 and 1 at vertices 15 and 14; triangle 11/16/17 then has only colours 0 and 2. -/
private theorem no_change02 (K : upper.graph.Coloring Palette)
    (h : PairChange 0 2 (word true) (sourceWord K)) : False := by
  have b1 : K 1 = 1 := (h 1).elim id id
  have b2 : K 2 = 0 ∨ K 2 = 2 := h 2
  have b3 : K 3 = 2 ∨ K 3 = 0 := h 3
  have b5 : K 5 = 3 := (h 5).elim id id
  have b6 : K 6 = 1 := (h 6).elim id id
  have b7 : K 7 = 2 ∨ K 7 = 0 := h 7
  have b8 : K 8 = 3 := (h 8).elim id id
  have b10 : K 10 = 1 := (h 10).elim id id
  have e1_15 := edge K 1 15 (by decide +kernel)
  have e2_15 := edge K 2 15 (by decide +kernel)
  have e3_15 := edge K 3 15 (by decide +kernel)
  have e2_3 := edge K 2 3 (by decide +kernel)
  have e13_5 := edge K 13 5 (by decide +kernel)
  have e13_6 := edge K 13 6 (by decide +kernel)
  have e7_13 := edge K 7 13 (by decide +kernel)
  have e7_14 := edge K 7 14 (by decide +kernel)
  have e13_14 := edge K 13 14 (by decide +kernel)
  have e14_8 := edge K 14 8 (by decide +kernel)
  have e11_8 := edge K 11 8 (by decide +kernel)
  have e11_14 := edge K 11 14 (by decide +kernel)
  have e16_8 := edge K 16 8 (by decide +kernel)
  have e16_10 := edge K 16 10 (by decide +kernel)
  have e17_1 := edge K 17 1 (by decide +kernel)
  have e17_15 := edge K 17 15 (by decide +kernel)
  have e11_16 := edge K 11 16 (by decide +kernel)
  have e11_17 := edge K 11 17 (by decide +kernel)
  have e16_17 := edge K 16 17 (by decide +kernel)
  have out15 := third_outside e2_3 e2_15 e3_15 b2 b3.symm
  have b15 : K 15 = 3 :=
    (remaining 0 2 1 3 (by decide +kernel) out15.1 out15.2).resolve_left (b1 ▸ e1_15.symm)
  have p13 := remaining 1 3 0 2 (by decide +kernel) (b6 ▸ e13_6) (b5 ▸ e13_5)
  have out14 := third_outside e7_13 e7_14 e13_14 b7.symm p13
  have b14 : K 14 = 1 :=
    (remaining 0 2 1 3 (by decide +kernel) out14.1 out14.2).resolve_right (b8 ▸ e14_8)
  have p11 := remaining 1 3 0 2 (by decide +kernel) (b14 ▸ e11_14) (b8 ▸ e11_8)
  have p16 := remaining 1 3 0 2 (by decide +kernel) (b10 ▸ e16_10) (b8 ▸ e16_8)
  have p17 := remaining 1 3 0 2 (by decide +kernel) (b1 ▸ e17_1) (b15 ▸ e17_15)
  exact triangle_not_two e11_16 e11_17 e16_17 p11 p16 p17

/-- Boundary vertex 5 and core vertices 12 and 13 form a triangle restricted to colours 0 and 3. -/
private theorem no_change03 (K : upper.graph.Coloring Palette)
    (h : PairChange 0 3 (word true) (sourceWord K)) : False := by
  have b3 : K 3 = 2 := (h 3).elim id id
  have b4 : K 4 = 1 := (h 4).elim id id
  have b5 : K 5 = 3 ∨ K 5 = 0 := h 5
  have b6 : K 6 = 1 := (h 6).elim id id
  have b7 : K 7 = 2 := (h 7).elim id id
  have e12_3 := edge K 12 3 (by decide +kernel)
  have e12_4 := edge K 12 4 (by decide +kernel)
  have e13_6 := edge K 13 6 (by decide +kernel)
  have e13_7 := edge K 13 7 (by decide +kernel)
  have e12_5 := edge K 12 5 (by decide +kernel)
  have e13_5 := edge K 13 5 (by decide +kernel)
  have e12_13 := edge K 12 13 (by decide +kernel)
  have p12 := remaining 1 2 0 3 (by decide +kernel) (b4 ▸ e12_4) (b3 ▸ e12_3)
  have p13 := remaining 1 2 0 3 (by decide +kernel) (b6 ▸ e13_6) (b7 ▸ e13_7)
  exact triangle_not_two e12_13 e12_5 e13_5 p12 p13 b5.symm

/-- Two adjacent core tips are both forced to colour zero by boundary triangles. -/
private theorem no_change12 (K : upper.graph.Coloring Palette)
    (h : PairChange 1 2 (word true) (sourceWord K)) : False := by
  have b3 : K 3 = 2 ∨ K 3 = 1 := h 3
  have b4 : K 4 = 1 ∨ K 4 = 2 := h 4
  have b5 : K 5 = 3 := (h 5).elim id id
  have b6 : K 6 = 1 ∨ K 6 = 2 := h 6
  have b7 : K 7 = 2 ∨ K 7 = 1 := h 7
  have e3_4 := edge K 3 4 (by decide +kernel)
  have e3_12 := edge K 3 12 (by decide +kernel)
  have e4_12 := edge K 4 12 (by decide +kernel)
  have e12_5 := edge K 12 5 (by decide +kernel)
  have e6_7 := edge K 6 7 (by decide +kernel)
  have e6_13 := edge K 6 13 (by decide +kernel)
  have e7_13 := edge K 7 13 (by decide +kernel)
  have e13_5 := edge K 13 5 (by decide +kernel)
  have e12_13 := edge K 12 13 (by decide +kernel)
  have out12 := third_outside e3_4 e3_12 e4_12 b3.symm b4
  have out13 := third_outside e6_7 e6_13 e7_13 b6 b7.symm
  have b12 : K 12 = 0 :=
    (remaining 1 2 0 3 (by decide +kernel) out12.1 out12.2).resolve_right (b5 ▸ e12_5)
  have b13 : K 13 = 0 :=
    (remaining 1 2 0 3 (by decide +kernel) out13.1 out13.2).resolve_right (b5 ▸ e13_5)
  exact e12_13 (b12.trans b13.symm)

/-- Two adjacent core tips are both forced to colour zero by boundary triangles. -/
private theorem no_change13 (K : upper.graph.Coloring Palette)
    (h : PairChange 1 3 (word true) (sourceWord K)) : False := by
  have b3 : K 3 = 2 := (h 3).elim id id
  have b4 : K 4 = 1 ∨ K 4 = 3 := h 4
  have b5 : K 5 = 3 ∨ K 5 = 1 := h 5
  have b6 : K 6 = 1 ∨ K 6 = 3 := h 6
  have b7 : K 7 = 2 := (h 7).elim id id
  have e4_5 := edge K 4 5 (by decide +kernel)
  have e12_3 := edge K 12 3 (by decide +kernel)
  have e4_12 := edge K 4 12 (by decide +kernel)
  have e5_12 := edge K 5 12 (by decide +kernel)
  have e5_6 := edge K 5 6 (by decide +kernel)
  have e5_13 := edge K 5 13 (by decide +kernel)
  have e6_13 := edge K 6 13 (by decide +kernel)
  have e13_7 := edge K 13 7 (by decide +kernel)
  have e12_13 := edge K 12 13 (by decide +kernel)
  have out12 := third_outside e4_5 e4_12 e5_12 b4 b5.symm
  have out13 := third_outside e5_6 e5_13 e6_13 b5.symm b6
  have b12 : K 12 = 0 :=
    (remaining 1 3 0 2 (by decide +kernel) out12.1 out12.2).resolve_right (b3 ▸ e12_3)
  have b13 : K 13 = 0 :=
    (remaining 1 3 0 2 (by decide +kernel) out13.1 out13.2).resolve_right (b7 ▸ e13_7)
  exact e12_13 (b12.trans b13.symm)

/-- Triangle 3/12/15 forces vertex 12 to zero, then 14 to one. Triangle 11/15/17 is restricted to colours 2 and 3. -/
private theorem no_change23 (K : upper.graph.Coloring Palette)
    (h : PairChange 2 3 (word true) (sourceWord K)) : False := by
  have b0 : K 0 = 0 := (h 0).elim id id
  have b1 : K 1 = 1 := (h 1).elim id id
  have b2 : K 2 = 0 := (h 2).elim id id
  have b3 : K 3 = 2 ∨ K 3 = 3 := h 3
  have b4 : K 4 = 1 := (h 4).elim id id
  have b7 : K 7 = 2 ∨ K 7 = 3 := h 7
  have b8 : K 8 = 3 ∨ K 8 = 2 := h 8
  have e17_0 := edge K 17 0 (by decide +kernel)
  have e17_1 := edge K 17 1 (by decide +kernel)
  have e15_1 := edge K 15 1 (by decide +kernel)
  have e15_2 := edge K 15 2 (by decide +kernel)
  have e3_15 := edge K 3 15 (by decide +kernel)
  have e3_12 := edge K 3 12 (by decide +kernel)
  have e15_12 := edge K 15 12 (by decide +kernel)
  have e12_4 := edge K 12 4 (by decide +kernel)
  have e7_8 := edge K 7 8 (by decide +kernel)
  have e7_14 := edge K 7 14 (by decide +kernel)
  have e8_14 := edge K 8 14 (by decide +kernel)
  have e14_12 := edge K 14 12 (by decide +kernel)
  have e11_12 := edge K 11 12 (by decide +kernel)
  have e11_14 := edge K 11 14 (by decide +kernel)
  have e11_15 := edge K 11 15 (by decide +kernel)
  have e11_17 := edge K 11 17 (by decide +kernel)
  have e15_17 := edge K 15 17 (by decide +kernel)
  have p15 := remaining 0 1 2 3 (by decide +kernel) (b2 ▸ e15_2) (b1 ▸ e15_1)
  have p17 := remaining 0 1 2 3 (by decide +kernel) (b0 ▸ e17_0) (b1 ▸ e17_1)
  have out12 := third_outside e3_15 e3_12 e15_12 b3 p15
  have b12 : K 12 = 0 :=
    (remaining 2 3 0 1 (by decide +kernel) out12.1 out12.2).resolve_right (b4 ▸ e12_4)
  have out14 := third_outside e7_8 e7_14 e8_14 b7 b8.symm
  have b14 : K 14 = 1 :=
    (remaining 2 3 0 1 (by decide +kernel) out14.1 out14.2).resolve_left (b12 ▸ e14_12)
  have p11 := remaining 0 1 2 3 (by decide +kernel) (b12 ▸ e11_12) (b14 ▸ e11_14)
  exact triangle_not_two e11_15 e11_17 e15_17 p11 p15 p17

private theorem no_diagonal (a : Palette) (K : upper.graph.Coloring Palette)
    (h : PairChange a a (word true) (sourceWord K)) : False := by
  apply no_change01 K
  intro j
  left
  simpa only [Equiv.swap_self, Equiv.refl_apply, or_self] using h j

theorem PairChange.comm {a b : Palette} {w w' : Boundary} (h : PairChange a b w w') :
    PairChange b a w w' := by
  simpa only [PairChange, Equiv.swap_comm] using h

/-- No pointwise selection of swaps in one colour pair gives a source colouring.
This is stronger than ruling out a single connected-component switch. -/
theorem no_pair_change (a b : Palette) (K : upper.graph.Coloring Palette) :
    ¬ PairChange a b (word true) (sourceWord K) := by
  fin_cases a <;> fin_cases b
  all_goals first
    | exact no_diagonal _ K
    | exact no_change01 K
    | exact no_change02 K
    | exact no_change03 K
    | exact no_change12 K
    | exact no_change13 K
    | exact no_change23 K
    | exact fun h => no_change01 K h.comm
    | exact fun h => no_change02 K h.comm
    | exact fun h => no_change03 K h.comm
    | exact fun h => no_change12 K h.comm
    | exact fun h => no_change13 K h.comm
    | exact fun h => no_change23 K h.comm

end FourColor.CorePairChangeObstruction
