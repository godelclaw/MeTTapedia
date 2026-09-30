import MettapediaFourColor.DiamondProfileReducibility

/-!
# The joint diamond contract as a two-vertex wiring

Two free wires join ports 0--1 and 4--5. The remaining four ports meet
two cubic vertices joined by one edge. Keeping that edge retains the
relation between the two insertions. The boundary relation of this wiring
is exactly the reference joint contract, with witnesses in both directions.
The existing shared repair then supplies compatible reconstruction histories.

This file concerns colouring witnesses. Planar occurrence, strict reduction
and geometric coverage require separate theorems.
-/

namespace FourColor.DiamondCoupledWiring

open Color DiamondConfigurations DiamondJointContract

/-- The seven edges include the two wires and the shared central edge 6. -/
structure Coloring where
  edge : Fin 7 → Color
  nonzero : ∀ i, edge i ≠ 0
  left : edge 1 + edge 2 = edge 6
  right : edge 4 + edge 5 = edge 6

def portEdge (i : Fin 8) : Fin 7 := ![0, 0, 1, 2, 3, 3, 4, 5] i

def word (k : Coloring) : List Color :=
  [k.edge 0, k.edge 0, k.edge 1, k.edge 2, k.edge 3, k.edge 3, k.edge 4, k.edge 5]

theorem word_ports (k : Coloring) :
    (List.finRange 8).map (fun i => k.edge (portEdge i)) = word k := rfl

private theorem cancel_middle (a b c : Color) : (a + b) + (b + c) = a + c := by
  calc
    (a + b) + (b + c) = a + (b + b) + c := by abel
    _ = a + c := by simp

/-- Face-colour contract witnesses give nonzero colours of all seven edges. -/
def ofContract (a b x y z w : Color) (h : Admissible a b x y z w) : Coloring where
  edge := ![a + x, a + y, y + b, b + z, b + w, w + a, a + b]
  nonzero := by
    intro i
    fin_cases i <;> dsimp <;>
      intro hz <;> have he := Color.add_eq_zero_iff.mp hz <;> rcases h with
        ⟨hab, hxa, hzb, hya, hyb, hwa, hwb⟩ <;> solve_by_elim [Ne.symm]
  left := cancel_middle a y b
  right := (cancel_middle b w a).trans (add_comm b a)

theorem ofContract_word (a b x y z w : Color) (h : Admissible a b x y z w) :
    word (ofContract a b x y z w h) = trace (boundary a b x y z w) := by
  change [a + x, a + x, a + y, y + b, b + z, b + z, b + w, w + a] = _
  simp only [boundary, trace_cons, List.cons_append, List.nil_append,
    pairmap_cons, pairmap_nil]
  rw [add_comm x a, add_comm z b]

theorem left_readback (k : Coloring) : k.edge 1 + k.edge 6 = k.edge 2 := by
  rw [← k.left, ← add_assoc, Color.add_self, zero_add]

theorem right_readback (k : Coloring) : k.edge 6 + k.edge 5 = k.edge 4 := by
  rw [← k.right, add_assoc, Color.add_self, add_zero]

/-- Choose one face colour as zero; the central edge retains the other choice.
All remaining face colours are reconstructed from actual wiring colours. -/
theorem admissible (k : Coloring) :
    Admissible 0 (k.edge 6) (k.edge 0) (k.edge 1)
      (k.edge 6 + k.edge 3) (k.edge 5) := by
  refine ⟨(k.nonzero 6).symm, k.nonzero 0, ?_, k.nonzero 1, ?_, k.nonzero 5, ?_⟩
  · intro h
    exact k.nonzero 3 (add_left_cancel (h.trans (add_zero _).symm))
  · intro h
    have hz := left_readback k
    rw [h, Color.add_self] at hz
    exact k.nonzero 2 hz.symm
  · intro h
    have hz := right_readback k
    rw [h, Color.add_self] at hz
    exact k.nonzero 4 hz.symm

theorem reconstruct_word (k : Coloring) :
    word k = trace (boundary 0 (k.edge 6) (k.edge 0) (k.edge 1)
      (k.edge 6 + k.edge 3) (k.edge 5)) := by
  simp only [boundary, trace_cons, List.cons_append, List.nil_append,
    pairmap_cons, pairmap_nil, zero_add, add_zero]
  rw [left_readback k, right_readback k, ← add_assoc, Color.add_self, zero_add,
    add_comm (k.edge 6 + k.edge 3) (k.edge 6), ← add_assoc, Color.add_self, zero_add]
  rfl

/-- Exact boundary elimination and reconstruction; no independent repair
certificate is checked for this representation. -/
theorem contractTrace_iff (et : List Color) :
    (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse et ↔
      ∃ k : Coloring, word k = et := by
  rw [DiamondJointContract.contractTrace_iff]
  constructor
  · rintro ⟨a, b, x, y, z, w, h, rfl⟩
    exact ⟨ofContract a b x y z w h, ofContract_word a b x y z w h⟩
  · rintro ⟨k, rfl⟩
    exact ⟨0, k.edge 6, k.edge 0, k.edge 1, k.edge 6 + k.edge 3, k.edge 5,
      admissible k, reconstruct_word k⟩

theorem repair (k : Coloring) :
    KempeCoclosure ((cfmap cf004).map.RingTrace (cfring cf004).reverse) (word k) :=
  DiamondProfileReducibility.repair004 _ ((contractTrace_iff _).mpr ⟨k, rfl⟩)

/-- The same exterior word initiates the already proved joint GSLT repair. -/
theorem compatible_history (k : Coloring) {Q : List Color → Prop}
    (closed : KempeClosed Q) (outside : Q (word k)) :
    ∃ et', ∃ c : DiamondInsertionGSLT.State .reference,
      ∃ x : DiamondInsertionGSLT.State .alternatives,
      Q et' ∧ et' = trace ((cfring cf004).reverse.map c.val) ∧
        DiamondInsertionGSLT.semantics.Supports DiamondInsertionGSLT.route x c :=
  DiamondProfileReducibility.compatible_history closed _
    ((contractTrace_iff _).mpr ⟨k, rfl⟩) outside

/-- Each insertion can separately receive a nonzero central colour, yet
the resulting boundary choices need not share one central colour. -/
theorem forgetting_seam_fails :
    ((.c1 : Color) + .c2 ≠ 0 ∧ (.c1 : Color) + .c3 ≠ 0) ∧
      ¬ ∃ k : Coloring, word k = [.c1, .c1, .c1, .c2, .c1, .c1, .c1, .c3] := by
  refine ⟨by decide, ?_⟩
  rintro ⟨k, hk⟩
  have hs : k.edge 1 + k.edge 2 = k.edge 4 + k.edge 5 := k.left.trans k.right.symm
  have hh : k.edge 0 = .c1 ∧ k.edge 0 = .c1 ∧ k.edge 1 = .c1 ∧ k.edge 2 = .c2 ∧
      k.edge 3 = .c1 ∧ k.edge 3 = .c1 ∧ k.edge 4 = .c1 ∧ k.edge 5 = .c3 := by
    simpa only [word, List.cons.injEq, and_true] using hk
  obtain ⟨_, _, h1, h2, _, _, h4, h5⟩ := hh
  rw [h1, h2, h4, h5] at hs
  exact (by decide : (.c2 : Color) ≠ .c3) (add_left_cancel hs)

end FourColor.DiamondCoupledWiring
