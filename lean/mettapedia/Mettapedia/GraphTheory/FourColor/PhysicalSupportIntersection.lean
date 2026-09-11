import Mettapedia.GraphTheory.FourColor.PhysicalColorNoFanout
import Mettapedia.GraphTheory.FourColor.PhysicalContextLanguage

/-!
# Physical support languages are not closed under intersection

The literal digon pairings `01|23` and `03|12` both accept a constant word.
Their common support forces three distinct ports equal. No nonempty cubic
tangle support, of any finite interior size, can be contained in that
intersection. Thus even weakening exact conjunction to nonempty one-sided
simulation does not yield a generic physical conjunction constructor.

This does not exclude a replacement chosen for one actual exterior, encoded
signals, or a construction not requiring this intersection. The two source
pieces are disconnected, as allowed by disjoint-union composition; no
connected-source version is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalSupportIntersection

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity PhysicalContextBits PhysicalColorNoFanout

abbrev Boundary := Fin 4 → {color : Color // color ≠ 0}
def support (t : Kind) : Set Boundary := taitSupport (ofOpenTangleData (localData t))

private theorem local_vert (t : Kind) (d : D) :
    (ofOpenTangleData (localData t)).vert d = vertex t d := by cases d <;> rfl

theorem mem_support_iff (t : Kind) (w : Boundary) :
    w ∈ support t ↔ ∃ c : Fin 4 → Color, Valid t (fun p => (w p).1) c := by
  constructor
  · rintro ⟨col, hp, hw⟩
    let c : Fin 4 → Color := fun e => col.color (.inl (e, false))
    have he : col.color = colors (fun p => (w p).1) c := by
      funext d
      rcases d with ⟨e, b⟩ | p
      · cases b
        · rfl
        · exact col.invariant (e, false)
      · exact congrFun hw p
    refine ⟨c, ?_⟩
    simpa only [IsProper, Valid, he, local_vert] using hp
  · rintro ⟨c, hc⟩
    let col : Coloring (ofOpenTangleData (localData t)) :=
      ⟨colors (fun p => (w p).1) c, by rintro ⟨e,b⟩; cases b <;> rfl⟩
    refine ⟨col, ?_, rfl⟩
    simpa only [IsProper, Valid, col, local_vert] using hc

private theorem valid_b (w c : Fin 4 → Color) :
    Valid .b w c ↔
      ProperColorTriple (w 0) (c 0) (c 1) ∧
      ProperColorTriple (w 3) (c 0) (c 1) ∧
      ProperColorTriple (w 1) (c 2) (c 3) ∧
      ProperColorTriple (w 2) (c 2) (c 3) := by
  simp only [Valid, colors, vertex, ends, port, Sum.forall, Prod.forall,
    Bool.forall_bool, Fin.forall_fin_succ, Fin.succ_zero_eq_one,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ, ProperColorTriple]
  aesop

private theorem unique_third : ∀ a b x y : Color,
    ProperColorTriple x a b → ProperColorTriple y a b → x = y := by decide

/-- Two actually realizable supports jointly impose the forbidden diagonal. -/
theorem intersection_forces_three_equal {w : Boundary}
    (hw : w ∈ support .a ∩ support .b) : w 0 = w 1 ∧ w 0 = w 2 := by
  obtain ⟨a, ha⟩ := (mem_support_iff .a w).mp hw.1
  obtain ⟨b, hb⟩ := (mem_support_iff .b w).mp hw.2
  obtain ⟨ha0, ha1, -⟩ := (valid_a _ _).mp ha
  obtain ⟨-, -, hb1, hb2⟩ := (valid_b _ _).mp hb
  have h01 := unique_third _ _ _ _ ha0 ha1
  have h12 := unique_third _ _ _ _ hb1 hb2
  exact ⟨Subtype.ext h01, Subtype.ext (h01.trans h12)⟩

theorem intersection_nonempty : (support .a ∩ support .b).Nonempty := by
  let w : Boundary := fun _ => ⟨red, by decide⟩
  refine ⟨w, (mem_support_iff .a w).mpr ?_, (mem_support_iff .b w).mpr ?_⟩
  all_goals exact ⟨![blue, purple, blue, purple], by decide⟩

/-- Not even a nonempty support-contained approximation to this conjunction
can be a finite cubic tangle. The interior size is unrestricted. -/
theorem no_nonempty_support_below_intersection {V I : Type}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (T : PortTangle V I (Fin 4)) (hcubic : IsCubic T)
    (hne : (taitSupport T).Nonempty) :
    ¬ taitSupport T ⊆ support .a ∩ support .b := by
  intro hsub
  apply support_not_subset_diagonal T hcubic hne 0 1 2 (by decide) (by decide) (by decide)
  intro w hw
  exact intersection_forces_three_equal (hsub hw)

theorem no_exact_intersection {V I : Type}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (T : PortTangle V I (Fin 4)) (hcubic : IsCubic T) :
    taitSupport T ≠ support .a ∩ support .b := by
  intro heq
  apply no_nonempty_support_below_intersection T hcubic
    (heq.symm ▸ intersection_nonempty)
  exact heq.subset

end Mettapedia.GraphTheory.FourColor.PhysicalSupportIntersection
