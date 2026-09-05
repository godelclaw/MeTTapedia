import Mettapedia.GraphTheory.FourColor.PresentedCapEnum

/-! The `k`-gon cap: `k` vertices in a cycle, each with one port; the smallest disc on `k`
ports with every vertex cubic.  The octagon passes the disc check by kernel decision. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation.PresentedCap

/-- at vertex `v` the slots are the edge to `v + 1`, the port, the edge from `v - 1` -/
def ngon (k : Nat) [NeZero k] : Pres k k k where
  tri v s := if s = 0 then Slot.edge v else if s = 1 then Slot.port v else Slot.edge (v - 1)
  endPos e b := if b then (e + 1, 2) else (e, 0)
  portPos i := (i, 1)

namespace Ngon

theorem valid8 : (ngon 8).Valid := by decide

theorem disc8 : (ngon 8).discCheck valid8 = true := by decide +kernel

theorem valid7 : (ngon 7).Valid := by decide

theorem disc7 : (ngon 7).discCheck valid7 = true := by decide +kernel

end Ngon

/-- a member of a list lies in one of its chunks -/
theorem mem_take_drop_of_mem {α : Type*} {l : List α} {u : α} (h : u ∈ l) (c : Nat)
    (hc : 0 < c) : ∃ j, u ∈ (l.drop (c * j)).take c := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  refine ⟨i / c, ?_⟩
  have hmod := Nat.mod_lt i hc
  have hdm := Nat.div_add_mod i c
  have hr : i % c < ((l.drop (c * (i / c))).take c).length := by
    rw [List.length_take, List.length_drop]
    omega
  have hidx : ((l.drop (c * (i / c))).take c)[i % c] = l[i] := by
    rw [List.getElem_take, List.getElem_drop]
    simp only [hdm]
  rw [← hidx]
  exact List.getElem_mem _

/-- a nonempty chunk starts before the end of the list -/
theorem lt_of_mem_take_drop {α : Type*} {l : List α} {u : α} {c j : Nat}
    (h : u ∈ (l.drop (c * j)).take c) : c * j < l.length := by
  by_contra hcon
  have : l.drop (c * j) = [] := List.drop_eq_nil_of_le (by omega)
  rw [this] at h
  simp at h

end Mettapedia.GraphTheory.FourColor.KempeDerivation.PresentedCap
