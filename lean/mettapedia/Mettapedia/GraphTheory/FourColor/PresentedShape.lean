import Mettapedia.GraphTheory.FourColor.PresentedCorridor
import Mettapedia.GraphTheory.FourColor.RungTwoTable

/-!
# Assembling a presented shape's table, and its shape check

`table_eq_of_forall` turns per-word kernel theorems `P.enumMask X = lit[X]` into
the table equality `P.table = lit`, so large cells can be checked one word per
theorem.  The two-darts-per-vertex half of `SlabShape` is decidable for a
presented tangle; connectivity is supplied by explicit chains.  The rung is
run through the generic route as a test: its shape check, table assembly and
stabilisation at index 9 all go through the presentation.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented
namespace Pres

open TubeRingOrbit ZigzagRing

variable {V N k : Nat} [NeZero k] (P : Pres V N k)

section Decidable
open GoertzelV24OpenTangleComposition
variable {Vt It : Type} [Fintype It] [DecidableEq It] {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)}

instance NotOut.decidable (x : SlabDart T) : Decidable (NotOut x) := by
  unfold NotOut; infer_instance

instance DistinctEdge.decidable (x x' : SlabDart T) : Decidable (DistinctEdge x x') := by
  unfold DistinctEdge; infer_instance

end Decidable

/-- per-word equalities assemble the table -/
theorem table_eq_of_forall (lit : List Nat) (hlen : lit.length = 3 ^ k)
    (h : ∀ X, X < 3 ^ k → P.enumMask X = lit[X]!) : P.table = lit := by
  apply List.ext_getElem
  · simp [table, hlen]
  · intro X hX _
    simp only [table, List.getElem_map, List.getElem_range]
    have hX' : X < 3 ^ k := by simpa [table] using hX
    rw [h X hX', getElem!_pos lit X (by omega)]

end Pres

/-! ## The rung through the generic route -/

namespace RungPres

open TubeRingOrbit ZigzagRing Pres

/-- the two-darts half of the shape check, decided -/
theorem two_darts : ∀ v : Fin 6, ∃ x x' : SlabDart (P.toTangle valid),
    (P.toTangle valid).vertOf x = v ∧ (P.toTangle valid).vertOf x' = v ∧
    NotOut x ∧ NotOut x' ∧ DistinctEdge x x' := by
  decide

/-- interior adjacency along the path -/
theorem adj (j : Fin 5) : InteriorAdj (P.toTangle valid) (endPos j false).1 (endPos j true).1 :=
  ⟨(j, false), rfl, rfl⟩

theorem adj' (j : Fin 5) : InteriorAdj (P.toTangle valid) (endPos j true).1 (endPos j false).1 :=
  ⟨(j, true), rfl, rfl⟩

theorem connected (u v : Fin 6) : Relation.ReflTransGen (InteriorAdj (P.toTangle valid)) u v := by
  have step : ∀ j : Fin 5, Relation.ReflTransGen (InteriorAdj (P.toTangle valid))
      (endPos j false).1 (endPos j true).1 := fun j => Relation.ReflTransGen.single (adj j)
  have step' : ∀ j : Fin 5, Relation.ReflTransGen (InteriorAdj (P.toTangle valid))
      (endPos j true).1 (endPos j false).1 := fun j => Relation.ReflTransGen.single (adj' j)
  have up : ∀ v : Fin 6, Relation.ReflTransGen (InteriorAdj (P.toTangle valid)) 0 v := by
    intro v
    fin_cases v
    · exact Relation.ReflTransGen.refl
    · exact step 0
    · exact (step 0).trans (step 1)
    · exact ((step 0).trans (step 1)).trans (step 2)
    · exact (((step 0).trans (step 1)).trans (step 2)).trans (step 3)
    · exact ((((step 0).trans (step 1)).trans (step 2)).trans (step 3)).trans (step 4)
  have down : ∀ v : Fin 6, Relation.ReflTransGen (InteriorAdj (P.toTangle valid)) v 0 := by
    intro v
    fin_cases v
    · exact Relation.ReflTransGen.refl
    · exact step' 0
    · exact (step' 1).trans (step' 0)
    · exact ((step' 2).trans (step' 1)).trans (step' 0)
    · exact (((step' 3).trans (step' 2)).trans (step' 1)).trans (step' 0)
    · exact ((((step' 4).trans (step' 3)).trans (step' 2)).trans (step' 1)).trans (step' 0)
  exact (down u).trans (up v)

theorem shape : SlabShape (P.toTangle valid) := ⟨two_darts, connected⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- the rung's table through the enumerator, checked against the sealed literal -/
theorem table_eq : P.table = RungTwo.rungTableLit := by
  apply table_eq_of_forall P RungTwo.rungTableLit (by decide)
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stabilizes9 : stabilizesAt 9 81 P.table = true := by
  rw [table_eq]; decide +kernel

/-- **the abstract stabilisation hypothesis of the rung, by the generic route** -/
theorem hstab (W : Set (Fin 4 → Color)) :
    (relImage (P.toTangle valid))^[9 + 1] W = (relImage (P.toTangle valid))^[9] W :=
  P.hstab_of_stabilizesAt valid stabilizes9 (by norm_num) W

end RungPres

end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor

/-! ## Generic helpers for shape checks and chunked stabilisation -/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented
namespace Pres

open TubeRingOrbit ZigzagRing

variable {V N k : Nat} [NeZero k] (P : Pres V N k) (hP : P.Valid)

theorem vertOf_inl (y : IDart (N := N)) :
    (P.toTangle hP).vertOf (Sum.inl y) = (P.endPos y.1 y.2).1 := rfl

theorem notOut_inl (y : IDart (N := N)) : NotOut (T := P.toTangle hP) (Sum.inl y) :=
  fun _ => Sum.inl_ne_inr

theorem alpha_fst (y : IDart (N := N)) : ((P.toTangle hP).interiorAlpha y).1 = y.1 := rfl

theorem distinctEdge_inl {y y' : IDart (N := N)} (h : y.1 ≠ y'.1) :
    DistinctEdge (T := P.toTangle hP) (Sum.inl y) (Sum.inl y') := by
  refine ⟨fun e => h (congrArg Prod.fst (Sum.inl_injective e)), ?_⟩
  rintro z z' hz hz'
  cases Sum.inl_injective hz
  cases Sum.inl_injective hz'
  intro e
  apply h
  have := congrArg Prod.fst e
  rwa [P.alpha_fst hP] at this

theorem notOut_inp (i : Fin k) : NotOut (T := P.toTangle hP) (Sum.inr (Sum.inl i)) :=
  fun _ h => Sum.inl_ne_inr (Sum.inr_injective h)

theorem distinctEdge_inp_inl (i : Fin k) (y : IDart (N := N)) :
    DistinctEdge (T := P.toTangle hP) (Sum.inr (Sum.inl i)) (Sum.inl y) :=
  ⟨Sum.inr_ne_inl, fun _ _ h => nomatch h⟩

theorem distinctEdge_inl_inp (y : IDart (N := N)) (i : Fin k) :
    DistinctEdge (T := P.toTangle hP) (Sum.inl y) (Sum.inr (Sum.inl i)) :=
  ⟨Sum.inl_ne_inr, fun _ _ _ h => nomatch h⟩

/-- interior adjacency along edge `j`, from its `false` end to its `true` end -/
theorem adj (j : Fin N) :
    InteriorAdj (P.toTangle hP) (P.endPos j false).1 (P.endPos j true).1 :=
  ⟨(j, false), rfl, rfl⟩

theorem adj' (j : Fin N) :
    InteriorAdj (P.toTangle hP) (P.endPos j true).1 (P.endPos j false).1 :=
  ⟨(j, true), rfl, rfl⟩

/-- range form of the stabilisation check -/
def stabilizesRangeAt (m lo len : Nat) (tab : List Nat) : Bool :=
  (List.range' lo len).all fun w => iterSet tab (m + 1) (1 <<< w) == iterSet tab m (1 <<< w)

theorem stabilizesAt_of_ranges (m n len : Nat) (tab : List Nat) (hlen : 0 < len)
    (h : ∀ c, c * len < n → stabilizesRangeAt m (c * len) len tab = true) :
    stabilizesAt m n tab = true := by
  unfold stabilizesAt
  rw [List.all_eq_true]
  intro w hw
  rw [List.mem_range] at hw
  have hle : w / len * len ≤ w := Nat.div_mul_le_self w len
  have hc := h (w / len) (by omega)
  unfold stabilizesRangeAt at hc
  rw [List.all_eq_true] at hc
  apply hc
  rw [List.mem_range']
  have hdm : w / len * len + w % len = w := Nat.div_add_mod' w len
  exact ⟨w % len, Nat.mod_lt w hlen, by rw [one_mul, hdm]⟩

/-! ### Eventually periodic corridors -/

/-- the stabilisation check at index `m` with period `p` -/
def stabilizesAtPeriod (m p n : Nat) (tab : List Nat) : Bool :=
  (List.range n).all fun w => iterSet tab (m + p) (1 <<< w) == iterSet tab m (1 <<< w)

def stabilizesRangeAtPeriod (m p lo len : Nat) (tab : List Nat) : Bool :=
  (List.range' lo len).all fun w => iterSet tab (m + p) (1 <<< w) == iterSet tab m (1 <<< w)

theorem stabilizesAtPeriod_of_ranges (m p n len : Nat) (tab : List Nat) (hlen : 0 < len)
    (h : ∀ c, c * len < n → stabilizesRangeAtPeriod m p (c * len) len tab = true) :
    stabilizesAtPeriod m p n tab = true := by
  unfold stabilizesAtPeriod
  rw [List.all_eq_true]
  intro w hw
  rw [List.mem_range] at hw
  have hle : w / len * len ≤ w := Nat.div_mul_le_self w len
  have hc := h (w / len) (by omega)
  unfold stabilizesRangeAtPeriod at hc
  rw [List.all_eq_true] at hc
  apply hc
  rw [List.mem_range']
  have hdm : w / len * len + w % len = w := Nat.div_add_mod' w len
  exact ⟨w % len, Nat.mod_lt w hlen, by rw [one_mul, hdm]⟩

theorem iterSet_stable_of_stabilizesAtPeriod {m p : Nat} {tab : List Nat}
    (h : stabilizesAtPeriod m p (3 ^ k) tab = true) {X : Nat} (hX : X < 3 ^ k) :
    iterSet tab (m + p) (1 <<< X) = iterSet tab m (1 <<< X) := by
  unfold stabilizesAtPeriod at h
  rw [List.all_eq_true] at h
  have := h X (List.mem_range.mpr hX)
  rwa [beq_iff_eq] at this

/-- **the abstract eventually-periodic stabilisation hypothesis from the kernel check** -/
theorem hstab_of_stabilizesAtPeriod {m p : Nat}
    (h : stabilizesAtPeriod m p (3 ^ k) P.table = true) (hm : 0 < m) (W : Set (Fin k → Color)) :
    (relImage (P.toTangle hP))^[m + p] W = (relImage (P.toTangle hP))^[m] W := by
  have hW : W = ⋃ w : W, ({(w : Fin k → Color)} : Set (Fin k → Color)) := by ext; simp
  rw [hW, P.relImage_iterate_iUnion hP, P.relImage_iterate_iUnion hP]
  congr 1
  funext w
  by_cases hw : ∀ i, (w : Fin k → Color) i ≠ 0
  · have hs : ({(w : Fin k → Color)} : Set (Fin k → Color)) = wordSet (1 <<< encW k w) := by
      rw [wordSet_singleton (encW_lt k w), wordOf_encW k w hw]
    rw [hs, P.relImage_iterate_wordSet hP, P.relImage_iterate_wordSet hP,
      iterSet_stable_of_stabilizesAtPeriod h (encW_lt k w)]
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : (relImage (P.toTangle hP))^[m' + 1 + p] {(w : Fin k → Color)} = ∅ := by
      rw [show m' + 1 + p = (m' + p) + 1 by omega, Function.iterate_succ_apply,
        P.relImage_singleton_zero hP hw, P.relImage_iterate_empty hP]
    have h2 : (relImage (P.toTangle hP))^[m' + 1] {(w : Fin k → Color)} = ∅ := by
      rw [Function.iterate_succ_apply, P.relImage_singleton_zero hP hw, P.relImage_iterate_empty hP]
    rw [h1, h2]

end Pres
end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor
