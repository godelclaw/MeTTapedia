import Mettapedia.GraphTheory.FourColor.SerialTangleFaceCode
import Mathlib.Data.Fintype.Inv

/-!
# Executable first-return permutations

The semantic first-return operator used classical decisions. Here the
same least positive return uses a bounded list search with the supplied
decidable marker predicate, and the inverse is a finite search. Equality with the semantic operator
is proved, including its full permutation rather than just cycle counts.
-/

namespace Mettapedia.GraphTheory.FourColor.FiniteFaceReturn

open GoertzelV24SeamFaceArc GoertzelV24OrderedCutFaceReturnProfile

variable {D : Type*} [Fintype D] [DecidableEq D]
  (p : Equiv.Perm D) (hit : D → Prop) [DecidablePred hit]

def time (x : {d // hit d}) : ℕ :=
  ((List.range (Fintype.card D + 1)).find?
    (fun n => decide (0 < n ∧ hit ((p ^ n) x.1)))).getD 0

theorem time_eq (x : {d // hit d}) :
    time p hit x = firstPositiveHitTime p hit x.1 x.2 := by
  let n := firstPositiveHitTime p hit x.1 x.2
  have hn : n ≤ Fintype.card D :=
    (firstPositiveHitTime_le_sameCycle_card p hit x.1 x.2).trans
      (Finset.card_le_card (Finset.filter_subset ..))
  have hs : (List.range (Fintype.card D + 1)).find?
      (fun j => decide (0 < j ∧ hit ((p ^ j) x.1))) = some n := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, n, by simpa using Nat.lt_succ_of_le hn, ?_, ?_⟩
    · simpa using And.intro (firstPositiveHitTime_pos p hit x.1 x.2)
        (firstPositiveHitTime_hits p hit x.1 x.2)
    · simp
    · intro j hj
      simp only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not]
      intro hh
      obtain ⟨hpos, hhit⟩ := hh
      exact not_hit_before_firstPositiveHitTime p hit x.1 x.2 hpos hj hhit
  simp only [time, hs, Option.getD_some, n]

def next (x : {d // hit d}) : {d // hit d} :=
  ⟨(p ^ time p hit x) x.1, by
    rw [time_eq]
    exact firstPositiveHitTime_hits p hit x.1 x.2⟩

theorem next_eq (x : {d // hit d}) : next p hit x = nextHitPerm p hit x := by
  apply Subtype.ext
  change (p ^ time p hit x) x.1 = (p ^ firstPositiveHitTime p hit x.1 x.2) x.1
  rw [time_eq]

theorem next_bijective : Function.Bijective (next p hit) := by
  have he : next p hit = (nextHitPerm p hit : {d // hit d} → {d // hit d}) :=
    funext (next_eq p hit)
  rw [he]
  exact (nextHitPerm p hit).bijective

def permutation : Equiv.Perm {d // hit d} :=
  letI : Fintype {d // hit d} := Subtype.fintype hit
  { toFun := next p hit
    invFun := Fintype.bijInv (next_bijective p hit)
    left_inv := Fintype.leftInverse_bijInv (next_bijective p hit)
    right_inv := Fintype.rightInverse_bijInv (next_bijective p hit) }

theorem permutation_eq : permutation p hit = nextHitPerm p hit := by
  apply Equiv.ext
  intro x
  exact next_eq p hit x

open SerialTangleFaceCode
variable {L P R : Type*} [Fintype L] [DecidableEq L]
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]

instance : DecidablePred (@ExternalCode L P R) := by
  rintro ((l | p) | (p | r)) <;> unfold ExternalCode <;> infer_instance

def transfer (a : Equiv.Perm (L ⊕ P)) (b : Equiv.Perm (P ⊕ R)) :
    Equiv.Perm (L ⊕ R) :=
  codeExternalCoordinate.permCongr
    (permutation (Equiv.sumCongr a b * codeSwap) ExternalCode)

theorem transfer_eq (a : Equiv.Perm (L ⊕ P)) (b : Equiv.Perm (P ⊕ R)) :
    transfer a b = SerialTangleFaceCode.transfer a b := by
  unfold transfer SerialTangleFaceCode.transfer
  rw [permutation_eq]

end Mettapedia.GraphTheory.FourColor.FiniteFaceReturn
