import Mettapedia.SetTheory.OpenTower.InternalTower
import Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Find
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Surjective bounded morphisms from the closed sets

Under cofinally many inaccessibles, the closed sets of one level are well-ordered by
membership. Every closed set has an immediate successor, the least closed set around it,
and the next closed set after any ω-chain of successors lies exactly ω steps later.

A nonempty finite reflexive transitive total relation therefore receives a surjective
bounded morphism from every closed set: worlds of equal mutual access form a cluster,
each cluster but the last occupies one ω-block of closed sets, and the last cluster
occupies the remaining unbounded tail. The value at a closed set is the cluster element
whose index is the position in that block, modulo the size of the cluster.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Potentialism

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
open Mettapedia.SetTheory.OpenTower.InternalTower
open Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
open Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
open scoped ZFSet

universe u

open Classical

abbrev closedMemRel (A B : {U : ZFSet.{u} // Closed U}) : Prop := A.1 ∈ B.1

instance : IsWellOrder {U : ZFSet.{u} // Closed U} closedMemRel :=
  closedSets_isWellOrder

/-- Membership of closed sets, read as an ordinal position. -/
abbrev closedTypein (A : {U : ZFSet.{u} // Closed U}) : Ordinal.{u + 1} :=
  Ordinal.typein closedMemRel A

/-- The empty set is not a member of itself. -/
example : ¬ closedMemRel ⟨(∅ : ZFSet.{u}), closed_empty⟩ ⟨∅, closed_empty⟩ :=
  ZFSet.notMem_empty _

/-- The empty set is a member of the least closed set around it. -/
example (h : CofinalInaccessibles.{u}) :
    closedMemRel ⟨(∅ : ZFSet.{u}), closed_empty⟩ ⟨univOf h ∅, univOf_closed h ∅⟩ :=
  mem_univOf h ∅

/-- A small ordinal below a natural number is that natural number. -/
theorem nat_of_ordinal_lt_nat {o : Ordinal} {n : ℕ} (h : o < n) :
    ∃ k : ℕ, k < n ∧ o = k := by
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (h.trans (Ordinal.natCast_lt_omega0 n))
  refine ⟨k, ?_, hk⟩
  rw [hk] at h
  exact Nat.cast_lt.mp h

/-- Between an ordinal and that ordinal plus ω, the only ordinals are finite shifts. -/
theorem eq_add_nat_of_le_of_lt_add_omega {a b : Ordinal} (hle : a ≤ b)
    (hlt : b < a + Ordinal.omega0) : ∃ n : ℕ, b = a + n := by
  classical
  obtain ⟨d, hd, hbd⟩ :=
    (Ordinal.lt_add_iff (b := a) (c := Ordinal.omega0) Ordinal.omega0_ne_zero).mp hlt
  obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hd
  have hwitness : ∃ n : ℕ, b ≤ a + n := ⟨k, hbd⟩
  let n0 := Nat.find hwitness
  have hn0 : b ≤ a + n0 := Nat.find_spec hwitness
  have hmin : ∀ m < n0, ¬ b ≤ a + m := fun m hm => Nat.find_min hwitness hm
  cases hzero : n0 with
  | zero =>
    have hb : b ≤ a := by
      rw [hzero, Nat.cast_zero, add_zero] at hn0
      exact hn0
    refine ⟨0, ?_⟩
    rw [Nat.cast_zero, add_zero]
    exact le_antisymm hb hle
  | succ m =>
    rw [hzero] at hn0 hmin
    have hltm : a + ↑m < b := lt_of_not_ge (hmin m (Nat.lt_succ_self m))
    have hsucc : a + ↑(m + 1) ≤ b := by
      rw [Nat.cast_succ, ← add_assoc]
      exact Order.succ_le_iff.mpr hltm
    exact ⟨m + 1, le_antisymm hn0 hsucc⟩

/-- Adding a finite amount stays strictly below an ω-shift. -/
theorem add_nat_lt_add_omega {a b : Ordinal} {t : ℕ} (h : a < b + Ordinal.omega0) :
    a + t < b + Ordinal.omega0 := by
  obtain ⟨d, hd, hle⟩ :=
    (Ordinal.lt_add_iff (b := b) (c := Ordinal.omega0) Ordinal.omega0_ne_zero).mp h
  obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hd
  have hshift : a + ↑t ≤ b + ↑k + ↑t := add_le_add_left hle ↑t
  have hsum : b + ↑k + ↑t = b + ↑(k + t) := by
    rw [add_assoc, Nat.cast_add]
  exact lt_of_le_of_lt (hshift.trans (le_of_eq hsum))
    (add_lt_add_right (Ordinal.natCast_lt_omega0 (k + t)) b)

/-- A multiple of a positive natural, plus a smaller natural, reduces to that natural. -/
theorem mod_mul_add_nat {n : ℕ} (hn : n ≠ 0) (q : Ordinal) {r : ℕ} (hr : r < n) :
    ((n : Ordinal) * q + r) % (n : Ordinal) = r := by
  have hdiv : ((n : Ordinal) * q + r) / (n : Ordinal) = q := by
    rw [Ordinal.mul_add_div q (Nat.cast_ne_zero.mpr hn),
      Ordinal.div_eq_zero_of_lt (Nat.cast_lt.mpr hr), add_zero]
  have hrepr := Ordinal.div_add_mod ((n : Ordinal) * q + r) (n : Ordinal)
  rw [hdiv] at hrepr
  exact add_left_cancel hrepr

/-- Adding a natural number commutes with reduction modulo a positive natural. -/
theorem ordMod_add_nat {a : Ordinal} {n b t : ℕ} (hn : 0 < n) (ht : t < n) (hb : b < n)
    (hbEq : a % (n : Ordinal) = b) :
    (a + t) % (n : Ordinal) = ((b + t) % n : ℕ) := by
  have hrepr := Ordinal.div_add_mod a (n : Ordinal)
  set q := a / (n : Ordinal)
  have hcast : (b : Ordinal) + ↑t = (b + t : ℕ) := (Nat.cast_add b t).symm
  have hsum : a + ↑t = (n : Ordinal) * q + (b + t : ℕ) := by
    rw [← hrepr, hbEq, add_assoc, hcast]
  by_cases hlt : b + t < n
  · rw [hsum, mod_mul_add_nat hn.ne' q hlt, Nat.mod_eq_of_lt hlt]
  · have hle : n ≤ b + t := Nat.not_lt.mp hlt
    have hr : b + t - n < n := by
      have h2 : b + t < n + n := Nat.add_lt_add hb ht
      omega
    have heq : b + t = n + (b + t - n) := by omega
    have hsum' : a + ↑t = (n : Ordinal) * Order.succ q + (b + t - n : ℕ) := by
      rw [hsum]
      have hcast2 : ((b + t : ℕ) : Ordinal) = ↑(n + (b + t - n)) := congrArg Nat.cast heq
      rw [hcast2, Nat.cast_add, ← add_assoc, (Ordinal.mul_succ (n : Ordinal) q).symm]
    rw [hsum', mod_mul_add_nat hn.ne' (Order.succ q) hr]
    have hnat : (b + t) % n = b + t - n := by
      nth_rw 1 [heq]
      rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]
    rw [hnat]

/-- From any residue, a bounded step reaches any other residue. -/
theorem exists_mod_shift (n r b : ℕ) (hn : 0 < n) (hr : r < n) (hb : b < n) :
    ∃ t : ℕ, t < n ∧ (b + t) % n = r := by
  refine ⟨(n - b + r) % n, Nat.mod_lt _ hn, ?_⟩
  have hsum : b + (n - b + r) = n + r := by omega
  calc
    (b + (n - b + r) % n) % n = (b + (n - b + r)) % n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    _ = (n + r) % n := by rw [hsum]
    _ = r := by rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]

/-- A finite positive multiple divides every multiple of ω. -/
theorem omega_mul_nat_mod_zero (n i : ℕ) (hn : 0 < n) :
    (Ordinal.omega0 * i) % (n : Ordinal) = 0 := by
  have hω : (n : Ordinal) ∣ Ordinal.omega0 :=
    ⟨Ordinal.omega0, (Ordinal.natCast_mul_omega0 hn).symm⟩
  have hdiv : ∀ k : ℕ, (n : Ordinal) ∣ Ordinal.omega0 * k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (↑(k + 1) : Ordinal) = Order.succ ↑k by rw [Nat.cast_succ]; rfl, Ordinal.mul_succ]
      exact (Ordinal.dvd_add_iff ih).mpr hω
  exact Ordinal.mod_eq_zero_of_dvd (hdiv i)

/-- The least closed set is the empty set, at position zero. -/
theorem closedTypein_empty : closedTypein ⟨(∅ : ZFSet.{u}), closed_empty⟩ = 0 := by
  have hne : Ordinal.type closedMemRel ≠ 0 :=
    Ordinal.type_ne_zero_iff_nonempty.mpr ⟨⟨∅, closed_empty⟩⟩
  have h0 : (0 : Ordinal) < Ordinal.type closedMemRel := lt_of_le_of_ne bot_le hne.symm
  have hle : closedTypein ⟨(∅ : ZFSet.{u}), closed_empty⟩ ≤ 0 := by
    rw [← Ordinal.typein_enum closedMemRel h0, Ordinal.typein_le_typein]
    intro hmem
    exact ZFSet.notMem_empty _ hmem
  exact le_antisymm hle bot_le

/-- The position of the empty set is zero, and the next closed set is not at zero. -/
example : closedTypein ⟨(∅ : ZFSet.{u}), closed_empty⟩ = 0 := closedTypein_empty

example (h : CofinalInaccessibles.{u}) :
    closedTypein ⟨univOf h ∅, univOf_closed h ∅⟩ ≠ 0 := by
  intro hz
  have hlt : closedTypein ⟨(∅ : ZFSet.{u}), closed_empty⟩ <
      closedTypein ⟨univOf h ∅, univOf_closed h ∅⟩ :=
    (Ordinal.typein_lt_typein closedMemRel).mpr (mem_univOf h ∅)
  rw [closedTypein_empty, hz] at hlt
  exact lt_irrefl _ hlt

/-- Inclusion of closed sets is the ordinal order of their positions. -/
theorem closedTypein_le_of_subset {A B : {U : ZFSet.{u} // Closed U}} (h : A.1 ⊆ B.1) :
    closedTypein A ≤ closedTypein B := by
  rw [Ordinal.typein_le_typein]
  intro hBA
  exact ZFSet.mem_irrefl _ (h hBA)

/-- An earlier position is included in a later one. -/
theorem subset_of_closedTypein_le {A B : {U : ZFSet.{u} // Closed U}}
    (h : closedTypein A ≤ closedTypein B) : A.1 ⊆ B.1 := by
  have hnot : ¬ closedMemRel B A := (Ordinal.typein_le_typein closedMemRel).mp h
  rcases closed_trichotomy A.2 B.2 with hmem | heq | hmem
  · exact closed_subset_of_mem B.2 hmem
  · exact heq ▸ fun _ hz => hz
  · exact absurd hmem hnot

/-- The least closed set around a closed set is the next position. -/
theorem closedTypein_univOf (h : CofinalInaccessibles.{u})
    (A : {U : ZFSet.{u} // Closed U}) :
    closedTypein ⟨univOf h A.1, univOf_closed h A.1⟩ = closedTypein A + 1 := by
  let next : {U : ZFSet.{u} // Closed U} := ⟨univOf h A.1, univOf_closed h A.1⟩
  have hlt : closedTypein A < closedTypein next :=
    (Ordinal.typein_lt_typein closedMemRel).mpr (mem_univOf h A.1)
  have hle : closedTypein A + 1 ≤ closedTypein next := Order.succ_le_iff.mpr hlt
  refine le_antisymm ?_ hle
  by_contra hgt
  have hbetween : closedTypein A + 1 < closedTypein next := lt_of_not_ge hgt
  have htop : closedTypein A + 1 < Ordinal.type closedMemRel :=
    hbetween.trans (Ordinal.typein_lt_type closedMemRel next)
  let C := Ordinal.enum closedMemRel ⟨closedTypein A + 1, htop⟩
  have htypeC : closedTypein C = closedTypein A + 1 := Ordinal.typein_enum _ _
  have hAC : closedMemRel A C := (Ordinal.typein_lt_typein closedMemRel).mp <| by
    change closedTypein A < closedTypein C
    rw [htypeC]
    exact Order.lt_succ _
  have hCnext : closedMemRel C next := (Ordinal.typein_lt_typein closedMemRel).mp <| by
    change closedTypein C < closedTypein next
    rw [htypeC]
    exact hbetween
  have hsub : univOf h A.1 ⊆ C.1 := univOf_minimal h hAC C.2
  have hsup : C.1 ⊆ next.1 := closed_subset_of_mem next.2 hCnext
  have heq : C = next := Subtype.ext (le_antisymm hsup hsub)
  rw [heq] at htypeC
  exact ne_of_lt hbetween htypeC.symm

/-- The tower of successive least closed sets, packaged with its closure proof. -/
noncomputable def chainPack (h : CofinalInaccessibles.{u})
    (A : {U : ZFSet.{u} // Closed U}) (n : ℕ) :
    {U : ZFSet.{u} // Closed U} :=
  ⟨chainFrom h A.1 n, (stageChain_chainFrom h A.2).closed n⟩

/-- The tower starts at its first stage. -/
example (h : CofinalInaccessibles.{u}) (A : {U : ZFSet.{u} // Closed U}) :
    chainPack h A 0 = A := by
  apply Subtype.ext
  simp [chainPack, chainFrom]

/-- The second stage of the tower is not the first. -/
example (h : CofinalInaccessibles.{u}) (A : {U : ZFSet.{u} // Closed U}) :
    chainPack h A 1 ≠ A := by
  intro heq
  have hmem : A.1 ∈ (chainPack h A 1).1 := by
    simp [chainPack, chainFrom, mem_univOf]
  rw [heq] at hmem
  exact ZFSet.mem_irrefl _ hmem

/-- Positions along the successor tower are the finite shifts of the start. -/
theorem closedTypein_chainFrom (h : CofinalInaccessibles.{u})
    (A : {U : ZFSet.{u} // Closed U}) (n : ℕ) :
    closedTypein (chainPack h A n) = closedTypein A + n := by
  induction n with
  | zero =>
    have : chainPack h A 0 = A := by
      apply Subtype.ext
      simp [chainPack, chainFrom]
    simp [this]
  | succ n ih =>
    have hstep := closedTypein_univOf h (chainPack h A n)
    have heq : chainPack h A (n + 1) =
        ⟨univOf h (chainPack h A n).1, univOf_closed h _⟩ := by
      apply Subtype.ext
      simp [chainPack, chainFrom]
    rw [heq, hstep, ih, Nat.cast_succ, add_assoc]

/-- A closed set that holds every stage of a tower holds their union. -/
theorem tower_union_mem {s : ℕ → ZFSet.{u}} (chain : StageChain s) {C : ZFSet.{u}}
    (hC : Closed C) (all : ∀ n, s n ∈ C) : ZFSet.iUnion s ∈ C := by
  classical
  have omega_in : ZFSet.omega ∈ C :=
    hC.transitive (s 2) (all 2) chain.omega_mem
  let index : ZFSet.{u} → ℕ := fun x =>
    if hx : ∃ n, natCode.{u} n = x then Classical.choose hx else 0
  have index_natCode : ∀ n, index (natCode.{u} n) = n := by
    intro n
    have hx : ∃ m, natCode.{u} m = natCode.{u} n := ⟨n, rfl⟩
    simp only [index, dif_pos hx]
    exact natCode_injective (Classical.choose_spec hx)
  let image := replacement ZFSet.omega (fun x => s (index x))
  have image_mem : image ∈ C :=
    hC.replacement_mem omega_in (fun x => s (index x)) (fun x _ => all (index x))
  have union_mem : ZFSet.sUnion image ∈ C := hC.union_mem image_mem
  have eqUnion : ZFSet.iUnion s = ZFSet.sUnion image := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := ZFSet.mem_iUnion.mp hz
      refine ZFSet.mem_sUnion.mpr ⟨s n, ?_, hn⟩
      exact mem_replacement.mpr ⟨natCode.{u} n, mem_omega_iff.mpr ⟨n, rfl⟩, by
        simp [index_natCode]⟩
    · intro hz
      obtain ⟨y, hy, hz⟩ := ZFSet.mem_sUnion.mp hz
      obtain ⟨x, hx, rfl⟩ := mem_replacement.mp hy
      exact ZFSet.mem_iUnion.mpr ⟨index x, hz⟩
  rw [← eqUnion] at union_mem
  exact union_mem

/-- The least closed set above a whole successor tower. -/
theorem univOf_tower_subset {s : ℕ → ZFSet.{u}} (chain : StageChain s)
    (h : CofinalInaccessibles.{u}) {C : ZFSet.{u}} (hC : Closed C) (all : ∀ n, s n ∈ C) :
    univOf h (ZFSet.iUnion s) ⊆ C :=
  univOf_minimal h (tower_union_mem chain hC all) hC

/-- Block starts: the empty set, then the least closed set above each successor tower. -/
noncomputable def blockStart (h : CofinalInaccessibles.{u}) :
    ℕ → {U : ZFSet.{u} // Closed U}
  | 0 => ⟨∅, closed_empty⟩
  | n + 1 =>
    ⟨univOf h (ZFSet.iUnion (chainFrom h (blockStart h n).1)), univOf_closed h _⟩

/-- The first block starts at the empty set. -/
example (h : CofinalInaccessibles.{u}) : (blockStart h 0).1 = ∅ := rfl

/-- The next block does not start at the empty set. -/
example (h : CofinalInaccessibles.{u}) : (blockStart h 1).1 ≠ ∅ := by
  intro heq
  have hmem := mem_univOf h (ZFSet.iUnion (chainFrom h (blockStart h 0).1))
  have : univOf h (ZFSet.iUnion (chainFrom h (blockStart h 0).1)) = ∅ := by
    simp [blockStart] at heq
    exact heq
  rw [this] at hmem
  exact ZFSet.notMem_empty _ hmem

/-- The next block starts exactly ω positions later. -/
theorem closedTypein_blockStart_succ (h : CofinalInaccessibles.{u}) (n : ℕ) :
    closedTypein (blockStart h (n + 1)) = closedTypein (blockStart h n) + Ordinal.omega0 := by
  let A := blockStart h n
  let s := chainFrom h A.1
  have chain : StageChain s := stageChain_chainFrom h A.2
  let jump : {U : ZFSet.{u} // Closed U} :=
    ⟨univOf h (ZFSet.iUnion s), univOf_closed h _⟩
  have heq : blockStart h (n + 1) = jump := by
    apply Subtype.ext
    rfl
  rw [heq]
  have hchain : ∀ k, closedTypein (chainPack h A k) < closedTypein jump := by
    intro k
    have hmem : (chainPack h A k).1 ∈ jump.1 := by
      have hsucc : s k ∈ s (k + 1) := chain.mem_succ k
      have hunion : s (k + 1) ∈ ZFSet.iUnion s :=
        ZFSet.mem_iUnion.mpr ⟨k + 2, chain.mem_succ (k + 1)⟩
      have hjump : ZFSet.iUnion s ∈ jump.1 := mem_univOf h _
      have hmid : s (k + 1) ∈ jump.1 := jump.2.transitive _ hjump hunion
      exact jump.2.transitive _ hmid hsucc
    exact (Ordinal.typein_lt_typein closedMemRel).mpr hmem
  have hge : closedTypein A + Ordinal.omega0 ≤ closedTypein jump := by
    by_contra hlt
    have hltω : closedTypein jump < closedTypein A + Ordinal.omega0 := lt_of_not_ge hlt
    obtain ⟨d, hd, hle⟩ :=
      (Ordinal.lt_add_iff (b := closedTypein A) (c := Ordinal.omega0) Ordinal.omega0_ne_zero).mp
        hltω
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hd
    have hcontra := hchain (k + 1)
    rw [closedTypein_chainFrom] at hcontra
    have hle' : closedTypein A + (↑k + 1) ≤ closedTypein A + ↑k := by
      have h1 : closedTypein A + ↑(k + 1) ≤ closedTypein A + ↑k :=
        (le_of_lt hcontra).trans hle
      rwa [Nat.cast_succ] at h1
    have hlt' : closedTypein A + ↑k < closedTypein A + (↑k + 1) := by
      rw [← add_assoc]
      exact Order.lt_succ _
    exact not_le_of_gt hlt' hle'
  refine le_antisymm ?_ hge
  by_contra hgt
  have hbetween : closedTypein A + Ordinal.omega0 < closedTypein jump := lt_of_not_ge hgt
  have htop : closedTypein A + Ordinal.omega0 < Ordinal.type closedMemRel :=
    hbetween.trans (Ordinal.typein_lt_type closedMemRel jump)
  let C := Ordinal.enum closedMemRel ⟨closedTypein A + Ordinal.omega0, htop⟩
  have htypeC : closedTypein C = closedTypein A + Ordinal.omega0 := Ordinal.typein_enum _ _
  have hall : ∀ k, s k ∈ C.1 := by
    intro k
    have hlt : closedTypein (chainPack h A k) < closedTypein C := by
      rw [htypeC, closedTypein_chainFrom]
      exact add_lt_add_right (Ordinal.natCast_lt_omega0 k) _
    exact (Ordinal.typein_lt_typein closedMemRel).mp hlt
  have hsub : jump.1 ⊆ C.1 := univOf_tower_subset chain h C.2 hall
  have hle : closedTypein jump ≤ closedTypein C := closedTypein_le_of_subset hsub
  rw [htypeC] at hle
  exact not_lt_of_ge hle hbetween

/-- Block starts sit at the multiples of ω. -/
theorem closedTypein_blockStart (h : CofinalInaccessibles.{u}) (i : ℕ) :
    closedTypein (blockStart h i) = Ordinal.omega0 * i := by
  induction i with
  | zero => simp [blockStart, closedTypein_empty]
  | succ i ih =>
    rw [closedTypein_blockStart_succ, ih]
    rw [show (↑(i + 1) : Ordinal) = Order.succ ↑i by rw [Nat.cast_succ]; rfl, ← Ordinal.mul_succ]

/-- Later block starts are later positions. -/
theorem closedTypein_blockStart_mono (h : CofinalInaccessibles.{u}) {i k : ℕ} (hik : i ≤ k) :
    closedTypein (blockStart h i) ≤ closedTypein (blockStart h k) := by
  induction k with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hik
    simp [this]
  | succ k ih =>
    by_cases hik' : i ≤ k
    · exact le_trans (ih hik') <| by
        rw [closedTypein_blockStart_succ]
        exact le_self_add
    · have : i = k + 1 := by omega
      simp [this]

/-- A closed set strictly inside the next ω-block is a finite successor of the block start. -/
theorem eq_chainFrom_of_typein_lt_omega (h : CofinalInaccessibles.{u})
    {A B : {U : ZFSet.{u} // Closed U}} (hlo : closedTypein A ≤ closedTypein B)
    (hhi : closedTypein B < closedTypein A + Ordinal.omega0) :
    ∃ n : ℕ, B = chainPack h A n := by
  obtain ⟨n, hn⟩ := eq_add_nat_of_le_of_lt_add_omega hlo hhi
  refine ⟨n, (Ordinal.typein_inj closedMemRel).mp ?_⟩
  change closedTypein B = closedTypein (chainPack h A n)
  rw [closedTypein_chainFrom, hn]

/-! ## Finite total preorders -/

/-- How many worlds are strictly before `w`. -/
noncomputable def preorderHeight {W : Type} [Fintype W] (R : W → W → Prop) (w : W) : ℕ :=
  (Finset.univ.filter (fun v => R v w ∧ ¬ R w v)).card

/-- The bottom of a two-point chain has no strict predecessor. -/
theorem fin2_height_bot :
    preorderHeight (fun (a b : Fin 2) => a ≤ b) 0 = 0 := by
  classical
  rw [preorderHeight, Finset.card_eq_zero]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro hv
  rcases hv with ⟨hvu, hnot⟩
  have hv0 : v = 0 := by
    have : v.1 ≤ 0 := Fin.le_iff_val_le_val.mp hvu
    exact Fin.ext (Nat.le_zero.mp this)
  rw [hv0] at hnot
  exact hnot le_rfl

/-- The top of a two-point chain has one strict predecessor. -/
theorem fin2_height_top :
    preorderHeight (fun (a b : Fin 2) => a ≤ b) 1 = 1 := by
  classical
  rw [preorderHeight]
  refine Finset.card_eq_one.mpr ⟨0, ?_⟩
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hv
    rcases hv with ⟨_, hnot⟩
    have hv1 : v ≠ 1 := by
      intro heq
      exact hnot (by simp [heq])
    have hval : v.1 = 0 ∨ v.1 = 1 := by
      have := v.isLt
      omega
    rcases hval with h0 | h1
    · exact Fin.ext h0
    · exact absurd (Fin.ext h1) hv1
  · intro hv
    rw [hv]
    refine ⟨Fin.le_iff_val_le_val.mpr (by decide : (0 : ℕ) ≤ 1), ?_⟩
    intro h
    have : (1 : ℕ) ≤ 0 := Fin.le_iff_val_le_val.mp h
    omega

example : preorderHeight (fun (a b : Fin 2) => a ≤ b) 0 = 0 := fin2_height_bot

example : preorderHeight (fun (a b : Fin 2) => a ≤ b) 1 ≠ 0 := by
  rw [fin2_height_top]
  decide

/-- A strict step raises the height. -/
theorem preorderHeight_lt_of_strict {W : Type} [Fintype W] {R : W → W → Prop}
    (trans : ∀ a b c, R a b → R b c → R a c) {a b : W} (hab : R a b) (hba : ¬ R b a) :
    preorderHeight R a < preorderHeight R b := by
  classical
  let pa := Finset.univ.filter (fun v => R v a ∧ ¬ R a v)
  let pb := Finset.univ.filter (fun v => R v b ∧ ¬ R b v)
  have hsub : pa ⊆ pb := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨_, hvR, hva⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, trans v a b hvR hab, ?_⟩
    intro hvb
    exact hva (trans a b v hab hvb)
  have hmem : a ∈ pb := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hba⟩
  have hnot : a ∉ pa := by
    intro ha
    rcases Finset.mem_filter.mp ha with ⟨_, hva, hna⟩
    exact hna hva
  have hne : pa ≠ pb := by
    intro heq
    exact hnot (heq ▸ hmem)
  change pa.card < pb.card
  exact Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨hsub, hne⟩)

/-- Mutual access leaves the height unchanged. -/
theorem preorderHeight_eq_of_mutual {W : Type} [Fintype W] {R : W → W → Prop}
    (trans : ∀ a b c, R a b → R b c → R a c) {a b : W} (hab : R a b) (hba : R b a) :
    preorderHeight R a = preorderHeight R b := by
  classical
  unfold preorderHeight
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    rcases hv with ⟨hvR, hva⟩
    refine ⟨trans v a b hvR hab, ?_⟩
    intro hvb
    exact hva (trans a b v hab hvb)
  · intro hv
    rcases hv with ⟨hvR, hvb⟩
    refine ⟨trans v b a hvR hba, ?_⟩
    intro hva
    exact hvb (trans b a v hba hva)

/-- Height compares exactly as the relation does. -/
theorem preorderHeight_le_iff {W : Type} [Fintype W] {R : W → W → Prop}
    (refl : ∀ w, R w w) (trans : ∀ a b c, R a b → R b c → R a c)
    (total : ∀ a b, R a b ∨ R b a) (a b : W) :
    preorderHeight R a ≤ preorderHeight R b ↔ R a b := by
  constructor
  · intro hle
    by_cases hab : a = b
    · subst hab
      exact refl a
    · rcases total a b with hR | hR
      · exact hR
      · by_cases hba : R a b
        · exact hba
        · exact absurd hle (not_le_of_gt (preorderHeight_lt_of_strict trans hR hba))
  · intro hab
    by_cases hba : R b a
    · exact le_of_eq (preorderHeight_eq_of_mutual trans hab hba)
    · exact le_of_lt (preorderHeight_lt_of_strict trans hab hba)

/-- The rank of a height among the heights that occur. -/
noncomputable def preorderIndex {W : Type} [Fintype W] (R : W → W → Prop) (w : W) : ℕ :=
  ((Finset.univ.image (preorderHeight R)).filter (fun n => n < preorderHeight R w)).card

/-- How many distinct heights occur. -/
noncomputable def preorderCount {W : Type} [Fintype W] (R : W → W → Prop) : ℕ :=
  (Finset.univ.image (preorderHeight R)).card

/-- How many worlds have a given height-rank. -/
noncomputable def preorderCard {W : Type} [Fintype W] (R : W → W → Prop) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun w => preorderIndex R w = i)).card

example : preorderIndex (fun (a b : Fin 2) => a ≤ b) 0 = 0 := by
  classical
  rw [preorderIndex, fin2_height_bot]
  simp

example : preorderIndex (fun (a b : Fin 2) => a ≤ b) 1 ≠ 0 := by
  classical
  rw [preorderIndex, fin2_height_top]
  have h0 : (0 : ℕ) ∈ Finset.univ.image (preorderHeight (fun (a b : Fin 2) => a ≤ b)) := by
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, fin2_height_bot⟩
  have hfilter : (Finset.univ.image (preorderHeight (fun (a b : Fin 2) => a ≤ b))).filter
      (fun n => n < 1) = {0} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ⟨⟨w, hw⟩, hlt⟩
      have hw' : preorderHeight (fun (a b : Fin 2) => a ≤ b) w = n := hw
      have : w = 0 ∨ w = 1 := by
        have hv : w.1 = 0 ∨ w.1 = 1 := by
          have := w.isLt
          omega
        rcases hv with h0 | h1
        · exact Or.inl (Fin.ext h0)
        · exact Or.inr (Fin.ext h1)
      rcases this with rfl | rfl
      · rw [fin2_height_bot] at hw'
        exact hw'.symm
      · rw [fin2_height_top] at hw'
        omega
    · intro hn
      rw [hn]
      exact ⟨⟨0, fin2_height_bot⟩, by decide⟩
  rw [hfilter]
  simp

/-- A nonempty carrier has at least one height. -/
theorem preorderCount_pos {W : Type} [Fintype W] [Nonempty W] (R : W → W → Prop) :
    0 < preorderCount R := by
  classical
  obtain ⟨w⟩ := ‹Nonempty W›
  exact Finset.card_pos.mpr ⟨preorderHeight R w,
    Finset.mem_image_of_mem _ (Finset.mem_univ w)⟩

/-- Every height-rank is strictly below the number of heights. -/
theorem preorderIndex_lt_count {W : Type} [Fintype W] (R : W → W → Prop) (w : W) :
    preorderIndex R w < preorderCount R := by
  classical
  let S := Finset.univ.image (preorderHeight R)
  have hmem : preorderHeight R w ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hsub : S.filter (fun n => n < preorderHeight R w) ⊆ S.erase (preorderHeight R w) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnS, hlt⟩
    exact Finset.mem_erase.mpr ⟨ne_of_lt hlt, hnS⟩
  have hle : preorderIndex R w ≤ preorderCount R - 1 := by
    rw [preorderIndex, preorderCount]
    rw [← Finset.card_erase_of_mem hmem]
    exact Finset.card_le_card hsub
  have hpos : 0 < preorderCount R := by
    rw [preorderCount]
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  omega

/-- The two-point chain has a height. -/
example : 0 < preorderCount (fun (a b : Fin 2) => a ≤ b) :=
  preorderCount_pos _

/-- The two-point chain does not have an empty set of heights. -/
example : preorderCount (fun (a b : Fin 2) => a ≤ b) ≠ 0 :=
  ne_of_gt (preorderCount_pos _)

/-- Every rank below the number of heights is the rank of some height that occurs. -/
theorem exists_index_nat (S : Finset ℕ) (i : ℕ) (hi : i < S.card) :
    ∃ n ∈ S, (S.filter (fun k => k < n)).card = i := by
  classical
  suffices ∀ c, ∀ S : Finset ℕ, S.card = c → ∀ i, i < c →
      ∃ n ∈ S, (S.filter (fun k => k < n)).card = i by
    exact this S.card S rfl i hi
  intro c
  induction c with
  | zero =>
    intro S hcard i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ c ih =>
    intro S hcard i hi
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hcard]
      exact Nat.succ_pos _
    have hm : S.min' hne ∈ S := Finset.min'_mem _ _
    have hmin : ∀ k ∈ S, S.min' hne ≤ k := (Finset.isLeast_min' S hne).2
    have hfilter0 : S.filter (fun k => k < S.min' hne) = ∅ := by
      ext k
      constructor
      · intro hk
        rcases Finset.mem_filter.mp hk with ⟨hkS, hlt⟩
        exact absurd hlt (not_lt_of_ge (hmin k hkS))
      · intro hk
        exact absurd hk (Finset.notMem_empty _)
    by_cases hi0 : i = 0
    · refine ⟨S.min' hne, hm, ?_⟩
      rw [hfilter0, hi0]
      simp
    · have hi1 : i - 1 < c := by omega
      have hcard' : (S.erase (S.min' hne)).card = c := by
        rw [Finset.card_erase_of_mem hm, hcard]
        omega
      obtain ⟨n, hn, hidx⟩ := ih (S.erase (S.min' hne)) hcard' (i - 1) hi1
      have hnS : n ∈ S := Finset.mem_of_mem_erase hn
      have hnm : n ≠ S.min' hne := (Finset.mem_erase.mp hn).1
      have hltn : S.min' hne < n := lt_of_le_of_ne (hmin n hnS) hnm.symm
      have hfilter : S.filter (fun k => k < n) =
          insert (S.min' hne) ((S.erase (S.min' hne)).filter (fun k => k < n)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · intro ⟨hk, hlt⟩
          by_cases hkm : k = S.min' hne
          · exact Or.inl hkm
          · exact Or.inr ⟨⟨hkm, hk⟩, hlt⟩
        · intro hk
          rcases hk with rfl | ⟨⟨_, hk⟩, hlt⟩
          · exact ⟨hm, hltn⟩
          · exact ⟨hk, hlt⟩
      have hnot : S.min' hne ∉ (S.erase (S.min' hne)).filter (fun k => k < n) := by
        intro hk
        exact Finset.notMem_erase _ _ (Finset.mem_filter.mp hk).1
      refine ⟨n, hnS, ?_⟩
      rw [hfilter, Finset.card_insert_of_notMem hnot, hidx]
      omega

/-- Every rank that occurs is the rank of at least one world. -/
theorem preorderCard_pos {W : Type} [Fintype W] (R : W → W → Prop) {i : ℕ}
    (hi : i < preorderCount R) : 0 < preorderCard R i := by
  classical
  let S := Finset.univ.image (preorderHeight R)
  have hS : S.card = preorderCount R := rfl
  obtain ⟨n, hn, hidx⟩ := exists_index_nat S i (by rw [hS]; exact hi)
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hn
  have hindex : preorderIndex R w = i := by
    rw [preorderIndex, hw, hidx]
  exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hindex⟩⟩

/-- The bottom rank of the two-point chain contains a world. -/
example : 0 < preorderCard (fun (a b : Fin 2) => a ≤ b) 0 := by
  classical
  have hindex : preorderIndex (fun (a b : Fin 2) => a ≤ b) 0 = 0 := by
    rw [preorderIndex, fin2_height_bot]
    simp
  have hpos : 0 < preorderCard (fun (a b : Fin 2) => a ≤ b)
      (preorderIndex (fun (a b : Fin 2) => a ≤ b) 0) :=
    preorderCard_pos _ (preorderIndex_lt_count _ 0)
  rwa [hindex] at hpos

/-- A rank past the carrier is empty on the two-point chain. -/
example : preorderCard (fun (a b : Fin 2) => a ≤ b) 5 = 0 := by
  classical
  rw [preorderCard, Finset.card_eq_zero]
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro h
  have hlt := preorderIndex_lt_count (fun (a b : Fin 2) => a ≤ b) w
  have hle : preorderCount (fun (a b : Fin 2) => a ≤ b) ≤ 2 := by
    calc
      preorderCount (fun (a b : Fin 2) => a ≤ b) =
          (Finset.univ.image (preorderHeight (fun (a b : Fin 2) => a ≤ b))).card := rfl
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = Fintype.card (Fin 2) := Finset.card_univ
      _ = 2 := Fintype.card_fin 2
  omega

/-- A lower height has a lower rank. -/
theorem preorderIndex_lt_of_height_lt {W : Type} [Fintype W] (R : W → W → Prop) {a b : W}
    (h : preorderHeight R a < preorderHeight R b) :
    preorderIndex R a < preorderIndex R b := by
  classical
  let S := Finset.univ.image (preorderHeight R)
  have hmem : preorderHeight R a ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hsub : S.filter (fun n => n < preorderHeight R a) ⊆
      S.filter (fun n => n < preorderHeight R b) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnS, hlt⟩
    exact Finset.mem_filter.mpr ⟨hnS, lt_trans hlt h⟩
  have hnot : preorderHeight R a ∉ S.filter (fun n => n < preorderHeight R a) := by
    intro hn
    exact absurd (Finset.mem_filter.mp hn).2 (lt_irrefl _)
  have hmem' : preorderHeight R a ∈ S.filter (fun n => n < preorderHeight R b) :=
    Finset.mem_filter.mpr ⟨hmem, h⟩
  have hne : S.filter (fun n => n < preorderHeight R a) ≠
      S.filter (fun n => n < preorderHeight R b) := by
    intro heq
    exact hnot (heq ▸ hmem')
  change (S.filter (fun n => n < preorderHeight R a)).card <
    (S.filter (fun n => n < preorderHeight R b)).card
  exact Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨hsub, hne⟩)

theorem preorderIndex_eq_of_height_eq {W : Type} [Fintype W] (R : W → W → Prop) {a b : W}
    (h : preorderHeight R a = preorderHeight R b) :
    preorderIndex R a = preorderIndex R b := by
  simp [preorderIndex, h]

/-- Rank compares exactly as height does. -/
theorem preorderIndex_le_iff_height_le {W : Type} [Fintype W] (R : W → W → Prop) (a b : W) :
    preorderIndex R a ≤ preorderIndex R b ↔ preorderHeight R a ≤ preorderHeight R b := by
  constructor
  · intro h
    rcases lt_trichotomy (preorderHeight R a) (preorderHeight R b) with hlt | heq | hgt
    · exact le_of_lt hlt
    · exact le_of_eq heq
    · exact absurd h (not_le_of_gt (preorderIndex_lt_of_height_lt R hgt))
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact le_of_lt (preorderIndex_lt_of_height_lt R hlt)
    · exact le_of_eq (preorderIndex_eq_of_height_eq R heq)

/-- Rank compares exactly as the relation does. -/
theorem preorderIndex_le_iff_rel {W : Type} [Fintype W] {R : W → W → Prop}
    (refl : ∀ w, R w w) (trans : ∀ a b c, R a b → R b c → R a c)
    (total : ∀ a b, R a b ∨ R b a) (a b : W) :
    preorderIndex R a ≤ preorderIndex R b ↔ R a b := by
  rw [preorderIndex_le_iff_height_le, preorderHeight_le_iff refl trans total]

/-- The worlds of one rank are counted by that rank's cluster. -/
theorem preorderCard_eq_fintype {W : Type} [Fintype W] (R : W → W → Prop) (i : ℕ) :
    Fintype.card {w : W // preorderIndex R w = i} = preorderCard R i := by
  classical
  refine Fintype.card_of_subtype (Finset.univ.filter (fun w => preorderIndex R w = i)) ?_
  intro w
  simp

/-- The world of rank `i` numbered `r` inside that rank. -/
noncomputable def preorderPick {W : Type} [Fintype W] (R : W → W → Prop) (i r : ℕ)
    (hr : r < preorderCard R i) : W :=
  ((Fintype.equivFinOfCardEq (preorderCard_eq_fintype R i)).symm ⟨r, hr⟩).1

/-- Numbering a world and reading it back returns the world. -/
theorem preorderPick_enum {W : Type} [Fintype W] (R : W → W → Prop) (w : W) :
    preorderPick R (preorderIndex R w)
      ((Fintype.equivFinOfCardEq (preorderCard_eq_fintype R (preorderIndex R w))) ⟨w, rfl⟩).val
      ((Fintype.equivFinOfCardEq (preorderCard_eq_fintype R (preorderIndex R w))) ⟨w, rfl⟩).isLt
      = w := by
  simp [preorderPick, Equiv.symm_apply_apply]

/-- The numbered world has the rank that was requested. -/
theorem preorderPick_index {W : Type} [Fintype W] (R : W → W → Prop) (i r : ℕ)
    (hr : r < preorderCard R i) :
    preorderIndex R (preorderPick R i r hr) = i := by
  exact
    ((Fintype.equivFinOfCardEq (preorderCard_eq_fintype R i)).symm ⟨r, hr⟩).property

/-- Equal cluster indices and equal numbers inside the cluster select the same world. -/
theorem preorderPick_eq_of_eq {W : Type} [Fintype W] (R : W → W → Prop)
    {i i' r r' : ℕ} (hi : i = i') (hrr : r = r')
    (hr : r < preorderCard R i) (hr' : r' < preorderCard R i') :
    preorderPick R i r hr = preorderPick R i' r' hr' := by
  subst hi
  subst hrr
  rfl

example : preorderIndex (fun (a b : Fin 2) => a ≤ b)
    (preorderPick (fun (a b : Fin 2) => a ≤ b) 0 0 (by
      classical
      have : 0 < preorderCard (fun (a b : Fin 2) => a ≤ b) 0 := by
        have hindex0 : preorderIndex (fun (a b : Fin 2) => a ≤ b) 0 = 0 := by
          rw [preorderIndex, fin2_height_bot]
          simp
        exact Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hindex0⟩⟩
      omega)) = 0 := by
  classical
  exact preorderPick_index _ 0 0 _

example : preorderIndex (fun (a b : Fin 2) => a ≤ b)
    (preorderPick (fun (a b : Fin 2) => a ≤ b) 0 0 (by
      classical
      have hindex0 : preorderIndex (fun (a b : Fin 2) => a ≤ b) 0 = 0 := by
        rw [preorderIndex, fin2_height_bot]
        simp
      have : 0 < preorderCard (fun (a b : Fin 2) => a ≤ b) 0 :=
        Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hindex0⟩⟩
      omega)) ≠ 1 := by
  classical
  rw [preorderPick_index]
  decide

/-! ## Blocks of closed sets -/

/-- The block of a closed set among the first `m` block starts. -/
noncomputable def closedBlock (h : CofinalInaccessibles.{u}) (m : ℕ)
    (A : {U : ZFSet.{u} // Closed U}) : ℕ :=
  Nat.findGreatest (fun i => i < m ∧ closedTypein (blockStart h i) ≤ closedTypein A) (m - 1)

/-- With one block, the empty set is in block zero. -/
example (h : CofinalInaccessibles.{u}) : closedBlock h 1 ⟨∅, closed_empty⟩ = 0 := by
  classical
  simp [closedBlock, blockStart, closedTypein_empty]

/-- With one block, a later closed set is still not in block one. -/
example (h : CofinalInaccessibles.{u}) :
    closedBlock h 1 ⟨univOf h ∅, univOf_closed h ∅⟩ ≠ 1 := by
  classical
  have : closedBlock h 1 ⟨univOf h ∅, univOf_closed h ∅⟩ ≤ 0 := Nat.findGreatest_le _
  omega

theorem closedBlock_spec (h : CofinalInaccessibles.{u}) {m : ℕ} (hm : 0 < m)
    (A : {U : ZFSet.{u} // Closed U}) :
    closedBlock h m A < m ∧
      closedTypein (blockStart h (closedBlock h m A)) ≤ closedTypein A := by
  classical
  let P : ℕ → Prop := fun i => i < m ∧ closedTypein (blockStart h i) ≤ closedTypein A
  have hp : P 0 := ⟨hm, by simp [blockStart, closedTypein_empty]⟩
  have hP : P (Nat.findGreatest P (m - 1)) :=
    Nat.findGreatest_spec (m := 0) (Nat.zero_le (m - 1)) hp
  have hle : Nat.findGreatest P (m - 1) ≤ m - 1 := Nat.findGreatest_le _
  have hdef : closedBlock h m A = Nat.findGreatest P (m - 1) := rfl
  rw [hdef]
  exact ⟨lt_of_le_of_lt hle (Nat.sub_lt hm Nat.one_pos), hP.2⟩

theorem closedBlock_le_of (h : CofinalInaccessibles.{u}) {m i : ℕ}
    {A : {U : ZFSet.{u} // Closed U}}
    (hi : i ≤ m - 1) (hp : i < m ∧ closedTypein (blockStart h i) ≤ closedTypein A) :
    i ≤ closedBlock h m A := by
  classical
  exact Nat.le_findGreatest hi hp

theorem closedBlock_maximal (h : CofinalInaccessibles.{u}) (m : ℕ)
    (A : {U : ZFSet.{u} // Closed U}) {i : ℕ}
    (hi : closedBlock h m A < i) (hile : i ≤ m - 1) :
    ¬ (i < m ∧ closedTypein (blockStart h i) ≤ closedTypein A) := by
  classical
  exact (Nat.findGreatest_eq_iff.mp rfl).2.2 hi hile

/-- Inside a block that is not the last, the next block start is strictly later. -/
theorem closedBlock_lt_next (h : CofinalInaccessibles.{u}) {m : ℕ} (_hm : 0 < m)
    (A : {U : ZFSet.{u} // Closed U}) (hfin : closedBlock h m A + 1 < m) :
    closedTypein A < closedTypein (blockStart h (closedBlock h m A + 1)) := by
  classical
  have hnot := closedBlock_maximal h m A (Nat.lt_succ_self _) (Nat.le_pred_of_lt hfin)
  exact lt_of_not_ge (by
    intro hle
    exact hnot ⟨hfin, hle⟩)

/-- A position between two successive block starts belongs to the earlier block. -/
theorem closedBlock_of_range (h : CofinalInaccessibles.{u}) {m i : ℕ} (hm : 0 < m)
    (hi : i + 1 < m) (A : {U : ZFSet.{u} // Closed U})
    (hlo : closedTypein (blockStart h i) ≤ closedTypein A)
    (hhi : closedTypein A < closedTypein (blockStart h (i + 1))) :
    closedBlock h m A = i := by
  classical
  have hle : i ≤ closedBlock h m A :=
    closedBlock_le_of h (Nat.le_pred_of_lt (Nat.lt_of_succ_lt hi)) ⟨Nat.lt_of_succ_lt hi, hlo⟩
  have hge : closedBlock h m A ≤ i := by
    by_contra hgt
    have hlt : i < closedBlock h m A := lt_of_not_ge hgt
    have hspec := (closedBlock_spec h hm A).2
    have hmono := closedTypein_blockStart_mono h (Nat.succ_le_of_lt hlt)
    have : closedTypein (blockStart h (i + 1)) ≤ closedTypein A := le_trans hmono hspec
    exact not_lt_of_ge this hhi
  omega

/-- The last block is everything at or above its start. -/
theorem closedBlock_tail (h : CofinalInaccessibles.{u}) {m : ℕ} (hm : 0 < m)
    (A : {U : ZFSet.{u} // Closed U})
    (hge : closedTypein (blockStart h (m - 1)) ≤ closedTypein A) :
    closedBlock h m A = m - 1 := by
  classical
  apply le_antisymm (Nat.findGreatest_le _)
  exact closedBlock_le_of h (le_refl _) ⟨Nat.sub_lt hm Nat.one_pos, hge⟩

/-- Inclusion does not move a closed set into an earlier block. -/
theorem closedBlock_mono (h : CofinalInaccessibles.{u}) {m : ℕ}
    {A B : {U : ZFSet.{u} // Closed U}} (hsub : A.1 ⊆ B.1) :
    closedBlock h m A ≤ closedBlock h m B := by
  classical
  have hle := closedTypein_le_of_subset hsub
  exact Nat.findGreatest_mono_left (fun i hi => ⟨hi.1, hi.2.trans hle⟩) _

/-- Every block that occurs has a positive cluster once the ranks are those of a preorder. -/
theorem closedBlock_card_ne_zero {W : Type} [Fintype W] [Nonempty W] (R : W → W → Prop)
    (h : CofinalInaccessibles.{u}) (A : {U : ZFSet.{u} // Closed U}) :
    preorderCard R (closedBlock h (preorderCount R) A) ≠ 0 := by
  have hm : 0 < preorderCount R := preorderCount_pos R
  have hlt := (closedBlock_spec h hm A).1
  exact (preorderCard_pos R hlt).ne'

/-- Position in the block, reduced modulo the cluster size. -/
noncomputable def closedDial {W : Type} [Fintype W] [Nonempty W]
    (h : CofinalInaccessibles.{u}) (R : W → W → Prop)
    (A : {U : ZFSet.{u} // Closed U}) : ℕ :=
  Classical.choose (nat_of_ordinal_lt_nat
    (Ordinal.mod_lt (closedTypein A)
      (Nat.cast_ne_zero.mpr (closedBlock_card_ne_zero R h A))))

/-- The dial is the ordinal remainder, and it lies strictly below the cluster size. -/
theorem closedDial_spec {W : Type} [Fintype W] [Nonempty W]
    (h : CofinalInaccessibles.{u}) (R : W → W → Prop)
    (A : {U : ZFSet.{u} // Closed U}) :
    closedDial h R A < preorderCard R (closedBlock h (preorderCount R) A) ∧
      closedTypein A % (preorderCard R (closedBlock h (preorderCount R) A) : Ordinal) =
        closedDial h R A :=
  Classical.choose_spec (nat_of_ordinal_lt_nat
    (Ordinal.mod_lt (closedTypein A)
      (Nat.cast_ne_zero.mpr (closedBlock_card_ne_zero R h A))))

/-- On the one-world frame the dial of the empty set is zero. -/
theorem unit_dial_empty (h : CofinalInaccessibles.{u}) :
    closedDial h (fun (_ _ : Unit) => True) ⟨∅, closed_empty⟩ = 0 := by
  classical
  have hheight : preorderHeight (fun (_ _ : Unit) => True) () = 0 := by
    unfold preorderHeight
    rw [Finset.card_eq_zero]
    ext v
    simp
  have hcount : preorderCount (fun (_ _ : Unit) => True) = 1 := by
    unfold preorderCount
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext n
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨w, hw⟩
      cases w
      exact (hheight.symm.trans hw).symm
    · intro hn
      exact ⟨(), hn ▸ hheight⟩
  have hindex : preorderIndex (fun (_ _ : Unit) => True) () = 0 := by
    unfold preorderIndex
    rw [hheight, Finset.card_eq_zero]
    ext n
    simp
  have hblock : closedBlock h (preorderCount (fun (_ _ : Unit) => True)) ⟨∅, closed_empty⟩ = 0 := by
    rw [hcount]
    unfold closedBlock
    simp [blockStart, closedTypein_empty]
  have hcard : preorderCard (fun (_ _ : Unit) => True) 0 = 1 := by
    unfold preorderCard
    rw [Finset.card_eq_one]
    refine ⟨(), ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    cases w
    simp [hindex]
  have hspec := (closedDial_spec h (fun (_ _ : Unit) => True) ⟨∅, closed_empty⟩).2
  rw [hblock, hcard, closedTypein_empty, Ordinal.zero_mod] at hspec
  exact (Nat.cast_injective (Nat.cast_zero.trans hspec)).symm

example (h : CofinalInaccessibles.{u}) :
    closedDial h (fun (_ _ : Unit) => True) ⟨∅, closed_empty⟩ = 0 :=
  unit_dial_empty h

example (h : CofinalInaccessibles.{u}) :
    closedDial h (fun (_ _ : Unit) => True) ⟨∅, closed_empty⟩ ≠ 1 := by
  rw [unit_dial_empty]
  decide

/-- **Block E.** Every nonempty finite reflexive transitive total preorder is the image of a
surjective bounded morphism from the closed sets. Forth follows inclusion. Back follows the
target relation. -/
theorem closed_bounded_onto_finite_total (h : CofinalInaccessibles.{u}) {W : Type}
    (R : W → W → Prop) (finite : Finite W) (inhab : Nonempty W) (refl : ∀ w, R w w)
    (trans : ∀ a b c, R a b → R b c → R a c) (total : ∀ a b, R a b ∨ R b a) :
    ∃ f : {U : ZFSet.{u} // Closed U} → W,
      (∀ w, ∃ A, f A = w) ∧
      (∀ A B, A.1 ⊆ B.1 → R (f A) (f B)) ∧
      (∀ A w, R (f A) w → ∃ B, A.1 ⊆ B.1 ∧ f B = w) := by
  let _ : Finite W := finite
  let _ : Fintype W := Fintype.ofFinite W
  let _ : Nonempty W := inhab
  classical
  let m := preorderCount R
  have hm : 0 < m := preorderCount_pos R
  let f (A : {U : ZFSet.{u} // Closed U}) : W :=
    preorderPick R (closedBlock h m A) (closedDial h R A) (closedDial_spec h R A).1
  have hpick (A) : preorderIndex R (f A) = closedBlock h m A :=
    preorderPick_index R _ _ _
  refine ⟨f, ?_, ?_, ?_⟩
  · intro w
    let j := preorderIndex R w
    have hj : j < m := preorderIndex_lt_count R w
    let e := Fintype.equivFinOfCardEq (preorderCard_eq_fintype R j)
    let r := (e ⟨w, rfl⟩).val
    have hr : r < preorderCard R j := (e ⟨w, rfl⟩).isLt
    have hw : preorderPick R j r hr = w := by
      simp [preorderPick, e, r, Equiv.symm_apply_apply]
    have hsz : 0 < preorderCard R j := preorderCard_pos R hj
    let A := chainPack h (blockStart h j) r
    have htype : closedTypein A = closedTypein (blockStart h j) + r :=
      closedTypein_chainFrom h (blockStart h j) r
    have hmod0 : closedTypein (blockStart h j) % (preorderCard R j : Ordinal) = 0 := by
      rw [closedTypein_blockStart]
      exact omega_mul_nat_mod_zero _ j hsz
    have hmod : closedTypein A % (preorderCard R j : Ordinal) = r := by
      rw [htype]
      have hstep := ordMod_add_nat hsz hr hsz hmod0
      rwa [Nat.zero_add, Nat.mod_eq_of_lt hr] at hstep
    have hblock : closedBlock h m A = j := by
      by_cases hfin : j + 1 < m
      · have hlo : closedTypein (blockStart h j) ≤ closedTypein A := by
          rw [htype]
          exact le_self_add
        have hhi : closedTypein A < closedTypein (blockStart h (j + 1)) := by
          rw [htype, closedTypein_blockStart_succ]
          exact add_lt_add_right (Ordinal.natCast_lt_omega0 r) _
        exact closedBlock_of_range h hm hfin A hlo hhi
      · have hjlast : j = m - 1 := by omega
        have hge : closedTypein (blockStart h (m - 1)) ≤ closedTypein A := by
          rw [← hjlast, htype]
          exact le_self_add
        rw [hjlast]
        exact closedBlock_tail h hm A hge
    have hdial : closedDial h R A = r := by
      have hspec := (closedDial_spec h R A).2
      rw [hblock] at hspec
      exact Nat.cast_injective (hspec.symm.trans hmod)
    refine ⟨A, (preorderPick_eq_of_eq R hblock hdial (closedDial_spec h R A).1 hr).trans hw⟩
  · intro A B hsub
    have hblocks : closedBlock h m A ≤ closedBlock h m B := closedBlock_mono h hsub
    have hindex : preorderIndex R (f A) ≤ preorderIndex R (f B) := by
      rw [hpick A, hpick B]
      exact hblocks
    exact (preorderIndex_le_iff_rel refl trans total (f A) (f B)).mp hindex
  · intro A w hR
    have hindex : closedBlock h m A ≤ preorderIndex R w := by
      have := (preorderIndex_le_iff_rel refl trans total (f A) w).mpr hR
      rwa [hpick A] at this
    let j := preorderIndex R w
    have hj : j < m := preorderIndex_lt_count R w
    let e := Fintype.equivFinOfCardEq (preorderCard_eq_fintype R j)
    let r := (e ⟨w, rfl⟩).val
    have hr : r < preorderCard R j := (e ⟨w, rfl⟩).isLt
    have hw : preorderPick R j r hr = w := by
      simp [preorderPick, e, r, Equiv.symm_apply_apply]
    have hsz : 0 < preorderCard R j := preorderCard_pos R hj
    rcases lt_or_eq_of_le hindex with hlt | heq
    · let B := chainPack h (blockStart h j) r
      have htype : closedTypein B = closedTypein (blockStart h j) + r :=
        closedTypein_chainFrom h (blockStart h j) r
      have hmod0 : closedTypein (blockStart h j) % (preorderCard R j : Ordinal) = 0 := by
        rw [closedTypein_blockStart]
        exact omega_mul_nat_mod_zero _ j hsz
      have hmod : closedTypein B % (preorderCard R j : Ordinal) = r := by
        rw [htype]
        have hstep := ordMod_add_nat hsz hr hsz hmod0
        rwa [Nat.zero_add, Nat.mod_eq_of_lt hr] at hstep
      have hblock : closedBlock h m B = j := by
        by_cases hfin : j + 1 < m
        · exact closedBlock_of_range h hm hfin B (by
            rw [htype]; exact le_self_add) (by
            rw [htype, closedTypein_blockStart_succ]
            exact add_lt_add_right (Ordinal.natCast_lt_omega0 r) _)
        · have hjlast : j = m - 1 := by omega
          have hge : closedTypein (blockStart h (m - 1)) ≤ closedTypein B := by
            rw [← hjlast, htype]
            exact le_self_add
          rw [hjlast]
          exact closedBlock_tail h hm B hge
      have hdial : closedDial h R B = r := by
        have hspec := (closedDial_spec h R B).2
        rw [hblock] at hspec
        exact Nat.cast_injective (hspec.symm.trans hmod)
      have hbelow : closedTypein A < closedTypein (blockStart h j) := by
        have hfinA : closedBlock h m A + 1 < m := by omega
        have hnext := closedBlock_lt_next h hm A hfinA
        exact lt_of_lt_of_le hnext
          (closedTypein_blockStart_mono h (Nat.succ_le_of_lt hlt))
      refine ⟨B, subset_of_closedTypein_le (le_of_lt (hbelow.trans_le (by
        rw [htype]; exact le_self_add))), ?_⟩
      exact (preorderPick_eq_of_eq R hblock hdial (closedDial_spec h R B).1 hr).trans hw
    · let sz := preorderCard R j
      have hbnd : closedTypein A % (sz : Ordinal) < sz :=
        Ordinal.mod_lt _ (Nat.cast_ne_zero.mpr hsz.ne')
      obtain ⟨b, hb, hbEq⟩ := nat_of_ordinal_lt_nat hbnd
      obtain ⟨t, ht, htmod⟩ := exists_mod_shift sz r b hsz hr hb
      let B := chainPack h A t
      have htype : closedTypein B = closedTypein A + t := closedTypein_chainFrom h A t
      have hmod : closedTypein B % (sz : Ordinal) = r := by
        rw [htype]
        have := ordMod_add_nat hsz ht hb hbEq
        rw [htmod] at this
        exact this
      have hsub : A.1 ⊆ B.1 := subset_of_closedTypein_le (by
        rw [htype]
        exact le_self_add)
      have hblock : closedBlock h m B = j := by
        by_cases hfin : j + 1 < m
        · have hblockA : closedBlock h m A = j := heq
          have hlo : closedTypein (blockStart h j) ≤ closedTypein B := by
            have hA := (closedBlock_spec h hm A).2
            rw [hblockA] at hA
            exact le_trans hA (by rw [htype]; exact le_self_add)
          have hhi : closedTypein B < closedTypein (blockStart h (j + 1)) := by
            have hAlt : closedTypein A < closedTypein (blockStart h (j + 1)) := by
              rw [← hblockA]
              exact closedBlock_lt_next h hm A (by rw [hblockA]; exact hfin)
            have hAω : closedTypein A < closedTypein (blockStart h j) + Ordinal.omega0 := by
              rw [← closedTypein_blockStart_succ]
              exact hAlt
            rw [htype, closedTypein_blockStart_succ]
            exact add_nat_lt_add_omega hAω
          exact closedBlock_of_range h hm hfin B hlo hhi
        · have hjlast : j = m - 1 := by omega
          have hA := (closedBlock_spec h hm A).2
          have hidx : closedBlock h m A = m - 1 := by
            rw [heq]
            change j = m - 1
            exact hjlast
          rw [hidx] at hA
          have htail :=
            closedBlock_tail h hm B (le_trans hA (by rw [htype]; exact le_self_add))
          rw [← hjlast] at htail
          exact htail
      have hdial : closedDial h R B = r := by
        have hspec := (closedDial_spec h R B).2
        rw [show preorderCard R (closedBlock h m B) = sz by rw [hblock]] at hspec
        exact Nat.cast_injective (hspec.symm.trans hmod)
      refine ⟨B, hsub, ?_⟩
      exact (preorderPick_eq_of_eq R hblock hdial (closedDial_spec h R B).1 hr).trans hw

end Mettapedia.SetTheory.OpenTower.Potentialism
