import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeTransport

/-!
# Flat codes: an executable representation of the fork code

`PhysicalForkCode.Code n` stores finite sets of functions, which is the right
object for proofs and the wrong one for kernel evaluation.  A flat code stores
the same data as lists of natural numbers: a colour presentation is a base-three
word (at a position with one shore edge the digit is the colour, at a position
with two it is the missing colour), a cut record is the binary word of its bits
followed by its three flags, and the face return is the list of its values.

`Represents f c` says that the flat code `f` stores exactly the code `c`.  This
file proves the basic facts: digit and bit decoding, the leaf, the root test,
and renaming of positions.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

open Equiv Equiv.Perm
open PhysicalForkCode

/-! ## Flat data -/

structure FCode where
  n : ℕ
  two : List Bool
  ret : List ℕ
  col : List ℕ
  cut : List ℕ
  deriving DecidableEq

def getB (l : List Bool) (i : ℕ) : Bool := l.getD i false

def getN (l : List ℕ) (i : ℕ) : ℕ := l.getD i 0

/-- The `i`-th base-three digit. -/
def dig (idx i : ℕ) : ℕ := idx / 3 ^ i % 3

/-- A base-three word, least significant digit first. -/
def enc3 : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 3 * enc3 ds

/-- A binary word, least significant bit first. -/
def enc2 : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * enc2 bs

/-- Insertion into a strictly increasing list. -/
def insertSorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertSorted x ys

/-- Sort and remove duplicates. -/
def normalize (l : List ℕ) : List ℕ := l.foldr insertSorted []

/-! ## Decoding -/

def fin3 (d : ℕ) : Fin 3 := ⟨d % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The colours carried at a position: one colour, or the complement of one. -/
def colourSet (two : Bool) (d : ℕ) : Finset (Fin 3) :=
  if two then Finset.univ.erase (fin3 d) else {fin3 d}

def presOf (n : ℕ) (two : List Bool) (idx : ℕ) : Fin n → Finset (Fin 3) :=
  fun i => colourSet (getB two i) (dig idx i)

def recOf (n : ℕ) (r : ℕ) : CutRecord n :=
  ⟨fun i => r.testBit i, r.testBit n, r.testBit (n + 1), r.testBit (n + 2)⟩

/-- The flat code `f` stores exactly the code `c`. -/
structure Represents {n : ℕ} (f : FCode) (c : Code n) : Prop where
  dim : f.n = n
  two : ∀ i : Fin n, getB f.two i = c.two i
  ret : ∀ i : Fin n, getN f.ret i = c.ret i
  colour : (f.col.map (presOf n f.two)).toFinset = c.colour
  cut : (f.cut.map (recOf n)).toFinset = c.cut

/-! ## Encoding lemmas -/

theorem dig_enc3 (ds : List ℕ) (h : ∀ d ∈ ds, d < 3) (i : ℕ) :
    dig (enc3 ds) i = ds.getD i 0 := by
  induction ds generalizing i with
  | nil => simp [dig, enc3]
  | cons d ds ih =>
      have hd : d < 3 := h d (by simp)
      have ht : ∀ d ∈ ds, d < 3 := fun x hx => h x (by simp [hx])
      cases i with
      | zero =>
          simp only [dig, enc3, pow_zero, Nat.div_one, List.getD_cons_zero]
          omega
      | succ i =>
          have := ih ht i
          simp only [dig, enc3, List.getD_cons_succ] at this ⊢
          have h3 : (d + 3 * enc3 ds) / 3 = enc3 ds := by omega
          rw [← this, pow_succ', ← Nat.div_div_eq_div_mul, h3]

theorem testBit_enc2 (bs : List Bool) (i : ℕ) : (enc2 bs).testBit i = bs.getD i false := by
  induction bs generalizing i with
  | nil => simp [enc2]
  | cons b bs ih =>
      cases i with
      | zero =>
          cases b <;> simp [enc2, Nat.testBit_zero]
      | succ i =>
          rw [List.getD_cons_succ, ← ih i, enc2, Nat.testBit_succ]
          congr 1
          cases b
          · simp
          · simp; omega

theorem mem_insertSorted (x y : ℕ) (l : List ℕ) : y ∈ insertSorted x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons z zs ih =>
      simp only [insertSorted]
      split_ifs with h1 h2
      · simp
      · subst h2; simp only [List.mem_cons]; tauto
      · simp only [List.mem_cons, ih]; tauto

theorem mem_normalize (y : ℕ) (l : List ℕ) : y ∈ normalize l ↔ y ∈ l := by
  induction l with
  | nil => simp [normalize]
  | cons x xs ih =>
      simp only [normalize, List.foldr_cons] at ih ⊢
      rw [mem_insertSorted, ih, List.mem_cons]

theorem toFinset_map_normalize {α : Type*} [DecidableEq α] (φ : ℕ → α) (l : List ℕ) :
    ((normalize l).map φ).toFinset = (l.map φ).toFinset := by
  ext a
  simp only [List.mem_toFinset, List.mem_map, mem_normalize]

/-! ## The leaf and the root -/

/-- The flat leaf code. -/
def leafF : FCode := ⟨2, [false, false], [1, 0], [0, 4, 8], [7, 8, 29, 30]⟩

theorem represents_leaf : Represents leafF leafCode := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · decide
  · have e7 : recOf 2 7 = ⟨![true, true], true, false, false⟩ := by
      ext1
      · funext i; fin_cases i <;> rfl
      all_goals rfl
    have e8 : recOf 2 8 = ⟨![false, false], false, true, false⟩ := by
      ext1
      · funext i; fin_cases i <;> rfl
      all_goals rfl
    have e29 : recOf 2 29 = ⟨![true, false], true, true, true⟩ := by
      ext1
      · funext i; fin_cases i <;> rfl
      all_goals rfl
    have e30 : recOf 2 30 = ⟨![false, true], true, true, true⟩ := by
      ext1
      · funext i; fin_cases i <;> rfl
      all_goals rfl
    simp only [leafF, List.map_cons, List.map_nil, e7, e8, e29, e30, leafCode]
    ext r
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert,
      Finset.mem_singleton]
    tauto

/-- The flat root test: no colouring, and no record splitting the vertices. -/
def rejectingF (q : FCode) : Bool :=
  q.col.isEmpty && !(q.cut.any fun r => r.testBit 0 && r.testBit 1)

theorem rejecting_of_represents {f : FCode} {c : Code 0} (h : Represents f c) :
    rejectingF f = true ↔ Rejecting c := by
  have hcolour : c.colour = ∅ ↔ f.col = [] := by
    rw [← h.colour, List.toFinset_eq_empty_iff, List.map_eq_nil_iff]
  have hcut : HasSmallCut c ↔ ∃ r ∈ f.cut, r.testBit 0 = true ∧ r.testBit 1 = true := by
    rw [HasSmallCut, ← h.cut]
    constructor
    · rintro ⟨r, hr, hin, hout⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
      exact ⟨x, hx, hin, hout⟩
    · rintro ⟨x, hx, hin, hout⟩
      exact ⟨recOf 0 x, List.mem_toFinset.mpr (List.mem_map_of_mem hx), hin, hout⟩
  rw [Rejecting, hcolour, hcut]
  simp only [rejectingF, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true', List.any_eq_false,
    Bool.and_eq_true, not_and, not_exists]

/-! ## Renaming positions -/

/-- Rename the positions of a flat code: position `k` reads position `σ[k]`. -/
def relabelF (c : FCode) (σ : List ℕ) : FCode :=
  ⟨c.n, σ.map (getB c.two), σ.map (fun i => σ.idxOf (getN c.ret i)),
   normalize (c.col.map fun idx => enc3 (σ.map (dig idx))),
   normalize (c.cut.map fun r =>
     enc2 (σ.map (fun i => r.testBit i) ++ [r.testBit c.n, r.testBit (c.n + 1), r.testBit (c.n + 2)]))⟩

/-- The position list of a renaming. -/
def permList {n : ℕ} (τ : Fin n ≃ Fin n) : List ℕ := (List.finRange n).map fun i => (τ i : ℕ)

theorem permList_getD {n : ℕ} (τ : Fin n ≃ Fin n) (i : Fin n) :
    (permList τ).getD i 0 = τ i := by
  simp [permList, List.getD_eq_getElem?_getD]

theorem permList_length {n : ℕ} (τ : Fin n ≃ Fin n) : (permList τ).length = n := by
  simp [permList]

theorem permList_idxOf {n : ℕ} (τ : Fin n ≃ Fin n) (i : Fin n) :
    (permList τ).idxOf (i : ℕ) = τ.symm i := by
  have hnd : (permList τ).Nodup := by
    rw [permList, List.nodup_map_iff_inj_on (List.nodup_finRange n)]
    intro a _ b _ h
    exact τ.injective (Fin.ext h)
  have hget : (permList τ)[(τ.symm i : ℕ)]'(by rw [permList_length]; exact (τ.symm i).2) = i := by
    simp [permList]
  rw [← hget]
  exact List.get_idxOf hnd ⟨τ.symm i, by rw [permList_length]; exact (τ.symm i).2⟩

theorem digits_lt (idx : ℕ) (σ : List ℕ) : ∀ d ∈ σ.map (dig idx), d < 3 := by
  intro d hd
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hd
  exact Nat.mod_lt _ (by norm_num)

theorem permList_map_getD {n : ℕ} {α : Type*} (τ : Fin n ≃ Fin n) (φ : ℕ → α) (d : α)
    (i : Fin n) : ((permList τ).map φ).getD i d = φ (τ i) := by
  simp [permList, List.getD_eq_getElem?_getD]

/-- **Flat renaming represents renaming.** -/
theorem represents_relabel {n : ℕ} {f : FCode} {c : Code n} (h : Represents f c)
    (τ : Fin n ≃ Fin n) : Represents (relabelF f (permList τ)) (c.relabel τ) := by
  refine ⟨h.dim, ?_, ?_, ?_, ?_⟩
  · intro i
    change ((permList τ).map (getB f.two)).getD i false = c.two (τ i)
    rw [permList_map_getD]
    exact h.two (τ i)
  · intro i
    change ((permList τ).map (fun i => (permList τ).idxOf (getN f.ret i))).getD i 0 =
      τ.symm (c.ret (τ i))
    rw [permList_map_getD, h.ret (τ i), permList_idxOf]
  · simp only [Code.relabel]
    rw [← h.colour]
    simp only [relabelF]
    rw [toFinset_map_normalize, List.map_map]
    ext b
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨idx, hidx, rfl⟩
      refine ⟨presOf n f.two idx, ⟨idx, hidx, rfl⟩, ?_⟩
      funext i
      simp only [Function.comp_apply, presOf, getB]
      rw [dig_enc3 _ (digits_lt idx _), permList_map_getD, permList_map_getD]
      rfl
    · rintro ⟨_, ⟨idx, hidx, rfl⟩, rfl⟩
      refine ⟨idx, hidx, ?_⟩
      funext i
      simp only [Function.comp_apply, presOf, getB]
      rw [dig_enc3 _ (digits_lt idx _), permList_map_getD, permList_map_getD]
      rfl
  · simp only [Code.relabel]
    rw [← h.cut]
    simp only [relabelF]
    rw [toFinset_map_normalize, List.map_map]
    suffices hrec : ∀ r, recOf n (enc2 (((permList τ).map fun i => r.testBit i) ++
        [r.testBit f.n, r.testBit (f.n + 1), r.testBit (f.n + 2)])) =
        CutRecord.relabel τ (recOf n r) by
      ext x
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨recOf n r, ⟨r, hr, rfl⟩, (hrec r).symm⟩
      · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
        exact ⟨r, hr, hrec r⟩
    intro r
    have hlen : ((permList τ).map fun i => r.testBit i).length = n := by
      rw [List.length_map, permList_length]
    simp only [recOf, CutRecord.relabel, h.dim]
    congr 1
    · funext i
      rw [testBit_enc2, List.getD_append _ _ _ _ (by rw [hlen]; exact i.2), permList_map_getD]
      rfl
    · rw [testBit_enc2, List.getD_append_right _ _ _ _ (by rw [hlen])]
      simp [hlen]
    · rw [testBit_enc2, List.getD_append_right _ _ _ _ (by rw [hlen]; omega)]
      simp [hlen]
    · rw [testBit_enc2, List.getD_append_right _ _ _ _ (by rw [hlen]; omega)]
      simp [hlen]

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
