import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlatPerm

/-!
# The flat fork

The executable fork of two flat codes reads a flat descriptor: the partner of
every child position (the position itself when it is unshared), and the kept
child positions in parent order.  Child positions are numbered left first.

**Theorem.**  If the flat codes store the child codes, the partner list stores
the pairing of a legal descriptor, and the mark list lists its kept marks, then
the flat fork stores the abstract fork.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

open Equiv Equiv.Perm
open GoertzelV24OrderedCutFaceReturnProfile
open PhysicalForkCode

/-! ## Numbered child positions -/

/-- The number of a child position: the left positions come first. -/
def pos (nL : ℕ) {nR : ℕ} : Fin nL ⊕ Fin nR → ℕ
  | .inl i => i
  | .inr j => nL + j

theorem pos_injective {nL nR : ℕ} : Function.Injective (pos nL (nR := nR)) := by
  rintro (i | j) (i' | j') h
  · exact congrArg Sum.inl (Fin.ext h)
  · have := i.2; simp only [pos] at h; omega
  · have := i'.2; simp only [pos] at h; omega
  · simp only [pos] at h; exact congrArg Sum.inr (Fin.ext (by omega))

theorem pos_lt {nL nR : ℕ} (a : Fin nL ⊕ Fin nR) : pos nL a < nL + nR := by
  cases a with
  | inl i => have := i.2; simp only [pos]; omega
  | inr j => have := j.2; simp only [pos]; omega

theorem pos_range {nL nR : ℕ} (x : ℕ) :
    x < nL + nR ↔ ∃ a : Fin nL ⊕ Fin nR, pos nL a = x := by
  constructor
  · intro hx
    by_cases h : x < nL
    · exact ⟨.inl ⟨x, h⟩, rfl⟩
    · exact ⟨.inr ⟨x - nL, by omega⟩, by simp only [pos]; omega⟩
  · rintro ⟨a, rfl⟩
    exact pos_lt a

theorem pos_inr_not_lt {nL nR : ℕ} (j : Fin nR) : ¬ pos nL (.inr j : Fin nL ⊕ Fin nR) < nL := by
  simp only [pos]; omega

theorem pos_inr_sub {nL nR : ℕ} (j : Fin nR) : pos nL (.inr j : Fin nL ⊕ Fin nR) - nL = j := by
  simp only [pos]; omega

/-! ## Reading the children at numbered positions -/

def twoAt (L R : FCode) (x : ℕ) : Bool := if x < L.n then getB L.two x else getB R.two (x - L.n)

def digAt (nL a b x : ℕ) : ℕ := if x < nL then dig a x else dig b (x - nL)

def bitAt (nL r s x : ℕ) : Bool := if x < nL then r.testBit x else s.testBit (x - nL)

def retAt (L R : FCode) (x : ℕ) : ℕ :=
  if x < L.n then getN L.ret x else L.n + getN R.ret (x - L.n)

/-- Two colour digits glue at a shared vertex. -/
def compatDig : Bool → Bool → ℕ → ℕ → Bool
  | false, false, x, y => x != y
  | true, false, x, y => x == y
  | false, true, x, y => x == y
  | true, true, _, _ => false

/-- The colour missing from two distinct colours. -/
def missing (x y : ℕ) : ℕ := (3 - x - y) % 3

theorem dig_lt (idx i : ℕ) : dig idx i < 3 := Nat.mod_lt _ (by norm_num)

theorem digAt_lt (nL a b x : ℕ) : digAt nL a b x < 3 := by
  unfold digAt; split <;> exact dig_lt _ _

theorem missing_lt (x y : ℕ) : missing x y < 3 := Nat.mod_lt _ (by norm_num)

theorem compatDig_iff (t u : Bool) {x y : ℕ} (hx : x < 3) (hy : y < 3) :
    compatDig t u x y = true ↔ Disjoint (colourSet t x) (colourSet u y) := by
  interval_cases x <;> interval_cases y <;> cases t <;> cases u <;> decide

theorem colourSet_missing {x y : ℕ} (hx : x < 3) (hy : y < 3) (hxy : x ≠ y) :
    colourSet true (missing x y) = colourSet false x ∪ colourSet false y := by
  interval_cases x <;> interval_cases y <;> first | decide | exact absurd rfl hxy

/-! ## The flat fork -/

def colOkF (L R : FCode) (pr : List ℕ) (a b : ℕ) : Bool :=
  (List.range (L.n + R.n)).all fun x =>
    getN pr x == x || compatDig (twoAt L R x) (twoAt L R (getN pr x)) (digAt L.n a b x)
      (digAt L.n a b (getN pr x))

def colOutF (L : FCode) (pr marks : List ℕ) (a b : ℕ) : ℕ :=
  enc3 (marks.map fun x =>
    if getN pr x == x then digAt L.n a b x
    else missing (digAt L.n a b x) (digAt L.n a b (getN pr x)))

def cutOkF (L R : FCode) (pr : List ℕ) (r s : ℕ) : Bool :=
  ((List.range (L.n + R.n)).all fun x => bitAt L.n r s (getN pr x) == bitAt L.n r s x) &&
    !(r.testBit (L.n + 2) && s.testBit (R.n + 2))

def cutOutF (L R : FCode) (marks : List ℕ) (r s : ℕ) : ℕ :=
  enc2 (marks.map (bitAt L.n r s) ++
    [r.testBit L.n || s.testBit R.n, r.testBit (L.n + 1) || s.testBit (R.n + 1),
      r.testBit (L.n + 2) || s.testBit (R.n + 2)])

/-- The merged returns after the pairing, on numbered positions. -/
def compList (L R : FCode) (pr : List ℕ) : List ℕ :=
  (List.range (L.n + R.n)).map fun x => retAt L R (getN pr x)

def keptList (N : ℕ) (marks : List ℕ) : List Bool :=
  (List.range N).map fun x => marks.contains x

/-- **The flat fork.** -/
def flatFork (L R : FCode) (pr marks : List ℕ) : FCode where
  n := marks.length
  two := marks.map fun x => if getN pr x == x then twoAt L R x else true
  ret := marks.map fun x =>
    marks.idxOf (firstRet (compList L R pr) (keptList (L.n + R.n) marks) (L.n + R.n) x)
  col := normalize (L.col.flatMap fun a => (R.col.filter (colOkF L R pr a)).map (colOutF L pr marks a))
  cut := normalize (L.cut.flatMap fun r => (R.cut.filter (cutOkF L R pr r)).map (cutOutF L R marks r))

/-! ## List lemmas -/

theorem getN_map_range {N x : ℕ} (F : ℕ → ℕ) (hx : x < N) :
    getN ((List.range N).map F) x = F x := by
  simp [getN, List.getD_eq_getElem?_getD, hx]

theorem getB_map_range {N x : ℕ} (F : ℕ → Bool) (hx : x < N) :
    getB ((List.range N).map F) x = F x := by
  simp [getB, List.getD_eq_getElem?_getD, hx]

theorem getD_map_finRange {n : ℕ} {α : Type*} (f : Fin n → α) (d : α) (k : Fin n) :
    ((List.finRange n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD]

theorem idxOf_map_finRange {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) (k : Fin n) :
    ((List.finRange n).map f).idxOf (f k) = k := by
  have hnd : ((List.finRange n).map f).Nodup := (List.nodup_finRange n).map hf
  have hlen : ((List.finRange n).map f).length = n := by simp
  have hget : ((List.finRange n).map f)[(k : ℕ)]'(by rw [hlen]; exact k.2) = f k := by simp
  rw [← hget]
  exact List.get_idxOf hnd ⟨k, by rw [hlen]; exact k.2⟩

/-! ## Correctness -/

section Marks

variable {nL nR nP : ℕ} {g : Glue nL nR nP} {marks : List ℕ}
  (hmarks : marks = (List.finRange nP).map fun k => pos nL (g.keep k))
include hmarks

theorem marks_length : marks.length = nP := by
  rw [hmarks]; simp

theorem map_marks {α : Type*} (F : ℕ → α) :
    marks.map F = (List.finRange nP).map fun k => F (pos nL (g.keep k)) := by
  rw [hmarks, List.map_map]
  rfl

theorem getB_map_marks (F : ℕ → Bool) (k : Fin nP) :
    getB (marks.map F) k = F (pos nL (g.keep k)) := by
  rw [map_marks hmarks, getB, getD_map_finRange]

theorem getN_map_marks (F : ℕ → ℕ) (k : Fin nP) :
    getN (marks.map F) k = F (pos nL (g.keep k)) := by
  rw [map_marks hmarks, getN, getD_map_finRange]

theorem mem_marks (z : Fin nL ⊕ Fin nR) : pos nL z ∈ marks ↔ z ∈ Set.range g.keep := by
  rw [hmarks, List.mem_map]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, pos_injective hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, List.mem_finRange k, rfl⟩

end Marks

section Correct

variable {nL nR nP : ℕ} {fL fR : FCode} {L : Code nL} {R : Code nR}

theorem twoAt_pos (hL : Represents fL L) (hR : Represents fR R) (z : Fin nL ⊕ Fin nR) :
    twoAt fL fR (pos nL z) = twoOf L R z := by
  cases z with
  | inl i =>
      have : (i : ℕ) < fL.n := hL.dim ▸ i.2
      simp only [twoAt, pos, this, ↓reduceIte, twoOf]
      exact hL.two i
  | inr j =>
      have h1 : ¬ pos nL (.inr j : Fin nL ⊕ Fin nR) < fL.n := hL.dim ▸ pos_inr_not_lt j
      have h2 : pos nL (.inr j : Fin nL ⊕ Fin nR) - fL.n = j := hL.dim ▸ pos_inr_sub j
      rw [twoAt, ite_eq_right h1, h2]
      exact hR.two j

theorem valOf_presOf (hL : Represents fL L) (hR : Represents fR R) (a b : ℕ)
    (z : Fin nL ⊕ Fin nR) :
    valOf (presOf nL fL.two a) (presOf nR fR.two b) z =
      colourSet (twoAt fL fR (pos nL z)) (digAt nL a b (pos nL z)) := by
  rw [twoAt_pos hL hR]
  cases z with
  | inl i =>
      simp only [valOf, presOf, twoOf, digAt, pos, i.2, ↓reduceIte]
      rw [hL.two i]
  | inr j =>
      simp only [valOf, presOf, twoOf, digAt]
      rw [ite_eq_right (pos_inr_not_lt j), pos_inr_sub, hR.two j]

theorem valOf_recOf (r s : ℕ) (z : Fin nL ⊕ Fin nR) :
    valOf (recOf nL r).bits (recOf nR s).bits z = bitAt nL r s (pos nL z) := by
  cases z with
  | inl i => simp only [valOf, recOf, bitAt, pos, i.2, ↓reduceIte]
  | inr j =>
      simp only [valOf, recOf, bitAt]
      rw [ite_eq_right (pos_inr_not_lt j), pos_inr_sub]

theorem retAt_pos (hL : Represents fL L) (hR : Represents fR R) (z : Fin nL ⊕ Fin nR) :
    retAt fL fR (pos nL z) = pos nL (merged L R z) := by
  cases z with
  | inl i =>
      have : (i : ℕ) < fL.n := hL.dim ▸ i.2
      simp only [retAt, pos, this, ↓reduceIte, merged, Equiv.sumCongr_apply, Sum.map_inl]
      exact hL.ret i
  | inr j =>
      have h1 : ¬ pos nL (.inr j : Fin nL ⊕ Fin nR) < fL.n := hL.dim ▸ pos_inr_not_lt j
      have h2 : pos nL (.inr j : Fin nL ⊕ Fin nR) - fL.n = j := hL.dim ▸ pos_inr_sub j
      rw [retAt, ite_eq_right h1, h2, hR.ret j, hL.dim]
      rfl

theorem getN_pr_eq_iff {g : Glue nL nR nP} {pr : List ℕ} (hpr : Stores (pos nL) pr g.pair)
    (z : Fin nL ⊕ Fin nR) : getN pr (pos nL z) = pos nL z ↔ g.pair z = z := by
  rw [hpr z]
  exact pos_injective.eq_iff

variable (hL : Represents fL L) (hR : Represents fR R) {g : Glue nL nR nP}
  {pr marks : List ℕ} (hpr : Stores (pos nL) pr g.pair)
include hL hR hpr

theorem colOkF_iff (a b : ℕ) :
    colOkF fL fR pr a b = true ↔
      ColourCompatible g (presOf nL fL.two a) (presOf nR fR.two b) := by
  rw [colOkF, List.all_eq_true, hL.dim, hR.dim]
  constructor
  · intro h z hz
    have := h (pos nL z) (List.mem_range.mpr (pos_lt z))
    rw [Bool.or_eq_true, beq_iff_eq, getN_pr_eq_iff hpr, hpr z] at this
    rcases this with h1 | h1
    · exact absurd h1 hz
    · rw [valOf_presOf hL hR, valOf_presOf hL hR]
      exact (compatDig_iff _ _ (digAt_lt _ _ _ _) (digAt_lt _ _ _ _)).mp h1
  · intro h x hx
    obtain ⟨z, rfl⟩ := (pos_range x).mp (List.mem_range.mp hx)
    rw [Bool.or_eq_true, beq_iff_eq, getN_pr_eq_iff hpr, hpr z]
    by_cases hz : g.pair z = z
    · exact Or.inl hz
    · right
      have := h z hz
      rw [valOf_presOf hL hR, valOf_presOf hL hR] at this
      exact (compatDig_iff _ _ (digAt_lt _ _ _ _) (digAt_lt _ _ _ _)).mpr this

omit hL hR in
theorem cutOkF_iff (hL : Represents fL L) (hR : Represents fR R) (r s : ℕ) :
    cutOkF fL fR pr r s = true ↔ CutCompatible g (recOf nL r) (recOf nR s) := by
  have hcost : ((recOf nL r).cost = true ∧ (recOf nR s).cost = true) ↔
      (r.testBit (nL + 2) = true ∧ s.testBit (nR + 2) = true) := Iff.rfl
  rw [cutOkF, Bool.and_eq_true, List.all_eq_true, hL.dim, hR.dim, Bool.not_eq_true',
    Bool.and_eq_false_iff, CutCompatible, hcost]
  constructor
  · rintro ⟨h, hc⟩
    refine ⟨fun z => ?_, ?_⟩
    · have := h (pos nL z) (List.mem_range.mpr (pos_lt z))
      rw [beq_iff_eq, hpr z] at this
      rw [valOf_recOf, valOf_recOf]
      exact this
    · rintro ⟨h1, h2⟩
      rcases hc with hc | hc <;> simp_all
  · rintro ⟨h, hc⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨z, rfl⟩ := (pos_range x).mp (List.mem_range.mp hx)
      rw [beq_iff_eq, hpr z, ← valOf_recOf, ← valOf_recOf]
      exact h z
    · by_cases h1 : r.testBit (nL + 2) = true
      · right
        by_contra h2
        exact hc ⟨h1, by simpa using h2⟩
      · left
        simpa using h1

variable (hmarks : marks = (List.finRange nP).map fun k => pos nL (g.keep k))
include hmarks

theorem flatFork_two (k : Fin nP) :
    getB (flatFork fL fR pr marks).two k = (fork L R g).two k := by
  change getB (marks.map _) k = _
  rw [getB_map_marks hmarks]
  simp only [fork]
  by_cases h : g.pair (g.keep k) = g.keep k
  · have h' : getN pr (pos nL (g.keep k)) = pos nL (g.keep k) := (getN_pr_eq_iff hpr _).mpr h
    rw [ite_eq_left (beq_iff_eq.mpr h'), ite_eq_left h, twoAt_pos hL hR]
  · have h' : ¬ (getN pr (pos nL (g.keep k)) == pos nL (g.keep k)) = true := by
      rw [beq_iff_eq, getN_pr_eq_iff hpr]; exact h
    rw [ite_eq_right h', ite_eq_right h]

theorem flatFork_ret (k : Fin nP) :
    getN (flatFork fL fR pr marks).ret k = (fork L R g).ret k := by
  change getN (marks.map _) k = _
  rw [getN_map_marks hmarks, hL.dim, hR.dim]
  have hst : Stores (pos nL) (compList fL fR pr) (merged L R * g.pair) := by
    intro z
    rw [compList, hL.dim, hR.dim, getN_map_range _ (pos_lt z), hpr z, retAt_pos hL hR]
    rfl
  have hk : ∀ z, getB (keptList (nL + nR) marks) (pos nL z) = true ↔ z ∈ Set.range g.keep := by
    intro z
    rw [keptList, getB_map_range _ (pos_lt z), List.contains_iff_mem]
    exact mem_marks hmarks z
  have hfuel : Fintype.card (Fin nL ⊕ Fin nR) ≤ nL + nR := by simp
  rw [firstRet_stores hst hk hfuel ⟨g.keep k, Set.mem_range_self k⟩, ← keep_fork_ret, hmarks,
    idxOf_map_finRange (fun k => pos nL (g.keep k)) (pos_injective.comp g.keep.injective)]

theorem colOutF_spec (hg : Legal L R g) (a b : ℕ) (hok : colOkF fL fR pr a b = true) :
    presOf nP (flatFork fL fR pr marks).two (colOutF fL pr marks a b) =
      colourOut g (presOf nL fL.two a) (presOf nR fR.two b) := by
  have hcompat := (colOkF_iff hL hR hpr a b).mp hok
  funext k
  have hD : ∀ d ∈ marks.map (fun x => if getN pr x == x then digAt fL.n a b x
      else missing (digAt fL.n a b x) (digAt fL.n a b (getN pr x))), d < 3 := by
    intro d hd
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
    split
    · exact digAt_lt _ _ _ _
    · exact missing_lt _ _
  have htwo := flatFork_two hL hR hpr hmarks k
  simp only [presOf, colOutF]
  rw [dig_enc3 _ hD, htwo]
  change colourSet _ (getN (marks.map _) k) = _
  rw [getN_map_marks hmarks, hL.dim]
  simp only [colourOut, fork]
  by_cases h : g.pair (g.keep k) = g.keep k
  · rw [ite_eq_left (beq_iff_eq.mpr ((getN_pr_eq_iff hpr _).mpr h)), ite_eq_left h, h,
      Finset.union_self, valOf_presOf hL hR, twoAt_pos hL hR]
  · have hopen : OpenAt L R g (g.keep k) := by
      by_contra hno
      exact hg.keep_closed _ h hno (Set.mem_range_self k)
    have hne : ¬ (getN pr (pos nL (g.keep k)) == pos nL (g.keep k)) = true := by
      rw [beq_iff_eq, getN_pr_eq_iff hpr]; exact h
    rw [ite_eq_right hne, ite_eq_right h, valOf_presOf hL hR, valOf_presOf hL hR, twoAt_pos hL hR,
      twoAt_pos hL hR, hopen.1, hopen.2, ← hpr]
    have hdis := hcompat _ h
    rw [valOf_presOf hL hR, valOf_presOf hL hR, twoAt_pos hL hR, twoAt_pos hL hR, hopen.1,
      hopen.2, ← hpr, ← compatDig_iff _ _ (digAt_lt _ _ _ _) (digAt_lt _ _ _ _)] at hdis
    have hxy : digAt nL a b (pos nL (g.keep k)) ≠ digAt nL a b (getN pr (pos nL (g.keep k))) := by
      simpa [compatDig] using hdis
    exact colourSet_missing (digAt_lt _ _ _ _) (digAt_lt _ _ _ _) hxy

omit hpr in
theorem cutOutF_spec (r s : ℕ) :
    recOf nP (cutOutF fL fR marks r s) = PhysicalForkCode.cutOut g (recOf nL r) (recOf nR s) := by
  have hlen : (marks.map (bitAt fL.n r s)).length = nP := by
    rw [List.length_map, marks_length hmarks]
  simp only [recOf, PhysicalForkCode.cutOut, cutOutF]
  congr 1
  · funext k
    rw [testBit_enc2, List.getD_append _ _ _ _ (by rw [hlen]; exact k.2), ← getB,
      getB_map_marks hmarks, hL.dim, ← valOf_recOf]
    rfl
  · rw [testBit_enc2, List.getD_append_right _ _ _ _ (by rw [hlen])]
    simp [marks_length hmarks, hL.dim, hR.dim]
  · rw [testBit_enc2, List.getD_append_right _ _ _ _ (by rw [hlen]; omega)]
    simp [marks_length hmarks, hL.dim, hR.dim]
  · rw [testBit_enc2, List.getD_append_right _ _ _ _ (by rw [hlen]; omega)]
    simp [marks_length hmarks, hL.dim, hR.dim]

/-- **The flat fork stores the abstract fork.** -/
theorem represents_flatFork (hg : Legal L R g) :
    Represents (flatFork fL fR pr marks) (fork L R g) where
  dim := marks_length hmarks
  two := flatFork_two hL hR hpr hmarks
  ret := flatFork_ret hL hR hpr hmarks
  colour := by
    change ((normalize _).map _).toFinset = _
    rw [toFinset_map_normalize]
    ext y
    simp only [List.mem_toFinset, List.mem_map, List.mem_flatMap, List.mem_filter, fork,
      Finset.mem_image, Finset.mem_filter, Finset.mem_product, ← hL.colour, ← hR.colour]
    constructor
    · rintro ⟨c, ⟨a, ha, ⟨b, ⟨hb, hok⟩, rfl⟩⟩, rfl⟩
      exact ⟨⟨presOf nL fL.two a, presOf nR fR.two b⟩,
        ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, (colOkF_iff hL hR hpr a b).mp hok⟩,
        (colOutF_spec hL hR hpr hmarks hg a b hok).symm⟩
    · rintro ⟨⟨bL, bR⟩, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hc⟩, rfl⟩
      have hok := (colOkF_iff hL hR hpr a b).mpr hc
      exact ⟨colOutF fL pr marks a b, ⟨a, ha, ⟨b, ⟨hb, hok⟩, rfl⟩⟩,
        colOutF_spec hL hR hpr hmarks hg a b hok⟩
  cut := by
    change ((normalize _).map _).toFinset = _
    rw [toFinset_map_normalize]
    ext y
    simp only [List.mem_toFinset, List.mem_map, List.mem_flatMap, List.mem_filter, fork,
      Finset.mem_image, Finset.mem_filter, Finset.mem_product, ← hL.cut, ← hR.cut]
    constructor
    · rintro ⟨c, ⟨r, hr, ⟨s, ⟨hs, hok⟩, rfl⟩⟩, rfl⟩
      exact ⟨⟨recOf nL r, recOf nR s⟩,
        ⟨⟨⟨r, hr, rfl⟩, ⟨s, hs, rfl⟩⟩, (cutOkF_iff hpr hL hR r s).mp hok⟩,
        (cutOutF_spec hL hR hmarks r s).symm⟩
    · rintro ⟨⟨rL, rR⟩, ⟨⟨⟨r, hr, rfl⟩, ⟨s, hs, rfl⟩⟩, hc⟩, rfl⟩
      have hok := (cutOkF_iff hpr hL hR r s).mpr hc
      exact ⟨cutOutF fL fR marks r s, ⟨r, hr, ⟨s, ⟨hs, hok⟩, rfl⟩⟩,
        cutOutF_spec hL hR hmarks r s⟩

end Correct

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
