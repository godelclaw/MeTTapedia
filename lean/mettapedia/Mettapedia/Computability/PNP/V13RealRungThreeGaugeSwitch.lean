import Mettapedia.Computability.PNP.V13RealRungOneQRowBound

/-!
# PNP v13 real rung three: gauge-compensated switching

This file starts the rung-three switching layer for the admissible linear
family.  The main results here are proven-shape finite counting statements:
full-rhs observers, and static column sketches plus full rhs, are bounded by
explicit subcube corner terms.  The row-sketch full-rhs theorem and the
low-degree public-bit correlation endpoint remain outside this file.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

abbrev V13RealLinearUniformWorld (m : Nat) :=
  V13F2LinearEquiv m × F2Vec m

def v13RealLinearUniformRhs {m : Nat}
    (omega : V13RealLinearUniformWorld m) : F2Vec m :=
  omega.1.toEquiv omega.2

theorem v13RealLinear_f2AddVec_singleBit_cancel {m : Nat}
    (x : F2Vec m) (i : Fin m) :
    f2AddVec (f2AddVec x (v13RealLinearSingleBit i))
      (v13RealLinearSingleBit i) = x := by
  funext r
  by_cases hr : r = i
  · subst r
    simp [f2AddVec, v13RealLinearSingleBit, f2_add_right_self]
  · simp [f2AddVec, v13RealLinearSingleBit, hr]

theorem v13RealLinear_f2AddVec_singleBit_inj {m : Nat}
    {x y : F2Vec m} {i : Fin m}
    (h :
      f2AddVec x (v13RealLinearSingleBit i) =
        f2AddVec y (v13RealLinearSingleBit i)) :
    x = y := by
  rw [← v13RealLinear_f2AddVec_singleBit_cancel x i,
    ← v13RealLinear_f2AddVec_singleBit_cancel y i, h]

def v13RealLinearTransvection {m : Nat} (i r : Fin m)
    (hri : r ≠ i) : V13F2LinearEquiv m where
  toEquiv :=
    { toFun := fun z c => if c = i then z i + z r else z c
      invFun := fun z c => if c = i then z i + z r else z c
      left_inv := by
        intro z
        funext c
        by_cases hc : c = i
        · subst c
          simp [hri, f2_add_right_self]
        · simp [hc]
      right_inv := by
        intro z
        funext c
        by_cases hc : c = i
        · subst c
          simp [hri, f2_add_right_self]
        · simp [hc] }
  map_add := by
    intro x y
    funext c
    by_cases hc : c = i
    · subst c
      simp [f2AddVec]
      ring
    · simp [f2AddVec, hc]
  map_zero := by
    funext c
    by_cases hc : c = i
    · subst c
      simp [f2ZeroVec]
    · simp [f2ZeroVec, hc]

theorem v13RealLinearTransvection_apply_of_ne {m : Nat}
    {i r : Fin m} (hri : r ≠ i) {c : Fin m} (hc : c ≠ i)
    (z : F2Vec m) :
    (v13RealLinearTransvection i r hri).toEquiv z c = z c := by
  simp [v13RealLinearTransvection, hc]

theorem v13RealLinearTransvection_apply_pivot {m : Nat}
    {i r : Fin m} (hri : r ≠ i) (z : F2Vec m) :
    (v13RealLinearTransvection i r hri).toEquiv z i =
      z i + z r := by
  simp [v13RealLinearTransvection]

theorem v13RealLinearTransvection_singleBit_fixed {m : Nat}
    {i r c : Fin m} (hri : r ≠ i) (hrc : r ≠ c) :
    (v13RealLinearTransvection i r hri).toEquiv
        (v13RealLinearSingleBit c) =
      v13RealLinearSingleBit c := by
  funext row
  by_cases hrow : row = i
  · subst row
    simp [v13RealLinearTransvection, v13RealLinearSingleBit, hrc]
  · simp [v13RealLinearTransvection, v13RealLinearSingleBit, hrow]

theorem v13RealLinearTransvection_apply_eq_add_singleBit_of_source_one
    {m : Nat} {i r : Fin m} (hri : r ≠ i) {z : F2Vec m}
    (hzr : z r = 1) :
    (v13RealLinearTransvection i r hri).toEquiv z =
      f2AddVec z (v13RealLinearSingleBit i) := by
  funext row
  by_cases hrow : row = i
  · subst row
    simp [v13RealLinearTransvection, f2AddVec, v13RealLinearSingleBit,
      hzr]
  · simp [v13RealLinearTransvection, f2AddVec, v13RealLinearSingleBit,
      hrow]

theorem v13RealLinearTransvection_apply_symm_apply_of_eq {m : Nat}
    {i r0 r1 : Fin m} (hr : r0 = r1)
    (h0 : r0 ≠ i) (h1 : r1 ≠ i) (z : F2Vec m) :
    (v13RealLinearTransvection i r1 h1).toEquiv
        ((v13RealLinearTransvection i r0 h0).toEquiv.symm z) = z := by
  subst r1
  funext c
  by_cases hc : c = i
  · subst c
    simp [v13RealLinearTransvection, h0, f2_add_right_self]
  · simp [v13RealLinearTransvection, hc]

abbrev V13RealLinearSupportedOn {m : Nat} (support : Finset (Fin m)) :=
  {x : F2Vec m // ∀ r : Fin m, r ∉ support → x r = 0}

noncomputable instance {m : Nat} (support : Finset (Fin m)) :
    Fintype (V13RealLinearSupportedOn support) := by
  classical
  unfold V13RealLinearSupportedOn
  infer_instance

noncomputable def v13RealLinearSupportedOnRestrictionEmbedding
    {m : Nat} (support : Finset (Fin m)) :
    V13RealLinearSupportedOn support ↪
      ({r : Fin m // r ∈ support} → ZMod 2) where
  toFun x := fun r => x.val r.val
  inj' := by
    intro x y h
    apply Subtype.ext
    funext r
    by_cases hr : r ∈ support
    · have hpoint := congrFun h ⟨r, hr⟩
      exact hpoint
    · rw [x.property r hr, y.property r hr]

theorem v13RealLinearSupportedOn_card_le {m : Nat}
    (support : Finset (Fin m)) :
    Fintype.card (V13RealLinearSupportedOn support) ≤
      2 ^ support.card := by
  classical
  have hle :
      Fintype.card (V13RealLinearSupportedOn support) ≤
        Fintype.card ({r : Fin m // r ∈ support} → ZMod 2) :=
    Fintype.card_le_of_embedding
      (v13RealLinearSupportedOnRestrictionEmbedding support)
  have hfun :
      Fintype.card ({r : Fin m // r ∈ support} → ZMod 2) =
        2 ^ support.card := by
    rw [Fintype.card_fun]
    have hzmod : Fintype.card (ZMod 2) = 2 := by
      norm_num
    rw [hzmod]
    have hsub :
        Fintype.card {r : Fin m // r ∈ support} = support.card :=
      Fintype.card_of_subtype support (fun r : Fin m => Iff.rfl)
    rw [hsub]
  exact hle.trans_eq hfun

structure V13RealLinearRhsOnlyObserver (m : Nat) where
  decide : F2Vec m → ZMod 2

structure V13RealLinearColumnSketchRhsObserver (m j : Nat) where
  cols : Finset (Fin m)
  decide : ({c : Fin m // c ∈ cols} → F2Vec m) → F2Vec m → ZMod 2
  readBudget : cols.card ≤ j

def V13RealLinearRhsOnlyObserver.toColumnSketch {m : Nat}
    (observer : V13RealLinearRhsOnlyObserver m) :
    V13RealLinearColumnSketchRhsObserver m 0 where
  cols := ∅
  decide := fun _ rhs => observer.decide rhs
  readBudget := by simp

def v13RealLinearColumnSketch {m : Nat}
    (cols : Finset (Fin m)) (A : V13F2LinearEquiv m) :
    ({c : Fin m // c ∈ cols} → F2Vec m) :=
  fun c => A.toEquiv (v13RealLinearSingleBit c.val)

def v13RealLinearColumnSketchRhsDecision {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (omega : V13RealLinearUniformWorld m) : ZMod 2 :=
  observer.decide (v13RealLinearColumnSketch observer.cols omega.1)
    (v13RealLinearUniformRhs omega)

def V13RealLinearColumnSketchRhsCorrect {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :=
  {omega : V13RealLinearUniformWorld m //
    v13RealLinearColumnSketchRhsDecision observer omega = omega.2 i}

def V13RealLinearColumnSketchRhsIncorrect {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :=
  {omega : V13RealLinearUniformWorld m //
    v13RealLinearColumnSketchRhsDecision observer omega ≠ omega.2 i}

noncomputable instance {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype (V13RealLinearColumnSketchRhsCorrect observer i) := by
  classical
  unfold V13RealLinearColumnSketchRhsCorrect
  infer_instance

noncomputable instance {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype (V13RealLinearColumnSketchRhsIncorrect observer i) := by
  classical
  unfold V13RealLinearColumnSketchRhsIncorrect
  infer_instance

def v13RealLinearGaugeSwitchCandidates {m : Nat}
    (cols : Finset (Fin m)) (i : Fin m) (y : F2Vec m) :
    Finset (Fin m) :=
  Finset.univ.filter (fun r => r ∉ insert i cols ∧ y r = 1)

def V13RealLinearColumnSketchRhsCorner {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :=
  {omega : V13RealLinearUniformWorld m //
    v13RealLinearGaugeSwitchCandidates observer.cols i
        (f2AddVec omega.2 (v13RealLinearSingleBit i)) = ∅}

def V13RealLinearColumnSketchRhsOffCornerCorrect {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :=
  {omega : V13RealLinearUniformWorld m //
    v13RealLinearColumnSketchRhsDecision observer omega = omega.2 i ∧
      v13RealLinearGaugeSwitchCandidates observer.cols i
        (f2AddVec omega.2 (v13RealLinearSingleBit i)) ≠ ∅}

noncomputable instance {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype (V13RealLinearColumnSketchRhsCorner observer i) := by
  classical
  unfold V13RealLinearColumnSketchRhsCorner
  infer_instance

noncomputable instance {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype (V13RealLinearColumnSketchRhsOffCornerCorrect observer i) := by
  classical
  unfold V13RealLinearColumnSketchRhsOffCornerCorrect
  infer_instance


noncomputable def v13RealLinearGaugeSwitchPivot {m : Nat}
    (cols : Finset (Fin m)) (i : Fin m) (y : F2Vec m)
    (h : v13RealLinearGaugeSwitchCandidates cols i y ≠ ∅) : Fin m :=
  (v13RealLinearGaugeSwitchCandidates cols i y).min'
    (Finset.nonempty_iff_ne_empty.mpr h)

theorem v13RealLinearGaugeSwitchPivot_mem {m : Nat}
    (cols : Finset (Fin m)) (i : Fin m) (y : F2Vec m)
    (h : v13RealLinearGaugeSwitchCandidates cols i y ≠ ∅) :
    v13RealLinearGaugeSwitchPivot cols i y h ∈
      v13RealLinearGaugeSwitchCandidates cols i y := by
  classical
  unfold v13RealLinearGaugeSwitchPivot
  exact Finset.min'_mem _ _

theorem v13RealLinearGaugeSwitchPivot_eq_of_eq {m : Nat}
    (cols : Finset (Fin m)) (i : Fin m) {y0 y1 : F2Vec m}
    (hy : y0 = y1)
    {h0 : v13RealLinearGaugeSwitchCandidates cols i y0 ≠ ∅}
    {h1 : v13RealLinearGaugeSwitchCandidates cols i y1 ≠ ∅} :
    v13RealLinearGaugeSwitchPivot cols i y0 h0 =
      v13RealLinearGaugeSwitchPivot cols i y1 h1 := by
  subst y1
  simp [v13RealLinearGaugeSwitchPivot]

noncomputable def
    v13RealLinearColumnSketchRhsCorrectToOffCornerOrCorner
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    V13RealLinearColumnSketchRhsCorrect observer i ↪
      V13RealLinearColumnSketchRhsOffCornerCorrect observer i ⊕
        V13RealLinearColumnSketchRhsCorner observer i where
  toFun omega := by
    classical
    by_cases hcorner :
        v13RealLinearGaugeSwitchCandidates observer.cols i
          (f2AddVec omega.val.2 (v13RealLinearSingleBit i)) = ∅
    · exact Sum.inr ⟨omega.val, hcorner⟩
    · exact Sum.inl ⟨omega.val, omega.property, hcorner⟩
  inj' := by
    intro omega0 omega1 hmap
    classical
    by_cases hcorner0 :
        v13RealLinearGaugeSwitchCandidates observer.cols i
          (f2AddVec omega0.val.2 (v13RealLinearSingleBit i)) = ∅ <;>
      by_cases hcorner1 :
        v13RealLinearGaugeSwitchCandidates observer.cols i
          (f2AddVec omega1.val.2 (v13RealLinearSingleBit i)) = ∅ <;>
      simp [hcorner0, hcorner1] at hmap
    · exact
        Subtype.ext
          (congrArg
            (fun omega :
              V13RealLinearColumnSketchRhsCorner observer i => omega.val)
            hmap)
    · exact
        Subtype.ext
          (congrArg
            (fun omega :
              V13RealLinearColumnSketchRhsOffCornerCorrect observer i =>
                omega.val)
            hmap)

noncomputable def
    v13RealLinearColumnSketchRhsWorldCorrectIncorrectEquiv
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    V13RealLinearUniformWorld m ≃
      V13RealLinearColumnSketchRhsCorrect observer i ⊕
        V13RealLinearColumnSketchRhsIncorrect observer i where
  toFun omega := by
    classical
    by_cases hcorrect :
        v13RealLinearColumnSketchRhsDecision observer omega = omega.2 i
    · exact Sum.inl ⟨omega, hcorrect⟩
    · exact Sum.inr ⟨omega, hcorrect⟩
  invFun y :=
    Sum.elim
      (fun omega : V13RealLinearColumnSketchRhsCorrect observer i =>
        omega.val)
      (fun omega : V13RealLinearColumnSketchRhsIncorrect observer i =>
        omega.val)
      y
  left_inv omega := by
    classical
    by_cases hcorrect :
        v13RealLinearColumnSketchRhsDecision observer omega = omega.2 i <;>
      simp [hcorrect]
  right_inv y := by
    classical
    cases y with
    | inl omega =>
        change
          (if hcorrect :
              v13RealLinearColumnSketchRhsDecision observer omega.val =
                omega.val.2 i then
              Sum.inl
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearColumnSketchRhsCorrect observer i)
            else
              Sum.inr
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearColumnSketchRhsIncorrect observer i)) =
            Sum.inl omega
        rw [dif_pos omega.property]
        rfl
    | inr omega =>
        change
          (if hcorrect :
              v13RealLinearColumnSketchRhsDecision observer omega.val =
                omega.val.2 i then
              Sum.inl
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearColumnSketchRhsCorrect observer i)
            else
              Sum.inr
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearColumnSketchRhsIncorrect observer i)) =
            Sum.inr omega
        rw [dif_neg omega.property]
        rfl

theorem v13RealLinearColumnSketch_transvection_columns_eq {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (A : V13F2LinearEquiv m) {i r : Fin m} (hri : r ≠ i)
    (hrcols : r ∉ observer.cols) :
    v13RealLinearColumnSketch observer.cols
        (v13RealLinearComp A (v13RealLinearTransvection i r hri)) =
      v13RealLinearColumnSketch observer.cols A := by
  funext c row
  have hrc : r ≠ c.val := by
    intro h
    subst r
    exact hrcols c.property
  simp [v13RealLinearColumnSketch, v13RealLinearComp,
    v13RealLinearTransvection_singleBit_fixed hri hrc]

theorem v13RealLinearColumnSketch_transvection_rhs_eq {m : Nat}
    (A : V13F2LinearEquiv m) {i r : Fin m} (hri : r ≠ i)
    {x y : F2Vec m}
    (hy : y = f2AddVec x (v13RealLinearSingleBit i))
    (hyr : y r = 1) :
    (v13RealLinearComp A (v13RealLinearTransvection i r hri)).toEquiv y =
      A.toEquiv x := by
  have hMy :
      (v13RealLinearTransvection i r hri).toEquiv y = x := by
    calc
      (v13RealLinearTransvection i r hri).toEquiv y =
          f2AddVec y (v13RealLinearSingleBit i) :=
        v13RealLinearTransvection_apply_eq_add_singleBit_of_source_one
          hri hyr
      _ = x := by
        rw [hy, v13RealLinear_f2AddVec_singleBit_cancel]
  simp [v13RealLinearComp, hMy]

noncomputable def
    v13RealLinearColumnSketchRhsOffCornerCorrectToIncorrect
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    V13RealLinearColumnSketchRhsOffCornerCorrect observer i ↪
      V13RealLinearColumnSketchRhsIncorrect observer i where
  toFun omega := by
    classical
    let x := omega.val.2
    let y := f2AddVec x (v13RealLinearSingleBit i)
    let candidates := v13RealLinearGaugeSwitchCandidates observer.cols i y
    have hnonempty : candidates ≠ ∅ := by
      simpa [candidates, y] using omega.property.2
    let r := v13RealLinearGaugeSwitchPivot observer.cols i y hnonempty
    have hrmem :
        r ∈ v13RealLinearGaugeSwitchCandidates observer.cols i y := by
      simpa [r] using
        v13RealLinearGaugeSwitchPivot_mem observer.cols i y hnonempty
    have hrnot : r ∉ insert i observer.cols := by
      exact (Finset.mem_filter.mp hrmem).2.1
    have hri : r ≠ i := by
      intro h
      exact hrnot (by simp [h])
    have hrcols : r ∉ observer.cols := by
      intro h
      exact hrnot (Finset.mem_insert_of_mem h)
    have hyr : y r = 1 := (Finset.mem_filter.mp hrmem).2.2
    let M := v13RealLinearTransvection i r hri
    let image : V13RealLinearUniformWorld m :=
      (v13RealLinearComp omega.val.1 M, y)
    refine ⟨image, ?_⟩
    have hcols :
        v13RealLinearColumnSketch observer.cols image.1 =
          v13RealLinearColumnSketch observer.cols omega.val.1 := by
      simpa [image, M] using
        v13RealLinearColumnSketch_transvection_columns_eq
          observer omega.val.1 hri hrcols
    have hrhs :
        v13RealLinearUniformRhs image =
          v13RealLinearUniformRhs omega.val := by
      simpa [image, v13RealLinearUniformRhs, y] using
        v13RealLinearColumnSketch_transvection_rhs_eq
          omega.val.1 hri (x := x) (y := y) (by rfl) hyr
    have hdecision :
        v13RealLinearColumnSketchRhsDecision observer image =
          v13RealLinearColumnSketchRhsDecision observer omega.val := by
      simp [v13RealLinearColumnSketchRhsDecision, hcols, hrhs]
    intro hbad
    have hyi : y i = x i + 1 := by
      simp [y, f2AddVec, v13RealLinearSingleBit]
    have hflip : x i + 1 = x i := by
      calc
        x i + 1 = y i := hyi.symm
        _ = v13RealLinearColumnSketchRhsDecision observer image := hbad.symm
        _ = v13RealLinearColumnSketchRhsDecision observer omega.val :=
          hdecision
        _ = x i := omega.property.1
    exact v13_zmod2_add_one_ne_self (x i) hflip
  inj' := by
    intro omega0 omega1 hmap
    classical
    apply Subtype.ext
    apply Prod.ext
    · let x0 := omega0.val.2
      let y0 := f2AddVec x0 (v13RealLinearSingleBit i)
      let x1 := omega1.val.2
      let y1 := f2AddVec x1 (v13RealLinearSingleBit i)
      let candidates0 := v13RealLinearGaugeSwitchCandidates observer.cols i y0
      let candidates1 := v13RealLinearGaugeSwitchCandidates observer.cols i y1
      have hnonempty0 : candidates0 ≠ ∅ := by
        simpa [candidates0, y0] using omega0.property.2
      have hnonempty1 : candidates1 ≠ ∅ := by
        simpa [candidates1, y1] using omega1.property.2
      let r0 := v13RealLinearGaugeSwitchPivot observer.cols i y0 hnonempty0
      let r1 := v13RealLinearGaugeSwitchPivot observer.cols i y1 hnonempty1
      have hrmem0 :
          r0 ∈ v13RealLinearGaugeSwitchCandidates observer.cols i y0 := by
        simpa [r0] using
          v13RealLinearGaugeSwitchPivot_mem observer.cols i y0 hnonempty0
      have hrmem1 :
          r1 ∈ v13RealLinearGaugeSwitchCandidates observer.cols i y1 := by
        simpa [r1] using
          v13RealLinearGaugeSwitchPivot_mem observer.cols i y1 hnonempty1
      have hrnot0 : r0 ∉ insert i observer.cols :=
        (Finset.mem_filter.mp hrmem0).2.1
      have hrnot1 : r1 ∉ insert i observer.cols :=
        (Finset.mem_filter.mp hrmem1).2.1
      have hri0 : r0 ≠ i := by
        intro h
        exact hrnot0 (by simp [h])
      have hri1 : r1 ≠ i := by
        intro h
        exact hrnot1 (by simp [h])
      have hval := congrArg Subtype.val hmap
      change
        (v13RealLinearComp omega0.val.1
              (v13RealLinearTransvection i r0 hri0), y0) =
          (v13RealLinearComp omega1.val.1
              (v13RealLinearTransvection i r1 hri1), y1) at hval
      have hy : y0 = y1 := congrArg Prod.snd hval
      have hr : r0 = r1 := by
        simpa [r0, r1, candidates0, candidates1] using
          v13RealLinearGaugeSwitchPivot_eq_of_eq observer.cols i hy
      have hcomp := congrArg Prod.fst hval
      apply v13RealLinearEquiv_ext
      intro z
      let M0 := v13RealLinearTransvection i r0 hri0
      have hpoint := congrArg
        (fun A : V13F2LinearEquiv m => A.toEquiv (M0.toEquiv.symm z))
        hcomp
      have hcancel :=
        v13RealLinearTransvection_apply_symm_apply_of_eq
          hr hri0 hri1 z
      simpa [v13RealLinearComp, M0, hcancel] using hpoint
    · let x0 := omega0.val.2
      let y0 := f2AddVec x0 (v13RealLinearSingleBit i)
      let x1 := omega1.val.2
      let y1 := f2AddVec x1 (v13RealLinearSingleBit i)
      let candidates0 := v13RealLinearGaugeSwitchCandidates observer.cols i y0
      let candidates1 := v13RealLinearGaugeSwitchCandidates observer.cols i y1
      have hnonempty0 : candidates0 ≠ ∅ := by
        simpa [candidates0, y0] using omega0.property.2
      have hnonempty1 : candidates1 ≠ ∅ := by
        simpa [candidates1, y1] using omega1.property.2
      let r0 := v13RealLinearGaugeSwitchPivot observer.cols i y0 hnonempty0
      let r1 := v13RealLinearGaugeSwitchPivot observer.cols i y1 hnonempty1
      have hrmem0 :
          r0 ∈ v13RealLinearGaugeSwitchCandidates observer.cols i y0 := by
        simpa [r0] using
          v13RealLinearGaugeSwitchPivot_mem observer.cols i y0 hnonempty0
      have hrmem1 :
          r1 ∈ v13RealLinearGaugeSwitchCandidates observer.cols i y1 := by
        simpa [r1] using
          v13RealLinearGaugeSwitchPivot_mem observer.cols i y1 hnonempty1
      have hrnot0 : r0 ∉ insert i observer.cols :=
        (Finset.mem_filter.mp hrmem0).2.1
      have hrnot1 : r1 ∉ insert i observer.cols :=
        (Finset.mem_filter.mp hrmem1).2.1
      have hri0 : r0 ≠ i := by
        intro h
        exact hrnot0 (by simp [h])
      have hri1 : r1 ≠ i := by
        intro h
        exact hrnot1 (by simp [h])
      have hval := congrArg Subtype.val hmap
      change
        (v13RealLinearComp omega0.val.1
              (v13RealLinearTransvection i r0 hri0), y0) =
          (v13RealLinearComp omega1.val.1
              (v13RealLinearTransvection i r1 hri1), y1) at hval
      have hy : y0 = y1 := congrArg Prod.snd hval
      exact v13RealLinear_f2AddVec_singleBit_inj hy

theorem
    v13RealLinearColumnSketchRhs_offCornerCorrect_card_le_incorrect
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype.card
        (V13RealLinearColumnSketchRhsOffCornerCorrect observer i) ≤
      Fintype.card
        (V13RealLinearColumnSketchRhsIncorrect observer i) :=
  Fintype.card_le_of_embedding
    (v13RealLinearColumnSketchRhsOffCornerCorrectToIncorrect observer i)

theorem
    v13RealLinearColumnSketchRhs_correct_card_le_incorrect_add_corner
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype.card (V13RealLinearColumnSketchRhsCorrect observer i) ≤
      Fintype.card (V13RealLinearColumnSketchRhsIncorrect observer i) +
        Fintype.card (V13RealLinearColumnSketchRhsCorner observer i) := by
  have hsplit :
      Fintype.card (V13RealLinearColumnSketchRhsCorrect observer i) ≤
        Fintype.card
          (V13RealLinearColumnSketchRhsOffCornerCorrect observer i ⊕
            V13RealLinearColumnSketchRhsCorner observer i) :=
    Fintype.card_le_of_embedding
      (v13RealLinearColumnSketchRhsCorrectToOffCornerOrCorner observer i)
  rw [Fintype.card_sum] at hsplit
  have hoff :=
    v13RealLinearColumnSketchRhs_offCornerCorrect_card_le_incorrect
      observer i
  omega

theorem
    v13RealLinearColumnSketchRhs_world_card_eq_correct_add_incorrect
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype.card (V13RealLinearUniformWorld m) =
      Fintype.card (V13RealLinearColumnSketchRhsCorrect observer i) +
        Fintype.card (V13RealLinearColumnSketchRhsIncorrect observer i) := by
  simpa [Fintype.card_sum] using
    Fintype.card_congr
      (v13RealLinearColumnSketchRhsWorldCorrectIncorrectEquiv observer i)

theorem
    v13RealLinearColumnSketchRhs_correct_card_mul_two_le_world_add_corner
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype.card (V13RealLinearColumnSketchRhsCorrect observer i) * 2 ≤
      Fintype.card (V13RealLinearUniformWorld m) +
        Fintype.card (V13RealLinearColumnSketchRhsCorner observer i) := by
  let C := Fintype.card (V13RealLinearColumnSketchRhsCorrect observer i)
  let I := Fintype.card (V13RealLinearColumnSketchRhsIncorrect observer i)
  let B := Fintype.card (V13RealLinearColumnSketchRhsCorner observer i)
  let T := Fintype.card (V13RealLinearUniformWorld m)
  have hcard : C ≤ I + B := by
    simpa [C, I, B] using
      v13RealLinearColumnSketchRhs_correct_card_le_incorrect_add_corner
        observer i
  have hworld : T = C + I := by
    simpa [T, C, I] using
      v13RealLinearColumnSketchRhs_world_card_eq_correct_add_incorrect
        observer i
  omega

noncomputable def
    v13RealLinearColumnSketchRhsCornerToMapSupportedEmbedding
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    V13RealLinearColumnSketchRhsCorner observer i ↪
      V13F2LinearEquiv m × V13RealLinearSupportedOn (insert i observer.cols) where
  toFun omega :=
    (omega.val.1,
      ⟨f2AddVec omega.val.2 (v13RealLinearSingleBit i), by
        intro r hr
        by_contra hnonzero
        have hone :
            f2AddVec omega.val.2 (v13RealLinearSingleBit i) r = 1 :=
          v13_zmod2_eq_one_of_ne_zero _ hnonzero
        have hmem :
            r ∈ v13RealLinearGaugeSwitchCandidates observer.cols i
              (f2AddVec omega.val.2 (v13RealLinearSingleBit i)) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr, hone⟩
        have hne :
            v13RealLinearGaugeSwitchCandidates observer.cols i
              (f2AddVec omega.val.2 (v13RealLinearSingleBit i)) ≠ ∅ :=
          Finset.ne_empty_of_mem hmem
        exact hne omega.property⟩)
  inj' := by
    intro omega0 omega1 hmap
    apply Subtype.ext
    apply Prod.ext
    · exact
        congrArg
          (fun z :
            V13F2LinearEquiv m ×
              V13RealLinearSupportedOn (insert i observer.cols) => z.1)
          hmap
    · have hy :
          f2AddVec omega0.val.2 (v13RealLinearSingleBit i) =
            f2AddVec omega1.val.2 (v13RealLinearSingleBit i) :=
        congrArg
          (fun z :
            V13F2LinearEquiv m ×
              V13RealLinearSupportedOn (insert i observer.cols) => z.2.val)
          hmap
      exact v13RealLinear_f2AddVec_singleBit_inj hy

theorem v13RealLinearColumnSketchRhsCorner_card_le
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype.card (V13RealLinearColumnSketchRhsCorner observer i) ≤
      Fintype.card (V13F2LinearEquiv m) *
        2 ^ (insert i observer.cols).card := by
  classical
  have hle :
      Fintype.card (V13RealLinearColumnSketchRhsCorner observer i) ≤
        Fintype.card
          (V13F2LinearEquiv m ×
            V13RealLinearSupportedOn (insert i observer.cols)) :=
    Fintype.card_le_of_embedding
      (v13RealLinearColumnSketchRhsCornerToMapSupportedEmbedding
        observer i)
  have hsupp :=
    v13RealLinearSupportedOn_card_le (insert i observer.cols)
  rw [Fintype.card_prod] at hle
  exact hle.trans (Nat.mul_le_mul_left _ hsupp)

theorem v13RealLinearColumnSketchRhsCorner_card_mul_two_pow_le
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    Fintype.card (V13RealLinearColumnSketchRhsCorner observer i) *
        2 ^ m ≤
      (2 * 2 ^ j) * Fintype.card (V13RealLinearUniformWorld m) := by
  classical
  let B := Fintype.card (V13RealLinearColumnSketchRhsCorner observer i)
  let S := Fintype.card (V13F2LinearEquiv m)
  let M := 2 ^ m
  let K := 2 ^ (insert i observer.cols).card
  have hcorner : B ≤ S * K := by
    simpa [B, S, K] using
      v13RealLinearColumnSketchRhsCorner_card_le observer i
  have hcardInsert : (insert i observer.cols).card ≤ j + 1 := by
    calc
      (insert i observer.cols).card ≤ observer.cols.card + 1 := by
        simpa [Nat.add_comm] using
          Finset.card_insert_le i observer.cols
      _ ≤ j + 1 := Nat.add_le_add_right observer.readBudget 1
  have hK : K ≤ 2 * 2 ^ j := by
    dsimp [K]
    calc
      2 ^ (insert i observer.cols).card ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hcardInsert
      _ = 2 * 2 ^ j := by
        rw [pow_succ, Nat.mul_comm]
  have hworld :
      Fintype.card (V13RealLinearUniformWorld m) = S * M := by
    dsimp [V13RealLinearUniformWorld, S, M]
    rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  calc
    B * M ≤ (S * K) * M := Nat.mul_le_mul_right M hcorner
    _ ≤ (S * (2 * 2 ^ j)) * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_left S hK)
    _ = (2 * 2 ^ j) * Fintype.card (V13RealLinearUniformWorld m) := by
      simp [hworld, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

noncomputable def v13RealLinearColumnSketchRhsSuccess {m j : Nat}
    (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) : Rat :=
  (Fintype.card (V13RealLinearColumnSketchRhsCorrect observer i) : Rat) /
    (Fintype.card (V13RealLinearUniformWorld m) : Rat)

theorem v13RealLinearColumnSketchRhs_success_bound
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    v13RealLinearColumnSketchRhsSuccess observer i ≤
      (1 / 2 : Rat) + (2 : Rat) ^ j / (2 : Rat) ^ m := by
  classical
  unfold v13RealLinearColumnSketchRhsSuccess
  let C := Fintype.card (V13RealLinearColumnSketchRhsCorrect observer i)
  let B := Fintype.card (V13RealLinearColumnSketchRhsCorner observer i)
  let T := Fintype.card (V13RealLinearUniformWorld m)
  let M := 2 ^ m
  let Q := 2 ^ j
  have hmain : C * 2 ≤ T + B := by
    simpa [C, B, T] using
      v13RealLinearColumnSketchRhs_correct_card_mul_two_le_world_add_corner
        observer i
  have hcorner : B * M ≤ (2 * Q) * T := by
    simpa [B, M, Q, T, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using v13RealLinearColumnSketchRhsCorner_card_mul_two_pow_le
        observer i
  have hTposNat : 0 < T := by
    dsimp [T, V13RealLinearUniformWorld]
    exact Fintype.card_pos_iff.mpr ⟨(v13RealLinearIdentity m, f2ZeroVec m)⟩
  have hMposNat : 0 < M := by
    dsimp [M]
    positivity
  have hTpos : (0 : Rat) < (T : Rat) := by
    exact_mod_cast hTposNat
  have hMpos : (0 : Rat) < (M : Rat) := by
    exact_mod_cast hMposNat
  have hmainRat : (C : Rat) * 2 ≤ (T : Rat) + (B : Rat) := by
    exact_mod_cast hmain
  have hcornerRat : (B : Rat) * (M : Rat) ≤
      (2 : Rat) * (Q : Rat) * (T : Rat) := by
    exact_mod_cast hcorner
  have hcombined :
      (C : Rat) * 2 * (M : Rat) ≤
        ((M : Rat) + 2 * (Q : Rat)) * (T : Rat) := by
    have hmainScaled :=
      mul_le_mul_of_nonneg_right hmainRat (le_of_lt hMpos)
    nlinarith [hmainScaled, hcornerRat]
  have hQrat : (Q : Rat) = (2 : Rat) ^ j := by
    dsimp [Q]
    norm_num
  have hMrat : (M : Rat) = (2 : Rat) ^ m := by
    dsimp [M]
    norm_num
  change (C : Rat) / (T : Rat) ≤
    (1 / 2 : Rat) + (2 : Rat) ^ j / (2 : Rat) ^ m
  rw [← hQrat, ← hMrat]
  rw [div_le_iff₀ hTpos]
  field_simp [hTpos.ne', hMpos.ne']
  nlinarith [hcombined]

theorem v13RealLinear_columnSketchRhs_success_bound
    {m j : Nat} (observer : V13RealLinearColumnSketchRhsObserver m j)
    (i : Fin m) :
    v13RealLinearColumnSketchRhsSuccess observer i ≤
      (1 / 2 : Rat) + (2 : Rat) ^ j / (2 : Rat) ^ m :=
  v13RealLinearColumnSketchRhs_success_bound observer i

noncomputable def v13RealLinearRhsOnlySuccess {m : Nat}
    (observer : V13RealLinearRhsOnlyObserver m) (i : Fin m) : Rat :=
  v13RealLinearColumnSketchRhsSuccess observer.toColumnSketch i

theorem v13RealLinear_rhsOnly_success_bound
    {m : Nat} (observer : V13RealLinearRhsOnlyObserver m) (i : Fin m) :
    v13RealLinearRhsOnlySuccess observer i ≤
      (1 / 2 : Rat) + 1 / (2 : Rat) ^ m := by
  simpa [v13RealLinearRhsOnlySuccess] using
    (v13RealLinearColumnSketchRhs_success_bound
      (observer := observer.toColumnSketch) (i := i))

end Mettapedia.Computability.PNP
