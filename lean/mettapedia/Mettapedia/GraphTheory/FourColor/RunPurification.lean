import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

variable {ι : Type*} [DecidableEq ι]

/-- Sum of color indicators attached to a finite family of runs. -/
def faceGenerator (γ : Color) (runs : Finset (Finset ι))
    (assign : Finset ι → Finset ι) : ι → Color :=
  ∑ R ∈ runs, indicatorChain γ (assign R)

/-- Pointwise per-run purification: if two chains agree off a run and differ by `γ` on the run,
their `chainXor` is exactly the run indicator. -/
theorem perRunPurification_pointwise (γ : Color) (R : Finset ι) {X Y : ι → Color}
    (h_off : ∀ e, e ∉ R → X e = Y e)
    (h_on : ∀ e ∈ R, chainXor X Y e = γ) :
    chainXor X Y = indicatorChain γ R := by
  funext e
  by_cases he : e ∈ R
  · simpa [indicatorChain, he] using h_on e he
  · have hXY : X e = Y e := h_off e he
    have hzero : chainXor X Y e = 0 := by
      simp [chainXor, hXY]
    simpa [indicatorChain, he] using hzero

/-- Per-run purification, algebraic form: if two assignments agree away from a distinguished run,
and differ on that run by the run indicator, then their whole face generators differ by that
same run indicator. -/
theorem perRunPurification_face (γ : Color) (runs : Finset (Finset ι))
    (R : Finset ι) (assign assign' : Finset ι → Finset ι)
    (hR : R ∈ runs)
    (h_off : ∀ S ∈ runs, S ≠ R → assign S = assign' S)
    (h_run :
      chainXor (indicatorChain γ (assign R)) (indicatorChain γ (assign' R)) =
        indicatorChain γ R) :
    chainXor (faceGenerator γ runs assign) (faceGenerator γ runs assign') =
      indicatorChain γ R := by
  have hsum_assign :=
    Finset.add_sum_erase (s := runs)
      (f := fun S : Finset ι => indicatorChain γ (assign S)) hR
  have hsum_assign' :=
    Finset.add_sum_erase (s := runs)
      (f := fun S : Finset ι => indicatorChain γ (assign' S)) hR
  set rest :=
    ∑ S ∈ runs.erase R, indicatorChain γ (assign S) with hrest_def
  set rest' :=
    ∑ S ∈ runs.erase R, indicatorChain γ (assign' S) with hrest'_def
  have hrest_eq : rest = rest' := by
    have hsum :
        ∑ S ∈ runs.erase R, indicatorChain γ (assign S) =
          ∑ S ∈ runs.erase R, indicatorChain γ (assign' S) := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      obtain ⟨hS_ne, hS_runs⟩ := Finset.mem_erase.mp hS
      have hassign := h_off S hS_runs hS_ne
      simp [hassign]
    simpa [rest, rest', hrest_def, hrest'_def] using hsum
  have hface_assign :
      indicatorChain γ (assign R) + rest =
        faceGenerator γ runs assign := by
    simpa [faceGenerator, rest, hrest_def] using hsum_assign
  have hface_assign' :
      indicatorChain γ (assign' R) + rest' =
        faceGenerator γ runs assign' := by
    simpa [faceGenerator, rest', hrest'_def] using hsum_assign'
  calc
    chainXor (faceGenerator γ runs assign) (faceGenerator γ runs assign')
        = chainXor (indicatorChain γ (assign R) + rest)
            (indicatorChain γ (assign' R) + rest') := by
              simp [hface_assign.symm, hface_assign'.symm]
    _ = chainXor (indicatorChain γ (assign R) + rest)
            (indicatorChain γ (assign' R) + rest) := by
              simp [hrest_eq]
    _ = chainXor (indicatorChain γ (assign R))
            (indicatorChain γ (assign' R)) :=
              chainXor_add_right_cancel _ _ _
    _ = indicatorChain γ R := h_run

/-- Summing the indicator chains over a finite partition of `boundary` recovers the indicator of
the whole boundary. -/
theorem indicatorChain_of_partition (γ : Color) (runs : Finset (Finset ι))
    (boundary : Finset ι)
    (h_subset : ∀ R ∈ runs, R ⊆ boundary)
    (h_cover : ∀ e ∈ boundary, ∃! R, R ∈ runs ∧ e ∈ R) :
    faceGenerator γ runs (fun R => R) = indicatorChain γ boundary := by
  funext e
  by_cases he : e ∈ boundary
  · rcases h_cover e he with ⟨R₀, hR₀P, huniq⟩
    rcases hR₀P with ⟨hR₀_runs, heR₀⟩
    have hsum :=
      Finset.add_sum_erase (s := runs)
        (f := fun S : Finset ι => if e ∈ S then γ else 0) hR₀_runs
    have hrest_zero :
        ∑ S ∈ runs.erase R₀, (if e ∈ S then γ else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro S hS
      obtain ⟨hSr, hS_runs⟩ := Finset.mem_erase.mp hS
      have : e ∉ S := by
        intro heS
        have hmatch : S = R₀ :=
          huniq S ⟨hS_runs, heS⟩
        exact hSr hmatch
      simp [this]
    have hsum_eval :
        ∑ S ∈ runs, (if e ∈ S then γ else 0) = γ := by
      simpa [heR₀, hrest_zero] using hsum.symm
    simpa [faceGenerator, indicatorChain, he] using hsum_eval
  · have hnot_mem : ∀ R ∈ runs, e ∉ R := by
      intro R hR heR
      exact he ((h_subset R hR) heR)
    have hsum_zero :
        ∑ S ∈ runs, (if e ∈ S then γ else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro S hS
      simp [hnot_mem S hS]
    simpa [faceGenerator, indicatorChain, he] using hsum_zero

/-- Face-level purification, algebraic form: if runs partition the boundary and every per-run
purification contributes exactly that run indicator, the aggregate contribution is the full
boundary indicator. -/
theorem faceLevelPurification (γ : Color) (runs : Finset (Finset ι))
    (boundary : Finset ι) (X : ι → Color) (Y : Finset ι → ι → Color)
    (h_run : ∀ R ∈ runs, chainXor X (Y R) = indicatorChain γ R)
    (h_subset : ∀ R ∈ runs, R ⊆ boundary)
    (h_cover : ∀ e ∈ boundary, ∃! R, R ∈ runs ∧ e ∈ R) :
    ∑ R ∈ runs, chainXor X (Y R) = indicatorChain γ boundary := by
  have hrewrite :
      ∑ R ∈ runs, chainXor X (Y R)
        = ∑ R ∈ runs, indicatorChain γ R := by
    refine Finset.sum_congr rfl ?_
    intro R hR
    simpa using h_run R hR
  have hpartition :=
    indicatorChain_of_partition (γ := γ) (runs := runs)
      (boundary := boundary) h_subset h_cover
  calc
    ∑ R ∈ runs, chainXor X (Y R)
        = ∑ R ∈ runs, indicatorChain γ R := hrewrite
    _ = faceGenerator γ runs (fun R => R) := rfl
    _ = indicatorChain γ boundary := hpartition

/-- Data for applying face-level purification to a boundary partition. -/
structure FaceRunPurificationData (ι : Type*) [DecidableEq ι] where
  γ : Color
  runs : Finset (Finset ι)
  boundary : Finset ι
  base : ι → Color
  switched : Finset ι → ι → Color
  run_chain : ∀ R ∈ runs, chainXor base (switched R) = indicatorChain γ R
  subset_boundary : ∀ R ∈ runs, R ⊆ boundary
  cover_boundary : ∀ e ∈ boundary, ∃! R, R ∈ runs ∧ e ∈ R

namespace FaceRunPurificationData

/-- The aggregated per-run purification equals the boundary indicator. -/
theorem boundary_indicator (D : FaceRunPurificationData ι) :
    ∑ R ∈ D.runs, chainXor D.base (D.switched R) =
      indicatorChain D.γ D.boundary :=
  faceLevelPurification (γ := D.γ) (runs := D.runs)
    (boundary := D.boundary) (X := D.base) (Y := D.switched)
    D.run_chain D.subset_boundary D.cover_boundary

end FaceRunPurificationData

/-- A combinatorial description of a face boundary decomposed into finite runs. -/
structure FaceRunPartition (ι : Type*) [DecidableEq ι] where
  runs : Finset (Finset ι)
  boundary : Finset ι
  subset_boundary : ∀ R ∈ runs, R ⊆ boundary
  cover_boundary : ∀ e ∈ boundary, ∃! R, R ∈ runs ∧ e ∈ R

namespace FaceRunPartition

/-- Per-run switch data for a fixed run partition. -/
structure SwitchData (P : FaceRunPartition ι) where
  γ : Color
  base : ι → Color
  switched : ∀ ⦃R⦄, R ∈ P.runs → ι → Color
  run_chain :
    ∀ {R} (hR : R ∈ P.runs),
      chainXor base (switched hR) = indicatorChain γ R

namespace SwitchData

variable {P : FaceRunPartition ι} (S : SwitchData P)

/-- Switched chain extended by zero away from the partition's runs. -/
def switchedTotal : Finset ι → ι → Color :=
  fun R => if hR : R ∈ P.runs then S.switched hR else 0

theorem switchedTotal_apply_of_mem {R : Finset ι} (hR : R ∈ P.runs) :
    S.switchedTotal R = S.switched hR := by
  funext e
  simp [switchedTotal, hR]

theorem switchedTotal_apply_of_not_mem {R : Finset ι} (hR : R ∉ P.runs) :
    S.switchedTotal R = 0 := by
  funext e
  simp [switchedTotal, hR]

theorem run_chain_total {R : Finset ι} (hR : R ∈ P.runs) :
    chainXor S.base (S.switchedTotal R) = indicatorChain S.γ R := by
  simpa [S.switchedTotal_apply_of_mem hR] using S.run_chain (P := P) hR

/-- Assemble face-run purification data from partition data and per-run switches. -/
def toPurificationData : FaceRunPurificationData ι where
  γ := S.γ
  runs := P.runs
  boundary := P.boundary
  base := S.base
  switched := S.switchedTotal
  run_chain := by
    intro R hR
    exact S.run_chain_total (P := P) hR
  subset_boundary := P.subset_boundary
  cover_boundary := P.cover_boundary

end SwitchData

end FaceRunPartition

/-- A run together with two disjoint complementary interior completion arcs. -/
structure NaiveRunCompletion (ι : Type*) [DecidableEq ι] where
  run : Finset ι
  leftArc : Finset ι
  rightArc : Finset ι
  run_left_disjoint : Disjoint run leftArc
  run_right_disjoint : Disjoint run rightArc
  left_right_disjoint : Disjoint leftArc rightArc
  leftArc_nonempty : leftArc.Nonempty

namespace NaiveRunCompletion

/-- The interior support left after cancelling the common run. -/
def interior (D : NaiveRunCompletion ι) : Finset ι :=
  D.leftArc ∪ D.rightArc

/-- The naive pre-switch chain supported on `R ∪ A`. -/
def before (D : NaiveRunCompletion ι) (γ : Color) : ι → Color :=
  indicatorChain γ (D.run ∪ D.leftArc)

/-- The naive post-switch chain supported on `R ∪ A'`. -/
def after (D : NaiveRunCompletion ι) (γ : Color) : ι → Color :=
  indicatorChain γ (D.run ∪ D.rightArc)

@[simp] theorem not_mem_leftArc_of_mem_run (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.run) : e ∉ D.leftArc := by
  exact fun hleft => Finset.disjoint_left.mp D.run_left_disjoint he hleft

@[simp] theorem not_mem_rightArc_of_mem_run (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.run) : e ∉ D.rightArc := by
  exact fun hright => Finset.disjoint_left.mp D.run_right_disjoint he hright

@[simp] theorem not_mem_run_of_mem_leftArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.leftArc) : e ∉ D.run := by
  exact fun hrun => Finset.disjoint_left.mp D.run_left_disjoint hrun he

@[simp] theorem not_mem_run_of_mem_rightArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.rightArc) : e ∉ D.run := by
  exact fun hrun => Finset.disjoint_left.mp D.run_right_disjoint hrun he

@[simp] theorem not_mem_rightArc_of_mem_leftArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.leftArc) : e ∉ D.rightArc := by
  exact fun hright => Finset.disjoint_left.mp D.left_right_disjoint he hright

@[simp] theorem not_mem_leftArc_of_mem_rightArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.rightArc) : e ∉ D.leftArc := by
  exact fun hleft => Finset.disjoint_left.mp D.left_right_disjoint hleft he

@[simp] theorem not_mem_interior_of_mem_run (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.run) : e ∉ D.interior := by
  simp [interior, D.not_mem_leftArc_of_mem_run he, D.not_mem_rightArc_of_mem_run he]

@[simp] theorem mem_interior_of_mem_leftArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.leftArc) : e ∈ D.interior := by
  simp [interior, he]

@[simp] theorem mem_interior_of_mem_rightArc (D : NaiveRunCompletion ι) {e : ι}
    (he : e ∈ D.rightArc) : e ∈ D.interior := by
  simp [interior, he]

/-- Pointwise cancellation calculation for the naive completion. -/
theorem chainXor_before_after_apply (D : NaiveRunCompletion ι) (γ : Color) (e : ι) :
    chainXor (D.before γ) (D.after γ) e = if e ∈ D.interior then γ else 0 := by
  by_cases hrun : e ∈ D.run
  · have hleft : e ∉ D.leftArc := D.not_mem_leftArc_of_mem_run hrun
    have hright : e ∉ D.rightArc := D.not_mem_rightArc_of_mem_run hrun
    simp [before, after, interior, chainXor, indicatorChain, hrun, hleft, hright]
  · by_cases hleft : e ∈ D.leftArc
    · have hrun' : e ∉ D.run := D.not_mem_run_of_mem_leftArc hleft
      have hright : e ∉ D.rightArc := D.not_mem_rightArc_of_mem_leftArc hleft
      simp [before, after, interior, chainXor, indicatorChain, hrun', hleft, hright]
    · by_cases hright : e ∈ D.rightArc
      · have hrun' : e ∉ D.run := D.not_mem_run_of_mem_rightArc hright
        have hleft' : e ∉ D.leftArc := D.not_mem_leftArc_of_mem_rightArc hright
        simp [before, after, interior, chainXor, indicatorChain, hrun', hleft', hright]
      · simp [before, after, interior, chainXor, indicatorChain, hrun, hleft, hright]

/-- The common run cancels, leaving only the complementary interior arcs. -/
theorem chainXor_before_after_eq_indicator_interior
    (D : NaiveRunCompletion ι) (γ : Color) :
    chainXor (D.before γ) (D.after γ) = indicatorChain γ D.interior := by
  funext e
  simpa [indicatorChain] using D.chainXor_before_after_apply γ e

end NaiveRunCompletion

/-- Main single-run obstruction: the naive completed-run `chainXor` is interior support, not run
support. -/
theorem per_run_xor_is_interior (D : NaiveRunCompletion ι) (γ : Color) :
    chainXor (D.before γ) (D.after γ) = indicatorChain γ D.interior :=
  D.chainXor_before_after_eq_indicator_interior γ

/-- On the run itself, the naive per-run `chainXor` always vanishes. -/
theorem per_run_xor_zero_on_run (D : NaiveRunCompletion ι) (γ : Color)
    {e : ι} (he : e ∈ D.run) :
    chainXor (D.before γ) (D.after γ) e = 0 := by
  rw [per_run_xor_is_interior]
  simp [indicatorChain, D.not_mem_interior_of_mem_run he]

/-- The naive completed-run model cannot produce the run indicator unless `γ = 0`. -/
theorem paper_claim_impossible (D : NaiveRunCompletion ι) (γ : Color) (hγ : γ ≠ 0) :
    chainXor (D.before γ) (D.after γ) ≠ indicatorChain γ D.run := by
  intro hEq
  obtain ⟨e, he⟩ := D.leftArc_nonempty
  have hLhs : chainXor (D.before γ) (D.after γ) e = γ := by
    rw [per_run_xor_is_interior]
    simp [indicatorChain, D.mem_interior_of_mem_leftArc he]
  have he_not_run : e ∉ D.run := D.not_mem_run_of_mem_leftArc he
  have hRhs : indicatorChain γ D.run e = 0 := by
    simp [indicatorChain, he_not_run]
  have : γ = 0 := by
    calc
      γ = chainXor (D.before γ) (D.after γ) e := hLhs.symm
      _ = indicatorChain γ D.run e := congrFun hEq e
      _ = 0 := hRhs
  exact hγ this

/-- The singleton partition on one run. -/
def singletonRunPartition (R : Finset ι) : FaceRunPartition ι where
  runs := {R}
  boundary := R
  subset_boundary := by
    intro S hS
    rw [Finset.mem_singleton.mp hS]
  cover_boundary := by
    intro e he
    refine ⟨R, ?_, ?_⟩
    · exact ⟨Finset.mem_singleton_self R, he⟩
    · intro S hS
      exact Finset.mem_singleton.mp hS.1

/-- The `FaceRunPartition.SwitchData` interface cannot be instantiated by the naive completed-run
chains, even in the one-run case. -/
theorem no_switchdata_from_naive_completion
    (D : NaiveRunCompletion ι) (γ : Color) (hγ : γ ≠ 0) :
    ¬ ∃ S : FaceRunPartition.SwitchData (singletonRunPartition D.run),
      S.γ = γ ∧
      S.base = D.before γ ∧
      S.switched (R := D.run) (by simp [singletonRunPartition]) = D.after γ := by
  intro h
  rcases h with ⟨S, hSγ, hSbase, hSswitched⟩
  have hRun :
      chainXor S.base (S.switched (R := D.run) (by simp [singletonRunPartition])) =
        indicatorChain S.γ D.run := by
    simpa [singletonRunPartition] using
      S.run_chain (R := D.run) (by simp [singletonRunPartition])
  rw [hSγ, hSbase, hSswitched] at hRun
  exact paper_claim_impossible D γ hγ hRun

end Mettapedia.GraphTheory.FourColor
