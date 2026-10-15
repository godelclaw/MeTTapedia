import Mettapedia.Logic.HostingStyles.Weighted.KernelPreservation

/-!
# Weight preservation along semiring maps

Closed-sum preservation is transported by every semiring homomorphism, via
`closedSum_mapRange`. A function on coefficients that is not a homomorphism
need not transport it: squaring sends the equality `2 = 1 + 1` to `4 ≠ 1 + 1`.

Along `supportHom`, preservation becomes a statement about the support
systems (`WeightedSystem.support`): an equation-closed set meets a source
step exactly when it meets the read-back of an image step.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Classical
open Mettapedia.GSLT
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.GSLT.GradedSupport

theorem closedSum_single {α K : Type*} [AddCommMonoid K] [DecidableEq α]
    (a : α) (n : K) (C : α → Prop) :
    closedSum (Finsupp.single a n) C = if C a then n else 0 := by
  classical
  by_cases hn : n = 0
  · subst hn
    rw [Finsupp.single_zero, closedSum_zero]
    split_ifs <;> rfl
  · unfold closedSum
    rw [Finsupp.support_single a hn, Finset.sum_singleton, Finsupp.single_eq_same]

/-! ## Transport along a semiring map -/

set_option linter.checkUnivs false in
/-- Change coefficients of both systems along one semiring map. The term map,
the label map, and the read-back stay where they are. -/
noncomputable def KernelMap.mapCoefficients {K L : Type*} [Semiring K] [Semiring L]
    {sourceSpace targetSpace : GSLT} (map : KernelMap K sourceSpace targetSpace)
    (φ : K →+* L) : KernelMap L sourceSpace targetSpace where
  source := map.source.mapCoefficients φ
  target := map.target.mapCoefficients φ
  term := map.term
  labelMap := map.labelMap
  readBack := map.readBack
  readBack_resp := map.readBack_resp

theorem closedSum_source_coefficients {K L : Type*} [Semiring K] [Semiring L]
    {sourceSpace targetSpace : GSLT} (map : KernelMap K sourceSpace targetSpace)
    (φ : K →+* L) (label : map.source.Label) (s : sourceSpace.Term)
    (C : sourceSpace.Term → Prop) :
    closedSum ((map.mapCoefficients φ).source.kernel label s) C =
      φ (closedSum (map.source.kernel label s) C) := by
  simpa [KernelMap.mapCoefficients, WeightedSystem.mapCoefficients,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] using
    closedSum_mapRange φ.toAddMonoidHom (map.source.kernel label s) C

theorem closedSum_target_coefficients {K L : Type*} [Semiring K] [Semiring L]
    {sourceSpace targetSpace : GSLT} (map : KernelMap K sourceSpace targetSpace)
    (φ : K →+* L) (label : map.source.Label) (s : sourceSpace.Term)
    (C : targetSpace.Term → Prop) :
    closedSum ((map.mapCoefficients φ).target.kernel
        ((map.mapCoefficients φ).labelMap label) ((map.mapCoefficients φ).term s)) C =
      φ (closedSum (map.target.kernel (map.labelMap label) (map.term s)) C) := by
  simpa [KernelMap.mapCoefficients, WeightedSystem.mapCoefficients,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] using
    closedSum_mapRange φ.toAddMonoidHom
      (map.target.kernel (map.labelMap label) (map.term s)) C

/-- **Every semiring map carries closed-sum preservation.** -/
theorem KernelPreserving.mapCoefficients {K L : Type*} [Semiring K] [Semiring L]
    {sourceSpace targetSpace : GSLT} {map : KernelMap K sourceSpace targetSpace}
    (φ : K →+* L) (preserves : KernelPreserving map) :
    KernelPreserving (map.mapCoefficients φ) := by
  intro label s C closed
  have eq := preserves label s C closed
  rw [closedSum_source_coefficients map φ label s C,
    closedSum_target_coefficients map φ label s
      (fun t => C ((map.mapCoefficients φ).readBack t))]
  have sameRead :
      closedSum (map.target.kernel (map.labelMap label) (map.term s))
        (fun t => C ((map.mapCoefficients φ).readBack t)) =
        closedSum (map.target.kernel (map.labelMap label) (map.term s))
          (fun t => C (map.readBack t)) := rfl
  rw [sameRead, eq]

/-- **Positive.** The identity remains preserving after "is nonzero". -/
theorem identity_supportHom_preserving :
    KernelPreserving ((kernelId (outcomeSystem (1 : ℕ))).mapCoefficients
      (WeightedSystem.supportHom ℕ nat_noCancellation)) :=
  KernelPreserving.mapCoefficients _ (kernelId_preserving _)

/-! ## Squaring is not a semiring map, and it breaks preservation -/

inductive SquarePoint where
  | star
  deriving DecidableEq

inductive SquareWing where
  | left
  | right
  deriving DecidableEq

def squareRead : SquareWing → SquarePoint := fun _ => .star

noncomputable def starRow : SquarePoint →₀ ℕ :=
  Finsupp.single .star 2

noncomputable def wingRow : SquareWing →₀ ℕ :=
  Finsupp.onFinset {.left, .right} (fun _ => 1) (by
    intro wing _
    cases wing <;> simp)

noncomputable def starRowSq : SquarePoint →₀ ℕ :=
  Finsupp.mapRange (fun n : ℕ => n * n) (by simp) starRow

noncomputable def wingRowSq : SquareWing →₀ ℕ :=
  Finsupp.mapRange (fun n : ℕ => n * n) (by simp) wingRow

theorem starRowSq_single : starRowSq = Finsupp.single SquarePoint.star 4 := by
  ext point
  cases point
  rw [starRowSq, Finsupp.mapRange_apply, starRow, Finsupp.single_eq_same,
    Finsupp.single_eq_same]

theorem wingRowSq_eq : wingRowSq = wingRow := by
  ext wing
  cases wing <;> rw [wingRowSq, Finsupp.mapRange_apply, wingRow, Finsupp.onFinset_apply]

theorem wingRow_closedSum (C : SquareWing → Prop) :
    closedSum wingRow C =
      (if C .left then 1 else 0) + (if C .right then 1 else 0) := by
  unfold wingRow
  rw [closedSum_onFinset]
  have pair : ({SquareWing.left, SquareWing.right} : Finset SquareWing) =
      insert .left {.right} := by
    ext wing
    simp
  rw [pair, Finset.sum_insert (by decide), Finset.sum_singleton]

noncomputable def squareSource : WeightedSystem (GSLT.stepFree SquarePoint) ℕ where
  Atom := Unit
  observes := fun _ _ => True
  observes_resp := fun _ _ _ _ => Iff.rfl
  Label := Unit
  kernel := fun _ _ => starRow
  kernel_resp := by
    intro _ _ _ same _ _
    cases same
    rfl

noncomputable def squareTarget : WeightedSystem (GSLT.stepFree SquareWing) ℕ where
  Atom := Unit
  observes := fun _ _ => True
  observes_resp := fun _ _ _ _ => Iff.rfl
  Label := Unit
  kernel := fun _ _ => wingRow
  kernel_resp := by
    intro _ _ _ same _ _
    cases same
    rfl

noncomputable def squareSourceSq : WeightedSystem (GSLT.stepFree SquarePoint) ℕ where
  Atom := Unit
  observes := fun _ _ => True
  observes_resp := fun _ _ _ _ => Iff.rfl
  Label := Unit
  kernel := fun _ _ => starRowSq
  kernel_resp := by
    intro _ _ _ same _ _
    cases same
    rfl

noncomputable def squareTargetSq : WeightedSystem (GSLT.stepFree SquareWing) ℕ where
  Atom := Unit
  observes := fun _ _ => True
  observes_resp := fun _ _ _ _ => Iff.rfl
  Label := Unit
  kernel := fun _ _ => wingRowSq
  kernel_resp := by
    intro _ _ _ same _ _
    cases same
    rfl

/-- Weights `2` on the star and `1` on each wing. -/
noncomputable def squareMap :
    KernelMap ℕ (GSLT.stepFree SquarePoint) (GSLT.stepFree SquareWing) where
  source := squareSource
  target := squareTarget
  term := fun _ => .left
  labelMap := id
  readBack := squareRead
  readBack_resp := by
    intro _ _ equivalent
    cases equivalent
    rfl

/-- The same map after squaring every coefficient. -/
noncomputable def squareMapSq :
    KernelMap ℕ (GSLT.stepFree SquarePoint) (GSLT.stepFree SquareWing) where
  source := squareSourceSq
  target := squareTargetSq
  term := fun _ => .left
  labelMap := id
  readBack := squareRead
  readBack_resp := by
    intro _ _ equivalent
    cases equivalent
    rfl

theorem SquarePoint.eq_star (point : SquarePoint) : point = .star := by
  cases point
  rfl

theorem closedSum_starRow (C : SquarePoint → Prop) :
    closedSum starRow C = if C .star then 2 else 0 := by
  rw [starRow, closedSum_single]

theorem closedSum_star_four :
    closedSum (Finsupp.single SquarePoint.star 4) (fun _ : SquarePoint => True) = 4 := by
  rw [closedSum_single, if_pos True.intro]

theorem wingRow_all : closedSum wingRow (fun _ : SquareWing => True) = 2 := by
  rw [wingRow_closedSum]
  simp only [if_true]

theorem Unit.eq_unit (point : Unit) : point = () := by
  cases point
  rfl

/-- **Before squaring.** `2 = 1 + 1` for every equation-closed set. -/
theorem squareMap_preserving : KernelPreserving squareMap := by
  intro label sourceTerm C _
  have labelUnit : label = () := Unit.eq_unit label
  have point : sourceTerm = .star := SquarePoint.eq_star sourceTerm
  subst labelUnit
  subst point
  have sourceSide :
      closedSum (squareMap.source.kernel () .star) C =
        if C .star then 2 else 0 := by
    have row : squareMap.source.kernel () .star = starRow := rfl
    exact (congrArg (fun f => closedSum f C) row).trans (closedSum_starRow C)
  have targetSide :
      closedSum (squareMap.target.kernel (squareMap.labelMap ()) (squareMap.term .star))
        (fun wing => C (squareMap.readBack wing)) =
        (if C .star then 1 else 0) + (if C .star then 1 else 0) := by
    have fold :
        closedSum (squareMap.target.kernel (squareMap.labelMap ()) (squareMap.term .star))
          (fun wing => C (squareMap.readBack wing)) =
          closedSum wingRow (fun wing => C (squareRead wing)) := rfl
    have summed := wingRow_closedSum (fun wing => C (squareRead wing))
    exact fold.trans (summed.trans (by rfl))
  have arith :
      (if C .star then 2 else 0) =
        (if C .star then 1 else 0) + (if C .star then 1 else 0) := by
    by_cases holds : C .star
    · simp [holds]
    · simp [holds]
  exact sourceSide.trans (arith.trans targetSide.symm)

/-- **Negative.** Squaring is not a semiring map, and `4 ≠ 1 + 1`. -/
theorem square_true_closed :
    ∀ x y : (GSLT.stepFree SquarePoint).Term, (GSLT.stepFree SquarePoint).Equiv x y →
      ((fun _ => True) x ↔ (fun _ => True) y) := by
  intro _ _ equivalent
  cases equivalent
  rfl

theorem squareMapSq_not_preserving : ¬ KernelPreserving squareMapSq := by
  intro preserves
  have sourceSide :
      closedSum (squareMapSq.source.kernel () .star) (fun _ => True) = 4 := by
    have kernelEq :
        squareMapSq.source.kernel () .star = Finsupp.single .star 4 :=
      starRowSq_single
    exact (congrArg (fun f => closedSum f (fun _ => True)) kernelEq).trans closedSum_star_four
  have targetSide :
      closedSum (squareMapSq.target.kernel (squareMapSq.labelMap ()) (squareMapSq.term .star))
        (fun wing => (fun _ => True) (squareMapSq.readBack wing)) = 2 := by
    have kernelEq :
        squareMapSq.target.kernel (squareMapSq.labelMap ()) (squareMapSq.term .star) = wingRow :=
      wingRowSq_eq
    exact (congrArg (fun f => closedSum f (fun _ => True)) kernelEq).trans wingRow_all
  have eq := preserves () .star (fun _ => True) square_true_closed
  exact absurd (sourceSide.symm.trans (eq.trans targetSide)) (by decide)

/-! ## Support systems -/

/-- **Support preservation.** The support system of the source meets an
equation-closed set exactly when the support system of the image has a step
whose read-back lies in that set. -/
def SupportPreserving {sourceSpace targetSpace : GSLT}
    (map : KernelMap OrBool sourceSpace targetSpace) : Prop :=
  ∀ (label : map.source.Label) (s : sourceSpace.Term) (C : sourceSpace.Term → Prop),
    (∀ x y, sourceSpace.Equiv x y → (C x ↔ C y)) →
      ((∃ target, (map.source.support OrBool.noCancellation).act label s target ∧ C target) ↔
        ∃ target, (map.target.support OrBool.noCancellation).act
          (map.labelMap label) (map.term s) target ∧ C (map.readBack target))

theorem support_meets_iff {S : GSLT} {K : Type*} [Semiring K]
    (W : WeightedSystem S K) (noCancel : NoCancellation K)
    (label : W.Label) (s : S.Term) (C : S.Term → Prop)
    (closed : ∀ x y, S.Equiv x y → (C x ↔ C y)) :
    (∃ target, (W.support noCancel).act label s target ∧ C target) ↔
      ∃ x ∈ (W.kernel label s).support, C x := by
  constructor
  · rintro ⟨target, acted, holds⟩
    rcases acted with ⟨x, member, equivalent⟩
    exact ⟨x, member, (closed x target equivalent).mpr holds⟩
  · rintro ⟨x, member, holds⟩
    exact ⟨x, ⟨x, member, S.equations.iseqv.refl x⟩, holds⟩

theorem orBool_eq_one_of_ne_zero {a : OrBool} (nonzero : a ≠ 0) : a = 1 := by
  cases a with
  | mk value =>
    cases value
    · exact absurd (OrBool.ext' rfl) nonzero
    · rfl

theorem supportHom_zero_iff_closedSum {K : Type*} [Semiring K]
    (noCancel : NoCancellation K) (a b : K) :
    WeightedSystem.supportHom K noCancel a = WeightedSystem.supportHom K noCancel b ↔ (a = 0 ↔ b = 0) := by
  constructor
  · intro same
    constructor
    · intro zeroA
      exact (WeightedSystem.supportHom_eq_zero_iff K noCancel b).mp (by rw [← same, zeroA, map_zero])
    · intro zeroB
      exact (WeightedSystem.supportHom_eq_zero_iff K noCancel a).mp (by rw [same, zeroB, map_zero])
  · intro iffZero
    by_cases zeroA : a = 0
    · have zeroB := iffZero.mp zeroA
      rw [zeroA, zeroB, map_zero]
    · have zeroB : b ≠ 0 := fun zero => zeroA (iffZero.mpr zero)
      have nonzeroA : WeightedSystem.supportHom K noCancel a ≠ 0 :=
        fun zero => zeroA ((WeightedSystem.supportHom_eq_zero_iff K noCancel a).mp zero)
      have nonzeroB : WeightedSystem.supportHom K noCancel b ≠ 0 :=
        fun zero => zeroB ((WeightedSystem.supportHom_eq_zero_iff K noCancel b).mp zero)
      exact (orBool_eq_one_of_ne_zero nonzeroA).trans (orBool_eq_one_of_ne_zero nonzeroB).symm

theorem mem_support_coefficients {K L : Type*} [Semiring K] [Semiring L]
    {S : GSLT} (W : WeightedSystem S K) (φ : K →+* L)
    (label : W.Label) (s : S.Term) (x : S.Term) :
    x ∈ ((W.mapCoefficients φ).kernel label s).support ↔ φ (W.kernel label s x) ≠ 0 := by
  simp only [WeightedSystem.mapCoefficients, Finsupp.mem_support_iff, Finsupp.mapRange_apply]

theorem mem_support_supportHom {K : Type*} [Semiring K] (noCancel : NoCancellation K)
    {S : GSLT} (W : WeightedSystem S K) (label : W.Label) (s x : S.Term) :
    x ∈ ((W.mapCoefficients (WeightedSystem.supportHom K noCancel)).kernel label s).support ↔
      x ∈ (W.kernel label s).support := by
  rw [mem_support_coefficients, Finsupp.mem_support_iff]
  exact not_congr (WeightedSystem.supportHom_eq_zero_iff K noCancel _)

/-- **Along `supportHom`, preservation is support preservation.** An
equation-closed set meets a step of the source support system exactly when it
meets the read-back of a step of the image support system. -/
theorem kernelPreserving_supportHom_iff {K : Type*} [Semiring K]
    (noCancel : NoCancellation K) {sourceSpace targetSpace : GSLT}
    (map : KernelMap K sourceSpace targetSpace) :
    KernelPreserving (map.mapCoefficients (WeightedSystem.supportHom K noCancel)) ↔
      SupportPreserving (map.mapCoefficients (WeightedSystem.supportHom K noCancel)) := by
  let φ := WeightedSystem.supportHom K noCancel
  let image := map.mapCoefficients φ
  have memSource : ∀ (label : map.source.Label) (s : sourceSpace.Term) (x : sourceSpace.Term),
      x ∈ (image.source.kernel label s).support ↔
        x ∈ (map.source.kernel label s).support := by
    intro label s x
    exact mem_support_supportHom noCancel map.source label s x
  have memTarget : ∀ (label : map.target.Label) (s : targetSpace.Term) (x : targetSpace.Term),
      x ∈ (image.target.kernel label s).support ↔
        x ∈ (map.target.kernel label s).support := by
    intro label s x
    exact mem_support_supportHom noCancel map.target label s x
  constructor
  · intro preserves label s C closed
    have sums := preserves label s C closed
    have sourceMapped := closedSum_source_coefficients map φ label s C
    have targetMapped :=
      closedSum_target_coefficients map φ label s (fun t => C (image.readBack t))
    rw [sourceMapped, targetMapped] at sums
    have nonzeroIff :
        closedSum (map.source.kernel label s) C ≠ 0 ↔
          closedSum (map.target.kernel (map.labelMap label) (map.term s))
            (fun t => C (image.readBack t)) ≠ 0 :=
      not_congr ((supportHom_zero_iff_closedSum noCancel _ _).mp sums)
    rw [support_meets_iff image.source OrBool.noCancellation label s C closed,
      support_meets_iff image.target OrBool.noCancellation (image.labelMap label)
        (image.term s) (fun t => C (image.readBack t))
        (fun x y equivalent => closed _ _ (image.readBack_resp equivalent))]
    constructor
    · rintro ⟨x, member, holds⟩
      have nonzero :=
        (closedSum_ne_zero_iff noCancel _ _).mpr ⟨x, (memSource label s x).mp member, holds⟩
      obtain ⟨y, memberT, holdsT⟩ :=
        (closedSum_ne_zero_iff noCancel _ _).mp (nonzeroIff.mp nonzero)
      exact ⟨y, (memTarget (image.labelMap label) (image.term s) y).mpr memberT, holdsT⟩
    · rintro ⟨y, member, holds⟩
      have nonzero :
          closedSum (map.target.kernel (map.labelMap label) (map.term s))
            (fun t => C (image.readBack t)) ≠ 0 :=
        (closedSum_ne_zero_iff noCancel _ (fun t => C (image.readBack t))).mpr
          ⟨y, (memTarget (map.labelMap label) (map.term s) y).mp member, holds⟩
      obtain ⟨x, memberS, holdsS⟩ :=
        (closedSum_ne_zero_iff noCancel _ _).mp (nonzeroIff.mpr nonzero)
      exact ⟨x, (memSource label s x).mpr memberS, holdsS⟩
  · intro supports label s C closed
    rw [closedSum_source_coefficients map φ label s C,
      closedSum_target_coefficients map φ label s (fun t => C (image.readBack t))]
    apply (supportHom_zero_iff_closedSum noCancel _ _).mpr
    have meets := supports label s C closed
    rw [support_meets_iff image.source OrBool.noCancellation label s C closed,
      support_meets_iff image.target OrBool.noCancellation (image.labelMap label)
        (image.term s) (fun t => C (image.readBack t))
        (fun x y equivalent => closed _ _ (image.readBack_resp equivalent))] at meets
    have nonzeroIff :
        closedSum (map.source.kernel label s) C ≠ 0 ↔
          closedSum (map.target.kernel (map.labelMap label) (map.term s))
            (fun t => C (image.readBack t)) ≠ 0 := by
      constructor
      · intro nonzero
        obtain ⟨x, member, holds⟩ := (closedSum_ne_zero_iff noCancel _ _).mp nonzero
        obtain ⟨y, memberT, holdsT⟩ :=
          meets.mp ⟨x, (memSource label s x).mpr member, holds⟩
        exact (closedSum_ne_zero_iff noCancel _
            (fun t => C (image.readBack t))).mpr
          ⟨y, (memTarget (map.labelMap label) (map.term s) y).mp memberT, holdsT⟩
      · intro nonzero
        obtain ⟨y, member, holds⟩ := (closedSum_ne_zero_iff noCancel _ _).mp nonzero
        obtain ⟨x, memberS, holdsS⟩ :=
          meets.mpr ⟨y, (memTarget (image.labelMap label) (image.term s) y).mpr member, holds⟩
        exact (closedSum_ne_zero_iff noCancel _ _).mpr
          ⟨x, (memSource label s x).mp memberS, holdsS⟩
    constructor
    · intro zeroS
      by_contra nonzeroT
      exact nonzeroIff.mpr nonzeroT zeroS
    · intro zeroT
      by_contra nonzeroS
      exact nonzeroIff.mp nonzeroS zeroT

/-- **Positive.** The identity preserves supports. -/
theorem identity_supportPreserving :
    SupportPreserving ((kernelId (outcomeSystem (1 : ℕ))).mapCoefficients
      (WeightedSystem.supportHom ℕ nat_noCancellation)) :=
  (kernelPreserving_supportHom_iff nat_noCancellation
    (kernelId (outcomeSystem (1 : ℕ)))).mp identity_supportHom_preserving

/-- A dead fan: every target coefficient is zero. -/
noncomputable def deadFan : KernelMap ℕ quiet (fanSpace 2) where
  source := outcomeSystem 1
  target := fanSystem 2 0
  term := quietEmbed 2 (by decide)
  labelMap := id
  readBack := fanRead
  readBack_resp := by
    intro _ _ equivalent
    cases equivalent
    rfl

theorem quiet_true_closed :
    ∀ x y : quiet.Term, quiet.Equiv x y →
      ((fun t => t = some true) x ↔ (fun t => t = some true) y) := by
  intro _ _ equivalent
  cases equivalent
  rfl

theorem dead_fan_raw_target :
    closedSum ((fanSystem 2 (0 : ℕ)).kernel () none) (fun t => fanRead t = some true) = 0 := by
  show closedSum (fanStep 2 (0 : ℕ) none) (fun t => fanRead t = some true) = 0
  rw [fanStep, closedSum_fanKernel]
  refine Finset.sum_eq_zero fun _ _ => ?_
  split_ifs <;> rfl

/-- **Negative.** After `supportHom`, the source closed sum on `some true` is `1`
and every target coefficient is zero, so the dead fan does not preserve supports. -/
theorem deadFan_not_supportPreserving :
    ¬ SupportPreserving (deadFan.mapCoefficients (WeightedSystem.supportHom ℕ nat_noCancellation)) := by
  intro supports
  have preserves :=
    (kernelPreserving_supportHom_iff nat_noCancellation deadFan).mpr supports
  let φ := WeightedSystem.supportHom ℕ nat_noCancellation
  have eq := preserves () none (fun t => t = some true) quiet_true_closed
  have sourceSide :
      closedSum ((deadFan.mapCoefficients φ).source.kernel () none) (fun t => t = some true) = 1 :=
    (closedSum_source_coefficients deadFan φ () none (fun t => t = some true)).trans
      ((congrArg φ closedSum_doubled_source).trans (RingHom.map_one φ))
  have rawTarget :
      closedSum (deadFan.target.kernel (deadFan.labelMap ()) (deadFan.term none))
        (fun t => deadFan.readBack t = some true) = 0 := by
    have fold :
        closedSum (deadFan.target.kernel (deadFan.labelMap ()) (deadFan.term none))
          (fun t => deadFan.readBack t = some true) =
          closedSum ((fanSystem 2 (0 : ℕ)).kernel () none) (fun t => fanRead t = some true) := rfl
    exact fold.trans dead_fan_raw_target
  have targetSide :
      closedSum ((deadFan.mapCoefficients φ).target.kernel
          ((deadFan.mapCoefficients φ).labelMap ()) ((deadFan.mapCoefficients φ).term none))
        (fun t => (fun s => s = some true) ((deadFan.mapCoefficients φ).readBack t)) = 0 :=
    (closedSum_target_coefficients deadFan φ () none
      (fun t => (fun s => s = some true) (deadFan.readBack t))).trans
      ((congrArg φ rawTarget).trans (RingHom.map_zero φ))
  exact absurd (sourceSide.symm.trans (eq.trans targetSide)) (by decide)

end Mettapedia.Logic.HostingStyles.Weighted
