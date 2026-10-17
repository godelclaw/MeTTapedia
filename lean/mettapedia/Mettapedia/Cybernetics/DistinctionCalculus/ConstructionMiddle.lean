import Mettapedia.Cybernetics.DistinctionCalculus.Exclusion

/-!
# Construction removes the middle

Dharmakīrti's law of contradiction, in Stcherbatsky's account, divides the universe of
discourse into a constructed part and its complement, with "nothing in the middle".  In the
distinction calculus an observer's indistinguishability is reflexive and symmetric but need
not be transitive, and the failure of transitivity, the sorites, carries the structure.  The
closure of an observer identifies whatever a chain of indistinguishable steps connects.  This
module relates the two: the dichotomy holds for the concepts of the closure, and fails for the
observer exactly where the sorites lives.

* **A middle is a sorites triple.**  An instance in neither a concept nor its exclusion is
  indistinguishable from a member and from an excluded instance, which exclude each other
  (`middle_sorites`).
* **No middle is saturation.**  A class and its exclusion cover everything exactly when the
  class is closed under indistinguishability (`union_excluded_eq_univ_iff_saturated`); a
  saturated class is a concept (`isConcept_of_saturated`).
* **Perception and construction.**  The constructed observer excludes two instances when no
  chain of indistinguishable steps connects them (`constructed`).
  - Saturation under the observer and under its construction coincide
    (`saturated_constructed_iff`).
  - The concepts of the observer without a middle are exactly the concepts of its construction
    (`noMiddle_concept_iff`).
  - Every concept of the construction has no middle (`union_excluded_constructed`).
* **Graded observers.**  Read a tolerance at a level `s`: two instances are apart when their
  similarity is below `s` (`Tolerance.LevelApart`).  Every concept at every level in `(0, 1]`
  has no middle exactly when the tolerance is ultrametric
  (`Tolerance.noMiddle_all_levels_iff_ultrametric`).  The metric law is not enough.

Controls.
* The three-instance observer of `Exclusion.Control` has a concept with a middle; its
  construction separates nothing (`Control.constructed_none`), and the concept `{0}` of the
  observer is not a concept of the construction (`Control.zero_not_constructed_concept`).
* A metric observer on three instances is not ultrametric and has a concept with a middle at
  level `3/4` (`Control.metricTolerance_metric`, `Control.metricTolerance_not_ultrametric`,
  `Control.metric_middle`).

References: Th. Stcherbatsky, *Buddhist Logic*, vol. 1 (1932), pp. 403 and 417;
B. Goertzel, *The Distinction Calculus* (corrected September 2026), Section 2.3, on the
transitivity classes, the closures and the sorites kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus.Exclusion

open Set

universe u

variable {V : Type u} {excludes : V → V → Prop}

/-- A class is **saturated** when it is closed under indistinguishability: whatever does not
exclude a member is a member. -/
def Saturated (excludes : V → V → Prop) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y, ¬ excludes x y → y ∈ S

/-- **The constructed observer**: two instances are excluded when no chain of
indistinguishable steps connects them. -/
def constructed (excludes : V → V → Prop) (x y : V) : Prop :=
  ¬ Relation.EqvGen (fun a b => ¬ excludes a b) x y

theorem constructed_symm (x y : V) : constructed excludes x y → constructed excludes y x :=
  fun notXY yx => notXY (Relation.EqvGen.symm _ _ yx)

theorem constructed_irrefl (x : V) : ¬ constructed excludes x x :=
  fun h => h (Relation.EqvGen.refl x)

theorem not_constructed_iff (x y : V) :
    ¬ constructed excludes x y ↔ Relation.EqvGen (fun a b => ¬ excludes a b) x y :=
  not_not

/-- The construction's indistinguishability is transitive. -/
theorem not_constructed_trans (x y z : V) :
    ¬ constructed excludes x y → ¬ constructed excludes y z → ¬ constructed excludes x z := by
  rw [not_constructed_iff, not_constructed_iff, not_constructed_iff]
  exact Relation.EqvGen.trans x y z

/-- The construction excludes only what the observer excludes. -/
theorem excludes_of_constructed {x y : V} (h : constructed excludes x y) : excludes x y :=
  Classical.byContradiction fun notXY => h (Relation.EqvGen.rel x y notXY)

/-- **Construction has no middle**: every concept of the construction, with its exclusion,
covers everything. -/
theorem union_excluded_constructed {S : Set V} (concept : IsConcept (constructed excludes) S) :
    S ∪ excluded (constructed excludes) S = univ :=
  (union_excluded_eq_univ_iff (excludes := constructed excludes) constructed_symm).mpr
    not_constructed_trans S concept

section Symmetric

variable (symm : ∀ x y, excludes x y → excludes y x)
include symm

/-- **A middle instance is the middle of a sorites triple**: it is indistinguishable from a
member and from an excluded instance, and these two exclude each other. -/
theorem middle_sorites {S : Set V} (concept : IsConcept excludes S) {y : V}
    (notIn : y ∉ S) (notOut : y ∉ excluded excludes S) :
    ∃ x ∈ S, ∃ z ∈ excluded excludes S, ¬ excludes x y ∧ ¬ excludes y z ∧ excludes x z := by
  rw [mem_excluded] at notOut
  push Not at notOut
  obtain ⟨x, inS, notYX⟩ := notOut
  have notIn' : y ∉ excluded excludes (excluded excludes S) := by rwa [concept]
  rw [mem_excluded] at notIn'
  push Not at notIn'
  obtain ⟨z, zOut, notYZ⟩ := notIn'
  exact ⟨x, inS, z, zOut, fun h => notYX (symm x y h), notYZ, symm z x (zOut inS)⟩

/-- **No middle is saturation.** -/
theorem union_excluded_eq_univ_iff_saturated (S : Set V) :
    S ∪ excluded excludes S = univ ↔ Saturated excludes S := by
  constructor
  · intro cover x inS y notXY
    have member : y ∈ S ∪ excluded excludes S := by
      rw [cover]
      trivial
    rcases member with inside | outside
    · exact inside
    · exact absurd (symm y x (outside inS)) notXY
  · intro saturated
    apply eq_univ_of_forall
    intro y
    by_cases inS : y ∈ S
    · exact Or.inl inS
    · refine Or.inr (mem_excluded.mpr fun x xIn => ?_)
      by_contra notYX
      exact inS (saturated x xIn y fun h => notYX (symm x y h))

/-- Saturation under the observer and under its construction coincide. -/
theorem saturated_constructed_iff (S : Set V) :
    Saturated (constructed excludes) S ↔ Saturated excludes S := by
  constructor
  · intro saturated x inS y notXY
    exact saturated x inS y fun h => h (Relation.EqvGen.rel x y notXY)
  · intro saturated
    have closed : ∀ a b, Relation.EqvGen (fun a b => ¬ excludes a b) a b → (a ∈ S ↔ b ∈ S) := by
      intro a b chain
      induction chain with
      | rel a b notAB =>
          exact ⟨fun aIn => saturated a aIn b notAB,
            fun bIn => saturated b bIn a fun h => notAB (symm b a h)⟩
      | refl a => exact Iff.rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ihAB ihBC => exact ihAB.trans ihBC
    intro x inS y notXY
    exact (closed x y ((not_constructed_iff x y).mp notXY)).mp inS

/-- **A saturated class is a concept**, and its exclusion is its complement. -/
theorem isConcept_of_saturated (irrefl : ∀ x, ¬ excludes x x) {S : Set V}
    (saturated : Saturated excludes S) : IsConcept excludes S := by
  have complEq : ∀ T : Set V, Saturated excludes T → excluded excludes T = Tᶜ := by
    intro T satT
    ext y
    constructor
    · intro member inT
      exact irrefl y (member inT)
    · intro notIn
      refine mem_excluded.mpr fun x xIn => ?_
      by_contra notYX
      exact notIn (satT x xIn y fun h => notYX (symm x y h))
  have complSat : Saturated excludes Sᶜ := by
    intro x xOut y notXY yIn
    exact xOut (saturated y yIn x fun h => notXY (symm y x h))
  rw [IsConcept, complEq S saturated, complEq Sᶜ complSat, compl_compl]

/-- **The concepts of the observer without a middle are exactly the concepts of its
construction.** -/
theorem noMiddle_concept_iff (irrefl : ∀ x, ¬ excludes x x) (S : Set V) :
    (IsConcept excludes S ∧ S ∪ excluded excludes S = univ) ↔
      IsConcept (constructed excludes) S := by
  constructor
  · rintro ⟨-, cover⟩
    exact isConcept_of_saturated (excludes := constructed excludes) constructed_symm
      constructed_irrefl
      ((saturated_constructed_iff symm S).mpr
        ((union_excluded_eq_univ_iff_saturated symm S).mp cover))
  · intro concept
    have saturated : Saturated excludes S :=
      (saturated_constructed_iff symm S).mp
        ((union_excluded_eq_univ_iff_saturated (excludes := constructed excludes)
          constructed_symm S).mp (union_excluded_constructed concept))
    exact ⟨isConcept_of_saturated symm irrefl saturated,
      (union_excluded_eq_univ_iff_saturated symm S).mpr saturated⟩

end Symmetric

end Mettapedia.Cybernetics.DistinctionCalculus.Exclusion

/-! ## Graded observers -/

namespace Mettapedia.Cybernetics.DistinctionCalculus.Tolerance

open Set Mettapedia.Cybernetics.DistinctionCalculus.Exclusion

universe v

variable {W : Type v} {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Apart at level `s`**: similarity below `s`. -/
def LevelApart (a : Tolerance W R) (s : R) (x y : W) : Prop :=
  a.similarity x y < s

/-- **The ultrametric law**: similarity across two steps is at least that of the weaker
step. -/
def Ultrametric (a : Tolerance W R) : Prop :=
  ∀ x y z, min (a.similarity x y) (a.similarity y z) ≤ a.similarity x z

theorem levelApart_symm (a : Tolerance W R) (s : R) (x y : W) :
    a.LevelApart s x y → a.LevelApart s y x := by
  unfold LevelApart
  rw [a.symmetric]
  exact id

theorem levelApart_irrefl (a : Tolerance W R) {s : R} (le : s ≤ 1) (x : W) :
    ¬ a.LevelApart s x x := by
  unfold LevelApart
  rw [a.reflexive]
  exact not_lt.mpr le

/-- **Every concept at every level has no middle exactly for ultrametric observers.** -/
theorem noMiddle_all_levels_iff_ultrametric (a : Tolerance W R) :
    (∀ s : R, 0 < s → s ≤ 1 → ∀ S, IsConcept (a.LevelApart s) S →
        S ∪ excluded (a.LevelApart s) S = univ) ↔ a.Ultrametric := by
  constructor
  · intro cover x y z
    by_cases positive : 0 < min (a.similarity x y) (a.similarity y z)
    · have trans := (union_excluded_eq_univ_iff (a.levelApart_symm _)).mp
        (cover _ positive (le_trans (min_le_left _ _) (a.bounded x y)))
      have chain := trans x y z
        (by unfold LevelApart; exact not_lt.mpr (min_le_left _ _))
        (by unfold LevelApart; exact not_lt.mpr (min_le_right _ _))
      unfold LevelApart at chain
      exact not_lt.mp chain
    · exact le_trans (not_lt.mp positive) (a.nonnegative x z)
  · intro ultra s _ _
    apply (union_excluded_eq_univ_iff (a.levelApart_symm s)).mpr
    intro x y z xy yz
    unfold LevelApart at xy yz ⊢
    rw [not_lt] at xy yz ⊢
    exact le_trans (le_min xy yz) (ultra x y z)

end Mettapedia.Cybernetics.DistinctionCalculus.Tolerance

/-! ## Controls -/

namespace Mettapedia.Cybernetics.DistinctionCalculus.Exclusion.Control

open Set Mettapedia.Cybernetics.DistinctionCalculus

/-- **The construction of the three-instance observer separates nothing**: `0` and `2` are
connected through `1`. -/
theorem constructed_none (x y : Fin 3) : ¬ constructed tolerance.Apart x y := by
  have toOne : ∀ z : Fin 3, Relation.EqvGen (fun a b => ¬ tolerance.Apart a b) z 1 := by
    intro z
    apply Relation.EqvGen.rel
    rw [apart_iff]
    fin_cases z <;> decide
  rw [not_constructed_iff]
  exact Relation.EqvGen.trans _ _ _ (toOne x) (Relation.EqvGen.symm _ _ (toOne y))

/-- The concept `{0}` of the observer, which has a middle, is not a concept of the
construction. -/
theorem zero_not_constructed_concept : ¬ IsConcept (constructed tolerance.Apart) {0} := by
  intro concept
  have none : excluded (constructed tolerance.Apart) {0} = ∅ := by
    ext y
    rw [mem_excluded]
    simp only [Set.mem_singleton_iff, forall_eq, Set.mem_empty_iff_false, iff_false]
    exact constructed_none y 0
  rw [IsConcept, none, excluded_empty] at concept
  have one : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := concept ▸ Set.mem_univ 1
  exact absurd one (by decide)

/-- Similarities of a metric observer with a middle at level `3/4`. -/
def metricSimilarity (x y : Fin 3) : ℚ :=
  if x = y then 1 else if (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) then 1 / 2 else 3 / 4

/-- Three instances: neighbours at similarity `3/4`, the ends at `1/2`. -/
def metricTolerance : DistinctionCalculus.Tolerance (Fin 3) where
  similarity := metricSimilarity
  nonnegative x y := by unfold metricSimilarity; split_ifs <;> norm_num
  bounded x y := by unfold metricSimilarity; split_ifs <;> norm_num
  reflexive x := by simp [metricSimilarity]
  symmetric x y := by fin_cases x <;> fin_cases y <;> simp [metricSimilarity]

/-- The observer satisfies the metric law. -/
theorem metricTolerance_metric : metricTolerance.Metric := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [DistinctionCalculus.Tolerance.distance, metricTolerance, metricSimilarity] <;> norm_num

/-- The observer is not ultrametric. -/
theorem metricTolerance_not_ultrametric : ¬ metricTolerance.Ultrametric := by
  intro ultra
  have chain := ultra 0 1 2
  simp [metricTolerance, metricSimilarity] at chain
  norm_num at chain

theorem metric_levelApart_iff (x y : Fin 3) :
    metricTolerance.LevelApart (3 / 4) x y ↔ (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) := by
  fin_cases x <;> fin_cases y <;>
    simp [DistinctionCalculus.Tolerance.LevelApart, metricTolerance, metricSimilarity] <;> norm_num

theorem metric_excluded_zero : excluded (metricTolerance.LevelApart (3 / 4)) {0} = {2} := by
  ext y
  rw [mem_excluded]
  fin_cases y <;> simp [metric_levelApart_iff]

theorem metric_excluded_two : excluded (metricTolerance.LevelApart (3 / 4)) {2} = {0} := by
  ext y
  rw [mem_excluded]
  fin_cases y <;> simp [metric_levelApart_iff]

/-- **The metric law does not remove the middle**: at level `3/4` the concept `{0}` of the
metric observer leaves `1` in neither it nor its exclusion. -/
theorem metric_middle :
    IsConcept (metricTolerance.LevelApart (3 / 4)) {0} ∧
      (1 : Fin 3) ∉ ({0} : Set (Fin 3)) ∪ excluded (metricTolerance.LevelApart (3 / 4)) {0} := by
  refine ⟨?_, ?_⟩
  · rw [IsConcept, metric_excluded_zero, metric_excluded_two]
  · rw [metric_excluded_zero]
    decide

end Mettapedia.Cybernetics.DistinctionCalculus.Exclusion.Control
