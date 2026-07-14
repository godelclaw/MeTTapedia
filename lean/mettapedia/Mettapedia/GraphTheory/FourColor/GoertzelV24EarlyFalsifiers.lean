import Mettapedia.GraphTheory.FourColor.GoertzelV24CurvatureScope

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24EarlyFalsifiers

open GoertzelV24CurvatureScope

/-- A facial desert: every face in the region is rainbow, equivalently no
face boundary in the region is bicolored. -/
def FacialDesert
    {Face : Type*}
    (faceInRegion : Face → Prop)
    (faceBoundaryIsBicolored : Face → Prop) : Prop :=
  ∀ face : Face, faceInRegion face → ¬ faceBoundaryIsBicolored face

/-- The stronger short-cycle condition: no Kempe cycle in the region up to a
specified length. This quantifies over cycles, not faces, and is not identified
with `FacialDesert`. -/
def ShortKempeCycleDesert
    {Cycle : Type*}
    (cycleInRegion : Cycle → Prop)
    (isKempeCycle : Cycle → Prop)
    (cycleLength : Cycle → Nat)
    (maximumLength : Nat) : Prop :=
  ∀ cycle : Cycle,
    cycleInRegion cycle →
    isKempeCycle cycle →
    cycleLength cycle <= maximumLength →
    False

/-- The explicit extra hypothesis needed before a facial test can control all
short Kempe cycles: every relevant short Kempe cycle must itself be a face
boundary. -/
def RelevantShortKempeCyclesAreFacial
    {Cycle Face : Type*}
    (cycleInRegion : Cycle → Prop)
    (isKempeCycle : Cycle → Prop)
    (cycleLength : Cycle → Nat)
    (maximumLength : Nat)
    (isBoundaryOf : Cycle → Face → Prop) : Prop :=
  ∀ cycle : Cycle,
    cycleInRegion cycle →
    isKempeCycle cycle →
    cycleLength cycle <= maximumLength →
    ∃ face : Face, isBoundaryOf cycle face

/-- Corrected general chiral-annulus statement: monodromy constrains total
enclosed combinatorial curvature modulo three, rather than the pentagon count
alone when longer faces may contribute negative curvature. -/
def ChiralAnnulusTotalEnclosedCurvatureModThreeStatement
    {Annulus : Type*}
    (isAllChiralHexagonalAnnulus : Annulus → Prop)
    (enclosedFaceSizes : Annulus → List Nat) : Prop :=
  ∀ annulus : Annulus,
    isAllChiralHexagonalAnnulus annulus →
    faceSizeCurvatureSum (enclosedFaceSizes annulus) % 3 = 0

/-- Honest 5/6-face specialization of the chiral-annulus statement. -/
def ChiralAnnulusFiveSixFacePentagonCountModThreeStatement
    {Annulus : Type*}
    (isAllChiralHexagonalAnnulus : Annulus → Prop)
    (enclosedFaceSizes : Annulus → List Nat) : Prop :=
  ∀ annulus : Annulus,
    isAllChiralHexagonalAnnulus annulus →
    FullereneFaceRestriction (enclosedFaceSizes annulus) →
    ((enclosedFaceSizes annulus).count 5 : Int) % 3 = 0

/-- With only pentagons and hexagons, total face curvature is exactly the
number of pentagons. -/
theorem faceSizeCurvatureSum_eq_pentagonCount_of_fullerene
    (faceSizes : List Nat) (hfaces : FullereneFaceRestriction faceSizes) :
    faceSizeCurvatureSum faceSizes = (faceSizes.count 5 : Int) := by
  induction faceSizes with
  | nil => simp [faceSizeCurvatureSum]
  | cons n rest ih =>
      have hn : n = 5 ∨ n = 6 := hfaces n (by simp)
      have hrest : FullereneFaceRestriction rest := by
        intro m hm
        exact hfaces m (by simp [hm])
      have htail := ih hrest
      unfold faceSizeCurvatureSum at htail
      rcases hn with rfl | rfl
      · unfold faceSizeCurvatureSum
        simp only [List.map_cons, List.sum_cons, List.count_cons]
        rw [htail]
        norm_num
        omega
      · unfold faceSizeCurvatureSum
        simp only [List.map_cons, List.sum_cons, List.count_cons]
        rw [htail]
        norm_num

theorem totalCurvatureModThree_iff_pentagonCountModThree_of_fullerene
    (faceSizes : List Nat) (hfaces : FullereneFaceRestriction faceSizes) :
    faceSizeCurvatureSum faceSizes % 3 = 0 ↔
      (faceSizes.count 5 : Int) % 3 = 0 := by
  rw [faceSizeCurvatureSum_eq_pentagonCount_of_fullerene faceSizes hfaces]

/-- A length is obtained from a preperiod by padding with whole cycles. -/
def HasPeriodicPaddingLength (preperiod period length : Nat) : Prop :=
  ∃ repetitions : Nat, length = preperiod + repetitions * period

/-- Corrected L2 fallback. A relevant profile reaches a recurrent profile
after a preperiod, the recurrent profile has a positive-period return, and
padding is guaranteed only in the corresponding length congruence class.
This does not assert a self-loop or acceptance at every larger length. -/
def PeriodicCorridorPumpingWithCongruence
    {Profile : Type*}
    (isAliveRelevant : Profile → Prop)
    (reachesInExactly : Nat → Profile → Profile → Prop) : Prop :=
  ∀ start : Profile,
    isAliveRelevant start →
    ∃ cycleEntry : Profile, ∃ preperiod period : Nat,
      0 < period ∧
      reachesInExactly preperiod start cycleEntry ∧
      reachesInExactly period cycleEntry cycleEntry ∧
      ∀ length : Nat,
        HasPeriodicPaddingLength preperiod period length →
        reachesInExactly length start cycleEntry

end GoertzelV24EarlyFalsifiers

end Mettapedia.GraphTheory.FourColor
