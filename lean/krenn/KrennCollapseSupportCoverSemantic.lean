import KrennCollapseSupportCover.GlobalFormula
import KrennCollapseSupportCover.Base

/-!
Semantic use of the global support-cover LRAT certificate.

The LRAT checker proves that the structured CNF is unsatisfiable.  This file
shows that a feasible reduced-collapse support which avoided every certified
stratum would satisfy that CNF, giving the required contradiction.
-/

namespace Krenn.CollapseSupportCover.Semantic

open GlobalFormula

def valuation (pattern : Fin 26 → Prop) : Sat.Valuation := fun index =>
  if coordinate : index < 26 then pattern ⟨index, coordinate⟩
  else if relation : index < 40 then
    relationLeftActive pattern ⟨index - 26, by omega⟩
  else False

/-- A stratum covers a pattern exactly when every literal in its no-cover
clause is false.  This clause-level presentation is the direct semantic seam
to the LRAT certificate. -/
def Covers (stratum : GlobalFormula.Stratum) (pattern : Fin 26 → Prop) : Prop :=
  List.Forall (valuation pattern).neg (stratumClause stratum)

theorem satisfies_iff_not_all_falsified (value : Sat.Valuation)
    (clause : Sat.Clause) :
    value.satisfies clause ↔ ¬ List.Forall value.neg clause := by
  classical
  induction clause with
  | nil => simp [Sat.Valuation.satisfies]
  | cons head tail inductionHypothesis =>
      simp [Sat.Valuation.satisfies, inductionHypothesis]

theorem satisfies_fmla_append (value : Sat.Valuation) {first second : Sat.Fmla}
    (firstSatisfied : value.satisfies_fmla first)
    (secondSatisfied : value.satisfies_fmla second) :
    value.satisfies_fmla (List.append first second) := by
  constructor
  intro clause member
  rcases List.mem_append.mp member with member | member
  · exact firstSatisfied.prop clause member
  · exact secondSatisfied.prop clause member

theorem satisfies_equivalenceClauses (value : Sat.Valuation)
    (qvar : Nat) (items : List Nat)
    (equivalence : value qvar ↔ ∀ item ∈ items, value item) :
    value.satisfies_fmla (equivalenceClauses qvar items) := by
  constructor
  intro clause member
  change clause ∈ List.append
    (items.map (fun item => ([.neg qvar, .pos item] : Sat.Clause)))
    [((.pos qvar) :: items.map .neg : Sat.Clause)] at member
  rcases List.mem_append.mp member with mapped | final
  · obtain ⟨item, itemMember, rfl⟩ := List.mem_map.mp mapped
    rw [satisfies_iff_not_all_falsified]
    intro allFalse
    have allFalseMem := List.forall_iff_forall_mem.mp allFalse
    have qTrue : value qvar := allFalseMem (.neg qvar) (by simp)
    have itemFalse : ¬ value item := allFalseMem (.pos item) (by simp)
    exact itemFalse ((equivalence.mp qTrue) item itemMember)
  · have clauseEquation : clause =
        ((.pos qvar) :: items.map .neg : Sat.Clause) :=
      List.mem_singleton.mp final
    subst clause
    rw [satisfies_iff_not_all_falsified]
    intro allFalse
    have allFalseMem := List.forall_iff_forall_mem.mp allFalse
    have qFalse : ¬ value qvar := allFalseMem (.pos qvar) (by simp)
    apply qFalse
    apply equivalence.mpr
    intro item itemMember
    exact allFalseMem (.neg item) (by simp [itemMember])

theorem feasible_at (pattern : Fin 26 → Prop) (feasible : Feasible pattern)
    (index : Fin 14) :
    relationLeftActive pattern index ↔ relationRightActive pattern index := by
  fin_cases index
  · exact feasible.1
  · exact feasible.2.1
  · exact feasible.2.2.1
  · exact feasible.2.2.2.1
  · exact feasible.2.2.2.2.1
  · exact feasible.2.2.2.2.2.1
  · exact feasible.2.2.2.2.2.2.1
  · exact feasible.2.2.2.2.2.2.2.1
  · exact feasible.2.2.2.2.2.2.2.2.1
  · exact feasible.2.2.2.2.2.2.2.2.2.1
  · exact feasible.2.2.2.2.2.2.2.2.2.2.1
  · exact feasible.2.2.2.2.2.2.2.2.2.2.2.1
  · exact feasible.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact feasible.2.2.2.2.2.2.2.2.2.2.2.2.2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem satisfies_relationFormula (pattern : Fin 26 → Prop)
    (feasible : Feasible pattern) :
    (valuation pattern).satisfies_fmla relationFormula := by
  let value := valuation pattern
  have left (index : Fin 14) (qvar : Nat) (items : List Nat)
      (qvarEquation : qvar = 26 + index) (itemsEquation :
        (∀ item ∈ items, value item) ↔ relationLeftActive pattern index) :
      value.satisfies_fmla (equivalenceClauses qvar items) := by
    apply satisfies_equivalenceClauses
    rw [qvarEquation, itemsEquation]
    have bound : 26 + (index : Nat) < 40 := by omega
    simp [value, valuation, bound]
  have right (index : Fin 14) (qvar : Nat) (items : List Nat)
      (qvarEquation : qvar = 26 + index) (itemsEquation :
        (∀ item ∈ items, value item) ↔ relationRightActive pattern index) :
      value.satisfies_fmla (equivalenceClauses qvar items) := by
    apply satisfies_equivalenceClauses
    rw [qvarEquation, itemsEquation]
    have bound : 26 + (index : Nat) < 40 := by omega
    simpa [value, valuation, bound] using feasible_at pattern feasible index
  have p00 := left 0 26 [0, 7] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p01 := right 0 26 [2, 5] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p02 := left 1 27 [0, 13] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p03 := right 1 27 [17, 23] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p04 := left 2 28 [1, 8] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p05 := right 2 28 [3, 6] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p06 := left 3 29 [1, 23] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p07 := right 3 29 [2, 22] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p08 := left 4 30 [3, 25] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p09 := right 4 30 [4, 24] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p10 := left 5 31 [4, 20] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p11 := right 5 31 [8, 21] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p12 := left 6 32 [5, 13] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p13 := right 6 32 [12, 19] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p14 := left 7 33 [6, 19] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p15 := right 7 33 [7, 18] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p16 := left 8 34 [9, 16] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p17 := right 8 34 [11, 14] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p18 := left 9 35 [9, 18] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p19 := right 9 35 [20] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p20 := left 10 36 [10, 17] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p21 := right 10 36 [12, 15] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p22 := left 11 37 [10, 21] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p23 := right 11 37 [11] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p24 := left 12 38 [14, 22] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p25 := right 12 38 [24] (by decide)
    (by simp [value, valuation, relationRightActive])
  have p26 := left 13 39 [15, 25] (by decide)
    (by simp [value, valuation, relationLeftActive])
  have p27 := right 13 39 [16] (by decide)
    (by simp [value, valuation, relationRightActive])
  simpa only [relationFormula, List.append_assoc, value] using
    satisfies_fmla_append value p00 <|
    satisfies_fmla_append value p01 <|
    satisfies_fmla_append value p02 <|
    satisfies_fmla_append value p03 <|
    satisfies_fmla_append value p04 <|
    satisfies_fmla_append value p05 <|
    satisfies_fmla_append value p06 <|
    satisfies_fmla_append value p07 <|
    satisfies_fmla_append value p08 <|
    satisfies_fmla_append value p09 <|
    satisfies_fmla_append value p10 <|
    satisfies_fmla_append value p11 <|
    satisfies_fmla_append value p12 <|
    satisfies_fmla_append value p13 <|
    satisfies_fmla_append value p14 <|
    satisfies_fmla_append value p15 <|
    satisfies_fmla_append value p16 <|
    satisfies_fmla_append value p17 <|
    satisfies_fmla_append value p18 <|
    satisfies_fmla_append value p19 <|
    satisfies_fmla_append value p20 <|
    satisfies_fmla_append value p21 <|
    satisfies_fmla_append value p22 <|
    satisfies_fmla_append value p23 <|
    satisfies_fmla_append value p24 <|
    satisfies_fmla_append value p25 <|
    satisfies_fmla_append value p26 p27

theorem everyFeasiblePatternCovered (pattern : Fin 26 → Prop)
    (feasible : Feasible pattern) :
    ∃ stratum ∈ strata, Covers stratum pattern := by
  classical
  by_contra noCover
  have avoids : ∀ stratum ∈ strata, ¬ Covers stratum pattern := by
    intro stratum member covered
    exact noCover ⟨stratum, member, covered⟩
  have satisfies : (valuation pattern).satisfies_fmla formula := by
    constructor
    intro clause member
    change clause ∈ List.append relationFormula (strata.map stratumClause) at member
    rcases List.mem_append.mp member with relationMember | stratumMember
    · exact (satisfies_relationFormula pattern feasible).prop clause relationMember
    · obtain ⟨stratum, stratumInData, rfl⟩ := List.mem_map.mp stratumMember
      rw [satisfies_iff_not_all_falsified]
      exact avoids stratum stratumInData
  exact contradiction (valuation pattern) satisfies

theorem covers_activity (stratum : GlobalFormula.Stratum)
    (pattern : Fin 26 → Prop) (covered : Covers stratum pattern)
    (relation : Fin 14) :
    if stratum.activeMask.testBit relation then
      relationLeftActive pattern relation
    else ¬ relationLeftActive pattern relation := by
  let literal := if stratum.activeMask.testBit relation then
        Sat.Literal.neg (26 + relation)
      else Sat.Literal.pos (26 + relation)
  have activityMember : List.Mem literal
      (activityLiterals stratum.activeMask) := by
    rw [activityLiterals]
    apply List.mem_map.mpr
    exact ⟨relation, List.mem_range.mpr relation.isLt, rfl⟩
  have clauseMember : List.Mem literal (stratumClause stratum) := by
    change List.Mem literal (List.append (activityLiterals stratum.activeMask)
      (zeroLiterals stratum.zeroMask))
    exact List.mem_append.mpr (Or.inl activityMember)
  have falsified := (List.forall_iff_forall_mem.mp covered) literal clauseMember
  have bound : 26 + (relation : Nat) < 40 := by omega
  by_cases active : stratum.activeMask.testBit relation
  · simpa [literal, active, Sat.Valuation.neg, valuation, bound] using falsified
  · simpa [literal, active, Sat.Valuation.neg, valuation, bound] using falsified

theorem covers_zero (stratum : GlobalFormula.Stratum)
    (pattern : Fin 26 → Prop) (covered : Covers stratum pattern)
    (coordinate : Fin 26) (zero : stratum.zeroMask.testBit coordinate) :
    ¬ pattern coordinate := by
  have zeroMember : List.Mem (Sat.Literal.pos coordinate)
      (zeroLiterals stratum.zeroMask) := by
    rw [zeroLiterals]
    apply List.mem_filterMap.mpr
    exact ⟨coordinate, List.mem_range.mpr coordinate.isLt, by simp [zero]⟩
  have clauseMember : List.Mem (Sat.Literal.pos coordinate)
      (stratumClause stratum) := by
    change List.Mem (Sat.Literal.pos coordinate)
      (List.append (activityLiterals stratum.activeMask)
        (zeroLiterals stratum.zeroMask))
    exact List.mem_append.mpr (Or.inr zeroMember)
  have falsified := (List.forall_iff_forall_mem.mp covered) _ clauseMember
  simpa [Sat.Valuation.neg, valuation, coordinate.isLt] using falsified

end Krenn.CollapseSupportCover.Semantic

#print axioms Krenn.CollapseSupportCover.Semantic.everyFeasiblePatternCovered
