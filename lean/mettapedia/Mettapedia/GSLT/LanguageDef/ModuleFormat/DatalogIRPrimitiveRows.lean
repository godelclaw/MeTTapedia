import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable
import Std.Data.String.ToNat

/-! The emitted primitive rows preserve and reflect the source comparisons.
Their indices address the prepared literal pool; different indices cannot
alias through the physical reference encoding. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

private instance : LawfulBEq ComparisonOperator where
  rfl := by intro operator; cases operator <;> rfl
  eq_of_beq := by intro first second same; cases first <;> cases second <;> cases same <;> rfl

theorem valueRef_injective : Function.Injective valueRef := by
  intro first second same
  have text := Pattern.fvar.inj same
  have digits := (String.append_right_inj "dl:value:").mp text
  exact Nat.repr_injective digits

theorem relationRef_injective : Function.Injective relationRef := by
  intro first second same
  have text := Pattern.fvar.inj same
  have digits := (String.append_right_inj "dl:relation:").mp text
  exact Nat.repr_injective digits

theorem comparisonName_injective : Function.Injective Join.comparisonName := by
  intro first second same
  cases first <;> cases second <;> simp_all [Join.comparisonName]

private theorem erased_operators_nodup (items : List ComparisonOperator) : items.eraseDups.Nodup := by
  cases items with
  | nil => simp
  | cons head rest =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro member
      have filtered := (List.mem_filter.mp (List.mem_eraseDups.mp member)).2
      simp at filtered
    · exact erased_operators_nodup (rest.filter (fun value => !(value == head)))
termination_by items.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem operators_nodup (program : Program) : (operators program).Nodup :=
  erased_operators_nodup _

theorem comparison_row_iff (program : Program) (pools : Join.Pools)
    (operator : ComparisonOperator) (first second : Nat) :
    (⟨Join.comparisonName operator,[valueRef first,valueRef second]⟩ : GeneralPremise.ProviderRow)
      ∈ comparisonRows program pools ↔
    operator ∈ operators program ∧ ∃ left right,
      pools.literals[first]? = some left ∧ pools.literals[second]? = some right ∧
      policy.Holds operator left right := by
  constructor
  · intro present
    obtain ⟨other,enabled,emitted⟩ := List.mem_flatMap.mp present
    obtain ⟨⟨left,leftIndex⟩,leftMember,emitted⟩ := List.mem_flatMap.mp emitted
    obtain ⟨⟨right,rightIndex⟩,rightMember,formed⟩ := List.mem_filterMap.mp emitted
    dsimp only at formed
    by_cases holds : compare other left right = true
    · rw [if_pos holds] at formed
      have same := Option.some.inj formed
      have sameOperator := comparisonName_injective (congrArg GeneralPremise.ProviderRow.relation same)
      have arguments := congrArg GeneralPremise.ProviderRow.values same
      have firstRef : valueRef leftIndex = valueRef first := (List.cons.inj arguments).1
      have secondRef : valueRef rightIndex = valueRef second :=
        (List.cons.inj (List.cons.inj arguments).2).1
      have sameFirst := valueRef_injective firstRef
      have sameSecond := valueRef_injective secondRef
      subst other
      subst leftIndex
      subst rightIndex
      exact ⟨enabled,left,right,List.mk_mem_zipIdx_iff_getElem?.mp leftMember,
        List.mk_mem_zipIdx_iff_getElem?.mp rightMember,(primitive_comparison_exact _ _ _).mp holds⟩
    · rw [if_neg holds] at formed
      cases formed
  · rintro ⟨enabled,left,right,leftAt,rightAt,holds⟩
    apply List.mem_flatMap.mpr
    refine ⟨operator,enabled,List.mem_flatMap.mpr ?_⟩
    refine ⟨(left,first),List.mk_mem_zipIdx_iff_getElem?.mpr leftAt,List.mem_filterMap.mpr ?_⟩
    refine ⟨(right,second),List.mk_mem_zipIdx_iff_getElem?.mpr rightAt,?_⟩
    simp [(primitive_comparison_exact _ _ _).mpr holds]

theorem source_guard_operator {program : Program} {clause : Clause} {comparison : Comparison}
    (source : Statement.rule clause ∈ program.statements)
    (guard : comparison ∈ Comparisons.guards clause) : comparison.operator ∈ operators program := by
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  exact ⟨.rule clause,source,List.mem_map.mpr ⟨comparison,guard,rfl⟩⟩

theorem source_guard_row_iff {program : Program} {clause : Clause} {comparison : Comparison}
    (source : Statement.rule clause ∈ program.statements)
    (guard : comparison ∈ Comparisons.guards clause) (pools : Join.Pools)
    (first second : Nat) (left right : Value)
    (leftAt : pools.literals[first]? = some left) (rightAt : pools.literals[second]? = some right) :
    (⟨Join.comparisonName comparison.operator,[valueRef first,valueRef second]⟩ : GeneralPremise.ProviderRow)
      ∈ comparisonRows program pools ↔ policy.Holds comparison.operator left right := by
  rw [comparison_row_iff]
  simp [source_guard_operator source guard,leftAt,rightAt]

namespace Controls

def numeric : Program := ⟨[.rule ⟨⟨["P"],[.var "X"]⟩,
  [.atom ⟨["P"],[.var "X"]⟩,.comparison ⟨.less,.var "X",.literal (.number 2)⟩]⟩]⟩
def pool : Join.Pools := ⟨[["P"]],[.number (-1),.number 2]⟩

#guard (comparisonRows numeric pool).contains ⟨Join.comparisonName .less,[valueRef 0,valueRef 1]⟩
#guard !(comparisonRows numeric pool).contains ⟨Join.comparisonName .less,[valueRef 1,valueRef 0]⟩
#guard !(comparisonRows numeric pool).contains ⟨Join.comparisonName .equal,[valueRef 0,valueRef 0]⟩
#guard !(comparisonRows numeric pool).contains ⟨Join.comparisonName .less,[valueRef 0,valueRef 2]⟩

end Controls

#print axioms valueRef_injective
#print axioms comparison_row_iff
#print axioms source_guard_row_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable
