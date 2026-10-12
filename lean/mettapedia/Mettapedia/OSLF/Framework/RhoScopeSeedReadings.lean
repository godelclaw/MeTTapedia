import Mettapedia.OSLF.Framework.RhoScopeGeneratorInterpretation
import Mettapedia.OSLF.Framework.RhoScopeExpressionLaws
import Mettapedia.OSLF.Framework.RhoGeneratedScopeStrata
import Mettapedia.OSLF.Framework.RhoGeneratedScopeInventory
import Mettapedia.OSLF.Syntax.RhoScopeQuotientControls
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Atomic parts and atomic name seeds give different scope readings

The displayed two-part generator first quotes an admitted pair of process
atoms. The seeded reading instead admits the two quoted atoms themselves and
then closes under quoted parallel compositions of dropped members. The
actual null/output atoms distinguish these readings on the source quotient.

The displayed generator's depth-zero name family has cardinality one. The
seeded reading additionally admits the quoted null, which the displayed
generator excludes at every finite depth. Consequently a counting recurrence
starting with two distinct atomic name seeds cannot be transferred to the
displayed generator without an additional comparison or a revised generator.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopeSeedReadings

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres
open RhoEquationGeneratedScope RhoGeneratedScopeInventory RhoGeneratedScopeStrata
open RhoScopeExpression RhoScopeGeneratorInterpretation RhoScopeExpressionLaws

def leftAtom (process : Process []) : Prop := process = zero []

def rightAtom (process : Process []) : Prop := process = visible

def atoms : Fin 2 → Process [] → Prop := Fin.cases leftAtom (fun _ => rightAtom)

def displayed : Expression (Fin 2) Srt.nm := generator 0 1

def seededBody : Expression (Fin 2) Srt.nm :=
  .or (.or (.quote (.atom 0)) (.quote (.atom 1)))
    (.quote (.par (.drop (.var 0)) (.drop (.var 0))))

def seeded : Expression (Fin 2) Srt.nm := .mu seededBody

theorem displayed_readout (env : RhoScopeExpression.Environment []) :
    denote atoms displayed env = generated leftAtom rightAtom :=
  generator_denotation atoms 0 1 env

theorem displayed_zero_stage (name : Name []) :
    Bounded leftAtom rightAtom 0 name ↔ name = quote visible := by
  rw [bounded_zero_iff_atoms]
  constructor
  · rintro ⟨first, second, rfl, rfl, readout⟩
    rw [join_zero_left] at readout
    exact readout.symm
  · intro same
    exact ⟨zero [], visible, rfl, rfl, (congrArg quote (join_zero_left visible)).trans same.symm⟩

def zeroStageEquiv : {name : Name [] // Bounded leftAtom rightAtom 0 name} ≃ PUnit.{1} where
  toFun := fun _ => .unit
  invFun := fun _ => ⟨quote visible, (displayed_zero_stage _).mpr rfl⟩
  left_inv := fun member => Subtype.ext ((displayed_zero_stage _).mp member.property).symm
  right_inv := fun value => by cases value; rfl

theorem displayed_zero_stage_cardinality :
    Nat.card {name : Name [] // Bounded leftAtom rightAtom 0 name} = 1 := by
  rw [Nat.card_congr zeroStageEquiv]
  exact Nat.card_unique

theorem displayed_retains_output : generated leftAtom rightAtom ≤
    fun name => 0 < RhoSourceOutputPredicate.count name := by
  apply generated_induction
  intro name
  rintro ⟨first, second, rfl, _, admitted⟩
  rw [count_quote, count_join]
  have positive : 0 < RhoSourceOutputPredicate.count second := by
    rcases admitted with rfl | ⟨inner, member, rfl⟩
    · exact Nat.zero_lt_one
    · simpa only [count_drop] using member
  exact positive.trans_le (Nat.le_add_left _ _)

theorem displayed_excludes_null (env : RhoScopeExpression.Environment []) :
    ¬ denote atoms displayed env (quote (zero [])) := by
  rw [displayed_readout]
  intro member
  have positive := displayed_retains_output _ member
  change 0 < RhoSourceOutputPredicate.count (quote (zero [])) at positive
  rw [count_quote] at positive
  exact Nat.lt_irrefl 0 positive

theorem seeded_admits_null (env : RhoScopeExpression.Environment []) :
    denote atoms seeded env (quote (zero [])) := by
  change denote atoms (.mu seededBody) env (quote (zero []))
  have unfolds := congrFun (mu_unfold atoms seededBody env) (quote (zero []))
  rw [← unfolds]
  change ((∃ process, leftAtom process ∧ quote process = quote (zero [])) ∨
      (∃ process, rightAtom process ∧ quote process = quote (zero []))) ∨ _
  exact Or.inl (Or.inl ⟨zero [], rfl, rfl⟩)

theorem seeded_admits_output (env : RhoScopeExpression.Environment []) :
    denote atoms seeded env (quote visible) := by
  change denote atoms (.mu seededBody) env (quote visible)
  have unfolds := congrFun (mu_unfold atoms seededBody env) (quote visible)
  rw [← unfolds]
  change ((∃ process, leftAtom process ∧ quote process = quote visible) ∨
      (∃ process, rightAtom process ∧ quote process = quote visible)) ∨ _
  exact Or.inl (Or.inr ⟨visible, rfl, rfl⟩)

theorem seed_names_distinct : quote (zero []) ≠ quote visible :=
  RhoScopeQuotientControls.quoted_output_not_null.symm

theorem displayed_and_seeded_extensions_differ (env : RhoScopeExpression.Environment []) :
    denote atoms displayed env ≠ denote atoms seeded env := by
  intro same
  exact displayed_excludes_null env (same.symm ▸ seeded_admits_null env)

theorem both_readings_are_closed : displayed.closedAt 0 = true ∧ seeded.closedAt 0 = true := by
  constructor
  · exact generator_closed 0 1
  · decide +kernel

end Mettapedia.OSLF.Framework.RhoScopeSeedReadings
