import Mettapedia.Logic.HOL.NaturalRecursionProofs
import Mettapedia.Logic.HOL.HOLLightStandardTheory
import Mettapedia.Logic.HOL.Soundness

/-!
# An inhabited recursion profile with a nonconstant Boolean result

Natural numbers interpret the number sort. The selection operation is
constructed over full domains, and primitive recursion supplies the required
existence statement. The retained proofs apply to Boolean recursion starting
at false and negating the preceding result. Thus their premises are jointly
realizable, and the result changes between zero and its successor.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.NaturalRecursionProofControls

abbrev number : Ty Unit := .base ()

inductive Const : Ty Unit → Type where
  | zero : Const number
  | successor : Const (number ⇒ number)
  | select : Const (SelectionProofs.Selection (number ⇒ .prop))
  | expected : Const (number ⇒ .prop)

def alternating : Nat → Prop
  | 0 => False
  | n + 1 => ¬ alternating n

def carrier (_ : Unit) : Type 1 := ULift.{1} Nat
def inhabitant (_ : Unit) : carrier () := ULift.up 0

noncomputable def meaning : {type : Ty Unit} → Const type → Ty.denote.{0, 0} carrier type
  | _, .zero => ULift.up 0
  | _, .successor => fun value => ULift.up (value.down + 1)
  | _, .select => HOLLightStandardTheory.selectionOperation carrier inhabitant (number ⇒ .prop)
  | _, .expected => fun value => ULift.up (alternating value.down)

noncomputable def model : HenkinModel.{0, 0, 0} Unit Const := .standard carrier meaning

def zero : ClosedTerm Const number := .const .zero
def successor : ClosedTerm Const (number ⇒ number) := .const .successor
def selection : ClosedTerm Const (SelectionProofs.Selection (number ⇒ .prop)) := .const .select
def base : ClosedFormula Const := .bot
def method : ClosedTerm Const (NaturalRecursionProofs.Method number .prop) :=
  .lam (.lam (.not (.var (.vs .vz))))
def function : ClosedTerm Const (number ⇒ .prop) :=
  NaturalRecursionProofs.recursor selection zero successor base method

def zeroProof := NaturalRecursionProofs.zeroImplication selection zero successor base method
def successorProof := NaturalRecursionProofs.successorImplication selection zero successor base method zero

theorem zeroProof_free : zeroProof.FunctionExtensionalityFree :=
  NaturalRecursionProofs.zeroImplication_free _ _ _ _ _
theorem successorProof_free : successorProof.FunctionExtensionalityFree :=
  NaturalRecursionProofs.successorImplication_free _ _ _ _ _ _

theorem existence_instance_free :
    (NaturalRecursionProofs.existence (Δ := [NaturalRecursionProofs.statement zero successor .prop,
      SelectionProofs.principle selection]) zero successor base method (.hyp 0)).FunctionExtensionalityFree :=
  NaturalRecursionProofs.existence_free
    (Δ := [NaturalRecursionProofs.statement zero successor .prop, SelectionProofs.principle selection])
    zero successor base method (.hyp 0) trivial

theorem computation_instance_free :
    (NaturalRecursionProofs.computation (Δ := [NaturalRecursionProofs.statement zero successor .prop,
      SelectionProofs.principle selection]) selection zero successor base method (.hyp 1) (.hyp 0)).FunctionExtensionalityFree :=
  NaturalRecursionProofs.computation_free
    (Δ := [NaturalRecursionProofs.statement zero successor .prop, SelectionProofs.principle selection])
    selection zero successor base method (.hyp 1) (.hyp 0) trivial trivial

theorem selection_holds : model.models (SelectionProofs.principle selection) := by
  intro predicate _ witness _ holds
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (number ⇒ .prop)
    predicate ⟨witness, holds⟩

theorem recursion_holds : model.models (NaturalRecursionProofs.statement zero successor .prop) := by
  intro initial _ step _
  let values : ULift.{1} Nat → ULift Prop :=
    fun index => Nat.rec initial (fun k previous => step previous (ULift.up k)) index.down
  refine ⟨values, trivial, ?_, ?_⟩
  · exact Iff.rfl
  · intro index _
    exact Iff.rfl

theorem zero_equation : model.models (.eq (.app function zero) base) := by
  have valid := Soundness.extTheorem_sound zeroProof.erase model
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  exact valid selection_holds recursion_holds

theorem successor_equation : model.models
    (.eq (.app function (.app successor zero)) (.app (.app method (.app function zero)) zero)) := by
  have valid := Soundness.extTheorem_sound successorProof.erase model
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  exact valid selection_holds recursion_holds

theorem zero_false : ¬ model.models (.app function zero) := by
  intro holds
  exact zero_equation.mp holds

theorem successor_true : model.models (.app function (.app successor zero)) :=
  successor_equation.mpr zero_false

/-- The fibre at each number requires its Boolean result to match an
independently defined alternating sequence. -/
def family : ClosedTerm Const (number ⇒ .prop ⇒ .prop) :=
  .lam (.lam (.eq (.var .vz) (.app (.const .expected) (.var (.vs .vz)))))

def dependentProof :=
  NaturalRecursionProofs.dependentImplication selection zero successor base method family

theorem dependentProof_free : dependentProof.FunctionExtensionalityFree :=
  NaturalRecursionProofs.dependentImplication_free _ _ _ _ _ _

theorem invariant_instance_free :
    (NaturalRecursionProofs.invariant (Δ := [
      NaturalRecursionProofs.methodPreserves successor method family,
      NaturalRecursionProofs.holds family zero base,
      NaturalRecursionProofs.equations zero successor base method function,
      NaturalRecursionProofs.inductionPrinciple zero successor])
      zero successor base method function family (.hyp 3) (.hyp 2) (.hyp 1) (.hyp 0)).FunctionExtensionalityFree :=
  NaturalRecursionProofs.invariant_free
    (Δ := [NaturalRecursionProofs.methodPreserves successor method family,
      NaturalRecursionProofs.holds family zero base,
      NaturalRecursionProofs.equations zero successor base method function,
      NaturalRecursionProofs.inductionPrinciple zero successor])
    zero successor base method function family (.hyp 3) (.hyp 2) (.hyp 1) (.hyp 0)
    trivial trivial trivial trivial

theorem induction_holds : model.models (NaturalRecursionProofs.inductionPrinciple zero successor) := by
  intro predicate _ premises value _
  exact Nat.rec (motive := fun n => (predicate (ULift.up n)).down)
    premises.1 (fun n previous => premises.2 (ULift.up n) trivial previous) value.down

theorem base_fits : model.models (NaturalRecursionProofs.holds family zero base) := Iff.rfl

theorem method_preserves : model.models (NaturalRecursionProofs.methodPreserves successor method family) := by
  intro index _ value _ previous
  change value.down ↔ alternating index.down at previous
  change (¬ value.down) ↔ ¬ alternating index.down
  exact not_congr previous

/-- The general retained proof, applied in the actual selected-recursion
model, establishes all fibres at once. -/
theorem dependent_typed : model.models (.all
    (NaturalRecursionProofs.holds (weaken family) (.var .vz) (.app (weaken function) (.var .vz)))) := by
  have valid := Soundness.extTheorem_sound dependentProof.erase model
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  exact valid selection_holds recursion_holds induction_holds base_fits method_preserves

theorem family_changes :
    model.models (NaturalRecursionProofs.holds family zero .bot) ∧
      ¬ model.models (NaturalRecursionProofs.holds family (.app successor zero) .bot) := by
  refine ⟨Iff.rfl, ?_⟩
  intro impossible
  exact impossible.mpr (fun no => no)

def falseFamily : ClosedTerm Const (number ⇒ .prop ⇒ .prop) := .lam (.lam (.not (.var .vz)))

theorem falseFamily_base : model.models (NaturalRecursionProofs.holds falseFamily zero base) :=
  fun no => no

/-- Fitting the base case alone does not license a dependent eliminator. -/
theorem falseFamily_step_refused :
    ¬ model.models (NaturalRecursionProofs.methodPreserves successor method falseFamily) := by
  intro preserves
  exact preserves (ULift.up 0) trivial (ULift.up False) trivial (fun no => no) (fun no => no)

theorem falseFamily_result_refused : ¬ model.models (.all
    (NaturalRecursionProofs.holds (weaken falseFamily) (.var .vz)
      (.app (weaken function) (.var .vz)))) := by
  intro every
  exact every (ULift.up 1) trivial successor_true

#print axioms zeroProof_free
#print axioms successorProof_free
#print axioms existence_instance_free
#print axioms computation_instance_free
#print axioms selection_holds
#print axioms recursion_holds
#print axioms zero_false
#print axioms successor_true
#print axioms dependentProof_free
#print axioms invariant_instance_free
#print axioms induction_holds
#print axioms method_preserves
#print axioms dependent_typed
#print axioms family_changes
#print axioms falseFamily_step_refused
#print axioms falseFamily_result_refused

end Mettapedia.Logic.HOL.NaturalRecursionProofControls
