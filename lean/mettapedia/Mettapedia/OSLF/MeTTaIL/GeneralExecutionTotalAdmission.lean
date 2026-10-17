import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralFamilyRecognition

/-!
# Executable totality admission of compiled authored work

The refinement inspects the selected annotated rewrite declarations and each
selected equation orientation in the actual execution environment. Its
obligations distinguish finite foundation admission from total interpretation
of the ordered premise and reduct work. Reduct projection uses the actual
validated operation; target representation and typing remain checked gates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission

def checkRule (plan : Plan) (rule : RulePlan) : Bool :=
  GeneralPremise.Static.checkRule (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.provider rule.rule rule.binding.spec

def checkEquation (plan : Plan) (equation : EquationPlan) : Bool :=
  GeneralPremise.Static.checkRule (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.provider equation.rule equation.binding.spec

/-- The ordinary compiled plan currently installs the finite-row provider.
Registered native services need their separately checked implementation and
source-image admission before they can establish totality here. -/
def checkGeneric (plan : Plan) : Bool :=
  plan.snapshot.provider.dynamicRelations.isEmpty &&
    GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment plan) &&
    plan.equations.all (checkEquation plan)

inductive Obligation where
  | foundation (reason : GeneralExecutionAdmission.Obligation)
  | childTotality
  | nativeServicesUnavailable (relations : List String)
  | ruleTotality (declarationIndex : Nat)
  | equationTotality (declarationIndex : Nat) (direction : ScopedEquationExecution.Orientation)
  | unsupportedTotalProfile
  deriving DecidableEq, Repr

def genericObligations (plan : Plan) : List Obligation :=
  (if plan.snapshot.provider.dynamicRelations.isEmpty then []
    else [.nativeServicesUnavailable plan.snapshot.provider.dynamicRelations]) ++
  (if GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment plan) then []
    else [.childTotality]) ++
  ((plan.rules.filter fun rule => !(checkRule plan rule)).map fun rule =>
    .ruleTotality rule.declarationIndex) ++
  ((plan.equations.filter fun equation => !(checkEquation plan equation)).map fun equation =>
    .equationTotality equation.declarationIndex equation.direction)

theorem checkGeneric_readout {plan : Plan} (checked : checkGeneric plan = true) :
    GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment plan) = true ∧
    ∀ equation ∈ plan.equations, checkEquation plan equation = true := by
  simp only [checkGeneric, Bool.and_eq_true] at checked
  exact ⟨checked.1.2, List.all_eq_true.mp checked.2⟩

theorem checkGeneric_no_dynamic {plan : Plan} (checked : checkGeneric plan = true) :
    plan.snapshot.provider.dynamicRelations = [] := by
  simp only [checkGeneric, Bool.and_eq_true] at checked
  exact List.isEmpty_iff.mp checked.1.1

/-- A finite-only plan cannot certify an uninstalled native implementation. -/
theorem checkGeneric_native_refused {plan : Plan}
    (registered : plan.snapshot.provider.dynamicRelations ≠ []) : checkGeneric plan = false := by
  cases found : plan.snapshot.provider.dynamicRelations with
  | nil => exact False.elim (registered found)
  | cons relation relations => simp only [checkGeneric, found, List.isEmpty_cons, Bool.false_and]

theorem native_unavailable_obligation {plan : Plan}
    (registered : plan.snapshot.provider.dynamicRelations ≠ []) :
    Obligation.nativeServicesUnavailable plan.snapshot.provider.dynamicRelations ∈ genericObligations plan := by
  cases found : plan.snapshot.provider.dynamicRelations with
  | nil => exact False.elim (registered found)
  | cons relation relations => simp [genericObligations, found]

theorem checkGeneric_equation {plan : Plan} (checked : checkGeneric plan = true)
    {equation : EquationPlan} (member : equation ∈ plan.equations) :
    checkEquation plan equation = true :=
  (checkGeneric_readout checked).2 equation member

theorem checkGeneric_rule {plan : Plan} (checked : checkGeneric plan = true)
    {rule : RulePlan} (member : rule ∈ plan.rules) : checkRule plan rule = true := by
  obtain ⟨index, declared⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨spec, specified, _, ruleChecked⟩ := GeneralPremise.Static.checkLanguage_rule
    (checkGeneric_readout checked).1 (GeneralPlanEnvironment.selected_rule plan declared)
  have same : spec = rule.binding.spec := Option.some.inj
    (specified.symm.trans (GeneralPlanEnvironment.selected_specification plan declared))
  subst spec
  exact ruleChecked

theorem genericObligations_empty {plan : Plan} (checked : checkGeneric plan = true) :
    genericObligations plan = [] := by
  have readout := checkGeneric_readout checked
  have rulesEmpty : (plan.rules.filter fun rule => !(checkRule plan rule)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro rule member
    rw [checkGeneric_rule checked member]
    simp only [Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  have equationsEmpty : (plan.equations.filter fun equation => !(checkEquation plan equation)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro equation member
    rw [readout.2 equation member]
    simp only [Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  simp only [genericObligations, checkGeneric_no_dynamic checked, List.isEmpty_nil,
    readout.1, if_true,
    rulesEmpty, equationsEmpty, List.map_nil, List.nil_append]

def checkTotality (plan : Plan) : Bool :=
  checkGeneric plan || GeneralGuardedBinderFamily.check plan.snapshot plan.permissions ||
    GeneralRhoFamily.check plan.snapshot plan.permissions

def totalityObligations (plan : Plan) : List Obligation :=
  if checkTotality plan then [] else .unsupportedTotalProfile :: genericObligations plan

structure Admission where
  execution : Plan
  obligations : List Obligation
  deriving Repr

def compile (snapshot : Snapshot) (permissions : Permissions) : Admission :=
  let execution := GeneralExecutionAdmission.compile snapshot permissions
  ⟨execution, execution.obligations.map Obligation.foundation ++ totalityObligations execution⟩

def Admission.complete (admission : Admission) : Bool := admission.obligations.isEmpty

theorem compile_execution (snapshot : Snapshot) (permissions : Permissions) :
    (compile snapshot permissions).execution = GeneralExecutionAdmission.compile snapshot permissions := rfl

theorem checkTotality_readout {plan : Plan} (checked : checkTotality plan = true) :
    checkGeneric plan = true ∨
    GeneralGuardedBinderFamily.check plan.snapshot plan.permissions = true ∨
    GeneralRhoFamily.check plan.snapshot plan.permissions = true := by
  simpa only [checkTotality, Bool.or_eq_true, or_assoc] using checked

theorem compile_complete_iff (snapshot : Snapshot) (permissions : Permissions) :
    (compile snapshot permissions).complete = true ↔
      (GeneralExecutionAdmission.compile snapshot permissions).complete = true ∧
      checkTotality (GeneralExecutionAdmission.compile snapshot permissions) = true := by
  constructor
  · intro checked
    have empty : (compile snapshot permissions).obligations = [] := List.isEmpty_iff.mp checked
    have parts := List.append_eq_nil_iff.mp empty
    have baseEmpty : (GeneralExecutionAdmission.compile snapshot permissions).obligations = [] :=
      List.map_eq_nil_iff.mp parts.1
    have baseComplete : (GeneralExecutionAdmission.compile snapshot permissions).complete = true :=
      List.isEmpty_iff.mpr baseEmpty
    refine ⟨baseComplete, ?_⟩
    by_cases total : checkTotality (GeneralExecutionAdmission.compile snapshot permissions) = true
    · exact total
    · have impossible : totalityObligations (GeneralExecutionAdmission.compile snapshot permissions) = [] := parts.2
      rw [totalityObligations, if_neg total] at impossible
      cases impossible
  · rintro ⟨base, total⟩
    have baseEmpty := List.isEmpty_iff.mp base
    apply List.isEmpty_iff.mpr
    simp only [compile, baseEmpty, totalityObligations, total, if_true, List.map_nil, List.nil_append]

theorem compile_foundation_checked {snapshot : Snapshot} {permissions : Permissions}
    (checked : (compile snapshot permissions).complete = true) :
    (GeneralExecutionAdmission.compile snapshot permissions).complete = true :=
  ((compile_complete_iff snapshot permissions).mp checked).1

theorem compile_totality_checked {snapshot : Snapshot} {permissions : Permissions}
    (checked : (compile snapshot permissions).complete = true) :
    checkTotality (GeneralExecutionAdmission.compile snapshot permissions) = true :=
  ((compile_complete_iff snapshot permissions).mp checked).2

theorem unsupported_obligation {snapshot : Snapshot} {permissions : Permissions}
    (unsupported : checkTotality (GeneralExecutionAdmission.compile snapshot permissions) = false) :
    Obligation.unsupportedTotalProfile ∈ (compile snapshot permissions).obligations := by
  simp only [compile, totalityObligations, unsupported, Bool.false_eq_true, if_false]
  exact List.mem_append_right _ List.mem_cons_self

theorem unsupported_not_complete {snapshot : Snapshot} {permissions : Permissions}
    (unsupported : checkTotality (GeneralExecutionAdmission.compile snapshot permissions) = false) :
    (compile snapshot permissions).complete = false := by
  cases checked : (compile snapshot permissions).complete with
  | false => rfl
  | true =>
      have total := compile_totality_checked checked
      rw [unsupported] at total
      cases total

theorem compile_complete_of_generic {snapshot : Snapshot} {permissions : Permissions}
    (foundation : (GeneralExecutionAdmission.compile snapshot permissions).complete = true)
    (total : checkGeneric (GeneralExecutionAdmission.compile snapshot permissions) = true) :
    (compile snapshot permissions).complete = true := by
  apply (compile_complete_iff snapshot permissions).mpr
  exact ⟨foundation, by simp only [checkTotality, total, Bool.true_or]⟩

theorem guarded_compilation_total (allowed : List EquationFrontierBinderProfile.Token) :
    (compile (GeneralGuardedBinderAdmission.snapshot allowed)
      GeneralGuardedBinderAdmission.permissions).complete = true := by
  apply (compile_complete_iff _ _).mpr
  refine ⟨GeneralGuardedBinderAdmission.admission_complete allowed, ?_⟩
  have family := (GeneralGuardedBinderFamily.check_iff
    (GeneralGuardedBinderAdmission.snapshot allowed) GeneralGuardedBinderAdmission.permissions).mpr
    ⟨allowed, rfl, rfl⟩
  change (checkGeneric (GeneralExecutionAdmission.compile _ _) ||
    GeneralGuardedBinderFamily.check (GeneralGuardedBinderAdmission.snapshot allowed)
      GeneralGuardedBinderAdmission.permissions ||
    GeneralRhoFamily.check (GeneralGuardedBinderAdmission.snapshot allowed)
      GeneralGuardedBinderAdmission.permissions) = true
  rw [family]
  simp only [Bool.or_true, Bool.true_or]

theorem rho_compilation_total :
    (compile GeneralRho.snapshot GeneralRho.permissions).complete = true := by
  apply (compile_complete_iff _ _).mpr
  refine ⟨GeneralRho.compilation_complete, ?_⟩
  have family := GeneralRhoFamily.original_comm_profile_recognized
  change (checkGeneric (GeneralExecutionAdmission.compile _ _) ||
    GeneralGuardedBinderFamily.check GeneralRho.snapshot GeneralRho.permissions ||
    GeneralRhoFamily.check GeneralRho.snapshot GeneralRho.permissions) = true
  rw [family]
  exact Bool.or_true _

#print axioms compile_complete_iff
#print axioms unsupported_not_complete
#print axioms guarded_compilation_total
#print axioms rho_compilation_total

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission
