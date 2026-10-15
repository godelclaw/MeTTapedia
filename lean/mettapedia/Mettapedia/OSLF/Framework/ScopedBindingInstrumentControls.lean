import Mettapedia.OSLF.Framework.ScopedBindingInstrumentLogic
import Mettapedia.OSLF.Syntax.ScopedBindingContextControls
import Mettapedia.OSLF.Syntax.RhoScopedEquationBindingControls

/-!
# Binding instrumentation controls and an authored rho consumer

The positional controls distinguish a captured variable from the enclosing
variable, and show that an empty kit cannot make that distinction. The rho
consumer uses the original source equations and the declared parallel-only
communication occurrences. Instrument inspection may enter an input body;
this does not grant permission to reduce inside that body.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ScopedInstruments.Controls

open ScopedEncoding

variable {S : Signature}

theorem argumentRelation_equality : ∀ {declarations : List (List S.Srt × S.Srt)}
    {context : Ctx S} {first second : Args S declarations context},
    BindingTermCongruenceQuotient.ArgumentRelation (fun first second => first = second)
      first second → first = second
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => by
      cases head
      exact congrArg (Args.cons _) (argumentRelation_equality tail)

def literalTheory (S : Signature) : EquationTheory S where
  relation first second := first = second
  reflexive _ := rfl
  symmetric := Eq.symm
  transitive := Eq.trans
  bind_relation := by
    intro context destination sort environment first second same
    exact congrArg (bind environment) same
  bind_pointwise := by
    intro context destination sort first second same value
    have equal : first = second := funext (fun sort => funext (same sort))
    exact congrArg (fun environment => bind environment value) equal
  operation_relation := by
    intro context sort operator first second related
    exact congrArg (Term.op operator) (argumentRelation_equality related)

open ScopedEncoding.Controls

def toyBase : BaseSystem (literalTheory toy) := BaseSystem.silent _

def complete : Constructor toy → Prop := fun _ => True

abbrev binder : Constructor toy := .operation [(), (), ()] () .binder

def bodyArguments : Arguments binder := .cons expectedBody .nil

theorem binder_builds_original_body : buildTerm binder bodyArguments = abstraction expectedBody := rfl

theorem binder_opens : Act toyBase complete (.ask binder)
    (.term (abstraction expectedBody)) (.bundle binder bodyArguments) :=
  .ask binder trivial rfl

/-- The projected body lives in four variable positions, one below this binder. -/
theorem binder_projects : Act toyBase complete (.get binder 0)
    (.bundle binder bodyArguments) (.term expectedBody) :=
  .get binder trivial 0 rfl

theorem capture_projection_rejected : ¬ Act toyBase complete (.get binder 0)
    (.bundle binder bodyArguments) (.term capturedBody) := by
  intro step
  exact capture_changes_body (Act.get_readout binder bodyArguments 0 capturedBody step)

theorem capture_not_bisimilar : ¬ Bisimilar toyBase complete
    (.term expectedBody) (.term capturedBody) := by
  intro related
  exact capture_changes_body ((bisimilar_iff_equation toyBase (fun _ => trivial) _ _).mp related)

theorem characteristic_accepts : Holds toyBase
    (Mettapedia.OSLF.Framework.SortedInstrumentCongruence.characteristic (encode expectedBody))
    expectedBody := (characteristic_iff toyBase expectedBody expectedBody).mpr rfl

theorem characteristic_rejects_capture : ¬ Holds toyBase
    (Mettapedia.OSLF.Framework.SortedInstrumentCongruence.characteristic (encode expectedBody))
    capturedBody := by
  intro holds
  exact capture_changes_body ((characteristic_iff toyBase expectedBody capturedBody).mp holds).symm

inductive SameInterface : State toy → State toy → Prop where
  | terms {context : Ctx toy} {sort : toy.Srt} (first second : Term toy context sort) :
      SameInterface (.term first) (.term second)

theorem empty_kit_no_step {label : Label toy toyBase.Label} {source target : State toy}
    (step : Act toyBase (fun _ => False) label source target) : False := by
  cases label with
  | proper label => exact label.elim
  | ask constructor => exact (Mettapedia.OSLF.Framework.SortedInstrumentCongruence.Act.ask_inv
      step.encode).1
  | get constructor position => exact (Mettapedia.OSLF.Framework.SortedInstrumentCongruence.Act.get_inv
      step.encode).1
  | build constructor => exact (Mettapedia.OSLF.Framework.SortedInstrumentCongruence.Act.build_inv
      step.encode).1

theorem sameInterface_empty_bisimulation :
    (system toyBase (fun _ => False)).IsBisimulation SameInterface := by
  refine ⟨?_, ?_, ?_⟩
  · intro first second related label target step
    exact False.elim (empty_kit_no_step step)
  · intro first second related label target step
    exact False.elim (empty_kit_no_step step)
  · intro first second related atom
    cases related
    cases atom with
    | inl scope => exact Iff.rfl
    | inr atom => exact atom.elim

theorem empty_kit_loses_capture : Bisimilar toyBase (fun _ => False)
    (.term expectedBody) (.term capturedBody) :=
  ⟨SameInterface, sameInterface_empty_bisimulation, .terms _ _⟩

/-! ## The source rho equations and independently authored communication -/

open RhoSchema RhoEquationConstructorControls RhoScopedEquationEventControls

def rhoTheory : EquationTheory sig :=
  BindingEquationFamilyModel.congruence (fun equation => equation ∈ rhoSourceE)

theorem rho_equation_iff {context : Ctx sig} {sort : sig.Srt}
    (first second : Term sig context sort) :
    rhoTheory.relation first second ↔ EqClosure rhoSourceE first second :=
  BindingEquationFamilyCongruence.related_mem_iff rhoSourceE first second

abbrev RhoPacked := Σ scope : Scope sig, TermQ rhoSourceE scope.1 scope.2

def pack {context : Ctx sig} {sort : sig.Srt} (value : Term sig context sort) : RhoPacked :=
  ⟨(context, sort), Quotient.mk _ value⟩

theorem pack_equation {context : Ctx sig} {sort : sig.Srt}
    {first second : Term sig context sort} (related : rhoTheory.relation first second) :
    pack first = pack second :=
  congrArg (Sigma.mk (context, sort)) (Quotient.sound ((rho_equation_iff first second).mp related))

abbrev RhoOccurrence := Σ scope : Scope sig,
  ScopedEquationEvents.Event rules parallelPermission scope

/-- Labels retain the actual authored firing and its scope. -/
def rhoBase : BaseSystem rhoTheory where
  Atom := Empty
  observes atom := atom.elim
  observes_resp atom := atom.elim
  Label := RhoOccurrence
  act := fun event {_} {_} before after =>
    pack before = ⟨event.1, event.2.sourceClass rhoSourceE⟩ ∧
      pack after = ⟨event.1, event.2.targetClass rhoSourceE⟩
  act_resp_left := by
    intro label source target first second next related step
    exact ⟨next, ⟨(pack_equation related).symm.trans step.1, step.2⟩,
      rhoTheory.reflexive next⟩
  act_resp_right := by
    intro label source target start next next' step related
    exact ⟨step.1, (pack_equation related).symm.trans step.2⟩

def rhoComplete : Constructor sig → Prop := fun _ => True

theorem actual_communication : Act rhoBase rhoComplete (.proper ⟨([], Srt.pr), occurrence 0⟩)
    (.term sourceProcess) (.term nilP) := Act.proper (base := rhoBase) ⟨rfl, rfl⟩

theorem duplicate_communication : Act rhoBase rhoComplete (.proper ⟨([], Srt.pr), occurrence 1⟩)
    (.term sourceProcess) (.term nilP) := Act.proper (base := rhoBase) ⟨rfl, rfl⟩

theorem firing_labels_distinct :
    (⟨([], Srt.pr), occurrence 0⟩ : RhoOccurrence) ≠ ⟨([], Srt.pr), occurrence 1⟩ := by
  intro same
  have indices : (0 : Fin 2) = 1 := congrArg (fun event : RhoOccurrence => event.2.index) same
  exact (by decide : (0 : Fin 2) ≠ 1) indices

/-- The complete theorem applies to the actual source equation family. -/
theorem rho_reconstruction {context : Ctx sig} {sort : sig.Srt}
    (first second : Term sig context sort) :
    Bisimilar rhoBase rhoComplete (.term first) (.term second) ↔
      EqClosure rhoSourceE first second :=
  (bisimilar_iff_equation rhoBase (fun _ => trivial) first second).trans
    (rho_equation_iff first second)

theorem changed_root_stays_related : Bisimilar rhoBase rhoComplete
    (.term (parallel (null : Term sig [] Srt.pr) null)) (.term (null : Term sig [] Srt.pr)) :=
  (rho_reconstruction _ _).mpr (parallel_null_equation _)

abbrev rhoInput : Constructor sig := .operation [Srt.nm] Srt.pr Op.inp

def enclosingBody : Term sig [Srt.nm, Srt.nm] Srt.pr :=
  .op Op.drp (.cons (.var (.succ .zero)) .nil)

def inputArguments : Arguments rhoInput := .cons (.var .zero) (.cons enclosingBody .nil)

theorem input_matches_original : buildTerm rhoInput inputArguments =
    RhoScopedEquationBindingControls.expectedOpenTarget := rfl

theorem input_opens : Act rhoBase rhoComplete (.ask rhoInput)
    (.term RhoScopedEquationBindingControls.expectedOpenTarget) (.bundle rhoInput inputArguments) :=
  .ask rhoInput trivial (rhoTheory.reflexive _)

theorem input_projects_under_binder : Act rhoBase rhoComplete (.get rhoInput 1)
    (.bundle rhoInput inputArguments) (.term enclosingBody) :=
  .get rhoInput trivial 1 (rhoTheory.reflexive _)

end Mettapedia.OSLF.Binding.ScopedInstruments.Controls
