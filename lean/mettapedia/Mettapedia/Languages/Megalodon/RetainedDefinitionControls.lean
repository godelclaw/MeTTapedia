import Mettapedia.Languages.Megalodon.CheckedProofReconstruction
import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution

/-!
# Defined and opaque constants in retained native proof reconstruction

The native definition-conversion example proves `idp p → p` by the identity
proof. Reconstructing it exposes the equation `idp = fun p => p` as an ordinary
HOL premise. The same native proof is rejected when `idp` is declared opaque.
Body formation alone cannot supply that equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.Megalodon.RetainedDefinitionControls
open MathdataKernel HenkinTermInterpretation HenkinTermInterpretation.NativeProof
open Mettapedia.Logic.HOL

abbrev env := definitionConversionEnvironment
abbrev Constants := Constant env

theorem checked : CheckedPlainDefinitions env where
  body := by
    intro name declaration body lookup defined representable
    simp only [env, definitionConversionEnvironment, Environment.lookupTerm?, lookupTermList?] at lookup
    split at lookup
    · cases lookup
      cases Option.some.inj defined
      exact ⟨rfl, rfl, trivial, rfl⟩
    · split at lookup
      · cases lookup
        cases defined
      · cases lookup

def idp : Constants (.arr .prop .prop) :=
  .named "idp" ⟨"idp", .arr .prop .prop, some (.lam .prop (.db 0))⟩ rfl rfl

def proposition : Constants .prop := .named "p" ⟨"p", .prop, none⟩ rfl rfl

def identityBody : ClosedTerm Constants (.arr .prop .prop) := .lam (.var .vz)
def theory : List (ClosedFormula Constants) := [.eq (.const idp) identityBody]

def equations : RetainedDeltaNormalization.DefinitionEquations checked theory := by
  intro type name declaration lookup typed body defined
  simp only [env, definitionConversionEnvironment, Environment.lookupTerm?, lookupTermList?] at lookup
  split at lookup
  · rename_i same
    have nameEq : name = "idp" := (beq_iff_eq.mp same).symm
    subst name
    cases lookup
    cases Option.some.inj defined
    have typeEq : type = .arr .prop .prop := reifyType_injective typed.symm
    subst type
    have bodyEq : checked.interpretBody "idp" _ rfl rfl (.lam .prop (.db 0)) rfl = identityBody :=
      erase_injective_of_eq_some (checked.erase_interpretBody _ _ _ _ _ _) rfl
    exact ProofSyntax.castIndices rfl (congrArg (Term.eq (.const idp)) bodyEq.symm)
      (.hyp ⟨0, by decide⟩)
  · split at lookup
    · cases lookup
      cases defined
    · cases lookup

def noKnown : CheckedProofReconstruction.KnownSources (environment := env) theory := by
  intro name raw lookup
  simp [env, definitionConversionEnvironment, Environment.lookupKnown?, lookupKnownList?] at lookup

def goal : ClosedFormula Constants := .imp (.app (.const idp) (.const proposition)) (.const proposition)

theorem goal_erased : erase goal = some definitionConversionGoal := rfl

theorem fragment : Fragment env 0 definitionConversionProof := by
  apply Fragment.proofLam
  · rfl
  · constructor <;> intro declaration lookup <;>
      simp [env, definitionConversionEnvironment, Environment.lookupTerm?, lookupTermList?] at lookup <;>
      subst declaration <;> rfl
  · exact .hyp 0

/-- The original native proof computes this retained source derivation with
its definition equation still visible among the assumptions. -/
def retained : ProofSyntax Constants theory goal :=
  CheckedProofReconstruction.checkedSourceDefined checked theory equations noKnown 16 0
    (Γ := []) [] (rawHypotheses := []) rfl definitionConversionProof fragment
    goal goal_erased definition_conversion_accepted

theorem opaque_refused :
    checkProof opaqueIdentityEnvironment 16 0 [] [] definitionConversionProof definitionConversionGoal = false :=
  opaque_identity_rejected

/-- Independent interpretations of the same declared symbol types. -/
def denoteConstant (identity : Bool) {type : Ty Base} (symbol : Constants type) :
    Ty.denote.{0, 1} (fun _ : Base => ULift.{1} Unit) type := by
  cases symbol with
  | primitive index lookup => simp [env, definitionConversionEnvironment] at lookup
  | named name declaration lookup typed =>
      simp only [env, definitionConversionEnvironment, Environment.lookupTerm?, lookupTermList?] at lookup
      split at lookup
      · cases lookup
        have typeEq : type = .arr .prop .prop := reifyType_injective typed.symm
        subst type
        exact fun value => if identity then value else .up True
      · split at lookup
        · cases lookup
          have typeEq : type = .prop := reifyType_injective typed.symm
          subst type
          exact .up False
        · cases lookup

def model (identity : Bool) : HenkinModel.{0, 0, 1} Base Constants :=
  .standard (fun _ => ULift.{1} Unit) (denoteConstant identity)

theorem identity_model_satisfies_equation :
    (model true).models (.eq (.const idp) identityBody) := by
  intro value _
  rfl

/-- Typing the same symbols does not establish the defining equation or the
source theorem. The alternative interpretation makes the antecedent true and
its consequent false. -/
theorem nonidentity_model_refutes_goal : ¬ (model false).models goal := by
  change ¬ (True → False)
  exact fun claimed => claimed trivial

theorem no_definition_free_proof : ¬ Nonempty (ProofSyntax Constants [] goal) := by
  rintro ⟨proof⟩
  apply nonidentity_model_refutes_goal
  exact Soundness.extDerivation_sound proof.erase
    ((model false).functionsRespectEqv_of_fullDomains
      (HenkinModel.fullDomains_standard _ _))
    (fun index => nomatch index)
    (by intro formula member; cases member)

namespace DefinitionErasure

/-- The original signature has only the parameter, before adding `idp`. -/
def oldEnvironment : Environment := {terms := [⟨"p", .prop, none⟩]}
abbrev OldConstants := Constant oldEnvironment

def oldProposition : OldConstants .prop := .named "p" ⟨"p", .prop, none⟩ rfl rfl

def images {type : Ty Base} (symbol : Constants type) : ClosedTerm OldConstants type := by
  cases symbol with
  | primitive index lookup => simp [env, definitionConversionEnvironment] at lookup
  | named name declaration lookup typed =>
      simp only [env, definitionConversionEnvironment, Environment.lookupTerm?, lookupTermList?] at lookup
      split at lookup
      · cases lookup
        have typeEq : type = .arr .prop .prop := reifyType_injective typed.symm
        subst type
        exact .lam (.var .vz)
      · split at lookup
        · cases lookup
          have typeEq : type = .prop := reifyType_injective typed.symm
          subst type
          exact .const oldProposition
        · cases lookup

def expandedGoal : ClosedFormula OldConstants :=
  .imp (.app (.lam (.var .vz)) (.const oldProposition)) (.const oldProposition)

theorem goal_expands : substConst (fun {type} => @images type) goal = expandedGoal := rfl

theorem theory_expands : theory.map (substConst (fun {type} => @images type)) =
    [.eq (.lam (.var .vz) : ClosedTerm OldConstants (.prop ⇒ .prop)) (.lam (.var .vz))] := rfl

/-- Substitute the actual defining body through every node of the retained
proof and discharge the resulting reflexive equation. The output signature
has no `idp` symbol and the output proof has no defining assumptions. -/
def proof : ProofSyntax OldConstants [] expandedGoal := by
  let expanded := ProofSyntax.substConst (fun {type} => @images type) retained
  let normalized : ProofSyntax OldConstants
      [.eq (.lam (.var .vz) : ClosedTerm OldConstants (.prop ⇒ .prop)) (.lam (.var .vz))]
      expandedGoal := ProofSyntax.castIndices theory_expands goal_expands expanded
  refine normalized.substituteHypotheses ?_
  intro occurrence
  have same : occurrence = 0 := Fin.eq_zero occurrence
  subst occurrence
  exact .eqRefl (.lam (.var .vz) : ClosedTerm OldConstants (.prop ⇒ .prop))

/-- The defining premise is necessary when the symbol is opaque, yet it is
eliminated by the actual signature interpretation that unfolds the body. -/
theorem expanded_derivable : ExtDerivation OldConstants [] expandedGoal := proof.erase

end DefinitionErasure

namespace Cyclic

def environment : Environment :=
  {terms := [⟨"loop", .prop, some (.named "loop")⟩]}

def loop : Constant environment .prop :=
  .named "loop" ⟨"loop", .prop, some (.named "loop")⟩ rfl rfl

theorem body_typed : inferTerm environment 0 [] (.named "loop") = some .prop := rfl

def equation : ProofSyntax (Constant environment) []
    (.eq (.const loop : ClosedTerm (Constant environment) .prop) (.const loop)) := .eqRefl _

/-- A typed definition with a provable reflexive equation still exhausts
all finite unfolding budgets. Equality evidence is not a termination proof. -/
theorem all_fuels_exhausted (fuel : Nat) :
    deltaNormalize environment fuel (.named "loop") = none := by
  induction fuel with
  | zero => simp [deltaNormalize, environment, Environment.lookupTerm?, lookupTermList?]
  | succ fuel ih =>
      simpa [deltaNormalize, environment, Environment.lookupTerm?, lookupTermList?] using ih

end Cyclic

end Mettapedia.Languages.Megalodon.RetainedDefinitionControls
