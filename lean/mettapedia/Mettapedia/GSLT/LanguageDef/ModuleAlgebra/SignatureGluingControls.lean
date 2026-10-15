import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SignatureGluing
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluingControls
import Mettapedia.OSLF.Syntax.BindingCloneFoldSubstitution

/-!
# Varying-signature gluing controls with an active binder

The Boolean valuation and substitution model is reused from the equation
gluing controls. Components declare distinct private constants and one shared
binding operator. The binding operator evaluates its body with the bound
variable set to a specified Boolean; older variables retain their values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SignatureGluingControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms

abbrev base := SemanticGluingControls.signature
abbrev sharedSubstitution := SemanticGluingControls.substitution

inductive Spec where
  | zero | one | binder
  deriving DecidableEq

def result (_ : Spec) : Unit := ()

def arity : Spec → List (List Unit × Unit)
  | .zero | .one => []
  | .binder => [([()], ())]

abbrev P := Presentation Nat String Spec

def sharedEntry : Entry Nat String Spec := ⟨0, "Bind", .binder⟩
def firstEntry : Entry Nat String Spec := ⟨1, "First", .zero⟩
def secondEntry : Entry Nat String Spec := ⟨2, "Second", .one⟩

def shared : P := ⟨{sharedEntry}, by decide⟩
def left : P := ⟨{sharedEntry, firstEntry}, by decide⟩
def right : P := ⟨{sharedEntry, secondEntry}, by decide⟩
def whole : P := ⟨{sharedEntry, firstEntry, secondEntry}, by decide⟩

theorem joined : join left right = some whole := by
  apply join_eq_some_iff.mpr
  decide

/-- The two component signatures contain genuinely different operators. -/
theorem distinct_operator_inventories :
    firstEntry ∈ left.val ∧ firstEntry ∉ right.val ∧
      secondEntry ∈ right.val ∧ secondEntry ∉ left.val := by decide

def extendValuation {Γ : Ctx base} (value : Bool)
    (valuation : SemanticGluingControls.Valuation Γ) :
    SemanticGluingControls.Valuation (() :: Γ) := fun _ var =>
  match var with
  | .zero => value
  | .succ old => valuation _ old

def evalBinder (value : Bool) {Γ : Ctx base} :
    FamilyArgs base sharedSubstitution.Carrier [([()], ())] Γ →
      sharedSubstitution.Carrier Γ ()
  | .cons body .nil => fun valuation => body (extendValuation value valuation)

theorem evalBinder_substitute (value : Bool) {Γ Δ : Ctx base}
    (env : BindingSubstitutionAlgebra.Environment base sharedSubstitution.Carrier Γ Δ)
    (args : FamilyArgs base sharedSubstitution.Carrier [([()], ())] Γ) :
    sharedSubstitution.substitute env (evalBinder value args) =
      evalBinder value (sharedSubstitution.substituteArgs env args) := by
  cases args with
  | cons body tail =>
      cases tail
      funext valuation
      apply congrArg body
      funext sort var
      cases var <;> rfl

def operation (boundValue : Bool) : (entry : Entry Nat String Spec) →
    SignatureGluing.Operation sharedSubstitution result arity entry
  | ⟨_, _, .zero⟩ => ⟨fun _ => fun _ => false, fun _ _ => rfl⟩
  | ⟨_, _, .one⟩ => ⟨fun _ => fun _ => true, fun _ _ => rfl⟩
  | ⟨_, _, .binder⟩ => ⟨fun args => evalBinder boundValue args,
      fun env args => evalBinder_substitute boundValue env args⟩

def assignment (boundValue : Bool) (p : P) :
    DependentAssignment (SignatureGluing.Operation sharedSubstitution result arity) p :=
  fun entry => operation boundValue entry.val

def combined : DependentAssignment
    (SignatureGluing.Operation sharedSubstitution result arity) whole :=
  glueDependent joined (assignment false left) (assignment false right)

noncomputable def model : SignatureGluing.Model sharedSubstitution result arity whole :=
  ⟨SignatureGluing.algebra sharedSubstitution result arity whole combined, rfl⟩

theorem agree_on_shared :
    ∀ entry hp hq, assignment false left ⟨entry, hp⟩ = assignment false right ⟨entry, hq⟩ :=
  fun _ _ _ => rfl

theorem retains_left (entry : Member left) :
    combined (includeLeft joined entry) = assignment false left entry :=
  glueDependent_left joined _ _ entry

theorem retains_right (entry : Member right) :
    combined (includeRight joined entry) = assignment false right entry :=
  glueDependent_right joined _ _ agree_on_shared entry

private def noVariables : SemanticGluingControls.Valuation [] := fun _ var => nomatch var

def boundVariable : FamilyArgs base sharedSubstitution.Carrier [([()], ())] [] :=
  .cons (sharedSubstitution.injectVar .zero) .nil

theorem binder_reads_its_bound_variable :
    evalBinder false boundVariable noVariables = false ∧
      evalBinder true boundVariable noVariables = true := ⟨rfl, rfl⟩

theorem binder_retains_older_variable (value : Bool) :
    evalBinder value (Γ := [()])
      (.cons (sharedSubstitution.injectVar (.succ .zero)) .nil)
      (fun _ _ => true) = true := rfl

/-- Both private operators exist in the union and retain different values. -/
theorem private_operations_remain_distinct :
    model.val.operation
        ⟨⟨firstEntry, by decide⟩, rfl⟩ (Γ := []) .nil noVariables = false ∧
      model.val.operation
        ⟨⟨secondEntry, by decide⟩, rfl⟩ (Γ := []) .nil noVariables = true := by
  constructor <;> rfl

def boundTerm : Term (SignatureGluing.signature base result arity whole) [] () :=
  .op ⟨⟨sharedEntry, by decide⟩, rfl⟩ (.cons (.var .zero) .nil)

theorem interprets_actual_bound_term :
    BindingCloneFoldSubstitution.interpret model.val boundTerm noVariables = false := rfl

/-- A binder that disagrees on its shared interpretation has no mediator,
although the declaration union is still accepted. -/
theorem incompatible_binders_have_no_glue :
    ¬ ∃ candidate : DependentAssignment
        (SignatureGluing.Operation sharedSubstitution result arity) whole,
      (∀ entry, candidate (includeLeft joined entry) = assignment false left entry) ∧
      (∀ entry, candidate (includeRight joined entry) = assignment true right entry) := by
  apply SignatureGluing.no_glue_of_disagreement joined _ _ sharedEntry (by decide) (by decide)
  intro same
  have impossible : false = true := congrArg
    (fun op : SignatureGluing.Operation sharedSubstitution result arity sharedEntry =>
      op.val (Γ := []) boundVariable noVariables) same
  exact Bool.false_ne_true impossible

/-- Agreement on an empty ancestor cannot detect an additional shared
operator. The complete overlap, rather than any ancestor, is required. -/
theorem empty_ancestor_agrees_despite_obstruction :
    restrictDependent (p := empty) (q := left) (by simp [empty]) (assignment false left) =
      restrictDependent (p := empty) (q := right) (by simp [empty]) (assignment true right) := by
  funext entry
  exact (Finset.notMem_empty entry.val entry.property).elim

theorem let_shared_once : join left left = some left ∧ left.val.card = 2 :=
  ⟨join_self left, by decide⟩

/-! ## A genuine change of sorts in signature morphisms -/

def coloredResult : Spec → Bool
  | .zero | .binder => false
  | .one => true

def coloredArity : Spec → List (List Bool × Bool)
  | .zero | .one => []
  | .binder => [([true], false)]

def coloredBase : Signature where
  Srt := Bool
  Op sort := {spec : Spec // coloredResult spec = sort}
  arity op := coloredArity op.val

def collapse (_ : Bool) : Unit := ()

abbrev targetSignature := SignatureGluing.signature base result arity whole

def collapsedImages : DependentAssignment
    (SignatureGluing.OperatorImage (S := coloredBase)
      targetSignature collapse coloredResult coloredArity) whole := fun entry =>
  ⟨⟨entry, rfl⟩, by
    change arity entry.val.body = mapArities collapse (coloredArity entry.val.body)
    cases entry.val.body <;> rfl⟩

def collapsedMap : SignatureGluing.SignatureMap (S := coloredBase)
    targetSignature collapse coloredResult coloredArity whole :=
  SignatureGluing.signatureMap (S := coloredBase)
    targetSignature collapse coloredResult coloredArity whole collapsedImages

theorem sort_map_identifies_distinct_sorts : false ≠ true ∧ collapse false = collapse true :=
  ⟨by decide, rfl⟩

/-- The binder binds a source `true` variable while producing a `false`
body. Both sorts map to the one target sort, and the arity is retained. -/
theorem collapsed_binder_arity :
    targetSignature.arity
      (collapsedMap.val.opMap ⟨⟨sharedEntry, by decide⟩, rfl⟩) = [([()], ())] := rfl

/-- Sharing a result sort does not license erasing the argument binder. -/
theorem nullary_operator_cannot_be_binder_image :
    targetSignature.arity ⟨⟨firstEntry, by decide⟩, rfl⟩ ≠
      mapArities collapse (coloredArity .binder) := by
  change ([] : List (List Unit × Unit)) ≠ [([()], ())]
  decide

/-- A sort-collapsing morphism can expose a target variable without a
source variable of the requested sort. Signature transport alone is not
a reflection theorem for scoped variables. -/
theorem variable_reflection_fails_after_sort_collapse :
    Nonempty (Var ([true].map collapse) ()) ∧ IsEmpty (Var [true] false) := by
  refine ⟨⟨.zero⟩, ⟨?_⟩⟩
  intro var
  cases var with
  | succ old => cases old

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SignatureGluingControls
