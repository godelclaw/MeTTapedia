import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# The source term fragment and its substitution boundary

The interactive `.mg` term grammar has no term-level type abstraction or
type-universal proposition constructor. Type applications are prefixes on
closed named/primitive heads. This structural invariant explains why its
term substitution can traverse a type application while the publication
Mathdata substitution leaves one intact: there is no term variable there.

The theorem below compares independently defined operations on every admitted
term in this fragment, at every substitution depth and replacement. It makes
no equivalence assertion on unrestricted Mathdata syntax. Type-variable scope,
type-argument arity, definition admission and conversion are separate checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceTermFragment
open MathdataKernel

inductive Head : Tm → Prop where
  | named (name : Name) : Head (.named name)
  | prim (index : Nat) : Head (.prim index)
  | typeApp {head : Tm} (type : Tp) : Head head → Head (.typeApp head type)

inductive Term : Tm → Prop where
  | db (index : Nat) : Term (.db index)
  | head {head : Tm} : Head head → Term head
  | app {function argument : Tm} : Term function → Term argument → Term (.app function argument)
  | lam (type : Tp) {body : Tm} : Term body → Term (.lam type body)
  | imp {domain codomain : Tm} : Term domain → Term codomain → Term (.imp domain codomain)
  | all (type : Tp) {body : Tm} : Term body → Term (.all type body)

def headCheck : Tm → Bool
  | .named _ | .prim _ => true
  | .typeApp head _ => headCheck head
  | _ => false

def termCheck : Tm → Bool
  | .db _ | .named _ | .prim _ => true
  | .app first second | .imp first second => termCheck first && termCheck second
  | .lam _ body | .all _ body => termCheck body
  | .typeApp head _ => headCheck head
  | .typeLam _ | .typeAll _ => false

theorem headCheck_iff (term : Tm) : headCheck term = true ↔ Head term := by
  constructor
  · intro accepted
    induction term with
    | named name => exact .named name
    | prim index => exact .prim index
    | typeApp head type ih => exact .typeApp type (ih accepted)
    | _ => simp [headCheck] at accepted
  · intro head
    induction head with
    | named | prim => rfl
    | typeApp _ _ ih => exact ih

theorem Head.termCheck {term : Tm} (head : Head term) : termCheck term = true := by
  cases head with
  | named | prim => rfl
  | typeApp type head => exact (headCheck_iff _).mpr head

theorem termCheck_iff (term : Tm) : termCheck term = true ↔ Term term := by
  constructor
  · intro accepted
    induction term with
    | db index => exact .db index
    | named name => exact .head (.named name)
    | prim index => exact .head (.prim index)
    | app function argument ihf iha =>
        simp only [termCheck, Bool.and_eq_true] at accepted
        exact .app (ihf accepted.1) (iha accepted.2)
    | imp domain codomain ihd ihc =>
        simp only [termCheck, Bool.and_eq_true] at accepted
        exact .imp (ihd accepted.1) (ihc accepted.2)
    | lam type body ih => exact .lam type (ih accepted)
    | all type body ih => exact .all type (ih accepted)
    | typeApp head type _ => exact .head (.typeApp type ((headCheck_iff _).mp accepted))
    | typeLam | typeAll => simp [termCheck] at accepted
  · intro term
    induction term with
    | db => rfl
    | head head => exact head.termCheck
    | app _ _ ihf iha | imp _ _ ihf iha => simp [termCheck, ihf, iha]
    | lam _ _ ih | all _ _ ih => exact ih

/-- The traversal performed by publication `mathdata.ml:tmsubst`, including
its deliberate boundary at type-level term constructors. -/
def publicationSubstitute (depth : Nat) (replacement : Tm) : Tm → Tm
  | .db index => if index < depth then .db index else if index = depth then
      Tm.shift 0 depth replacement else .db (index - 1)
  | .app function argument =>
      .app (publicationSubstitute depth replacement function) (publicationSubstitute depth replacement argument)
  | .lam type body => .lam type (publicationSubstitute (depth + 1) replacement body)
  | .imp domain codomain =>
      .imp (publicationSubstitute depth replacement domain) (publicationSubstitute depth replacement codomain)
  | .all type body => .all type (publicationSubstitute (depth + 1) replacement body)
  | term => term

theorem Head.shift {head : Tm} (admitted : Head head) (cutoff amount : Nat) :
    Tm.shift cutoff amount head = head := by
  induction admitted <;> simp_all [Tm.shift]

theorem Head.instantiate {head : Tm} (admitted : Head head) (depth : Nat) (replacement : Tm) :
    Tm.instantiateAt depth replacement head = head := by
  induction admitted <;> simp_all [Tm.instantiateAt]

theorem Head.publicationSubstitute {head : Tm} (admitted : Head head) (depth : Nat) (replacement : Tm) :
    publicationSubstitute depth replacement head = head := by
  cases admitted <;> rfl

/-- The two actual traversals coincide on every source-fragment input, with
no assumption that the substituted term is ground or has no type variables. -/
theorem substitution_agrees {body : Tm} (admitted : Term body) (depth : Nat) (replacement : Tm) :
    publicationSubstitute depth replacement body = Tm.instantiateAt depth replacement body := by
  induction admitted generalizing depth with
  | db => rfl
  | head head => rw [head.publicationSubstitute, head.instantiate]
  | app _ _ ihf iha => simp [publicationSubstitute, Tm.instantiateAt, ihf, iha]
  | imp _ _ ihd ihc => simp [publicationSubstitute, Tm.instantiateAt, ihd, ihc]
  | lam _ _ ih | all _ _ ih => simp [publicationSubstitute, Tm.instantiateAt, ih]

theorem Term.shift {body : Tm} (admitted : Term body) (cutoff amount : Nat) :
    Term (Tm.shift cutoff amount body) := by
  induction admitted generalizing cutoff with
  | db index => simp only [Tm.shift]; split <;> exact .db _
  | head head => rw [head.shift]; exact .head head
  | app _ _ ihf iha => exact .app (ihf _) (iha _)
  | imp _ _ ihd ihc => exact .imp (ihd _) (ihc _)
  | lam type _ ih => exact .lam type (ih _)
  | all type _ ih => exact .all type (ih _)

theorem Term.instantiate {body replacement : Tm} (admitted : Term body) (argument : Term replacement)
    (depth : Nat) : Term (Tm.instantiateAt depth replacement body) := by
  induction admitted generalizing depth with
  | db index =>
      simp only [Tm.instantiateAt]
      split
      · exact .db _
      · split
        · exact argument.shift _ _
        · exact .db _
  | head head => rw [head.instantiate]; exact .head head
  | app _ _ ihf iha => exact .app (ihf _) (iha _)
  | imp _ _ ihd ihc => exact .imp (ihd _) (ihc _)
  | lam type _ ih => exact .lam type (ih _)
  | all type _ ih => exact .all type (ih _)

theorem checked_substitution_stays_in_fragment {body replacement : Tm}
    (bodyChecked : termCheck body = true) (argumentChecked : termCheck replacement = true) (depth : Nat) :
    termCheck (publicationSubstitute depth replacement body) = true := by
  have admitted := (termCheck_iff body).mp bodyChecked
  rw [substitution_agrees admitted]
  exact (termCheck_iff _).mpr (admitted.instantiate ((termCheck_iff replacement).mp argumentChecked) depth)

theorem genuine_type_prefix_allowed :
    termCheck (.app (.typeApp (.named "polymorphic") (.var 0)) (.db 0)) = true := rfl

theorem open_polymorphic_head_refused : termCheck (.typeApp (.db 0) .prop) = false := rfl
theorem mixed_type_binder_refused : termCheck (.typeLam (.db 0)) = false := rfl

/-- The distinction remains observable outside the source fragment. -/
theorem unrestricted_substitution_disagrees :
    publicationSubstitute 0 (.named "p") (.typeLam (.db 0)) ≠
      Tm.instantiateAt 0 (.named "p") (.typeLam (.db 0)) := by decide

end Mettapedia.Languages.Megalodon.SourceTermFragment
