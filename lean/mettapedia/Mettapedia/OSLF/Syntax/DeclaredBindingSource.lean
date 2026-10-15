import Mettapedia.OSLF.Syntax.DeclaredBindingActivation

/-!
# The named authored source and its lexical-fresh operational projection

Resolution constructs the intrinsic fragment at an explicit context.
The independent operational projection uses the existing scope-policy source:
lambda parameters and local pattern slots have distinct roles, and a where
value is projected before extending the body's role environment.
Neither construction claims to formalize the runtime reader.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation

namespace Named

abbrev context (names : List Nat) : Ctx Target.sig := names.map (fun _ => .term)

def lookup : (names : List Nat) → Nat → Option (Var (context names) .term)
  | [], _ => none
  | first :: rest, name =>
      if first = name then some .zero else (lookup rest name).map Var.succ

theorem lookup_outside : ∀ (names : List Nat) (name : Nat),
    name ∉ names → lookup names name = none
  | [], _, _ => rfl
  | first :: rest, name, absent => by
      have different : first ≠ name := fun equal => absent (by simp [equal])
      have missing : name ∉ rest := fun member => absent (by simp [member])
      simp only [lookup, if_neg different, lookup_outside rest name missing, Option.map_none]

inductive Payload where
  | name (name : Nat)
  | app (function argument : Payload)
  | lambda (name : Nat) (body : Payload)

def Payload.resolve : (names : List Nat) → Payload → Option (Term Target.sig (context names) .term)
  | names, .name chosen => (lookup names chosen).map Term.var
  | names, .app function argument => do
      let f ← function.resolve names
      let a ← argument.resolve names
      pure (LambdaContextualRung.appT f a)
  | names, .lambda chosen body =>
      (body.resolve (chosen :: names)).map LambdaContextualRung.lamT

inductive Source where
  | lambda (name : Nat) (body : Source)
  | whereBinding (name : Nat) (value : Payload) (body : Source)
  | result (payload : Payload)

/-- Local names are introduced in bodies only. Resolution failure retains
the boundary of the admitted context instead of inventing a closed name. -/
def Source.resolve : (names : List Nat) → Source → Option (Program (context names))
  | names, .lambda name body => (body.resolve (name :: names)).map Program.lambda
  | names, .whereBinding name value body => do
      let v ← value.resolve names
      let b ← body.resolve (name :: names)
      pure (Program.whereBinding v b)
  | names, .result payload => (payload.resolve names).map Program.result

theorem unbound_name_rejected :
    Source.resolve [] (.result (.name 17)) = none := rfl

theorem own_value_not_in_scope :
    Source.resolve [] (.whereBinding 17 (.name 17) (.result (.name 17))) = none := rfl

theorem erroneously_extended_value_would_resolve :
    Payload.resolve [17] (.name 17) = some (.var .zero) := rfl

theorem value_uses_outer_binding :
    Source.resolve [17] (.whereBinding 17 (.name 17) (.result (.name 17))) =
      some (.whereBinding (.var .zero) (.result (.var .zero))) := rfl

theorem renamed_locals_same_resolved_program :
    Source.resolve [9] (.lambda 3 (.whereBinding 4 (.name 3)
      (.result (.app (.name 4) (.name 9))))) =
    Source.resolve [9] (.lambda 5 (.whereBinding 6 (.name 5)
      (.result (.app (.name 6) (.name 9))))) := rfl

theorem live_dependency_resolves :
    Source.resolve [9] (.lambda 3 (.result (.app (.name 3) (.name 9)))) =
      some (.lambda (.result (LambdaContextualRung.appT (.var .zero) (.var (.succ .zero))))) := rfl

inductive Role where
  | parameter
  | store

open Mettapedia.GSLT.LanguageDef.TemplateScope

def operationalVariable (roles : List (Nat × Role)) (chosen : Nat) : Src Nat Nat :=
  match roles.lookup chosen with
  | some .parameter => .par chosen
  | some .store => .sv chosen
  | none => .sv chosen

def Payload.operational : List (Nat × Role) → Payload → Src Nat Nat
  | roles, .name chosen => operationalVariable roles chosen
  | roles, .app function argument => .app (function.operational roles) (argument.operational roles)
  | roles, .lambda chosen body => .lam chosen none (body.operational ((chosen, .parameter) :: roles))

def Source.operational : List (Nat × Role) → Source → Src Nat Nat
  | roles, .lambda chosen body => .lam chosen none (body.operational ((chosen, .parameter) :: roles))
  | roles, .whereBinding chosen value body =>
      .letS (.sv chosen) (value.operational roles) (body.operational ((chosen, .store) :: roles)) none
  | roles, .result payload => payload.operational roles

/-- The authored `where` projection actually enters the established
lexical-fresh activation construction, with its value outside the new frame. -/
theorem operational_where_activation (root : Owner) (env : REnv Nat) (pos : Owner)
    (roles : List (Nat × Role)) (chosen : Nat) (value : Payload) (body : Source) :
    elabLF root env [] pos ((Source.whereBinding chosen value body).operational roles) =
      .app (.lam (letParam (pos ++ [2]) chosen) [(pos ++ [2], chosen)]
        (.letP (.var (.src (pos ++ [2], chosen)))
          (.pvar (letParam (pos ++ [2]) chosen))
          (elabLF root (env.update [chosen] (pos ++ [2])) [] (pos ++ [2])
            (body.operational ((chosen, .store) :: roles)))))
        (elabLF root env [] (pos ++ [1]) (value.operational roles)) :=
  Activation.lexical_where_shape root env pos chosen _ _

theorem operational_shadow_keeps_value_role :
    (Source.whereBinding 17 (.name 17) (.result (.name 17))).operational [(17, .parameter)] =
      .letS (.sv 17) (.par 17) (.sv 17) none := rfl

theorem operational_nested_bindings :
    (Source.lambda 3 (.whereBinding 4 (.name 3)
      (.whereBinding 4 (.name 4) (.result (.name 4))))).operational [] =
      .lam 3 none (.letS (.sv 4) (.par 3)
        (.letS (.sv 4) (.sv 4) (.sv 4) none) none) := rfl

theorem result_operational_erasure (roles : List (Nat × Role)) (payload : Payload) :
    (Source.result payload).operational roles = payload.operational roles := rfl

end Named

end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation
