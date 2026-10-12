import Mettapedia.OSLF.Syntax.BindingCloneEquationTransport
import Mettapedia.OSLF.Syntax.BindingCloneContextComparison
import Mettapedia.OSLF.Syntax.LambdaContextualRung

/-!
# Context-respecting interpretation of the declared binding package

The scope-resolved fragment has one fresh variable at each `binding:lambda`
or `binding:where`. The latter's value remains in the outer context. Target
lambda terms occurring in a value or a `binding:result` payload are retained
through explicit base constructors. Neither parsing nor arbitrary relational
patterns are identified with this scope-resolved fragment.

The target is the independently specified contextual lambda signature.
`where` denotes application of an abstraction, and `result` is transparent.
The source model is constructed over every target binding-clone algebra;
its operation/substitution obligations are proved from the target operations.
The established initial fold then supplies simultaneous-substitution and
renaming preservation, including arbitrary ambient contexts and binder lifts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation

open FreeBindingTerms BindingSubstitutionAlgebra BindingCloneFoldSubstitution

namespace Target
abbrev sig := LambdaContextualRung.sig
end Target

inductive Op : LambdaContextualRung.Srt → Type where
  | baseApp : Op .term
  | baseLam : Op .term
  | lambda : Op .term
  | whereBinding : Op .term
  | result : Op .term

abbrev sig : Signature where
  Srt := Target.sig.Srt
  Op := Op
  arity := fun {_} op => match op with
    | .baseApp => [([], .term), ([], .term)]
    | .baseLam | .lambda => [([.term], .term)]
    | .whereBinding => [([], .term), ([.term], .term)]
    | .result => [([], .term)]

def lambda {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) :
    Term sig Γ .term := .op .lambda (.cons body .nil)

def whereBinding {Γ : Ctx sig} (value : Term sig Γ .term)
    (body : Term sig (.term :: Γ) .term) : Term sig Γ .term :=
  .op .whereBinding (.cons value (.cons body .nil))

def result {Γ : Ctx sig} (payload : Term sig Γ .term) : Term sig Γ .term :=
  .op .result (.cons payload .nil)

universe u v

/-- Reuse the target's substitution carrier at the definitionally identical
sorts and contexts; no source operation or substitution law is assumed. -/
def targetSubstitution (A : BindingCloneAlgebra.Algebra.{u} Target.sig) :
    BindingSubstitutionAlgebra.Algebra.{u} sig where
  Carrier := A.substitution.Carrier
  injectVar := A.substitution.injectVar
  substitute := A.substitution.substitute
  substitute_var := A.substitution.substitute_var
  substitute_identity := A.substitution.substitute_identity
  substitute_comp := A.substitution.substitute_comp

theorem targetSubstitution_lift (A : BindingCloneAlgebra.Algebra.{u} Target.sig)
    {Γ Δ : Ctx sig} (env : Environment sig A.substitution.Carrier Γ Δ) :
    ∀ (bs : List sig.Srt),
      (targetSubstitution A).liftEnvironment env bs =
        A.substitution.liftEnvironment env bs
  | [] => rfl
  | _ :: bs => by
      funext s x
      cases x with
      | zero => rfl
      | succ old =>
          change A.substitution.weaken
            ((targetSubstitution A).liftEnvironment env bs s old) =
              A.substitution.weaken (A.substitution.liftEnvironment env bs s old)
          rw [targetSubstitution_lift A env bs]

/-- Read one existing semantic argument vector without changing its signature. -/
def argumentHead {S : Signature} {F : Ctx S → S.Srt → Type u}
    {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt} {rest : List (List S.Srt × S.Srt)} :
    FamilyArgs S F ((bs, s) :: rest) Γ → F (bs ++ Γ) s
  | .cons head _ => head

def argumentTail {S : Signature} {F : Ctx S → S.Srt → Type u}
    {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt} {rest : List (List S.Srt × S.Srt)} :
    FamilyArgs S F ((bs, s) :: rest) Γ → FamilyArgs S F rest Γ
  | .cons _ tail => tail

theorem argumentHead_substitute {S : Signature} (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (env : Environment S A.Carrier Γ Δ)
    {bs : List S.Srt} {s : S.Srt} {rest : List (List S.Srt × S.Srt)} :
    ∀ (args : FamilyArgs S A.Carrier ((bs, s) :: rest) Γ),
      argumentHead (A.substituteArgs env args) =
        A.substitute (A.liftEnvironment env bs) (argumentHead args)
  | .cons _ _ => rfl

theorem argumentTail_substitute {S : Signature} (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (env : Environment S A.Carrier Γ Δ)
    {bs : List S.Srt} {s : S.Srt} {rest : List (List S.Srt × S.Srt)} :
    ∀ (args : FamilyArgs S A.Carrier ((bs, s) :: rest) Γ),
      argumentTail (A.substituteArgs env args) = A.substituteArgs env (argumentTail args)
  | .cons _ _ => rfl

theorem argumentHead_map {S : Signature}
    {F : Ctx S → S.Srt → Type u} {G : Ctx S → S.Srt → Type v}
    (f : {Γ : Ctx S} → {s : S.Srt} → F Γ s → G Γ s)
    {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt} {rest : List (List S.Srt × S.Srt)} :
    ∀ (args : FamilyArgs S F ((bs, s) :: rest) Γ),
      argumentHead (FamilyArgs.map f args) = f (argumentHead args)
  | .cons _ _ => rfl

theorem argumentTail_map {S : Signature}
    {F : Ctx S → S.Srt → Type u} {G : Ctx S → S.Srt → Type v}
    (f : {Γ : Ctx S} → {s : S.Srt} → F Γ s → G Γ s)
    {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt} {rest : List (List S.Srt × S.Srt)} :
    ∀ (args : FamilyArgs S F ((bs, s) :: rest) Γ),
      argumentTail (FamilyArgs.map f args) = FamilyArgs.map f (argumentTail args)
  | .cons _ _ => rfl

def operation (A : BindingCloneAlgebra.Algebra.{u} Target.sig)
    {Γ : Ctx sig} {s : sig.Srt} (op : sig.Op s)
    (args : FamilyArgs sig A.substitution.Carrier (sig.arity op) Γ) :
    A.substitution.Carrier Γ s :=
  match op with
  | .baseApp => A.operation .app (.cons (argumentHead args)
      (.cons (argumentHead (argumentTail args)) .nil))
  | .baseLam => A.operation .lam (.cons (argumentHead args) .nil)
  | .lambda => A.operation .lam (.cons (argumentHead args) .nil)
  | .whereBinding => A.operation .app
      (.cons (A.operation .lam (.cons (argumentHead (argumentTail args)) .nil))
        (.cons (argumentHead args) .nil))
  | .result => argumentHead args

theorem operation_substitute (A : BindingCloneAlgebra.Algebra.{u} Target.sig)
    {Γ Δ : Ctx sig} {s : sig.Srt}
    (env : Environment sig A.substitution.Carrier Γ Δ) (op : sig.Op s)
    (args : FamilyArgs sig A.substitution.Carrier (sig.arity op) Γ) :
    A.substitution.substitute env (operation A op args) =
      operation A op ((targetSubstitution A).substituteArgs env args) := by
  cases op with
  | baseApp =>
      simp only [operation, argumentHead_substitute, argumentTail_substitute,
        Algebra.liftEnvironment]
      exact A.operation_substitute env .app
        (.cons (argumentHead args) (.cons (argumentHead (argumentTail args)) .nil))
  | baseLam =>
      simp only [operation, argumentHead_substitute, targetSubstitution_lift]
      exact A.operation_substitute env .lam (.cons (argumentHead args) .nil)
  | lambda =>
      simp only [operation, argumentHead_substitute, targetSubstitution_lift]
      exact A.operation_substitute env .lam (.cons (argumentHead args) .nil)
  | whereBinding =>
      simp only [operation, argumentHead_substitute, argumentTail_substitute,
        targetSubstitution_lift]
      rw [A.operation_substitute]
      change A.operation .app
          (.cons (A.substitution.substitute env
            (A.operation .lam (.cons (argumentHead (argumentTail args)) .nil)))
            (.cons (A.substitution.substitute env (argumentHead args)) .nil)) = _
      rw [A.operation_substitute]
      rfl
  | result =>
      simp only [operation, argumentHead_substitute, Algebra.liftEnvironment]
      rfl

/-- The authored constructors, including derived binding and erasure,
form an actual source model over each independently specified target model. -/
def model (A : BindingCloneAlgebra.Algebra.{u} Target.sig) :
    BindingCloneAlgebra.Algebra.{u} sig where
  substitution := targetSubstitution A
  operation := operation A
  operation_substitute := operation_substitute A

def lower {Γ : Ctx sig} {s : sig.Srt} (term : Term sig Γ s) :
    Term Target.sig Γ s := interpret (model (BindingCloneAlgebra.terms Target.sig)) term

@[simp] theorem lower_var {Γ : Ctx sig} {s : sig.Srt} (x : Var Γ s) :
    lower (.var x) = .var x := rfl

@[simp] theorem lower_lambda {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) :
    lower (lambda body) = LambdaContextualRung.lamT (lower body) := rfl

@[simp] theorem lower_where {Γ : Ctx sig} (value : Term sig Γ .term)
    (body : Term sig (.term :: Γ) .term) :
    lower (whereBinding value body) =
      LambdaContextualRung.appT (LambdaContextualRung.lamT (lower body))
        (lower value) := rfl

@[simp] theorem lower_result {Γ : Ctx sig} (payload : Term sig Γ .term) :
    lower (result payload) = lower payload := rfl

/-- The transport square, for every source term and simultaneous environment. -/
theorem lower_bind {Γ Δ : Ctx sig} {s : sig.Srt}
    (sigma : Sub sig Γ Δ) (term : Term sig Γ s) :
    lower (bind sigma term) = bind (fun s x => lower (sigma s x)) (lower term) :=
  interpret_bind (model (BindingCloneAlgebra.terms Target.sig)) sigma term

theorem lower_rename {Γ Δ : Ctx sig} {s : sig.Srt}
    (rho : Ren sig Γ Δ) (term : Term sig Γ s) :
    lower (rename rho term) = rename (S := Target.sig) rho (lower term) := by
  have naturality := interpret_rename (model (BindingCloneAlgebra.terms Target.sig)) rho term
  exact naturality.trans (bind_var_eq_rename (S := Target.sig) rho (lower term))

/-- Fresh local projections and live enclosing dependencies are treated
uniformly beneath any declared binder list. -/
theorem lower_liftSub {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    (bs : List sig.Srt) (s : sig.Srt) (x : Var (bs ++ Γ) s) :
    lower (liftSub sigma bs s x) =
      liftSub (S := Target.sig) (fun s x => lower (sigma s x)) bs s x := by
  have lifted := liftedInterpretation_apply
    (model (BindingCloneAlgebra.terms Target.sig)) sigma bs s x
  have comparison := targetSubstitution_lift
    (BindingCloneAlgebra.terms Target.sig) (fun s x => lower (sigma s x)) bs
  change (targetSubstitution (BindingCloneAlgebra.terms Target.sig)).liftEnvironment
    (fun s x => lower (sigma s x)) bs s x = lower (liftSub sigma bs s x) at lifted
  rw [comparison] at lifted
  change (BindingSubstitutionAlgebra.terms Target.sig).liftEnvironment
    (fun s x => lower (sigma s x)) bs s x = lower (liftSub sigma bs s x) at lifted
  rw [terms_liftEnvironment_eq_liftSub] at lifted
  exact lifted.symm

theorem lower_identity {Γ : Ctx sig} {s : sig.Srt} (term : Term sig Γ s) :
    lower (bind (fun _ x => .var x) term) = lower term := by
  rw [bind_id]

theorem lower_composition {Γ Δ Θ : Ctx sig} {s : sig.Srt}
    (first : Sub sig Γ Δ) (second : Sub sig Δ Θ) (term : Term sig Γ s) :
    lower (bind second (bind first term)) =
      bind (fun s x => bind (fun s y => lower (second s y)) (lower (first s x)))
        (lower term) := by
  rw [lower_bind, lower_bind, bind_comp]

/-- The target payload language is embedded without inventing any of the
authored wrappers. Its variables retain their ambient context. -/
def payloadSubstitution : BindingSubstitutionAlgebra.Algebra Target.sig where
  Carrier := Term sig
  injectVar := fun x => Term.var (S := sig) x
  substitute := fun env term => bind (S := sig) env term
  substitute_var := by intros; rfl
  substitute_identity := by intro Γ s term; exact bind_id term
  substitute_comp := by intro Γ Δ Θ s first second term; exact bind_comp first second term

theorem payloadSubstitution_lift {Γ Δ : Ctx Target.sig} (env : Sub sig Γ Δ) :
    ∀ (bs : List Target.sig.Srt),
      payloadSubstitution.liftEnvironment env bs = liftSub (S := sig) env bs
  | [] => rfl
  | _ :: bs => by
      funext s x
      cases x with
      | zero => rfl
      | succ old =>
          change bind (fun _ v => Term.var (.succ v))
              (payloadSubstitution.liftEnvironment env bs s old) =
            weaken (liftSub env bs s old)
          rw [payloadSubstitution_lift env bs]
          exact bind_var_eq_rename (fun _ v => Var.succ v) _

def payloadModel : BindingCloneAlgebra.Algebra Target.sig where
  substitution := payloadSubstitution
  operation := fun {_} {_} op args => match op with
    | .app => .op .baseApp (.cons (argumentHead args)
        (.cons (argumentHead (argumentTail args)) .nil))
    | .lam => .op .baseLam (.cons (argumentHead args) .nil)
  operation_substitute := by
    intro Γ Δ s env op args
    cases op with
    | app =>
        simp only [argumentHead_substitute, argumentTail_substitute]
        rfl
    | lam =>
        simp only [argumentHead_substitute]
        change Term.op (S := sig) Op.baseLam
            (.cons (bind (S := sig) (liftSub (S := sig) env [LambdaContextualRung.Srt.term])
              (argumentHead args)) .nil) =
          Term.op (S := sig) Op.baseLam (.cons (bind (S := sig)
            (payloadSubstitution.liftEnvironment env [LambdaContextualRung.Srt.term])
            (argumentHead args)) .nil)
        rw [payloadSubstitution_lift]

def embed {Γ : Ctx Target.sig} {s : Target.sig.Srt} (term : Term Target.sig Γ s) :
    Term sig Γ s := interpret payloadModel term

theorem embed_bind {Γ Δ : Ctx Target.sig} {s : Target.sig.Srt}
    (sigma : Sub Target.sig Γ Δ) (term : Term Target.sig Γ s) :
    embed (bind sigma term) = bind (fun s x => embed (sigma s x)) (embed term) :=
  interpret_bind payloadModel sigma term

theorem embed_liftSub {Γ Δ : Ctx Target.sig} (sigma : Sub Target.sig Γ Δ)
    (bs : List Target.sig.Srt) (s : Target.sig.Srt) (x : Var (bs ++ Γ) s) :
    embed (liftSub sigma bs s x) =
      liftSub (S := sig) (fun s x => embed (sigma s x)) bs s x := by
  have lifted := liftedInterpretation_apply payloadModel sigma bs s x
  change payloadSubstitution.liftEnvironment
      (fun s x => embed (sigma s x)) bs s x = embed (liftSub sigma bs s x) at lifted
  rw [payloadSubstitution_lift] at lifted
  exact lifted.symm

theorem lower_embed : ∀ {Γ : Ctx Target.sig} {s : Target.sig.Srt}
    (term : Term Target.sig Γ s), lower (embed term) = term
  | _, _, .var _ => rfl
  | _, _, .op .app (.cons f (.cons a .nil)) => by
      change LambdaContextualRung.appT (lower (embed f)) (lower (embed a)) =
        LambdaContextualRung.appT f a
      rw [lower_embed f, lower_embed a]
  | _, _, .op .lam (.cons body .nil) => by
      change LambdaContextualRung.lamT (lower (embed body)) =
        LambdaContextualRung.lamT body
      rw [lower_embed body]

/-- The exact scope-resolved authored grammar: wrapper bodies are recursively
lowered; a `where` value and a `result` payload are opaque target-language
terms. Each admitted pattern is one locally introduced variable. -/
inductive Program : Ctx sig → Type where
  | lambda {Γ : Ctx sig} (body : Program (.term :: Γ)) : Program Γ
  | whereBinding {Γ : Ctx sig} (value : Term Target.sig Γ .term)
      (body : Program (.term :: Γ)) : Program Γ
  | result {Γ : Ctx sig} (payload : Term Target.sig Γ .term) : Program Γ

def Program.source : {Γ : Ctx sig} → Program Γ → Term sig Γ .term
  | _, .lambda body => DeclaredBindingInterpretation.lambda body.source
  | _, .whereBinding value body => DeclaredBindingInterpretation.whereBinding (embed value) body.source
  | _, .result payload => DeclaredBindingInterpretation.result (embed payload)

/-- This independently structural interpretation states the authored
semantics, before comparison with the generic initial fold. -/
def Program.meaning : {Γ : Ctx sig} → Program Γ → Term Target.sig Γ .term
  | _, .lambda body => LambdaContextualRung.lamT body.meaning
  | _, .whereBinding value body =>
      LambdaContextualRung.appT (LambdaContextualRung.lamT body.meaning) value
  | _, .result payload => payload

theorem Program.lower_source : ∀ {Γ : Ctx sig} (program : Program Γ),
    lower program.source = program.meaning
  | _, .lambda body => by rw [Program.source, lower_lambda, lower_source body]; rfl
  | _, .whereBinding value body => by
      rw [Program.source, lower_where, lower_embed, lower_source body]; rfl
  | _, .result payload => by rw [Program.source, lower_result, lower_embed]; rfl

/-- The authored fragment is closed under substitution of its opaque payload
language. Values use the outer environment; recursive bodies use its lift. -/
def Program.substitute : {Γ Δ : Ctx sig} → Sub Target.sig Γ Δ → Program Γ → Program Δ
  | _, _, sigma, .lambda body => .lambda (body.substitute (liftSub sigma [.term]))
  | _, _, sigma, .whereBinding value body =>
      .whereBinding (bind sigma value) (body.substitute (liftSub sigma [.term]))
  | _, _, sigma, .result payload => .result (bind sigma payload)

theorem Program.source_substitute : ∀ {Γ Δ : Ctx sig}
    (sigma : Sub Target.sig Γ Δ) (program : Program Γ),
    (program.substitute sigma).source =
      bind (fun s x => embed (sigma s x)) program.source
  | _, _, sigma, .lambda body => by
      change DeclaredBindingInterpretation.lambda
          (body.substitute (liftSub sigma [.term])).source =
        DeclaredBindingInterpretation.lambda
          (bind (liftSub (fun s x => embed (sigma s x)) [.term]) body.source)
      rw [source_substitute]
      congr 2
      funext s x
      exact embed_liftSub sigma [.term] s x
  | _, _, sigma, .whereBinding value body => by
      change DeclaredBindingInterpretation.whereBinding (embed (bind sigma value))
          (body.substitute (liftSub sigma [.term])).source =
        DeclaredBindingInterpretation.whereBinding
          (bind (fun s x => embed (sigma s x)) (embed value))
          (bind (liftSub (fun s x => embed (sigma s x)) [.term]) body.source)
      rw [embed_bind, source_substitute]
      congr 2
      funext s x
      exact embed_liftSub sigma [.term] s x
  | _, _, sigma, .result payload => by
      change DeclaredBindingInterpretation.result (embed (bind sigma payload)) =
        DeclaredBindingInterpretation.result
          (bind (fun s x => embed (sigma s x)) (embed payload))
      rw [embed_bind]

/-- This law is proved for the independent structural meaning, not by
defining the meaning to be its generic lowering. -/
theorem Program.meaning_substitute : ∀ {Γ Δ : Ctx sig}
    (sigma : Sub Target.sig Γ Δ) (program : Program Γ),
    (program.substitute sigma).meaning = bind sigma program.meaning
  | _, _, sigma, .lambda body => by
      change LambdaContextualRung.lamT
          (body.substitute (liftSub sigma [.term])).meaning =
        LambdaContextualRung.lamT (bind (liftSub sigma [.term]) body.meaning)
      rw [meaning_substitute]
  | _, _, sigma, .whereBinding value body => by
      change LambdaContextualRung.appT
          (LambdaContextualRung.lamT (body.substitute (liftSub sigma [.term])).meaning)
          (bind sigma value) =
        LambdaContextualRung.appT
          (LambdaContextualRung.lamT (bind (liftSub sigma [.term]) body.meaning))
          (bind sigma value)
      rw [meaning_substitute]
  | _, _, _, .result _ => rfl

theorem Program.substitute_identity : ∀ {Γ : Ctx sig} (program : Program Γ),
    program.substitute (fun _ x => .var x) = program
  | _, .lambda body => by
      simp only [substitute, liftSub_var]
      exact congrArg Program.lambda (Program.substitute_identity body)
  | _, .whereBinding value body => by
      simp only [substitute, liftSub_var, bind_id]
      exact congrArg (Program.whereBinding value) (Program.substitute_identity body)
  | _, .result payload => by simp only [substitute, bind_id]

theorem Program.substitute_composition : ∀ {Γ Δ Θ : Ctx sig}
    (first : Sub Target.sig Γ Δ) (second : Sub Target.sig Δ Θ) (program : Program Γ),
    (program.substitute first).substitute second =
      program.substitute (fun s x => bind second (first s x))
  | _, _, _, first, second, .lambda body => by
      simp only [substitute, substitute_composition, liftSub_comp]
  | _, _, _, first, second, .whereBinding value body => by
      simp only [substitute, substitute_composition, bind_comp, liftSub_comp]
  | _, _, _, _, _, .result _ => by simp only [substitute, bind_comp]

def Program.renamed {Γ Δ : Ctx sig} (rho : Ren Target.sig Γ Δ) (program : Program Γ) :
    Program Δ := program.substitute (fun s x => .var (rho s x))

theorem Program.meaning_rename {Γ Δ : Ctx sig} (rho : Ren Target.sig Γ Δ)
    (program : Program Γ) :
    (program.renamed rho).meaning = rename rho program.meaning := by
  rw [renamed, meaning_substitute, bind_var_eq_rename]

theorem Program.source_rename {Γ Δ : Ctx sig} (rho : Ren Target.sig Γ Δ)
    (program : Program Γ) :
    (program.renamed rho).source = rename (S := sig) rho program.source := by
  rw [renamed, source_substitute]
  exact bind_var_eq_rename (S := sig) rho program.source

end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation
