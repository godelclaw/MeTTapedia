import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.OSLF.Syntax.SortedConstructorContexts

/-!
# Context-indexed constructors for intrinsically scoped binding terms

The context is part of every interface. An operator argument occupies its
declared extended context, and a variable constructor retains its actual
position. These are constructor data, without an assumed term comparison or
an interpretation of binding equations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open Mettapedia.OSLF.SortedConstructors

variable (S : Binding.Signature)

abbrev Scope := Binding.Ctx S × S.Srt

inductive Constructor where
  | variable (context : Binding.Ctx S) (sort : S.Srt)
      (position : Binding.Var context sort)
  | operation (context : Binding.Ctx S) (sort : S.Srt) (operator : S.Op sort)

abbrev signature : SortedConstructors.Signature where
  Srt := Scope S
  Constructor := Constructor S
  arity := fun constructor => match constructor with
    | .variable _ _ _ => 0
    | .operation _ _ operator => (S.arity operator).length
  input := fun constructor position => match constructor with
    | .variable _ _ _ => Fin.elim0 position
    | .operation context _ operator =>
        let declaration := (S.arity operator).get position
        (declaration.1 ++ context, declaration.2)
  output := fun constructor => match constructor with
    | .variable context sort _ => (context, sort)
    | .operation context sort _ => (context, sort)

variable {S}

/-- Every coordinate is read from the original ordered argument list. -/
def argumentsAt : {declarations : List (List S.Srt × S.Srt)} →
    {context : Binding.Ctx S} → Binding.Args S declarations context →
      (position : Fin declarations.length) →
        Binding.Term S ((declarations.get position).1 ++ context)
          (declarations.get position).2
  | _, _, .nil => fun position => Fin.elim0 position
  | _, _, .cons head tail => Fin.cases head (argumentsAt tail)

/-- Independently assemble an argument list from its complete typed family. -/
def assembleArguments (context : Binding.Ctx S) :
    (declarations : List (List S.Srt × S.Srt)) →
    ((position : Fin declarations.length) →
      Binding.Term S ((declarations.get position).1 ++ context)
        (declarations.get position).2) → Binding.Args S declarations context
  | [], _ => .nil
  | _ :: tail, arguments =>
      .cons (arguments 0) (assembleArguments context tail (fun position => arguments position.succ))

theorem assemble_argumentsAt : ∀ {declarations : List (List S.Srt × S.Srt)}
    {context : Binding.Ctx S} (arguments : Binding.Args S declarations context),
    assembleArguments context declarations (argumentsAt arguments) = arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg (Binding.Args.cons head) (assemble_argumentsAt tail)

theorem argumentsAt_assemble (context : Binding.Ctx S) :
    ∀ (declarations : List (List S.Srt × S.Srt))
      (arguments : (position : Fin declarations.length) →
        Binding.Term S ((declarations.get position).1 ++ context)
          (declarations.get position).2),
      argumentsAt (assembleArguments context declarations arguments) = arguments
  | [], arguments => by funext position; exact Fin.elim0 position
  | _ :: tail, arguments => by
      funext position
      refine Fin.cases ?_ (fun previous => ?_) position
      · rfl
      · exact congrFun (argumentsAt_assemble context tail
          (fun previous => arguments previous.succ)) previous

def argumentEquiv (context : Binding.Ctx S) (declarations : List (List S.Srt × S.Srt)) :
    Binding.Args S declarations context ≃
      ((position : Fin declarations.length) →
        Binding.Term S ((declarations.get position).1 ++ context)
          (declarations.get position).2) where
  toFun := argumentsAt
  invFun := assembleArguments context declarations
  left_inv := assemble_argumentsAt
  right_inv := argumentsAt_assemble context declarations

end Mettapedia.OSLF.Binding.ScopedEncoding
