import Mettapedia.OSLF.Syntax.ScopedBindingSortedSignature

/-!
# Complete scoped binding term readout

Encoding keeps the operator, every declared binding prefix, each variable
position and the entire argument family. The independent inverse traverses
the sorted constructor tree and assembles the original binding arguments.
Both roundtrips are proved structurally.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open Mettapedia.OSLF.SortedConstructors

variable {S : Binding.Signature}

mutual
def encode : {context : Binding.Ctx S} → {sort : S.Srt} →
    Binding.Term S context sort → SortedConstructors.Term (signature S) (context, sort)
  | context, sort, .var position =>
      .node (signature := signature S) (Constructor.variable context sort position)
        (fun position => Fin.elim0 position)
  | context, sort, .op operator arguments =>
      .node (signature := signature S) (Constructor.operation (S := S) context sort operator)
        (encodeArguments arguments)

def encodeArguments : {declarations : List (List S.Srt × S.Srt)} →
    {context : Binding.Ctx S} → Binding.Args S declarations context →
      (position : Fin declarations.length) →
        SortedConstructors.Term (signature S)
          ((declarations.get position).1 ++ context, (declarations.get position).2)
  | _, _, .nil => fun position => Fin.elim0 position
  | _, _, .cons head tail => Fin.cases (encode head) (encodeArguments tail)
end

noncomputable section

def decode {scope : Scope S} (term : SortedConstructors.Term (signature S) scope) :
    Binding.Term S scope.1 scope.2 :=
  @SortedConstructors.Term.rec (signature S)
    (fun scope _ => Binding.Term S scope.1 scope.2)
    (fun constructor _arguments readings => match constructor with
      | .variable _ _ position => .var position
      | .operation context _ operator =>
          .op operator (assembleArguments context (S.arity operator) readings)) scope term

mutual
theorem decode_encode : ∀ {context : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term S context sort), decode (encode term) = term
  | _, _, .var _ => rfl
  | _, _, .op operator arguments => by
      change Binding.Term.op operator
        (assembleArguments _ (S.arity operator) (fun position => decode (encodeArguments arguments position))) = _
      rw [decode_encodeArguments]

theorem decode_encodeArguments : ∀ {declarations : List (List S.Srt × S.Srt)}
    {context : Binding.Ctx S} (arguments : Binding.Args S declarations context),
    assembleArguments context declarations
      (fun position => decode (encodeArguments arguments position)) = arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      change Binding.Args.cons (decode (encode head))
        (assembleArguments _ _ (fun position => decode (encodeArguments tail position))) = _
      rw [decode_encode head, decode_encodeArguments tail]
end

theorem encodeArguments_assemble (context : Binding.Ctx S) :
    ∀ (declarations : List (List S.Srt × S.Srt))
      (arguments : (position : Fin declarations.length) →
        Binding.Term S ((declarations.get position).1 ++ context)
          (declarations.get position).2),
      encodeArguments (assembleArguments context declarations arguments) =
        fun position => encode (arguments position)
  | [], arguments => by funext position; exact Fin.elim0 position
  | _ :: tail, arguments => by
      funext position
      refine Fin.cases ?_ (fun previous => ?_) position
      · rfl
      · exact congrFun (encodeArguments_assemble context tail
          (fun previous => arguments previous.succ)) previous

theorem encode_decode {scope : Scope S}
    (term : SortedConstructors.Term (signature S) scope) : encode (decode term) = term := by
  apply @SortedConstructors.Term.rec (signature S)
    (fun scope term => encode (decode term) = term) (t := term)
  intro constructor arguments inductionHypothesis
  cases constructor with
      | «variable» context sort position =>
        change SortedConstructors.Term.node (signature := signature S)
          (Constructor.variable context sort position) (fun impossible => Fin.elim0 impossible) = _
        apply congrArg (SortedConstructors.Term.node (signature := signature S)
          (Constructor.variable context sort position))
        funext impossible
        exact Fin.elim0 impossible
      | operation context sort operator =>
        change SortedConstructors.Term.node (signature := signature S)
          (Constructor.operation (S := S) context sort operator)
          (encodeArguments (assembleArguments context (S.arity operator)
            (fun position => decode (arguments position)))) = _
        apply congrArg (SortedConstructors.Term.node (signature := signature S)
          (Constructor.operation (S := S) context sort operator))
        exact (encodeArguments_assemble context (S.arity operator)
          (fun position => decode (arguments position))).trans (funext inductionHypothesis)

def termEquiv (scope : Scope S) : Binding.Term S scope.1 scope.2 ≃
    SortedConstructors.Term (signature S) scope where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem encode_injective {context : Binding.Ctx S} {sort : S.Srt} :
    Function.Injective (encode (S := S) (context := context) (sort := sort)) :=
  (termEquiv (context, sort)).injective

end

end Mettapedia.OSLF.Binding.ScopedEncoding
