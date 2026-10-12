import Mettapedia.OSLF.Syntax.ScopedBindingSortedReadout
import Mettapedia.OSLF.Syntax.BindingEquationFamilyModel
import Mettapedia.OSLF.Syntax.SortedConstructorCongruences

/-!
# Scoped binding equations in the context-indexed constructor algebra

The existing binding congruence keeps substitution and every declared binder.
Its transport through the independently proved term equivalence is a sorted
constructor congruence. Both the equation relation and complete argument
families are compared, without choosing representatives or imposing a size
condition on the equations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ScopedInstruments

open ScopedEncoding

variable {S : Signature}

abbrev EquationTheory (S : Signature) := BindingTermCongruenceQuotient.Congruence S

theorem assemble_argumentRelation (E : EquationTheory S) (context : Ctx S) :
    ∀ (declarations : List (List S.Srt × S.Srt))
      (first second : (position : Fin declarations.length) →
        Term S ((declarations.get position).1 ++ context) (declarations.get position).2),
      (∀ position, E.relation (first position) (second position)) →
      BindingTermCongruenceQuotient.ArgumentRelation E.relation
        (assembleArguments context declarations first) (assembleArguments context declarations second)
  | [], _, _, _ => .nil
  | _ :: tail, first, second, related =>
      .cons (related 0) (assemble_argumentRelation E context tail
        (fun position => first position.succ) (fun position => second position.succ)
        (fun position => related position.succ))

theorem encodeArguments_at : ∀ {declarations : List (List S.Srt × S.Srt)}
    {context : Ctx S} (arguments : Args S declarations context)
    (position : Fin declarations.length),
    encodeArguments arguments position = encode (argumentsAt arguments position)
  | _, _, .nil, position => Fin.elim0 position
  | _, _, .cons head tail, position => by
      refine Fin.cases ?_ (fun previous => ?_) position
      · rfl
      · exact encodeArguments_at tail previous

theorem encode_operation {context : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (arguments : Args S (S.arity operator) context) :
    encode (.op operator arguments) = SortedConstructors.Term.node
      (signature := signature S) (Constructor.operation context sort operator)
      (fun position => encode (argumentsAt arguments position)) :=
  congrArg (SortedConstructors.Term.node (signature := signature S)
    (Constructor.operation context sort operator)) (funext (encodeArguments_at arguments))

/-- An opening returns original scoped arguments, including the empty
argument list of a variable probe. -/
def Arguments : Constructor S → Type
  | .variable context _ _ => Args S [] context
  | .operation context _ operator => Args S (S.arity operator) context

def buildTerm : (constructor : Constructor S) → Arguments constructor →
    Term S ((signature S).output constructor).1 ((signature S).output constructor).2
  | .variable _ _ position, _ => .var position
  | .operation _ _ operator, arguments => .op operator arguments

def readArguments : (constructor : Constructor S) → Arguments constructor →
    (position : Fin ((signature S).arity constructor)) →
      Term S ((signature S).input constructor position).1
        ((signature S).input constructor position).2
  | .variable _ _ _, _ => fun position => Fin.elim0 position
  | .operation _ _ _, arguments => argumentsAt arguments

def assemble : (constructor : Constructor S) →
    ((position : Fin ((signature S).arity constructor)) →
      Term S ((signature S).input constructor position).1
        ((signature S).input constructor position).2) → Arguments constructor
  | .variable _ _ _, _ => .nil
  | .operation context _ operator, arguments => assembleArguments context (S.arity operator) arguments

theorem assemble_read (constructor : Constructor S) (arguments : Arguments constructor) :
    assemble constructor (readArguments constructor arguments) = arguments := by
  cases constructor with
  | «variable» context sort position => cases arguments; rfl
  | operation context sort operator => exact assemble_argumentsAt arguments

theorem read_assemble (constructor : Constructor S)
    (arguments : (position : Fin ((signature S).arity constructor)) →
      Term S ((signature S).input constructor position).1
        ((signature S).input constructor position).2) :
    readArguments constructor (assemble constructor arguments) = arguments := by
  cases constructor with
  | «variable» context sort position => funext impossible; exact Fin.elim0 impossible
  | operation context sort operator => exact argumentsAt_assemble context (S.arity operator) arguments

theorem encode_build (constructor : Constructor S) (arguments : Arguments constructor) :
    encode (buildTerm constructor arguments) = SortedConstructors.Term.node
      (signature := signature S) constructor
      (fun position => encode (readArguments constructor arguments position)) := by
  cases constructor with
  | «variable» context sort position =>
      apply congrArg (SortedConstructors.Term.node (signature := signature S)
        (Constructor.variable context sort position))
      funext impossible
      exact Fin.elim0 impossible
  | operation context sort operator => exact encode_operation operator arguments

theorem decode_node (constructor : Constructor S)
    (arguments : (position : Fin ((signature S).arity constructor)) →
      SortedConstructors.Term (signature S) ((signature S).input constructor position)) :
    decode (SortedConstructors.Term.node constructor arguments) =
      buildTerm constructor (assemble constructor (fun position => decode (arguments position))) := by
  cases constructor <;> rfl

/-- This congruence is constructed from the original binding relation. -/
def sortedTheory (E : EquationTheory S) : SortedConstructors.Congruence (signature S) where
  Rel first second := E.relation (decode first) (decode second)
  refl value := E.reflexive (decode value)
  symm := E.symmetric
  trans := E.transitive
  node constructor first second related := by
    cases constructor with
    | «variable» context sort position => exact E.reflexive (.var position)
    | operation context sort operator =>
        exact E.operation_relation operator
          (assemble_argumentRelation E context (S.arity operator)
            (fun position => decode (first position))
            (fun position => decode (second position)) related)

@[simp]
theorem sorted_relation_encode (E : EquationTheory S) {context : Ctx S} {sort : S.Srt}
    (first second : Term S context sort) :
    (sortedTheory E).Rel (encode first) (encode second) ↔ E.relation first second := by
  change E.relation (decode (encode first)) (decode (encode second)) ↔ _
  rw [decode_encode, decode_encode]

/-- Authored equation families, including all contextual instances, fit this
transport through their existing substitution congruence. -/
theorem family_relation_encode {metas : List (MetaArity S)}
    (family : EqAxiom S metas → Prop) {context : Ctx S} {sort : S.Srt}
    (first second : Term S context sort) :
    (sortedTheory (BindingEquationFamilyModel.congruence family)).Rel
        (encode first) (encode second) ↔
      BindingEquationFamilyCongruence.Related family first second :=
  sorted_relation_encode (BindingEquationFamilyModel.congruence family) first second

end Mettapedia.OSLF.Binding.ScopedInstruments
