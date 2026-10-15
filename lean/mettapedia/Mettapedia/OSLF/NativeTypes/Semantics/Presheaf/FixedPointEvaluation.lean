import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables

/-!
# Complete common-grammar readouts of derived fixed-point formulas

The evaluator traverses the actual predicate function binder and argument
binder. The bound operator atom is read by typed native application, while
the authored atoms are transported by the earned weakening/binder square.
The full formulas are compared with independently constructed quantified
native meanings, not defined by evaluating the formula itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointEvaluation

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open PredicateVariables NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension

universe u v z
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {n : Nat} {Atom : Type z}
variable {P : Cᵒᵖ ⥤ Type u}

noncomputable def atomProjection (A : NativeType P) :
    totalSpace (argumentType A).decoded ⟶ totalSpace A.decoded :=
  totalReindexMap (totalProjection (predicate A).decoded) A.decoded

noncomputable def transformed (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :=
  Monotone.operator (fun atom => (atoms atom).preimage (atomProjection A))
    body checked (boundMembership A)

noncomputable def preGuard (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor (totalSpace (predicate A).decoded) :=
  forallAlong (totalProjection (argumentType A).decoded)
    (transformed A atoms body checked ⇨ boundMembership A)

noncomputable def postGuard (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor (totalSpace (predicate A).decoded) :=
  forallAlong (totalProjection (argumentType A).decoded)
    (boundMembership A ⇨ transformed A atoms body checked)

noncomputable def testedMembership (A : NativeType P) (value : A.decoded.sections) :
    Subfunctor (totalSpace (predicate A).decoded) :=
  nativeHolds (FixedPointSyntax.applicationValue (argumentType A) (generic A)
    (ContextualLocalUniverses.substituteTerm (type := A) value
      (totalProjection (predicate A).decoded)))

noncomputable def least (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) : Subfunctor P :=
  forallAlong (totalProjection (predicate A).decoded)
    (preGuard A atoms body checked ⇨ testedMembership A value)

noncomputable def greatest (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) : Subfunctor P :=
  (postGuard A atoms body checked ⊓ testedMembership A value).image
    (totalProjection (predicate A).decoded)

theorem inserted_predicate_mapping :
    (FixedPointSyntax.insertPredicate : Renaming (n + 1) (n + 2)) =
      liftRenaming (Fin.succ : Renaming n (n + 1)) := by
  funext position
  cases position using Fin.cases <;> rfl

theorem evaluate_operatorAt (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (atoms : Atom → PropExpr S (n + 1))
    (meanings : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (domainRead : model.evaluateType context domain = some A)
    (atomRead : ∀ atom, model.evaluatePredicate (context.snoc A) (atoms atom) = some (meanings atom)) :
    model.evaluatePredicate ((context.snoc (predicate A)).snoc (argumentType A))
      (FixedPointSyntax.operatorAt domain atoms body) = some (transformed A meanings body checked) := by
  let insertion := (ModelRenaming.weaken context (predicate A)).lift A
  have atomWeak : ∀ atom,
      model.evaluatePredicate ((context.snoc (predicate A)).snoc (argumentType A))
        ((atoms atom).rename FixedPointSyntax.insertPredicate) =
          some ((meanings atom).preimage (atomProjection A)) := by
    intro atom
    rw [inserted_predicate_mapping]
    exact model.evaluatePredicate_rename (products_substitution C) (atoms atom) _ _ _
      insertion (meanings atom) (atomRead atom)
  exact RefinementBridge.evaluate_operator_body model _ _ _
    (FixedPointSyntax.candidateAt domain) (boundMembership A) atomWeak
    (evaluate_candidateAt model context domain A domainRead) body checked

theorem evaluate_prefixed (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (atoms : Atom → PropExpr S (n + 1))
    (meanings : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (domainRead : model.evaluateType context domain = some A)
    (atomRead : ∀ atom, model.evaluatePredicate (context.snoc A) (atoms atom) = some (meanings atom)) :
    model.evaluatePredicate (context.snoc (predicate A))
      (FixedPointSyntax.prefixed domain atoms body) = some (preGuard A meanings body checked) := by
  have domainWeak := model.evaluateType_rename (products_substitution C) domain _ context
    Fin.succ (ModelRenaming.weaken context (predicate A)) A domainRead
  have impliesRead := model.evaluate_implies _ _ _ _ _
    (evaluate_operatorAt model context domain A atoms meanings body checked domainRead atomRead)
    (evaluate_candidateAt model context domain A domainRead)
  rw [himpPointwise_eq_himp] at impliesRead
  exact model.evaluate_all _ _ _ _ _ domainWeak impliesRead

theorem evaluate_postfixed (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (atoms : Atom → PropExpr S (n + 1))
    (meanings : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (domainRead : model.evaluateType context domain = some A)
    (atomRead : ∀ atom, model.evaluatePredicate (context.snoc A) (atoms atom) = some (meanings atom)) :
    model.evaluatePredicate (context.snoc (predicate A))
      (FixedPointSyntax.postfixed domain atoms body) = some (postGuard A meanings body checked) := by
  have domainWeak := model.evaluateType_rename (products_substitution C) domain _ context
    Fin.succ (ModelRenaming.weaken context (predicate A)) A domainRead
  have impliesRead := model.evaluate_implies _ _ _ _ _
    (evaluate_candidateAt model context domain A domainRead)
    (evaluate_operatorAt model context domain A atoms meanings body checked domainRead atomRead)
  rw [himpPointwise_eq_himp] at impliesRead
  exact model.evaluate_all _ _ _ _ _ domainWeak impliesRead

/-- Every emitted least formula executes through the complete common
native grammar, including both actual dependent binders and application. -/
theorem evaluate_least (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (atoms : Atom → PropExpr S (n + 1))
    (meanings : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (tested : TermExpr S n) (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (atomRead : ∀ atom, model.evaluatePredicate (context.snoc A) (atoms atom) = some (meanings atom))
    (valueRead : model.evaluateTerm context tested = some ⟨A, value⟩) :
    model.evaluatePredicate context (FixedPointSyntax.least domain atoms body tested) =
      some (least A meanings body checked value) := by
  have implication := model.evaluate_implies _ _ _ _ _
    (evaluate_prefixed model context domain A atoms meanings body checked domainRead atomRead)
    (evaluate_application_under_predicate model context domain tested A value domainRead valueRead)
  rw [himpPointwise_eq_himp] at implication
  exact model.evaluate_all _ _ _ _ _
    (FixedPointSyntax.evaluate_predicateType model context domain A domainRead) implication

/-- The greatest formula likewise executes the genuine existential witness
and conjunction through the same original native evaluator. -/
theorem evaluate_greatest (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (atoms : Atom → PropExpr S (n + 1))
    (meanings : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (tested : TermExpr S n) (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (atomRead : ∀ atom, model.evaluatePredicate (context.snoc A) (atoms atom) = some (meanings atom))
    (valueRead : model.evaluateTerm context tested = some ⟨A, value⟩) :
    model.evaluatePredicate context (FixedPointSyntax.greatest domain atoms body tested) =
      some (greatest A meanings body checked value) := by
  have conjunction := model.evaluate_and _ _ _ _ _
    (evaluate_postfixed model context domain A atoms meanings body checked domainRead atomRead)
    (evaluate_application_under_predicate model context domain tested A value domainRead valueRead)
  exact model.evaluate_exists _ _ _ _ _
    (FixedPointSyntax.evaluate_predicateType model context domain A domainRead) conjunction

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointEvaluation
