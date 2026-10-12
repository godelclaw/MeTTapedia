import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Logic
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Monotone
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPredicateInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitution

/-!
# The intuitionistic fragment inside the shared native dependent syntax

The intermediate formula is embedded into the original `Refinement.PropExpr`.
Its independent presheaf meaning agrees with the existing evaluator after
each supplied atomic code has been interpreted. This consumes the actual
native dependent syntax and evaluator, including restriction-sensitive
implication. Renaming and capture-avoiding simultaneous substitution act on
the original embedded codes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.RefinementBridge

open _root_.CategoryTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Logic

universe u v z

variable {S : Symbols.{v}} {Atom : Type z}

/-- Embed into the shared, independently authored native proposition grammar. -/
def embed {n : Nat} (atoms : Atom → PropExpr S n) : Formula Atom → PropExpr S n
  | .atom name => atoms name
  | .top => .truth
  | .bot => .falsehood
  | .conj left right => .and (embed atoms left) (embed atoms right)
  | .disj left right => .or (embed atoms left) (embed atoms right)
  | .impl left right => .implies (embed atoms left) (embed atoms right)

theorem embed_substitution {n m : Nat} (atoms : Atom → PropExpr S n)
    (substitution : Substitution S n m) (formula : Formula Atom) :
    (embed atoms formula).substitute substitution =
      embed (fun name => (atoms name).substitute substitution) formula := by
  induction formula with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | conj _ _ left right => simp only [embed, PropExpr.substitute, left, right]
  | disj _ _ left right => simp only [embed, PropExpr.substitute, left, right]
  | impl _ _ left right => simp only [embed, PropExpr.substitute, left, right]

theorem embed_renaming {n m : Nat} (atoms : Atom → PropExpr S n)
    (renameMap : Renaming n m) (formula : Formula Atom) :
    (embed atoms formula).rename renameMap =
      embed (fun name => (atoms name).rename renameMap) formula := by
  induction formula with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | conj _ _ left right => simp only [embed, PropExpr.rename, left, right]
  | disj _ _ left right => simp only [embed, PropExpr.rename, left, right]
  | impl _ _ left right => simp only [embed, PropExpr.rename, left, right]

variable {C : Type u} [Category.{u} C]

/-- Atom evaluation is the only supplied leaf comparison. The generated
logical meaning follows by traversing the shared native syntax evaluator. -/
theorem evaluate_embed (model : ModelData S C) {n : Nat} (context : Scope C n)
    (atoms : Atom → PropExpr S n) (meanings : Atom → Subfunctor context.1)
    (atomicReadout : ∀ name, model.evaluatePredicate context (atoms name) =
      some (meanings name)) (formula : Formula Atom) :
    model.evaluatePredicate context (embed atoms formula) =
      some (denote meanings formula) := by
  induction formula with
  | atom name => exact atomicReadout name
  | top => exact model.evaluate_truth context
  | bot => exact model.evaluate_falsehood context
  | conj first second left right =>
      exact model.evaluate_and context _ _ _ _ left right
  | disj first second left right =>
      exact model.evaluate_or context _ _ _ _ left right
  | impl first second left right =>
      have readout := model.evaluate_implies context _ _ _ _ left right
      rw [himpPointwise_eq_himp] at readout
      exact readout

/-- Consequently every generalized section of the native evaluator's result
has the independently specified Kripke--Joyal meaning. -/
theorem native_readout_iff_satisfaction (model : ModelData S C) {n : Nat}
    (context : Scope C n) (atoms : Atom → PropExpr S n)
    (meanings : Atom → Subfunctor context.1)
    (atomicReadout : ∀ name, model.evaluatePredicate context (atoms name) =
      some (meanings name)) (formula : Formula Atom)
    (predicate : Subfunctor context.1)
    (readout : model.evaluatePredicate context (embed atoms formula) = some predicate)
    (world : Cᵒᵖ) (value : context.1.obj world) :
    value ∈ predicate.obj world ↔ Satisfaction meanings formula world value := by
  have same := (Option.some.inj (readout.symm.trans
    (evaluate_embed model context atoms meanings atomicReadout formula)))
  rw [same]
  exact denote_iff_satisfaction meanings formula world value

/-- The checked fixed-point body is evaluated in the same native dependent
grammar as other predicates. The right-hand atom is its supplied bound
predicate code; no second native evaluator is introduced. -/
theorem evaluate_operator_body (model : ModelData S C) {n : Nat}
    (context : Scope C n) (atoms : Atom → PropExpr S n)
    (meanings : Atom → Subfunctor context.1) (boundCode : PropExpr S n)
    (candidate : Subfunctor context.1)
    (atomicReadout : ∀ name, model.evaluatePredicate context (atoms name) =
      some (meanings name))
    (boundReadout : model.evaluatePredicate context boundCode = some candidate)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    model.evaluatePredicate context
      (embed (Sum.elim atoms (fun _ => boundCode)) body) =
        some (Monotone.operator meanings body checked candidate) := by
  apply evaluate_embed
  intro name
  cases name with
  | inl name => exact atomicReadout name
  | inr _ => exact boundReadout

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.RefinementBridge
