import Mettapedia.TypeTheory.JudgmentDerivation

/-!
# Independent extensions of an indexed judgment presentation

The new rule symbols and their premise positions are supplied independently
of a model and of generated derivations. The extended presentation retains
both original and added rule occurrences. Interpretation is the recursive
fold into the original rule algebra together with local added operations.
Neither whole-proof soundness nor a pre-existing interpreter is a field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JudgmentDerivation

universe u v

variable (S : Signature.{u})

structure Extension where
  Rule : S.Judgment → Type u
  Premise : {judgment : S.Judgment} → Rule judgment → Type u
  hypothesis : {judgment : S.Judgment} → (rule : Rule judgment) →
    Premise rule → S.Judgment

namespace Extension

variable {S}

def signature (E : Extension S) : Signature.{u} where
  Judgment := S.Judgment
  Rule judgment := S.Rule judgment ⊕ E.Rule judgment
  Premise
    | .inl rule => S.Premise rule
    | .inr rule => E.Premise rule
  hypothesis
    | .inl rule, position => S.hypothesis rule position
    | .inr rule, position => E.hypothesis rule position

def inclusion (E : Extension S) : SignatureMap S E.signature where
  judgment := id
  rule := Sum.inl
  position _ position := position
  hypothesis _ _ := rfl

def addedSignature (E : Extension S) : Signature.{u} where
  Judgment := S.Judgment
  Rule := E.Rule
  Premise := E.Premise
  hypothesis := E.hypothesis

def addedInclusion (E : Extension S) : SignatureMap E.addedSignature E.signature where
  judgment := id
  rule := Sum.inr
  position _ position := position
  hypothesis _ _ := rfl

/-- The interpretation operation for each new rule uses its actual premises. -/
abbrev LocalOperations (E : Extension S) (A : Algebra.{u, v} S) :=
  {judgment : S.Judgment} → (rule : E.Rule judgment) →
    ((position : E.Premise rule) → A.Carrier (E.hypothesis rule position)) →
      A.Carrier judgment

def extendAlgebra (E : Extension S) (A : Algebra.{u, v} S)
    (operations : E.LocalOperations A) : Algebra.{u, v} E.signature where
  Carrier := A.Carrier
  conclude
    | .inl rule, premises => A.conclude rule premises
    | .inr rule, premises => operations rule premises

@[simp] theorem extendAlgebra_original (E : Extension S) (A : Algebra.{u, v} S)
    (operations : E.LocalOperations A) {judgment : S.Judgment} (rule : S.Rule judgment)
    (premises : (position : S.Premise rule) → A.Carrier (S.hypothesis rule position)) :
    (E.extendAlgebra A operations).conclude (.inl rule) premises = A.conclude rule premises := rfl

@[simp] theorem extendAlgebra_added (E : Extension S) (A : Algebra.{u, v} S)
    (operations : E.LocalOperations A) {judgment : S.Judgment} (rule : E.Rule judgment)
    (premises : (position : E.Premise rule) → A.Carrier (E.hypothesis rule position)) :
    (E.extendAlgebra A operations).conclude (.inr rule) premises = operations rule premises := rfl

def original (E : Extension S) {judgment : S.Judgment}
    (tree : Derivation S judgment) : Derivation E.signature judgment :=
  E.inclusion.translate tree

def add (E : Extension S) {judgment : S.Judgment} (rule : E.Rule judgment)
    (premises : (position : E.Premise rule) → Derivation E.signature (E.hypothesis rule position)) :
    Derivation E.signature judgment := .node (.inr rule) premises

theorem interpret_original (E : Extension S) (A : Algebra.{u, v} S)
    (operations : E.LocalOperations A) {judgment : S.Judgment} (tree : Derivation S judgment) :
    interpret (E.extendAlgebra A operations) (E.original tree) = interpret A tree := by
  induction tree with
  | node rule premises ih =>
      change A.conclude rule
          (fun position => interpret (E.extendAlgebra A operations) (E.original (premises position))) =
        A.conclude rule (fun position => interpret A (premises position))
      congr 1
      funext position
      exact ih position

@[simp] theorem interpret_add (E : Extension S) (A : Algebra.{u, v} S)
    (operations : E.LocalOperations A) {judgment : S.Judgment} (rule : E.Rule judgment)
    (premises : (position : E.Premise rule) → Derivation E.signature (E.hypothesis rule position)) :
    interpret (E.extendAlgebra A operations) (E.add rule premises) =
      operations rule (fun position => interpret (E.extendAlgebra A operations) (premises position)) := rfl

/-- The actual tree inclusion retains the old root rule and every child. -/
theorem original_node (E : Extension S) {judgment : S.Judgment} (rule : S.Rule judgment)
    (premises : (position : S.Premise rule) → Derivation S (S.hypothesis rule position)) :
    E.original (.node rule premises) =
      .node (.inl rule) (fun position => E.original (premises position)) := rfl

end Extension

end Mettapedia.TypeTheory.JudgmentDerivation
