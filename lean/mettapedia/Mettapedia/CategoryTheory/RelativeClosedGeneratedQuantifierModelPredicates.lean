import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelClosure
import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObjectMaps

/-!
# Actual predicate declaration maps of closure interpretations

Successful independent model readings determine the proposition, truth and
both-input conjunction images of the actual quotient functor. Terminal and
product readings and both projection readings earn the complete operation
squares. The finite-limit and canonical closed comparisons are those of the
earned structural interpretation, so both quantifier squares follow from
local operation uniqueness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory Iteration

universe k w
variable {C : Type k} [Category.{k} C] {stage : Stage C}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {quantifiers : InternalPredicateQuantifiedObject.Operations D}
variable (initial : Model quantifiers stage)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem postcast {before after first second : D}
    (source : before = first) (target : after = second)
    {original : before ⟶ after} {value : first ⟶ second} (reading : HEq original value) :
    original ≫ eqToHom target = eqToHom source ≫ value := by
  subst first
  subst second
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using eq_of_heq reading

theorem model_proposition_read :
    (modelDiagram initial).obj (operations stage).proposition = quantifiers.predicates.proposition :=
  RelativeClosedSyntax.Interpretation.objectValue_unique (modelAssignment initial) (modelRealization initial)
    (operations stage).proposition quantifiers.predicates.proposition (completedModel initial).proposition

theorem model_terminal_read : (modelDiagram initial).obj (𝟙_ (Object (signature stage))) = 𝟙_ D :=
  RelativeClosedSyntax.Interpretation.functor_terminal_object (modelAssignment initial) (modelRealization initial)

theorem model_product_read :
    (modelDiagram initial).obj ((operations stage).proposition ⊗ (operations stage).proposition) =
      quantifiers.predicates.proposition ⊗ quantifiers.predicates.proposition :=
  RelativeClosedSyntax.Interpretation.objectValue_unique (modelAssignment initial) (modelRealization initial)
    (product (operations stage).proposition (operations stage).proposition)
    (quantifiers.predicates.proposition ⊗ quantifiers.predicates.proposition)
    ((modelAssignment initial).evaluate_product (completedModel initial).proposition
      (completedModel initial).proposition)

theorem model_truth_heq : HEq ((modelDiagram initial).map (operations stage).truth) quantifiers.predicates.truth :=
  RelativeClosedSyntax.Interpretation.functor_map_heq (modelAssignment initial) (modelRealization initial)
    (truth stage) quantifiers.predicates.truth (completedModel initial).truth

theorem model_conjunction_heq :
    HEq ((modelDiagram initial).map (operations stage).conjunction) quantifiers.predicates.conjunction :=
  RelativeClosedSyntax.Interpretation.functor_map_heq (modelAssignment initial) (modelRealization initial)
    (language stage).conjunction quantifiers.predicates.conjunction (completedModel initial).conjunction

theorem model_truth_square :
    (modelDiagram initial).map (operations stage).truth ≫ eqToHom (model_proposition_read initial) =
      toUnit ((modelDiagram initial).obj (𝟙_ (Object (signature stage)))) ≫ quantifiers.predicates.truth :=
  (postcast (model_terminal_read initial) (model_proposition_read initial) (model_truth_heq initial)).trans
    (congrArg (fun arrow => arrow ≫ quantifiers.predicates.truth) (toUnit_unique _ _))

theorem model_conjunction_square :
    (modelDiagram initial).map (operations stage).conjunction ≫ eqToHom (model_proposition_read initial) =
      lift ((modelDiagram initial).map (fst (operations stage).proposition (operations stage).proposition) ≫
          eqToHom (model_proposition_read initial))
        ((modelDiagram initial).map (snd (operations stage).proposition (operations stage).proposition) ≫
          eqToHom (model_proposition_read initial)) ≫ quantifiers.predicates.conjunction := by
  have retained := postcast (model_product_read initial) (model_proposition_read initial)
    (model_conjunction_heq initial)
  have firstRead := RelativeClosedSyntax.Interpretation.functor_map_heq
    (modelAssignment initial) (modelRealization initial)
    (RawHom.first (operations stage).proposition (operations stage).proposition)
    (fst quantifiers.predicates.proposition quantifiers.predicates.proposition)
      ((modelAssignment initial).evaluate_first (completedModel initial).proposition
        (completedModel initial).proposition)
  have secondRead := RelativeClosedSyntax.Interpretation.functor_map_heq
    (modelAssignment initial) (modelRealization initial)
    (RawHom.second (operations stage).proposition (operations stage).proposition)
    (snd quantifiers.predicates.proposition quantifiers.predicates.proposition)
      ((modelAssignment initial).evaluate_second (completedModel initial).proposition
        (completedModel initial).proposition)
  have first := postcast (model_product_read initial) (model_proposition_read initial) firstRead
  have second := postcast (model_product_read initial) (model_proposition_read initial) secondRead
  change (modelDiagram initial).map (fst (operations stage).proposition (operations stage).proposition) ≫
    eqToHom (model_proposition_read initial) = eqToHom (model_product_read initial) ≫
      fst quantifiers.predicates.proposition quantifiers.predicates.proposition at first
  change (modelDiagram initial).map (snd (operations stage).proposition (operations stage).proposition) ≫
    eqToHom (model_proposition_read initial) = eqToHom (model_product_read initial) ≫
      snd quantifiers.predicates.proposition quantifiers.predicates.proposition at second
  rw [first, second, ← comp_lift, lift_fst_snd, Category.comp_id]
  exact retained

def modelPredicateMap : InternalConjunctiveObject.Map (operations stage) quantifiers.predicates where
  functor := modelDiagram initial
  proposition := eqToIso (model_proposition_read initial)
  truth := model_truth_square initial
  conjunction := model_conjunction_square initial

def modelQuantifiedMap : InternalPredicateQuantifiedObject.Map (quantifiedOperations (stage := stage)) quantifiers where
  predicates := modelPredicateMap initial
  finite := modelDiagram_preservesFiniteLimits initial
  closed := RelativeClosedSyntax.Interpretation.functor_closed (modelAssignment initial) (modelRealization initial)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
