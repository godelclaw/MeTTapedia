import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureStages
import Lean.Elab.Tactic.Omega

/-!
# Finite origins of complete closure expressions

An actual sequence of signature maps advances a supplied stage by any
finite number of successors. Whole expressions commute with this advance.
Every object and arrow expression in the merged signature is recovered at
one finite stage, including the arrows inside equalizer presentations and
all arguments of an equalizer lift. This is raw expression recovery;
recovery of a complete generated derivation is a further theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

def advance (depth : Nat) : (extra : Nat) →
    SignatureMap (stages initial depth).presentation (stages initial (depth + extra)).presentation
  | 0 => SignatureMap.identity (stages initial depth).presentation
  | extra + 1 => (advance depth extra).compose (stages initial (depth + extra)).inclusion

theorem advance_object_read (depth extra : Nat) (code : ObjectCode C (stages initial depth).symbols) :
    objectCode initial (depth + extra)
      (code.map (advance initial depth extra).base
        (advance initial depth extra).objects (advance initial depth extra).arrows) =
      objectCode initial depth code := by
  induction extra with
  | zero => exact congrArg (objectCode initial depth) (ObjectCode.map_identity code)
  | succ extra inductionHypothesis =>
      have decomposed := ObjectCode.map_compose (advance initial depth extra).base
        (stages initial (depth + extra)).inclusion.base (advance initial depth extra).objects
        (stages initial (depth + extra)).inclusion.objects (advance initial depth extra).arrows
        (stages initial (depth + extra)).inclusion.arrows code
      exact (congrArg (objectCode initial (depth + extra + 1)) decomposed.symm).trans
        ((objectCode_step initial (depth + extra) _).trans inductionHypothesis)

theorem advance_arrow_read (depth extra : Nat) (code : ArrowCode C (stages initial depth).symbols) :
    arrowCode initial (depth + extra)
      (code.map (advance initial depth extra).base
        (advance initial depth extra).objects (advance initial depth extra).arrows) =
      arrowCode initial depth code := by
  induction extra with
  | zero => exact congrArg (arrowCode initial depth) (ArrowCode.map_identity code)
  | succ extra inductionHypothesis =>
      have decomposed := ArrowCode.map_compose (advance initial depth extra).base
        (stages initial (depth + extra)).inclusion.base (advance initial depth extra).objects
        (stages initial (depth + extra)).inclusion.objects (advance initial depth extra).arrows
        (stages initial (depth + extra)).inclusion.arrows code
      exact (congrArg (arrowCode initial (depth + extra + 1)) decomposed.symm).trans
        ((arrowCode_step initial (depth + extra) _).trans inductionHypothesis)

theorem raise_object {depth : Nat} (code : ObjectCode C (stages initial depth).symbols)
    (later : Nat) (admitted : depth ≤ later) :
    ∃ recovered : ObjectCode C (stages initial later).symbols,
      objectCode initial later recovered = objectCode initial depth code := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le admitted
  exact ⟨code.map (advance initial depth extra).base
    (advance initial depth extra).objects (advance initial depth extra).arrows,
      advance_object_read initial depth extra code⟩

theorem raise_arrow {depth : Nat} (code : ArrowCode C (stages initial depth).symbols)
    (later : Nat) (admitted : depth ≤ later) :
    ∃ recovered : ArrowCode C (stages initial later).symbols,
      arrowCode initial later recovered = arrowCode initial depth code := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le admitted
  exact ⟨code.map (advance initial depth extra).base
    (advance initial depth extra).objects (advance initial depth extra).arrows,
      advance_arrow_read initial depth extra code⟩

def initialObject : (depth : Nat) → initial.symbols.ObjectName → (stages initial depth).symbols.ObjectName
  | 0, origin => origin
  | depth + 1, origin => initialObject depth origin

theorem initialObject_read : (depth : Nat) → (origin : initial.symbols.ObjectName) →
    objects initial depth (initialObject initial depth origin) = origin
  | 0, _ => rfl
  | depth + 1, origin => initialObject_read depth origin

mutual

theorem objectCode_finite : (code : ObjectCode C (symbols initial)) →
    ∃ depth, ∃ recovered : ObjectCode C (stages initial depth).symbols,
      objectCode initial depth recovered = code
  | .base object => ⟨0, .base object, rfl⟩
  | .name origin => ⟨0, .name origin, rfl⟩
  | .terminal => ⟨0, .terminal, rfl⟩
  | .product first second => by
      obtain ⟨before, firstCode, firstRead⟩ := objectCode_finite first
      obtain ⟨after, secondCode, secondRead⟩ := objectCode_finite second
      obtain ⟨left, leftRead⟩ := raise_object initial firstCode (max before after) (le_max_left _ _)
      obtain ⟨right, rightRead⟩ := raise_object initial secondCode (max before after) (le_max_right _ _)
      refine ⟨max before after, .product left right, ?_⟩
      change ObjectCode.product (objectCode initial _ left) (objectCode initial _ right) = ObjectCode.product first second
      rw [leftRead, rightRead, firstRead, secondRead]
  | .exponential argument result => by
      obtain ⟨before, argumentCode, argumentRead⟩ := objectCode_finite argument
      obtain ⟨after, resultCode, resultRead⟩ := objectCode_finite result
      obtain ⟨left, leftRead⟩ := raise_object initial argumentCode (max before after) (le_max_left _ _)
      obtain ⟨right, rightRead⟩ := raise_object initial resultCode (max before after) (le_max_right _ _)
      refine ⟨max before after, .exponential left right, ?_⟩
      change ObjectCode.exponential (objectCode initial _ left) (objectCode initial _ right) = ObjectCode.exponential argument result
      rw [leftRead, rightRead, argumentRead, resultRead]
  | .equalizer source target first second => by
      obtain ⟨one, sourceCode, sourceRead⟩ := objectCode_finite source
      obtain ⟨two, targetCode, targetRead⟩ := objectCode_finite target
      obtain ⟨three, firstCode, firstRead⟩ := arrowCode_finite first
      obtain ⟨four, secondCode, secondRead⟩ := arrowCode_finite second
      let depth := max one (max two (max three four))
      obtain ⟨source', sourceRead'⟩ := raise_object initial sourceCode depth (by omega)
      obtain ⟨target', targetRead'⟩ := raise_object initial targetCode depth (by omega)
      obtain ⟨first', firstRead'⟩ := raise_arrow initial firstCode depth (by omega)
      obtain ⟨second', secondRead'⟩ := raise_arrow initial secondCode depth (by omega)
      refine ⟨depth, .equalizer source' target' first' second', ?_⟩
      change ObjectCode.equalizer (objectCode initial _ source') (objectCode initial _ target')
        (arrowCode initial _ first') (arrowCode initial _ second') = ObjectCode.equalizer source target first second
      rw [sourceRead', targetRead', firstRead', secondRead', sourceRead, targetRead, firstRead, secondRead]

theorem arrowCode_finite : (code : ArrowCode C (symbols initial)) →
    ∃ depth, ∃ recovered : ArrowCode C (stages initial depth).symbols,
      arrowCode initial depth recovered = code
  | .base arrow => ⟨0, .base arrow, rfl⟩
  | .name (.inl origin) => ⟨0, .name origin, rfl⟩
  | .name (.inr ⟨depth, origin⟩) => ⟨depth + 1, .name (.inr origin), rfl⟩
  | .identity object => by
      obtain ⟨depth, recovered, read⟩ := objectCode_finite object
      refine ⟨depth, .identity recovered, ?_⟩
      change ArrowCode.identity (objectCode initial _ recovered) = ArrowCode.identity object
      rw [read]
  | .compose first second => by
      obtain ⟨before, firstCode, firstRead⟩ := arrowCode_finite first
      obtain ⟨after, secondCode, secondRead⟩ := arrowCode_finite second
      obtain ⟨left, leftRead⟩ := raise_arrow initial firstCode (max before after) (le_max_left _ _)
      obtain ⟨right, rightRead⟩ := raise_arrow initial secondCode (max before after) (le_max_right _ _)
      refine ⟨max before after, .compose left right, ?_⟩
      change ArrowCode.compose (arrowCode initial _ left) (arrowCode initial _ right) = ArrowCode.compose first second
      rw [leftRead, rightRead, firstRead, secondRead]
  | .terminal source => by
      obtain ⟨depth, recovered, read⟩ := objectCode_finite source
      refine ⟨depth, .terminal recovered, ?_⟩
      change ArrowCode.terminal (objectCode initial _ recovered) = ArrowCode.terminal source
      rw [read]
  | .first first second => by
      obtain ⟨before, firstCode, firstRead⟩ := objectCode_finite first
      obtain ⟨after, secondCode, secondRead⟩ := objectCode_finite second
      obtain ⟨left, leftRead⟩ := raise_object initial firstCode (max before after) (le_max_left _ _)
      obtain ⟨right, rightRead⟩ := raise_object initial secondCode (max before after) (le_max_right _ _)
      refine ⟨max before after, .first left right, ?_⟩
      change ArrowCode.first (objectCode initial _ left) (objectCode initial _ right) = ArrowCode.first first second
      rw [leftRead, rightRead, firstRead, secondRead]
  | .second first second => by
      obtain ⟨before, firstCode, firstRead⟩ := objectCode_finite first
      obtain ⟨after, secondCode, secondRead⟩ := objectCode_finite second
      obtain ⟨left, leftRead⟩ := raise_object initial firstCode (max before after) (le_max_left _ _)
      obtain ⟨right, rightRead⟩ := raise_object initial secondCode (max before after) (le_max_right _ _)
      refine ⟨max before after, .second left right, ?_⟩
      change ArrowCode.second (objectCode initial _ left) (objectCode initial _ right) = ArrowCode.second first second
      rw [leftRead, rightRead, firstRead, secondRead]
  | .pair first second => by
      obtain ⟨before, firstCode, firstRead⟩ := arrowCode_finite first
      obtain ⟨after, secondCode, secondRead⟩ := arrowCode_finite second
      obtain ⟨left, leftRead⟩ := raise_arrow initial firstCode (max before after) (le_max_left _ _)
      obtain ⟨right, rightRead⟩ := raise_arrow initial secondCode (max before after) (le_max_right _ _)
      refine ⟨max before after, .pair left right, ?_⟩
      change ArrowCode.pair (arrowCode initial _ left) (arrowCode initial _ right) = ArrowCode.pair first second
      rw [leftRead, rightRead, firstRead, secondRead]
  | .evaluation argument result => by
      obtain ⟨before, argumentCode, argumentRead⟩ := objectCode_finite argument
      obtain ⟨after, resultCode, resultRead⟩ := objectCode_finite result
      obtain ⟨left, leftRead⟩ := raise_object initial argumentCode (max before after) (le_max_left _ _)
      obtain ⟨right, rightRead⟩ := raise_object initial resultCode (max before after) (le_max_right _ _)
      refine ⟨max before after, .evaluation left right, ?_⟩
      change ArrowCode.evaluation (objectCode initial _ left) (objectCode initial _ right) = ArrowCode.evaluation argument result
      rw [leftRead, rightRead, argumentRead, resultRead]
  | .curry context argument result body => by
      obtain ⟨one, contextCode, contextRead⟩ := objectCode_finite context
      obtain ⟨two, argumentCode, argumentRead⟩ := objectCode_finite argument
      obtain ⟨three, resultCode, resultRead⟩ := objectCode_finite result
      obtain ⟨four, bodyCode, bodyRead⟩ := arrowCode_finite body
      let depth := max one (max two (max three four))
      obtain ⟨context', contextRead'⟩ := raise_object initial contextCode depth (by omega)
      obtain ⟨argument', argumentRead'⟩ := raise_object initial argumentCode depth (by omega)
      obtain ⟨result', resultRead'⟩ := raise_object initial resultCode depth (by omega)
      obtain ⟨body', bodyRead'⟩ := raise_arrow initial bodyCode depth (by omega)
      refine ⟨depth, .curry context' argument' result' body', ?_⟩
      change ArrowCode.curry (objectCode initial _ context') (objectCode initial _ argument')
        (objectCode initial _ result') (arrowCode initial _ body') = ArrowCode.curry context argument result body
      rw [contextRead', argumentRead', resultRead', bodyRead', contextRead, argumentRead, resultRead, bodyRead]
  | .equalizerArrow source target first second => by
      obtain ⟨one, sourceCode, sourceRead⟩ := objectCode_finite source
      obtain ⟨two, targetCode, targetRead⟩ := objectCode_finite target
      obtain ⟨three, firstCode, firstRead⟩ := arrowCode_finite first
      obtain ⟨four, secondCode, secondRead⟩ := arrowCode_finite second
      let depth := max one (max two (max three four))
      obtain ⟨source', sourceRead'⟩ := raise_object initial sourceCode depth (by omega)
      obtain ⟨target', targetRead'⟩ := raise_object initial targetCode depth (by omega)
      obtain ⟨first', firstRead'⟩ := raise_arrow initial firstCode depth (by omega)
      obtain ⟨second', secondRead'⟩ := raise_arrow initial secondCode depth (by omega)
      refine ⟨depth, .equalizerArrow source' target' first' second', ?_⟩
      change ArrowCode.equalizerArrow (objectCode initial _ source') (objectCode initial _ target')
        (arrowCode initial _ first') (arrowCode initial _ second') = ArrowCode.equalizerArrow source target first second
      rw [sourceRead', targetRead', firstRead', secondRead', sourceRead, targetRead, firstRead, secondRead]
  | .equalizerLift source target first second context candidate => by
      obtain ⟨one, sourceCode, sourceRead⟩ := objectCode_finite source
      obtain ⟨two, targetCode, targetRead⟩ := objectCode_finite target
      obtain ⟨three, firstCode, firstRead⟩ := arrowCode_finite first
      obtain ⟨four, secondCode, secondRead⟩ := arrowCode_finite second
      obtain ⟨five, contextCode, contextRead⟩ := objectCode_finite context
      obtain ⟨six, candidateCode, candidateRead⟩ := arrowCode_finite candidate
      let depth := max one (max two (max three (max four (max five six))))
      obtain ⟨source', sourceRead'⟩ := raise_object initial sourceCode depth (by omega)
      obtain ⟨target', targetRead'⟩ := raise_object initial targetCode depth (by omega)
      obtain ⟨first', firstRead'⟩ := raise_arrow initial firstCode depth (by omega)
      obtain ⟨second', secondRead'⟩ := raise_arrow initial secondCode depth (by omega)
      obtain ⟨context', contextRead'⟩ := raise_object initial contextCode depth (by omega)
      obtain ⟨candidate', candidateRead'⟩ := raise_arrow initial candidateCode depth (by omega)
      refine ⟨depth, .equalizerLift source' target' first' second' context' candidate', ?_⟩
      change ArrowCode.equalizerLift (objectCode initial _ source') (objectCode initial _ target')
        (arrowCode initial _ first') (arrowCode initial _ second')
        (objectCode initial _ context') (arrowCode initial _ candidate') =
          ArrowCode.equalizerLift source target first second context candidate
      rw [sourceRead', targetRead', firstRead', secondRead', contextRead', candidateRead',
        sourceRead, targetRead, firstRead, secondRead, contextRead, candidateRead]

end

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
