import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureProofFiniteOrigin

/-!
# Complete predicate and route comparisons into closure

Each actual stage map retains the single authored proposition and the whole
conjunction and truth arrows. Structural power, ordered-function and
precomposition codes transport through the real declaration map. Finite
proof recovery therefore supplies an actual typed route whose complete
translation is the independently supplied closure route.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory

universe k l
variable {C : Type k} [Category.{k} C] {beforeSymbols : Symbols.{k}}
variable {E : Type l} [Category.{l} E] {afterSymbols : Symbols.{l}}
variable {before : Signature (C := C) (symbols := beforeSymbols)}
variable {after : Signature (C := E) (symbols := afterSymbols)}

theorem PredicateSyntax.eq_of_read {first second : PredicateSyntax before}
    (objects : first.proposition = second.proposition)
    (arrows : first.conjunction.code = second.conjunction.code) : first = second := by
  rcases first with ⟨firstObject, firstArrow⟩
  rcases second with ⟨secondObject, secondArrow⟩
  dsimp only at objects arrows
  subst secondObject
  have same := RawHom.ext arrows
  subst secondArrow
  rfl

theorem Route.eq_of_read {first second : Route before}
    (sources : first.source = second.source) (targets : first.target = second.target)
    (arrows : first.arrow.code = second.arrow.code) : first = second := by
  rcases first with ⟨firstSource, firstTarget, firstArrow⟩
  rcases second with ⟨secondSource, secondTarget, secondArrow⟩
  dsimp only at sources targets arrows
  subst secondSource secondTarget
  have same := RawHom.ext arrows
  subst secondArrow
  rfl

namespace Translation

variable (mapping : SignatureMap before after) (language : PredicateSyntax before)

theorem power (object : Object before) :
    mapping.object (language.power object) =
      (language.translate mapping).power (mapping.object object) := Object.ext rfl

theorem powerConjunction (object : Object before) :
    (mapping.rawArrow (language.powerConjunction object)).code =
      ((language.translate mapping).powerConjunction (mapping.object object)).code := rfl

theorem precomposition (route : Route before) :
    (mapping.rawArrow (language.precomposition route)).code =
      ((language.translate mapping).precomposition (route.translate mapping)).code := rfl

theorem orderedFunctions (object : Object before) :
    mapping.object (language.orderedFunctions object) =
      (language.translate mapping).orderedFunctions (mapping.object object) := Object.ext rfl

theorem smaller (object : Object before) :
    (mapping.rawArrow (language.smaller object)).code =
      ((language.translate mapping).smaller (mapping.object object)).code := rfl

theorem larger (object : Object before) :
    (mapping.rawArrow (language.larger object)).code =
      ((language.translate mapping).larger (mapping.object object)).code := rfl

theorem powerMeet {context : Object before} (object : Object before)
    (first second : RawHom context (language.power object)) :
    (mapping.rawArrow (language.powerMeet object first second)).code =
      (.compose (.pair (mapping.rawArrow first).code (mapping.rawArrow second).code)
        ((language.translate mapping).powerConjunction (mapping.object object)).code : ArrowCode E afterSymbols) := rfl

end Translation

namespace Closure

open Iteration

variable (initial : Stage C)

theorem conjunction_successor (stage : Stage C) :
    stage.next.language.conjunction.code =
      (stage.inclusion.rawArrow stage.language.conjunction).code :=
  SignatureMap.arrow_code_compose (arrowInclusion stage.presentation stage.language)
    (equationInclusion stage.presentation stage.language) stage.language.conjunction

theorem conjunction_retained : (depth : Nat) →
    arrowCode initial depth (stages initial depth).language.conjunction.code =
      (language initial).conjunction.code
  | 0 => rfl
  | depth + 1 =>
      (congrArg (arrowCode initial (depth + 1)) (conjunction_successor (stages initial depth))).trans
        ((arrowCode_step initial depth _).trans (conjunction_retained depth))

theorem language_retained (depth : Nat) :
    (stages initial depth).language.translate (stageMap initial depth) = language initial :=
  PredicateSyntax.eq_of_read (proposition_retained initial depth) (conjunction_retained initial depth)

theorem truth_successor (stage : Stage C) :
    stage.next.truth.code = (stage.inclusion.rawArrow stage.truth).code :=
  SignatureMap.arrow_code_compose (arrowInclusion stage.presentation stage.language)
    (equationInclusion stage.presentation stage.language) stage.truth

theorem truth_retained : (depth : Nat) →
    arrowCode initial depth (stages initial depth).truth.code = (truth initial).code
  | 0 => rfl
  | depth + 1 =>
      (congrArg (arrowCode initial (depth + 1)) (truth_successor (stages initial depth))).trans
        ((arrowCode_step initial depth _).trans (truth_retained depth))

theorem route_finite (route : Route (signature initial)) :
    ∃ depth, ∃ previous : Route (stages initial depth).presentation,
      previous.translate (stageMap initial depth) = route := by
  obtain ⟨depth, previousSource, previousTarget, previousArrow, sourceRead, targetRead, arrowRead⟩ :=
    whole_arrow_finite initial route.arrow
  exact ⟨depth, ⟨previousSource, previousTarget, previousArrow⟩,
    Route.eq_of_read sourceRead targetRead arrowRead⟩

end Closure

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier
