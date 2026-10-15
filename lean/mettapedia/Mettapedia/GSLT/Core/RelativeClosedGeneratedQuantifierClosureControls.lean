import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureProofFiniteOrigin
import Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierIterationControls

/-!
# Complete closure recovery retains proof occurrences and new routes

Two actual derivations of the same equation can use different later
declarations. Their complete proof bounds differ, so inspecting only the
conclusion cannot recover that traversal account. The concrete generated
second-stage quantifier retains its whole typed route and cannot be renamed
from any first-stage-free raw expression. The independent finite-stage
native consumer remains parameter-sensitive and rejects empty inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierClosureControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory RelativeClosedGeneratedQuantifier
open Iteration Closure

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

def typingOnly (origin : (symbols initial).EquationName) :
    Derivation (signature initial) (.equation ((signature initial).equationSource origin)
      ((signature initial).equationTarget origin) ((signature initial).left origin) ((signature initial).left origin)) :=
  .reflexivity ((headers initial).left origin)

def declaredRoundtrip (origin : (symbols initial).EquationName) :
    Derivation (signature initial) (.equation ((signature initial).equationSource origin)
      ((signature initial).equationTarget origin) ((signature initial).left origin) ((signature initial).left origin)) :=
  .transitivity (.declaredEquation origin ((headers initial).left origin) ((headers initial).right origin))
    (.symmetry (.declaredEquation origin ((headers initial).left origin) ((headers initial).right origin)))

theorem the_same_conclusion_retains_a_strictly_larger_actual_proof_account
    (depth : Nat) (law : Law (stages initial depth).presentation) :
    proofBound initial (typingOnly initial (.inr ⟨depth, law⟩)) <
      proofBound initial (declaredRoundtrip initial (.inr ⟨depth, law⟩)) := by
  simp only [typingOnly, declaredRoundtrip, proofBound, equationBirth]
  omega

theorem conclusion_alone_cannot_recover_every_actual_proof_account
    (depth : Nat) (law : Law (stages initial depth).presentation) :
    ¬∃ account : Judgment C (symbols initial) → Nat,
      ∀ {judgment} (tree : Derivation (signature initial) judgment), account judgment = proofBound initial tree := by
  rintro ⟨account, reads⟩
  have first := reads (typingOnly initial (.inr ⟨depth, law⟩))
  have second := reads (declaredRoundtrip initial (.inr ⟨depth, law⟩))
  have different := the_same_conclusion_retains_a_strictly_larger_actual_proof_account initial depth law
  exact (Nat.ne_of_lt different) (first.symm.trans second)

theorem the_declared_roundtrip_has_actual_finite_stage_recovery
    (depth : Nat) (law : Law (stages initial depth).presentation) :
    ∃ recoveredDepth, Nonempty (Recovery initial recoveredDepth
      (.equation ((signature initial).equationSource (.inr ⟨depth, law⟩))
        ((signature initial).equationTarget (.inr ⟨depth, law⟩))
        ((signature initial).left (.inr ⟨depth, law⟩)) ((signature initial).left (.inr ⟨depth, law⟩)))) :=
  judgment_finite initial (declaredRoundtrip initial (.inr ⟨depth, law⟩))

def concreteInitial := RelativeClosedGeneratedQuantifierIterationControls.initial

def completeSecondRoute : Route (signature concreteInitial) :=
  RelativeClosedGeneratedQuantifierIterationControls.secondRoute.translate (stageMap concreteInitial 2)

def secondOrigin : (symbols concreteInitial).ArrowName :=
  .inr ⟨1, ⟨.existential, RelativeClosedGeneratedQuantifierIterationControls.firstRoute⟩⟩

theorem the_whole_second_route_retains_its_actual_added_origin :
    completeSecondRoute.arrow.code = .name secondOrigin := rfl

theorem no_initial_primitive_is_that_second_stage_origin :
    ¬∃ previous : concreteInitial.symbols.ArrowName, arrows concreteInitial 0 previous = secondOrigin := by
  intro impossible
  have bound := (arrows_preimage concreteInitial 0 secondOrigin).mp impossible
  change 2 ≤ 0 at bound
  omega

theorem no_complete_initial_raw_expression_maps_to_the_added_second_operator :
    ¬∃ previous : ArrowCode RelativeClosedGeneratedQuantifierControls.source.closed.Obj concreteInitial.symbols,
      arrowCode concreteInitial 0 previous = completeSecondRoute.arrow.code := by
  rintro ⟨previous, read⟩
  rw [the_whole_second_route_retains_its_actual_added_origin] at read
  cases previous <;> simp only [arrowCode, ArrowCode.map, ArrowCode.name.injEq, reduceCtorEq] at read
  rename_i origin
  exact no_initial_primitive_is_that_second_stage_origin ⟨origin, read⟩

theorem the_whole_generated_second_route_has_actual_typed_recovery :
    ∃ depth, ∃ previousSource previousTarget : Object (stages concreteInitial depth).presentation,
      ∃ previous : RawHom previousSource previousTarget,
        (stageMap concreteInitial depth).object previousSource = completeSecondRoute.source ∧
        (stageMap concreteInitial depth).object previousTarget = completeSecondRoute.target ∧
        ((stageMap concreteInitial depth).rawArrow previous).code = completeSecondRoute.arrow.code :=
  whole_arrow_finite concreteInitial completeSecondRoute.arrow

theorem the_independent_native_second_operator_retains_its_complete_function_input
    (first second : Nat → Nat) (parameter : Nat) :
    ElementaryTypePredicateReadout.Contains
      (RelativeClosedGeneratedQuantifierIterationControls.output first second)
      (RelativeClosedGeneratedQuantifierIterationControls.firstImage
        (RelativeClosedGeneratedQuantifierIterationControls.chosen first second parameter), parameter) :=
  RelativeClosedGeneratedQuantifierIterationControls.actual_second_stage_admits_the_complete_first_stage_result
    first second parameter

end Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierClosureControls
