import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelIteration

/-!
# A realized successor is determined by its old meanings

Restriction retains the independently supplied base and old declarations.
Actual new header readings cast each supplied complete operator to its two
function objects. The six authored equations then earn its local quantifier
qualification. Complete operation uniqueness determines both new arrows;
no new-operator image or whole-expression compatibility is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.UniversalStage

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Iteration

universe k w z
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {quantifiers : InternalPredicateQuantifiedObject.Operations D} {stage : Stage C}

private theorem conjunction_retained :
    stage.next.language.conjunction.code =
      (stage.inclusion.rawArrow stage.language.conjunction).code :=
  SignatureMap.arrow_code_compose (arrowInclusion stage.presentation stage.language)
    (equationInclusion stage.presentation stage.language) stage.language.conjunction

private theorem truth_retained :
    stage.next.truth.code = (stage.inclusion.rawArrow stage.truth).code :=
  SignatureMap.arrow_code_compose (arrowInclusion stage.presentation stage.language)
    (equationInclusion stage.presentation stage.language) stage.truth

def restrict (supplied : Model quantifiers stage.next) : Model quantifiers stage where
  meanings := stage.inclusion.precompose supplied.meanings
  admitted := stage.inclusion.realization_precompose supplied.meanings supplied.admitted
  proposition :=
    (stage.inclusion.evaluateObject_precompose supplied.meanings stage.language.proposition.code).symm.trans
      ((congrArg supplied.meanings.evaluateObject
        (congrArg Object.code stage.proposition_retained).symm).trans supplied.proposition)
  conjunction :=
    (stage.inclusion.evaluateArrow_precompose supplied.meanings stage.language.conjunction.code).symm.trans
      ((congrArg supplied.meanings.evaluateArrow conjunction_retained.symm).trans supplied.conjunction)
  truth :=
    (stage.inclusion.evaluateArrow_precompose supplied.meanings stage.truth.code).symm.trans
      ((congrArg supplied.meanings.evaluateArrow truth_retained.symm).trans supplied.truth)

def arrowMeanings (supplied : Model quantifiers stage.next) :
    RelativeClosedSyntax.Interpretation.Assignment C
      (ArrowExtension.extendedSymbols stage.symbols (Operation stage.presentation)) D where
  base := supplied.meanings.base
  object := supplied.meanings.object
  arrow := supplied.meanings.arrow

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_extensionality {symbols : Symbols.{k}}
    {first second : RelativeClosedSyntax.Interpretation.Assignment C symbols D}
    (bases : first.base = second.base)
    (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  rcases first with ⟨firstBase, firstObjects, firstArrows⟩
  rcases second with ⟨secondBase, secondObjects, secondArrows⟩
  dsimp only at bases objects arrows
  subst secondBase secondObjects secondArrows
  rfl

theorem equation_extension_read (supplied : Model quantifiers stage.next) :
    EquationExtension.extendAssignment (Index := Law stage.presentation) (arrowMeanings supplied) =
      supplied.meanings := by
  rcases supplied with ⟨⟨base, objects, arrows⟩, admitted, proposition, conjunction, truth⟩
  rfl

theorem arrow_decomposition (supplied : Model quantifiers stage.next) :
    arrowMeanings supplied = ArrowExtension.extendAssignment (restrict supplied).meanings
      (fun origin => supplied.meanings.arrow (.inr origin)) := by
  apply assignment_extensionality
  · change supplied.meanings.base = (𝟭 C ⋙ 𝟭 C) ⋙ supplied.meanings.base
    rw [Functor.id_comp, Functor.id_comp]
  · rfl
  · funext origin
    cases origin <;> rfl

theorem arrow_realization (supplied : Model quantifiers stage.next) :
    RelativeClosedSyntax.Interpretation.Realization (arrowSignature stage.presentation stage.language)
      (arrowMeanings supplied) :=
  (equationInclusion stage.presentation stage.language).realization_precompose
    supplied.meanings supplied.admitted

theorem added_headers (supplied : Model quantifiers stage.next) :
    ArrowExtension.AddedAdmission stage.presentation (arrowDeclaration stage.presentation stage.language)
      (restrict supplied).meanings (fun origin => supplied.meanings.arrow (.inr origin)) := by
  have admitted := arrow_realization supplied
  rw [arrow_decomposition] at admitted
  exact ArrowExtension.necessary_admission stage.presentation
    (arrowDeclaration stage.presentation stage.language) (restrict supplied).meanings
      (fun origin => supplied.meanings.arrow (.inr origin)) admitted

def castArrow (supplied : RelativeClosedSyntax.Interpretation.ArrowValue D) {source target : D}
    (first : supplied.source = source) (last : supplied.target = target) : source ⟶ target :=
  eqToHom first.symm ≫ supplied.arrow ≫ eqToHom last

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem castArrow_value (supplied : RelativeClosedSyntax.Interpretation.ArrowValue D) {source target : D}
    (first : supplied.source = source) (last : supplied.target = target) :
    (⟨source, target, castArrow supplied first last⟩ : RelativeClosedSyntax.Interpretation.ArrowValue D) =
      supplied := by
  rcases supplied with ⟨before, after, arrow⟩
  dsimp only at first last
  subst source target
  simp only [castArrow, eqToHom_refl, Category.id_comp, Category.comp_id]

theorem endpoints (supplied : Model quantifiers stage.next) (origin : Operation stage.presentation) :
    (supplied.meanings.arrow (.inr origin)).source =
        Interpretation.power stage.presentation (restrict supplied).meanings (restrict supplied).admitted
          quantifiers.predicates origin.route.source ∧
      (supplied.meanings.arrow (.inr origin)).target =
        Interpretation.power stage.presentation (restrict supplied).meanings (restrict supplied).admitted
          quantifiers.predicates origin.route.target := by
  have actual := added_headers supplied
  constructor
  · exact Option.some.inj ((actual.source origin).symm.trans
      (Readout.power_read stage.language (restrict supplied).meanings quantifiers.predicates
        (restrict supplied).proposition
        (RelativeClosedSyntax.Interpretation.objectValue_readout
          (restrict supplied).meanings (restrict supplied).admitted origin.route.source)))
  · exact Option.some.inj ((actual.target origin).symm.trans
      (Readout.power_read stage.language (restrict supplied).meanings quantifiers.predicates
        (restrict supplied).proposition
        (RelativeClosedSyntax.Interpretation.objectValue_readout
          (restrict supplied).meanings (restrict supplied).admitted origin.route.target)))

def meaning (supplied : Model quantifiers stage.next) :
    Interpretation.Meaning stage.presentation (restrict supplied).meanings (restrict supplied).admitted
      quantifiers.predicates where
  universal route := castArrow (supplied.meanings.arrow (.inr ⟨.universal, route⟩))
    (endpoints supplied ⟨.universal, route⟩).1 (endpoints supplied ⟨.universal, route⟩).2
  existential route := castArrow (supplied.meanings.arrow (.inr ⟨.existential, route⟩))
    (endpoints supplied ⟨.existential, route⟩).1 (endpoints supplied ⟨.existential, route⟩).2

theorem added_complete_read (supplied : Model quantifiers stage.next)
    (origin : Operation stage.presentation) :
    Interpretation.added stage.presentation (restrict supplied).meanings (restrict supplied).admitted
      quantifiers.predicates (meaning supplied) origin = supplied.meanings.arrow (.inr origin) := by
  rcases origin with ⟨kind, route⟩
  cases kind with
  | universal =>
    exact castArrow_value _ (endpoints supplied ⟨.universal, route⟩).1
      (endpoints supplied ⟨.universal, route⟩).2
  | existential =>
    exact castArrow_value _ (endpoints supplied ⟨.existential, route⟩).1
      (endpoints supplied ⟨.existential, route⟩).2

theorem final_assignment_read (supplied : Model quantifiers stage.next) :
    Interpretation.finalAssignment stage.presentation (restrict supplied).meanings (restrict supplied).admitted
      quantifiers.predicates (meaning supplied) = supplied.meanings := by
  have arrows := arrow_decomposition supplied
  have inputs : Interpretation.added stage.presentation (restrict supplied).meanings
      (restrict supplied).admitted quantifiers.predicates (meaning supplied) =
        fun origin => supplied.meanings.arrow (.inr origin) := funext (added_complete_read supplied)
  change EquationExtension.extendAssignment
    (ArrowExtension.extendAssignment (restrict supplied).meanings
      (Interpretation.added stage.presentation (restrict supplied).meanings (restrict supplied).admitted
        quantifiers.predicates (meaning supplied))) = _
  rw [inputs, ← arrows, equation_extension_read]

theorem admission (supplied : Model quantifiers stage.next) :
    Interpretation.Admission stage.presentation (restrict supplied).meanings (restrict supplied).admitted
      quantifiers.predicates (meaning supplied) := by
  apply (Interpretation.realization_iff stage.presentation stage.language
    (restrict supplied).meanings (restrict supplied).admitted quantifiers.predicates (meaning supplied)
      (restrict supplied).proposition (restrict supplied).conjunction).mp
  rw [final_assignment_read]
  exact supplied.admitted

theorem universal_read (supplied : Model quantifiers stage.next) (route : Route stage.presentation) :
    (meaning supplied).universal route =
      ((restrict supplied).meaning).universal route :=
  quantifiers.universal_unique _
    (Interpretation.universalQualification stage.presentation (restrict supplied).meanings
      (restrict supplied).admitted quantifiers.predicates (meaning supplied) (admission supplied) route)

theorem existential_read (supplied : Model quantifiers stage.next) (route : Route stage.presentation) :
    (meaning supplied).existential route =
      ((restrict supplied).meaning).existential route :=
  quantifiers.existential_unique _
    (Interpretation.existentialQualification stage.presentation (restrict supplied).meanings
      (restrict supplied).admitted quantifiers.predicates (meaning supplied) (admission supplied) route)

theorem meaning_unique (supplied : Model quantifiers stage.next) :
    meaning supplied = (restrict supplied).meaning := by
  exact congrArg₂ Interpretation.Meaning.mk
    (funext (universal_read supplied)) (funext (existential_read supplied))

theorem successor_unique (supplied : Model quantifiers stage.next) :
    supplied.meanings = (restrict supplied).next.meanings := by
  exact (final_assignment_read supplied).symm.trans
    (congrArg (Interpretation.finalAssignment stage.presentation (restrict supplied).meanings
      (restrict supplied).admitted quantifiers.predicates) (meaning_unique supplied))

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.UniversalStage
