import Mettapedia.UniversalAlgebra.Interpretation
import Mettapedia.UniversalAlgebra.EquationalLogic

/-!
# Interpretations between equation systems

A signature interpretation becomes an interpretation of equation systems only
when every translated source equation is a generated consequence of the target
system.  Such interpretations transport all equational consequences and pull
target models back to source models.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Mettapedia.Logic

universe u v w

variable {S : Signature.{u}} {T : Signature.{v}} {U : Signature.{w}}

namespace Equation

/-- Translate both sides of an equation along a signature interpretation. -/
def translate (interpretation : Signature.Interpretation S T)
    (equation : Equation S) : Equation T :=
  (equation.1.translate interpretation, equation.2.translate interpretation)

@[simp] theorem translate_id (equation : Equation S) :
    equation.translate (Signature.Interpretation.id S) = equation := by
  rcases equation with ⟨left, right⟩
  simp only [translate, Term.translate_id]

theorem translate_comp (first : Signature.Interpretation S T)
    (second : Signature.Interpretation T U) (equation : Equation S) :
    equation.translate (first.comp second) =
      (equation.translate first).translate second := by
  rcases equation with ⟨left, right⟩
  simp only [translate, Term.translate_comp]

end Equation

namespace EquationSystem

/-- A structural interpretation of one equation system in another.  The
operation map is algebraic, and every source equation is required to become a
generated target consequence. -/
structure Interpretation (source : EquationSystem S)
    (target : EquationSystem T) : Type (max u v) where
  symbols : Signature.Interpretation S T
  axiom_consequence : ∀ equation, equation ∈ source →
    EquationalConsequence target (equation.translate symbols)

namespace Interpretation

/-- Every equation-system interpretation transports every generated
equational consequence. -/
theorem mapConsequence {source : EquationSystem S}
    {target : EquationSystem T} (interpretation : Interpretation source target)
    {equation : Equation S} :
    EquationalConsequence source equation →
      EquationalConsequence target
        (equation.translate interpretation.symbols) := by
  intro derivation
  refine derivation.induction_on
    (P := fun equation => EquationalConsequence target
      (equation.translate interpretation.symbols)) ?_ ?_ ?_ ?_ ?_
  · intro equation member substitution
    have translatedAxiom := interpretation.axiom_consequence _ member
    have substituted := EquationalConsequence.subst translatedAxiom
      (fun index => (substitution index).translate interpretation.symbols)
    simpa only [Equation.translate, Equation.subst, Term.translate_subst]
      using substituted
  · intro term
    exact EquationalConsequence.refl target (term.translate interpretation.symbols)
  · intro _ _ derived
    exact EquationalConsequence.symm derived
  · intro _ _ _ first second
    exact EquationalConsequence.trans first second
  · intro symbol left right components
    apply EquationalConsequence.substitution_congr
      (interpretation.symbols.operation symbol).1
      (Term.finSubstitution (fun position =>
        (left position).translate interpretation.symbols))
      (Term.finSubstitution (fun position =>
        (right position).translate interpretation.symbols))
    intro index
    by_cases below : index < S.arity symbol
    · simp only [Term.finSubstitution, below, dite_true]
      exact components ⟨index, below⟩
    · simp only [Term.finSubstitution, below, dite_false]
      exact EquationalConsequence.refl target (.var index)

/-- The identity signature interpretation preserves every equation system. -/
def id (system : EquationSystem S) : Interpretation system system where
  symbols := Signature.Interpretation.id S
  axiom_consequence equation member := by
    simpa only [Equation.translate_id] using
      EquationalConsequence.of_mem member

/-- Consequence-equivalent systems over one signature interpret one another
through the identity operation map. -/
def ofSameConsequences {source target : EquationSystem S}
    (equivalent : source.SameConsequences target) :
    Interpretation source target where
  symbols := Signature.Interpretation.id S
  axiom_consequence equation member := by
    simpa only [Equation.translate_id] using
      (equivalent equation).mp (EquationalConsequence.of_mem member)

/-- Equation-system interpretations compose. -/
def comp {firstSystem : EquationSystem S}
    {secondSystem : EquationSystem T} {thirdSystem : EquationSystem U}
    (first : Interpretation firstSystem secondSystem)
    (second : Interpretation secondSystem thirdSystem) :
    Interpretation firstSystem thirdSystem where
  symbols := first.symbols.comp second.symbols
  axiom_consequence equation member := by
    have firstConsequence := first.axiom_consequence equation member
    have composedConsequence := second.mapConsequence firstConsequence
    simpa only [Equation.translate_comp] using composedConsequence

end Interpretation

/-- `source` is algebraically interpretable in `target` when an explicit
equation-system interpretation exists. -/
def IsInterpretableIn (source : EquationSystem S)
    (target : EquationSystem T) : Prop :=
  Nonempty (Interpretation source target)

theorem isInterpretableIn_refl (system : EquationSystem S) :
    IsInterpretableIn system system :=
  ⟨Interpretation.id system⟩

theorem isInterpretableIn_trans {firstSystem : EquationSystem S}
    {secondSystem : EquationSystem T} {thirdSystem : EquationSystem U}
    (firstSecond : IsInterpretableIn firstSystem secondSystem)
    (secondThird : IsInterpretableIn secondSystem thirdSystem) :
    IsInterpretableIn firstSystem thirdSystem := by
  rcases firstSecond with ⟨first⟩
  rcases secondThird with ⟨second⟩
  exact ⟨first.comp second⟩

end EquationSystem

namespace Equation

/-- A translated equation holds in a target model exactly when the source
equation holds in the induced reduct. -/
theorem holds_translate_iff_reduct {Carrier : Type w}
    (interpretation : Signature.Interpretation S T)
    (targetModel : Model T Carrier) (equation : Equation S) :
    (equation.translate interpretation).Holds targetModel ↔
      equation.Holds (targetModel.reduct interpretation) := by
  simp only [Equation.Holds, Equation.translate, Term.evaluate_translate]

end Equation

namespace EquationSystem.Interpretation

/-- Every target model satisfying the target equations pulls back to a source
model satisfying the source equations. -/
theorem reduct_satisfies {source : EquationSystem S}
    {target : EquationSystem T} (interpretation : Interpretation source target)
    {Carrier : Type w} (targetModel : Model T Carrier)
    (satisfiesTarget : targetModel.Satisfies target) :
    (targetModel.reduct interpretation.symbols).Satisfies source := by
  intro equation member
  have translatedConsequence := interpretation.axiom_consequence equation member
  have translatedHolds := EquationalConsequence.holdsInModel
    translatedConsequence targetModel satisfiesTarget
  exact (Equation.holds_translate_iff_reduct interpretation.symbols
    targetModel equation).mp translatedHolds

/-- Interpretations preserve model-theoretic consequence at every selected
carrier universe. -/
theorem mapEntailsAt {source : EquationSystem S}
    {target : EquationSystem T} (interpretation : Interpretation source target)
    {equation : Equation S} (entailed : EntailsAt.{u, w} source equation) :
    EntailsAt.{v, w} target
      (equation.translate interpretation.symbols) := by
  intro Carrier targetModel satisfiesTarget
  have sourceHolds := entailed Carrier
    (targetModel.reduct interpretation.symbols)
    (interpretation.reduct_satisfies targetModel satisfiesTarget)
  exact (Equation.holds_translate_iff_reduct interpretation.symbols
    targetModel equation).mpr sourceHolds

end EquationSystem.Interpretation

end Mettapedia.UniversalAlgebra
