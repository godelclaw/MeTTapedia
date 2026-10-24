import Mettapedia.UniversalAlgebra.EquationalLogic
import Mettapedia.Logic.RuleConservativeExtension

/-!
# Conservative extension of equation systems

An equation-system extension is conservative when every added equation was
already an equational consequence of the original system.  This file proves
that criterion from substitution admissibility and also proves its sharp
negative boundary: adjoining a genuinely underivable equation changes the
consequence relation.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Mettapedia.Logic

universe u

variable {S : Signature.{u}}

namespace EquationSystem

/-- Append a finite list of equation occurrences to an equation system. -/
def extend (system : EquationSystem S) (additional : List (Equation S)) :
    EquationSystem S where
  equations := system.equations ++ additional

/-- Adding only already-derivable equations preserves every equational
consequence, in both directions. -/
theorem extend_sameConsequences (system : EquationSystem S)
    (additional : List (Equation S))
    (redundant : ∀ equation ∈ additional,
      EquationalConsequence system equation) :
    SameConsequences (system.extend additional) system := by
  intro equation
  constructor
  · intro extensionDerivation
    apply EquationalConsequence.translate_axioms (source := system)
      (target := system.extend additional) _ extensionDerivation
    intro listedEquation listedEquationMem
    change listedEquation ∈ system.equations ++ additional at listedEquationMem
    rw [List.mem_append] at listedEquationMem
    rcases listedEquationMem with originalMem | additionalMem
    · exact EquationalConsequence.of_mem originalMem
    · exact redundant listedEquation additionalMem
  · intro originalDerivation
    exact EquationalConsequence.mono (fun listedEquation listedEquationMem => by
      change listedEquation ∈ system.equations ++ additional
      exact List.mem_append_left additional listedEquationMem) originalDerivation

/-- Negative boundary: adjoining one genuinely underivable equation cannot
preserve the consequence relation. -/
theorem extend_not_sameConsequences_of_not_consequence
    (system : EquationSystem S) (equation : Equation S)
    (notDerivable : ¬ EquationalConsequence system equation) :
    ¬ SameConsequences (system.extend [equation]) system := by
  intro sameConsequences
  have inExtension : equation ∈ system.extend [equation] := by
    change equation ∈ system.equations ++ [equation]
    exact List.mem_append_right _ (by simp)
  exact notDerivable ((sameConsequences equation).mp
    (EquationalConsequence.of_mem inExtension))

end EquationSystem

end Mettapedia.UniversalAlgebra
