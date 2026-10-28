import Mettapedia.Languages.VibeITP.Spec.Execution
import Mettapedia.Languages.VibeITP.Spec.SimultaneousInstantiation

/-!
# Derivability with simultaneous instantiation

The new calculus contains existing observed derivations and closes under rules
whose premises may themselves use simultaneous instantiation. Every supplied
replacement must be formed, including shadowed entries. Execution retains its
actual observation and guard. This is a source-calculus extension, not a
conservativity or denotational soundness theorem.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Spec

inductive DerivesWithExecutionV2 (theory : Theory) (observations : List ExecutionObservation) :
    Term → Prop where
  | base {statement : Term} :
      DerivesWithExecution theory observations statement →
        DerivesWithExecutionV2 theory observations statement
  | modusPonens {antecedent conclusion : Term} :
      DerivesWithExecutionV2 theory observations (.impl antecedent conclusion) →
      DerivesWithExecutionV2 theory observations antecedent →
        DerivesWithExecutionV2 theory observations conclusion
  | instantiateMany {source result : Term} {replacements : List (SymId × Term)} :
      DerivesWithExecutionV2 theory observations source →
      (∀ pair ∈ replacements, WellFormed theory.sig pair.2 = true) →
      SimultaneousInstantiation.statement theory.sig replacements source = some result →
        DerivesWithExecutionV2 theory observations result
  | jit {safe : Term} {observation : ExecutionObservation} :
      DerivesWithExecutionV2 theory observations safe → observation ∈ observations →
      GuardedExecution safe observation →
        DerivesWithExecutionV2 theory observations observation.statement

/-- Static v2 derivability uses no execution observations. -/
abbrev DerivesV2 (theory : Theory) : Term → Prop := DerivesWithExecutionV2 theory []

namespace DerivesWithExecutionV2

theorem instantiate {theory : Theory} {observations : List ExecutionObservation}
    {source result value : Term} {symbol : SymId}
    (derived : DerivesWithExecutionV2 theory observations source)
    (formed : WellFormed theory.sig value = true)
    (accepted : instantiateStatement theory.sig symbol value source = some result) :
    DerivesWithExecutionV2 theory observations result := by
  apply instantiateMany (replacements := [(symbol, value)]) derived
  · intro pair member
    have same : pair = (symbol, value) := by simpa using member
    subst pair
    exact formed
  · simpa only [SimultaneousInstantiation.statement_singleton] using accepted

theorem observation_extension {theory : Theory} {before after : List ExecutionObservation}
    (included : ∀ observation ∈ before, observation ∈ after) {statement : Term}
    (derived : DerivesWithExecutionV2 theory before statement) :
    DerivesWithExecutionV2 theory after statement := by
  induction derived with
  | base original => exact .base (derives_with_execution_observation_extension included original)
  | modusPonens _ _ implication premise => exact .modusPonens implication premise
  | instantiateMany _ formed accepted premise => exact .instantiateMany premise formed accepted
  | jit _ member guarded premise => exact .jit premise (included _ member) guarded

end DerivesWithExecutionV2

theorem static_derives_v2 {theory : Theory} {statement : Term}
    (derived : Derives theory statement) : DerivesV2 theory statement :=
  .base (static_derives_with_execution derived [])

instance : ExecutionCalculus DerivesWithExecutionV2 where
  fromBase := DerivesWithExecutionV2.base
  modusPonens := DerivesWithExecutionV2.modusPonens
  instantiate := DerivesWithExecutionV2.instantiate
  jit := DerivesWithExecutionV2.jit
  observation_extension := fun included derived =>
    DerivesWithExecutionV2.observation_extension included derived

#print axioms DerivesWithExecutionV2.instantiate
#print axioms DerivesWithExecutionV2.observation_extension
#print axioms static_derives_v2

end Mettapedia.Languages.VibeITP.Spec
