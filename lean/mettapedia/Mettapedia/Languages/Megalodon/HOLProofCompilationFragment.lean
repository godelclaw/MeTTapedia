import Mettapedia.Languages.Megalodon.ProofCompilation
import Mettapedia.Languages.Megalodon.HOLTermFormation
import Mettapedia.Languages.Megalodon.MonomorphicProof

/-!
# The all-constructor compiler stays in the monomorphic replay fragment

All encoded source arguments have native monomorphic syntax. With
monomorphic supplied extensionality programs, the complete compiler emits
the grammar supported by the existing Henkin proof interpreter.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.Megalodon.HOLProofCompilationFragment

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation NativeProof
open HOLTermFormation

variable {environment : Environment}

theorem compile_monomorphic (functional : Tp → Tp → Pf) (propositional : Pf)
    (functionalOrdinary : ∀ domain result, monomorphic (functional domain result) = true)
    (propositionalOrdinary : monomorphic propositional = true)
    {gamma : Ctx Base} {assumptions : List (Formula (Constant environment) gamma)}
    {conclusion : Formula (Constant environment) gamma}
    (source : ProofSyntax (Constant environment) assumptions conclusion) :
    monomorphic (ProofCompilation.compile functional propositional source) = true := by
  induction source <;>
    simp_all [ProofCompilation.compile, LogicalProofCompilation.applyTerms,
      LogicalProofCompilation.applyProofs, monomorphic, supported,
      ImpredicativeLogicalProofs.truthIntroduction, ImpredicativeLogicalProofs.falsityElimination,
      ImpredicativeLogicalProofs.conjunctionIntroduction, ImpredicativeLogicalProofs.conjunctionLeft,
      ImpredicativeLogicalProofs.conjunctionRight, ImpredicativeLogicalProofs.disjunctionLeft,
      ImpredicativeLogicalProofs.disjunctionRight, ImpredicativeLogicalProofs.disjunctionElimination,
      ImpredicativeLogicalProofs.existentialIntroduction, ImpredicativeLogicalProofs.existentialElimination,
      ImpredicativeLogicalProofs.falsity,
      ImpredicativeLogicalProofs.conjunction, ImpredicativeLogicalProofs.disjunction,
      ImpredicativeLogicalProofs.existential,
      RelationEqualityProofs.reflexivity, RelationEqualityProofs.symmetry,
      RelationEqualityProofs.transitivity, RelationEqualityProofs.functionCongruence,
      RelationEqualityProofs.argumentCongruence, RelationEqualityProofs.propositionElimination,
      RelationEqualityProofs.propositionEliminationReverse, RelationEqualityProofs.substitution,
      RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
      RelationEqualityProofs.relationApply, Tm.shift]

theorem compile_fragment (functional : Tp → Tp → Pf) (propositional : Pf)
    (functionalOrdinary : ∀ domain result, monomorphic (functional domain result) = true)
    (propositionalOrdinary : monomorphic propositional = true) {depth : Nat}
    (plain : PlainEnvironment environment depth)
    {gamma : Ctx Base} {assumptions : List (Formula (Constant environment) gamma)}
    {conclusion : Formula (Constant environment) gamma}
    (source : ProofSyntax (Constant environment) assumptions conclusion) :
    Fragment environment depth (ProofCompilation.compile functional propositional source) :=
  fragment_of_monomorphic plain
    (compile_monomorphic functional propositional functionalOrdinary propositionalOrdinary source)

#print axioms compile_monomorphic
#print axioms compile_fragment

end Mettapedia.Languages.Megalodon.HOLProofCompilationFragment
