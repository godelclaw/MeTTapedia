import Mettapedia.Languages.Megalodon.LogicalProofCompilation
import Mettapedia.Languages.Megalodon.ExtensionalityAxioms

/-!
# Executable expansion of retained HOL proofs into Megalodon proof terms

All 29 retained source constructors produce actual Mathdata proof syntax.
Functional and propositional extensionality are explicit supplied programs;
they must be justified in the chosen declaration/axiom profile. Beta and eta
use the target checker's conversion, whose finite budget remains separate.

This computes proof data and agrees with the existing logical compiler on its
admitted fragment. General acceptance and sufficient normalization budgets for
arbitrary inputs are further obligations, not fields assumed by this producer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ProofCompilation

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation
open ImpredicativeLogicalProofs
open LogicalProofCompilation (applyTerms applyProofs)

variable {environment : Environment}

def compile (functional : Tp → Tp → Pf) (propositional : Pf) : {gamma : Ctx Base} → {assumptions : List (Formula (Constant environment) gamma)} →
    {conclusion : Formula (Constant environment) gamma} →
    ProofSyntax (Constant environment) assumptions conclusion → Pf
  | _, _, _, .hyp occurrence => .hyp occurrence.val
  | _, _, _, .topI => truthIntroduction
  | _, _, conclusion, .botE inner =>
      let body := compile functional propositional inner
      (.proofApp (.termApp falsityElimination (HOLTermEncoding.native conclusion)) body)
  | _, _, _, @ProofSyntax.andI _ _ _ _ first second left right =>
      let leftProof := compile functional propositional left
      let rightProof := compile functional propositional right
      (applyProofs (applyTerms conjunctionIntroduction
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) [leftProof, rightProof])
  | _, _, _, @ProofSyntax.andEL _ _ _ _ first second inner =>
      let body := compile functional propositional inner
      (.proofApp (applyTerms conjunctionLeft
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) body)
  | _, _, _, @ProofSyntax.andER _ _ _ _ first second inner =>
      let body := compile functional propositional inner
      (.proofApp (applyTerms conjunctionRight
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) body)
  | _, _, _, @ProofSyntax.orIL _ _ _ _ first second inner =>
      let body := compile functional propositional inner
      (.proofApp (applyTerms disjunctionLeft
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) body)
  | _, _, _, @ProofSyntax.orIR _ _ _ _ first second inner =>
      let body := compile functional propositional inner
      (.proofApp (applyTerms disjunctionRight
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) body)
  | _, _, conclusion, @ProofSyntax.orE _ _ _ _ first second _ cases left right =>
      let casesProof := compile functional propositional cases
      let leftProof := compile functional propositional left
      let rightProof := compile functional propositional right
      (applyProofs (applyTerms disjunctionElimination
        [HOLTermEncoding.native first, HOLTermEncoding.native second, HOLTermEncoding.native conclusion])
        [casesProof, .proofLam (HOLTermEncoding.native first) leftProof,
          .proofLam (HOLTermEncoding.native second) rightProof])
  | _, _, _, @ProofSyntax.impI _ _ _ _ premise _ inner =>
      let body := compile functional propositional inner
      (.proofLam (HOLTermEncoding.native premise) body)
  | _, _, _, .impE function argument =>
      let functionProof := compile functional propositional function
      let argumentProof := compile functional propositional argument
      (.proofApp functionProof argumentProof)
  | _, _, _, @ProofSyntax.notI _ _ _ _ premise inner =>
      let body := compile functional propositional inner
      (.proofLam (HOLTermEncoding.native premise) body)
  | _, _, _, .notE negative positive =>
      let negativeProof := compile functional propositional negative
      let positiveProof := compile functional propositional positive
      (.proofApp negativeProof positiveProof)
  | _, _, _, @ProofSyntax.allI _ _ _ _ domain _ inner =>
      let body := compile functional propositional inner
      (.termLam (reifyType domain) body)
  | _, _, _, .allE argument inner =>
      let body := compile functional propositional inner
      (.termApp body (HOLTermEncoding.native argument))
  | _, _, _, @ProofSyntax.exI _ _ _ _ domain predicate argument inner =>
      let body := compile functional propositional inner
      (.proofApp (applyTerms (existentialIntroduction (reifyType domain))
        [HOLTermEncoding.native (.lam predicate), HOLTermEncoding.native argument]) body)
  | _, _, conclusion, @ProofSyntax.exE _ _ _ _ domain predicate _ witness inner =>
      let witnessProof := compile functional propositional witness
      let body := compile functional propositional inner
      (applyProofs (applyTerms (existentialElimination (reifyType domain))
        [HOLTermEncoding.native (.lam predicate), HOLTermEncoding.native conclusion])
        [witnessProof, .termLam (reifyType domain) (.proofLam (HOLTermEncoding.native predicate) body)])
  | _, _, _, @ProofSyntax.eqRefl _ _ _ _ source value =>
      .termApp (RelationEqualityProofs.reflexivity (reifyType source)) (HOLTermEncoding.native value)
  | _, _, _, @ProofSyntax.eqSymm _ _ _ _ source first second inner =>
      .proofApp (applyTerms (RelationEqualityProofs.symmetry (reifyType source))
        [HOLTermEncoding.native first, HOLTermEncoding.native second])
        (compile functional propositional inner)
  | _, _, _, @ProofSyntax.eqTrans _ _ _ _ source first second third left right =>
      applyProofs (applyTerms (RelationEqualityProofs.transitivity (reifyType source))
        [HOLTermEncoding.native first, HOLTermEncoding.native second, HOLTermEncoding.native third])
        [compile functional propositional left, compile functional propositional right]
  | _, _, _, @ProofSyntax.eqPropI _ _ _ _ first second left right =>
      .proofApp (applyTerms propositional [HOLTermEncoding.native first, HOLTermEncoding.native second])
        (applyProofs (applyTerms conjunctionIntroduction
          [HOLTermEncoding.native (.imp first second), HOLTermEncoding.native (.imp second first)])
          [compile functional propositional left, compile functional propositional right])
  | _, _, _, @ProofSyntax.eqPropEL _ _ _ _ first second inner =>
      .proofApp (applyTerms RelationEqualityProofs.propositionElimination
        [HOLTermEncoding.native first, HOLTermEncoding.native second])
        (compile functional propositional inner)
  | _, _, _, @ProofSyntax.eqPropER _ _ _ _ first second inner =>
      .proofApp (applyTerms RelationEqualityProofs.propositionEliminationReverse
        [HOLTermEncoding.native first, HOLTermEncoding.native second])
        (compile functional propositional inner)
  | _, _, _, @ProofSyntax.eqApp _ _ _ _ domain result first second argument inner =>
      .proofApp (applyTerms (RelationEqualityProofs.functionCongruence (reifyType domain) (reifyType result))
        [HOLTermEncoding.native first, HOLTermEncoding.native second, HOLTermEncoding.native argument])
        (compile functional propositional inner)
  | _, _, _, @ProofSyntax.eqAppArg _ _ _ _ domain result function first second inner =>
      .proofApp (applyTerms (RelationEqualityProofs.argumentCongruence (reifyType domain) (reifyType result))
        [HOLTermEncoding.native function, HOLTermEncoding.native first, HOLTermEncoding.native second])
        (compile functional propositional inner)
  | _, _, _, @ProofSyntax.eqLam _ _ _ _ domain result first second inner =>
      .proofApp (applyTerms (functional (reifyType domain) (reifyType result))
        [HOLTermEncoding.native (.lam first), HOLTermEncoding.native (.lam second)])
        (.termLam (reifyType domain) (compile functional propositional inner))
  | _, _, _, @ProofSyntax.funExt _ _ _ _ domain result first second inner =>
      .proofApp (applyTerms (functional (reifyType domain) (reifyType result))
        [HOLTermEncoding.native first, HOLTermEncoding.native second])
        (compile functional propositional inner)
  | _, _, _, @ProofSyntax.beta _ _ _ _ _domain result argument body =>
      .termApp (RelationEqualityProofs.reflexivity (reifyType result))
        (HOLTermEncoding.native (instantiate argument body))
  | _, _, _, @ProofSyntax.eta _ _ _ _ domain result function =>
      .termApp (RelationEqualityProofs.reflexivity (reifyType (.arr domain result)))
        (HOLTermEncoding.native function)

/-- Logical proofs retain precisely the existing compiled program, independently
of the supplied extensionality programs. -/
theorem logical_agreement (functional : Tp → Tp → Pf) (propositional : Pf)
    {gamma : Ctx Base} {assumptions : List (Formula (Constant environment) gamma)}
    {conclusion : Formula (Constant environment) gamma}
    (proof : ProofSyntax (Constant environment) assumptions conclusion)
    (fragment : ImpredicativeConnectives.connectiveFragment proof = true) :
    LogicalProofCompilation.compile proof = some (compile functional propositional proof) := by
  induction proof <;>
    simp_all [compile, LogicalProofCompilation.compile, ImpredicativeConnectives.connectiveFragment]

#print axioms compile
#print axioms logical_agreement

end Mettapedia.Languages.Megalodon.ProofCompilation
