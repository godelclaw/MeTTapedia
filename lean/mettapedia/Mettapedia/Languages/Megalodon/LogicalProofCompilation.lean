import Mettapedia.Languages.Megalodon.HOLTermEncoding
import Mettapedia.Languages.Megalodon.ImpredicativeLogicalProofs

/-!
# Retained logical HOL proofs compiled to Mathdata proof terms

All connective and quantifier proof rules use the actual native combinators.
Terms use the full HOL encoder, including binary-relation equality inside
formulas. Equality proof rules have a separate compiler boundary; they are
not silently admitted as known propositions here. Output is proof data for
the existing checker, with its explicit environment and conversion budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.LogicalProofCompilation

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation
open ImpredicativeLogicalProofs

def applyTerms (proof : Pf) (arguments : List Tm) : Pf := arguments.foldl Pf.termApp proof
def applyProofs (proof : Pf) (premises : List Pf) : Pf := premises.foldl Pf.proofApp proof

variable {environment : Environment}

def compile : {gamma : Ctx Base} → {assumptions : List (Formula (Constant environment) gamma)} →
    {conclusion : Formula (Constant environment) gamma} →
    ProofSyntax (Constant environment) assumptions conclusion → Option Pf
  | _, _, _, .hyp occurrence => some (.hyp occurrence.val)
  | _, _, _, .topI => some truthIntroduction
  | _, _, conclusion, .botE inner => do
      let body ← compile inner
      pure (.proofApp (.termApp falsityElimination (HOLTermEncoding.native conclusion)) body)
  | _, _, _, @ProofSyntax.andI _ _ _ _ first second left right => do
      let leftProof ← compile left
      let rightProof ← compile right
      pure (applyProofs (applyTerms conjunctionIntroduction
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) [leftProof, rightProof])
  | _, _, _, @ProofSyntax.andEL _ _ _ _ first second inner => do
      let body ← compile inner
      pure (.proofApp (applyTerms conjunctionLeft
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) body)
  | _, _, _, @ProofSyntax.andER _ _ _ _ first second inner => do
      let body ← compile inner
      pure (.proofApp (applyTerms conjunctionRight
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) body)
  | _, _, _, @ProofSyntax.orIL _ _ _ _ first second inner => do
      let body ← compile inner
      pure (.proofApp (applyTerms disjunctionLeft
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) body)
  | _, _, _, @ProofSyntax.orIR _ _ _ _ first second inner => do
      let body ← compile inner
      pure (.proofApp (applyTerms disjunctionRight
        [HOLTermEncoding.native first, HOLTermEncoding.native second]) body)
  | _, _, conclusion, @ProofSyntax.orE _ _ _ _ first second _ cases left right => do
      let casesProof ← compile cases
      let leftProof ← compile left
      let rightProof ← compile right
      pure (applyProofs (applyTerms disjunctionElimination
        [HOLTermEncoding.native first, HOLTermEncoding.native second, HOLTermEncoding.native conclusion])
        [casesProof, .proofLam (HOLTermEncoding.native first) leftProof,
          .proofLam (HOLTermEncoding.native second) rightProof])
  | _, _, _, @ProofSyntax.impI _ _ _ _ premise _ inner => do
      let body ← compile inner
      pure (.proofLam (HOLTermEncoding.native premise) body)
  | _, _, _, .impE function argument => do
      let functionProof ← compile function
      let argumentProof ← compile argument
      pure (.proofApp functionProof argumentProof)
  | _, _, _, @ProofSyntax.notI _ _ _ _ premise inner => do
      let body ← compile inner
      pure (.proofLam (HOLTermEncoding.native premise) body)
  | _, _, _, .notE negative positive => do
      let negativeProof ← compile negative
      let positiveProof ← compile positive
      pure (.proofApp negativeProof positiveProof)
  | _, _, _, @ProofSyntax.allI _ _ _ _ domain _ inner => do
      let body ← compile inner
      pure (.termLam (reifyType domain) body)
  | _, _, _, .allE argument inner => do
      let body ← compile inner
      pure (.termApp body (HOLTermEncoding.native argument))
  | _, _, _, @ProofSyntax.exI _ _ _ _ domain predicate argument inner => do
      let body ← compile inner
      pure (.proofApp (applyTerms (existentialIntroduction (reifyType domain))
        [HOLTermEncoding.native (.lam predicate), HOLTermEncoding.native argument]) body)
  | _, _, conclusion, @ProofSyntax.exE _ _ _ _ domain predicate _ witness inner => do
      let witnessProof ← compile witness
      let body ← compile inner
      pure (applyProofs (applyTerms (existentialElimination (reifyType domain))
        [HOLTermEncoding.native (.lam predicate), HOLTermEncoding.native conclusion])
        [witnessProof, .termLam (reifyType domain) (.proofLam (HOLTermEncoding.native predicate) body)])
  | _, _, _, .eqRefl _ | _, _, _, .eqSymm _ | _, _, _, .eqTrans _ _
  | _, _, _, .eqPropI _ _ | _, _, _, .eqPropEL _ | _, _, _, .eqPropER _
  | _, _, _, .eqApp _ _ | _, _, _, .eqAppArg _ _ | _, _, _, .eqLam _
  | _, _, _, .funExt _ | _, _, _, .beta _ _ | _, _, _, .eta _ => none

private theorem isSome_one (value : Option Pf) (assemble : Pf → Pf) :
    (value.bind fun proof => some (assemble proof)).isSome = value.isSome := by
  cases value <;> rfl

private theorem isSome_two (first second : Option Pf) (assemble : Pf → Pf → Pf) :
    (first.bind fun left => second.bind fun right => some (assemble left right)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

private theorem isSome_three (first second third : Option Pf) (assemble : Pf → Pf → Pf → Pf) :
    (first.bind fun cases => second.bind fun left => third.bind fun right =>
      some (assemble cases left right)).isSome =
      (first.isSome && second.isSome && third.isSome) := by
  cases first <;> cases second <;> cases third <;> rfl

/-- Exact syntactic coverage. Equality may occur in source formulas; it is
the equality proof rules that require the additional compilation stage. -/
theorem compile_isSome {gamma : Ctx Base} {assumptions : List (Formula (Constant environment) gamma)}
    {conclusion : Formula (Constant environment) gamma}
    (proof : ProofSyntax (Constant environment) assumptions conclusion) :
    (compile proof).isSome = ImpredicativeConnectives.connectiveFragment proof := by
  induction proof <;>
    simp_all [compile, ImpredicativeConnectives.connectiveFragment,
      isSome_one, isSome_two, isSome_three]

end Mettapedia.Languages.Megalodon.LogicalProofCompilation
