import Mettapedia.Languages.Megalodon.HOLEqualityProofInference
import Mettapedia.Languages.Megalodon.HOLLogicalProofInference
import Mettapedia.Languages.Megalodon.ExtensionalityAxioms
import Mettapedia.Languages.Megalodon.HOLTermFormation

/-!
# HOL equality introduction from explicit native extensionality programs

Functional and propositional extensionality remain supplied guest proofs.
The constructions instantiate their precise schemas and combine them with
the retained source premises. They do not assert those schemas for an
undeclared environment or for every type of an ambient host calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLExtensionalityProofInference

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLNormalForms HOLProofInference

variable {environment : Environment} {gamma : Ctx Base} {domain result : Ty Base}
variable {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}

def functionalFormula (domain result : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := domain ⇒ result) (.all (σ := domain ⇒ result)
    (.imp (.all (σ := domain)
      (.eq (.app (.var (.vs (.vs .vz))) (.var .vz))
        (.app (.var (.vs .vz)) (.var .vz))))
      (.eq (.var (.vs .vz)) (.var .vz))))

def propositionalFormula : Formula (Constant environment) gamma :=
  .all (σ := .prop) (.all (σ := .prop)
    (.imp (.and (.imp (.var (.vs .vz)) (.var .vz))
      (.imp (.var .vz) (.var (.vs .vz)))) (.eq (.var (.vs .vz)) (.var .vz))))

theorem functional_code (domain result : Ty Base) :
    normalFormCode (functionalFormula domain result (environment := environment) (gamma := gamma)) =
      ExtensionalityAxioms.Native.functional (reifyType domain) (reifyType result) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [functionalFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt,
    ExtensionalityAxioms.Native.functional, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem propositional_code :
    normalFormCode (propositionalFormula (environment := environment) (gamma := gamma)) =
      ExtensionalityAxioms.Native.propositional := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [propositionalFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.conjunctionFormula,
    weaken, rename, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt,
    ExtensionalityAxioms.Native.propositional, ImpredicativeLogicalProofs.conjunction,
    RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
    RelationEqualityProofs.relationApply]

theorem known_functional {name : Name}
    (declared : environment.lookupKnown? name = some
      (ExtensionalityAxioms.Native.functional (reifyType domain) (reifyType result))) :
    Infers depth assumptions (.known name) (functionalFormula domain result) := by
  refine ⟨32, ?_⟩
  rw [functional_code]
  apply ProofJudgment.Proves.known declared
  simp [MathdataKernel.normalize, deltaNormalize, ExtensionalityAxioms.Native.functional,
    RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
    RelationEqualityProofs.relationApply, Tm.normalize, Tm.normalizeOne, Tm.shift]

theorem known_propositional {name : Name}
    (declared : environment.lookupKnown? name = some ExtensionalityAxioms.Native.propositional) :
    Infers depth assumptions (.known name) propositionalFormula := by
  refine ⟨32, ?_⟩
  rw [propositional_code]
  apply ProofJudgment.Proves.known declared
  simp [MathdataKernel.normalize, deltaNormalize, ExtensionalityAxioms.Native.propositional,
    ImpredicativeLogicalProofs.conjunction,
    RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
    RelationEqualityProofs.relationApply, Tm.normalize, Tm.normalizeOne, Tm.shift]

theorem funExt {axiomProgram program : Pf}
    {left right : Term (Constant environment) gamma (domain ⇒ result)}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (axiomInferred : Infers depth assumptions axiomProgram (functionalFormula domain result))
    (inferred : Infers depth assumptions program
      (.all (.eq (.app (weaken left) (.var .vz)) (.app (weaken right) (.var .vz))))) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp axiomProgram (native left)) (native right)) program)
      (.eq left right) := by
  have specialized := HOLProofSpecialization.allE2 left right leftFormed rightFormed
    leftNormal rightNormal contextNormal axiomInferred
  have function : Infers depth assumptions
      (.termApp (.termApp axiomProgram (native left)) (native right))
      (.imp (.all (.eq (.app (weaken left) (.var .vz)) (.app (weaken right) (.var .vz))))
        (.eq left right)) := by
    simpa only [subst, Subst.cons, Subst.single, Subst.lift, weaken] using specialized
  exact HOLProofInference.impE function inferred

theorem eqLam {axiomProgram program : Pf}
    {left right : Term (Constant environment) (domain :: gamma) result}
    (domainFormed : (reifyType domain).plainWellFormed depth = true)
    (leftFormed : plainAnnotations depth (native (.lam left)) = true)
    (rightFormed : plainAnnotations depth (native (.lam right)) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native (.lam left)))
    (rightNormal : DeltaNormalInvariant.Normal environment (native (.lam right)))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (axiomInferred : Infers depth assumptions axiomProgram (functionalFormula domain result))
    (inferred : Infers depth (weakenHyps assumptions) program (.eq left right)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp axiomProgram (native (.lam left))) (native (.lam right)))
        (.termLam (reifyType domain) program)) (.eq (.lam left) (.lam right)) := by
  apply funExt leftFormed rightFormed leftNormal rightNormal contextNormal axiomInferred
  apply HOLProofInference.of_conversion (HOLProofInference.allI domainFormed inferred)
  exact BetaEtaSubstitution.all_congr (BetaEtaSubstitution.eq_congr
    (.symm _ _ (BetaEtaSubstitution.apply_weakened_abstraction left))
    (.symm _ _ (BetaEtaSubstitution.apply_weakened_abstraction right)))

theorem eqPropI {axiomProgram leftProgram rightProgram : Pf}
    {left right : Formula (Constant environment) gamma}
    (leftFormed : plainAnnotations depth (native left) = true)
    (rightFormed : plainAnnotations depth (native right) = true)
    (leftNormal : DeltaNormalInvariant.Normal environment (native left))
    (rightNormal : DeltaNormalInvariant.Normal environment (native right))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (axiomInferred : Infers depth assumptions axiomProgram propositionalFormula)
    (one : Infers depth assumptions leftProgram (.imp left right))
    (two : Infers depth assumptions rightProgram (.imp right left)) :
    Infers depth assumptions
      (.proofApp (.termApp (.termApp axiomProgram (native left)) (native right))
        (.proofApp (.proofApp (.termApp (.termApp
          ImpredicativeLogicalProofs.conjunctionIntroduction (native (.imp left right)))
          (native (.imp right left))) leftProgram) rightProgram)) (.eq left right) := by
  have specialized := HOLProofSpecialization.allE2 left right leftFormed rightFormed
    leftNormal rightNormal contextNormal axiomInferred
  have function : Infers depth assumptions
      (.termApp (.termApp axiomProgram (native left)) (native right))
      (.imp (.and (.imp left right) (.imp right left)) (.eq left right)) := by
    simpa only [subst, Subst.cons, Subst.single] using specialized
  have forwardFormed : plainAnnotations depth (native (.imp left right)) = true := by
    simp [HOLTermFormation.native_imp, plainAnnotations, leftFormed, rightFormed]
  have reverseFormed : plainAnnotations depth (native (.imp right left)) = true := by
    simp [HOLTermFormation.native_imp, plainAnnotations, leftFormed, rightFormed]
  have forwardNormal : DeltaNormalInvariant.Normal environment (native (.imp left right)) := by
    rw [HOLTermFormation.native_imp]
    exact DeltaNormalInvariant.pair leftNormal rightNormal
  have reverseNormal : DeltaNormalInvariant.Normal environment (native (.imp right left)) := by
    rw [HOLTermFormation.native_imp]
    exact DeltaNormalInvariant.pair rightNormal leftNormal
  exact HOLProofInference.impE function
    (HOLLogicalProofInference.andI forwardFormed reverseFormed forwardNormal reverseNormal
      contextNormal one two)

#print axioms functional_code
#print axioms propositional_code
#print axioms known_functional
#print axioms known_propositional
#print axioms funExt
#print axioms eqLam
#print axioms eqPropI

end Mettapedia.Languages.Megalodon.HOLExtensionalityProofInference
