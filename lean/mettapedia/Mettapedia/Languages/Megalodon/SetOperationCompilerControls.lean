import Mettapedia.Languages.Megalodon.SetOperationCompilerAcceptance

/-!
# Canonical contexts and changed conclusions in material HOL compilation

A reducible source hypothesis remains usable through its canonical encoded
representation. Supplying the authored redex as an unnormalized native
hypothesis fails the reference check, while a changed canonical conclusion
is refused at every budget. Duplicate hypothesis occurrences retain their
distinct proof indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.SetOperationCompilerControls

open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLNormalForms HOLProofInference
open SetOperationExtensionality

def reducibleTruth : ClosedFormula Symbol := .app (.lam (.var .vz)) .top

def retainedHypothesis : ProofSyntax Symbol [reducibleTruth] reducibleTruth := .hyp 0

theorem canonical_truth :
    normalFormCode (term [] reducibleTruth) = ImpredicativeLogicalProofs.truth := by
  have reduced : EtaConversion.BetaEtaConv (term [] reducibleTruth)
      (.top : ClosedFormula (Constant (environment []))) :=
    BetaEtaSubstitution.beta (.var .vz) .top
  exact (normalFormCode_eq_of_conversion reduced).trans normalFormCode_top

theorem compiled_hypothesis : compile [] retainedHypothesis = .hyp 0 := by
  simp [compile, proof, retainedHypothesis, ProofSyntax.mapTypes,
    HOLProofCompilationCorrectness.compile_castIndices, ProofCompilation.compile]

theorem canonical_hypothesis_accepted :
    ∃ fuel, checkProof (environment []) fuel 0 [] [ImpredicativeLogicalProofs.truth]
      (compile [] retainedHypothesis) (native (term [] reducibleTruth)) = true := by
  have accepted := SetOperationCompilerAcceptance.accepted [] retainedHypothesis
    (by intro domain result member; simp [retainedHypothesis,
      HOLProofCompilationCorrectness.functionalTypes] at member)
  simpa only [List.map_cons, List.map_nil, canonical_truth] using accepted

theorem authored_hypothesis_refused :
    checkProof (environment []) 32 0 [] [native (term [] reducibleTruth)]
      (compile [] retainedHypothesis) (native (term [] reducibleTruth)) = false := by
  rw [compiled_hypothesis]
  simp [term, reducibleTruth, mapTypes, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.truth,
    erase, reifyType, variableIndex, Var.mapTypes, checkProof, checkNormalizedProof, inferProof,
    MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Tm.instantiate, Tm.instantiateAt, Tm.shift]

theorem forged_falsity_refused (fuel : Nat) :
    checkProof (environment []) fuel 0 [] [ImpredicativeLogicalProofs.truth]
      (compile [] retainedHypothesis)
      (native (.bot : ClosedFormula (Constant (environment [])))) = false := by
  have inferred := HOLProofInference.hyp 0 [term [] reducibleTruth] ⟨0, by simp⟩
  have normal : DeltaNormalInvariant.Normal (environment [])
      (native (.bot : ClosedFormula (Constant (environment [])))) :=
    fun name entry _ lookup => SetOperationSemantics.lookup_opaque name entry lookup
  have different : normalFormCode (term [] reducibleTruth) ≠
      normalFormCode (.bot : ClosedFormula (Constant (environment []))) := by
    rw [canonical_truth, normalFormCode_bot]
    decide
  have refused := HOLProofInference.refuses_other_normal_form inferred normal different fuel
  simpa only [List.map_cons, List.map_nil, canonical_truth, compiled_hypothesis] using refused

theorem duplicate_occurrences :
    compile [] (ProofSyntax.hyp (Const := Symbol) (Δ := [reducibleTruth, reducibleTruth]) 0) = .hyp 0 ∧
    compile [] (ProofSyntax.hyp (Const := Symbol) (Δ := [reducibleTruth, reducibleTruth]) 1) = .hyp 1 ∧
    (Pf.hyp 0 ≠ Pf.hyp 1) := by
  constructor
  · simp [compile, proof, ProofSyntax.mapTypes,
      HOLProofCompilationCorrectness.compile_castIndices, ProofCompilation.compile]
  constructor
  · simp [compile, proof, ProofSyntax.mapTypes,
      HOLProofCompilationCorrectness.compile_castIndices, ProofCompilation.compile]
  · decide

#print axioms canonical_hypothesis_accepted
#print axioms authored_hypothesis_refused
#print axioms forged_falsity_refused
#print axioms duplicate_occurrences

end Mettapedia.Languages.Megalodon.SetOperationCompilerControls
