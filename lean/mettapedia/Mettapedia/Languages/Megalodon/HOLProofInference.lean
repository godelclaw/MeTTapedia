import Mettapedia.Languages.Megalodon.HOLNormalForms
import Mettapedia.Languages.Megalodon.TypedProofApplication

/-!
# Native inference with typed HOL goals and ordered contexts

The judgment retains an actual native proof program and its inferred
proposition. Source assumptions and conclusions are read through the computed
normal form of the full HOL encoding. Checking the authored conclusion also
requires its definition-unfolding policy; that connection is proved below.

The rule constructions use the existing native checker and budget
monotonicity. They are inputs to the all-constructor compiler theorem, not a
replacement for that theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLProofInference

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation ProofJudgment HOLNormalForms HOLTermEncoding

variable {environment : Environment} {gamma : Ctx Base} {domain : Ty Base}

def context (depth : Nat) (assumptions : List (Formula (Constant environment) gamma)) : Context :=
  ⟨depth, gamma.map reifyType, assumptions.map normalFormCode⟩

def Infers (depth : Nat) (assumptions : List (Formula (Constant environment) gamma))
    (program : Pf) (conclusion : Formula (Constant environment) gamma) : Prop :=
  ∃ fuel, Proves environment fuel (context depth assumptions) program (normalFormCode conclusion)

theorem of_assumptions_eq {depth : Nat}
    {assumptions other : List (Formula (Constant environment) gamma)}
    {program : Pf} {conclusion : Formula (Constant environment) gamma}
    (same : assumptions = other) (inferred : Infers depth assumptions program conclusion) :
    Infers depth other program conclusion :=
  (congrArg (fun entries => Infers depth entries program conclusion) same).mp inferred

theorem of_conclusion_eq {depth : Nat}
    {assumptions : List (Formula (Constant environment) gamma)}
    {program : Pf} {source target : Formula (Constant environment) gamma}
    (same : source = target) (inferred : Infers depth assumptions program source) :
    Infers depth assumptions program target :=
  (congrArg (Infers depth assumptions program) same).mp inferred

theorem of_conversion {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}
    {program : Pf} {source target : Formula (Constant environment) gamma}
    (inferred : Infers depth assumptions program source)
    (converted : EtaConversion.BetaEtaConv source target) : Infers depth assumptions program target := by
  obtain ⟨fuel, derived⟩ := inferred
  refine ⟨fuel, ?_⟩
  rw [← normalFormCode_eq_of_conversion converted]
  exact derived

theorem context_cons (depth : Nat) (assumptions : List (Formula (Constant environment) gamma))
    (premise : Formula (Constant environment) gamma) :
    context depth (premise :: assumptions) =
      (context depth assumptions).proofBinder (normalFormCode premise) := rfl

theorem context_weaken (depth : Nat) (assumptions : List (Formula (Constant environment) gamma)) :
    context depth (weakenHyps (σ := domain) assumptions) =
      (context depth assumptions).termBinder (reifyType domain) := by
  simp [context, weakenHyps, Context.termBinder, List.map_map, normalFormCode_weaken]

theorem hyp (depth : Nat) (assumptions : List (Formula (Constant environment) gamma))
    (index : Fin assumptions.length) :
    Infers depth assumptions (.hyp index.val) (assumptions.get index) := by
  refine ⟨0, .hyp ?_⟩
  simp [context, index.isLt]

theorem topI (depth : Nat) (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions ImpredicativeLogicalProofs.truthIntroduction .top := by
  refine ⟨32, ?_⟩
  rw [normalFormCode_top]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.truthIntroduction_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

theorem impE {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}
    {function argument : Pf} {premise conclusion : Formula (Constant environment) gamma}
    (functionInferred : Infers depth assumptions function (.imp premise conclusion))
    (argumentInferred : Infers depth assumptions argument premise) :
    Infers depth assumptions (.proofApp function argument) conclusion := by
  obtain ⟨first, functionDerived⟩ := functionInferred
  obtain ⟨second, argumentDerived⟩ := argumentInferred
  rw [normalFormCode_imp] at functionDerived
  exact ⟨max first second, TypedProofApplication.proof_application functionDerived argumentDerived⟩

theorem impI {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}
    {program : Pf} {premise conclusion : Formula (Constant environment) gamma}
    (formed : plainAnnotations depth (native premise) = true)
    (unfoldingAbsent : DeltaNormalInvariant.Normal environment (native premise))
    (inferred : Infers depth (premise :: assumptions) program conclusion) :
    Infers depth assumptions (.proofLam (native premise) program) (.imp premise conclusion) := by
  obtain ⟨bodyFuel, bodyDerived⟩ := inferred
  let completed := NormalizationTermination.completeNative (encode premise) (native_erased premise)
    unfoldingAbsent
  let fuel := max bodyFuel completed.val.1
  have normalized : MathdataKernel.normalize environment completed.val.1 (native premise) =
      some (normalFormCode premise) := completed.property
  have more := FuelledConversionProfile.normalize_mono environment _ _
    (Nat.le_max_right bodyFuel completed.val.1) normalized
  refine ⟨fuel, ?_⟩
  rw [normalFormCode_imp]
  apply Proves.proofLam (native_infers premise depth formed) more
  simpa only [context_cons] using
    SourceCursor.proof_mono (Nat.le_max_left bodyFuel completed.val.1) bodyDerived

theorem allI {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}
    {program : Pf} {body : Formula (Constant environment) (domain :: gamma)}
    (formed : (reifyType domain).plainWellFormed depth = true)
    (inferred : Infers depth (weakenHyps assumptions) program body) :
    Infers depth assumptions (.termLam (reifyType domain) program) (.all body) := by
  obtain ⟨fuel, bodyDerived⟩ := inferred
  refine ⟨fuel, ?_⟩
  rw [normalFormCode_all]
  apply Proves.termLam formed
  simpa only [context_weaken] using bodyDerived

private theorem encode_instantiate (argument : Term (Constant environment) gamma domain)
    (body : Formula (Constant environment) (domain :: gamma)) :
    encode (instantiate argument body) = instantiate (encode argument) (encode body) := by
  unfold instantiate
  rw [encode_subst]
  apply subst_ext
  intro type index
  cases index <;> rfl

theorem allE {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}
    {program : Pf} {body : Formula (Constant environment) (domain :: gamma)}
    (argument : Term (Constant environment) gamma domain)
    (formed : plainAnnotations depth (native argument) = true)
    (argumentNormal : DeltaNormalInvariant.Normal environment (native argument))
    (contextNormal : DeltaNormalInvariant.ContextNormal environment (context depth assumptions))
    (inferred : Infers depth assumptions program (.all body)) :
    Infers depth assumptions (.termApp program (native argument)) (instantiate argument body) := by
  obtain ⟨functionFuel, functionDerived⟩ := inferred
  rw [normalFormCode_all] at functionDerived
  have bodyNormal : DeltaNormalInvariant.Normal environment (normalFormCode body) := by
    simpa only [DeltaNormalInvariant.Normal, NativeSupport.termSupport] using
      DeltaNormalInvariant.inferred_normal functionDerived contextNormal
  obtain ⟨fuel, output, normalized, derived⟩ :=
    TypedProofApplication.term_application (normalForm body) (normalForm_erased body)
      (encode argument) (native_erased argument) formed argumentNormal contextNormal functionDerived
  have actualErased : erase (instantiate (encode argument) (normalForm body)) =
      some (Tm.instantiate (native argument) (normalFormCode body)) := by
    rw [erase_instantiate _ _ (native_erased argument), normalForm_erased body]
    rfl
  have actualNormalized : Tm.normalize fuel (Tm.instantiate (native argument) (normalFormCode body)) =
      some output := by
    rw [← DeltaNormalInvariant.application_normalization environment fuel bodyNormal
      (DeltaNormalInvariant.fixed argumentNormal fuel)]
    exact normalized
  let completed := NormalizationTermination.complete (encode (instantiate argument body))
    (native_erased (instantiate argument body))
  have goalNormalized : Tm.normalize completed.val.1 (native (instantiate argument body)) =
      some (normalFormCode (instantiate argument body)) := completed.property
  have converted : EtaConversion.BetaEtaConv (encode (instantiate argument body))
      (instantiate (encode argument) (normalForm body)) := by
    rw [encode_instantiate]
    exact BetaEtaSubstitution.subst (Subst.single (encode argument)) (encoded_to_normalForm body)
  have same := NormalizationNormalForm.normalize_coherent _ _
    (native_erased (instantiate argument body)) actualErased converted goalNormalized actualNormalized
  refine ⟨fuel, ?_⟩
  rw [same]
  exact derived

theorem checked_of_inferred {depth : Nat} {assumptions : List (Formula (Constant environment) gamma)}
    {program : Pf} {conclusion : Formula (Constant environment) gamma}
    (unfoldingAbsent : DeltaNormalInvariant.Normal environment (native conclusion))
    (inferred : Infers depth assumptions program conclusion) :
    ∃ fuel, checkProof environment fuel depth (gamma.map reifyType)
      (assumptions.map normalFormCode) program (native conclusion) = true := by
  obtain ⟨proofFuel, derived⟩ := inferred
  let completed := NormalizationTermination.completeNative (encode conclusion)
    (native_erased conclusion) unfoldingAbsent
  let fuel := max proofFuel completed.val.1
  have normalized : MathdataKernel.normalize environment completed.val.1 (native conclusion) =
      some (normalFormCode conclusion) := completed.property
  refine ⟨fuel, (ProofJudgment.check_iff environment fuel (context depth assumptions) _ _).mpr ?_⟩
  exact ⟨normalFormCode conclusion,
    FuelledConversionProfile.normalize_mono environment _ _ (Nat.le_max_right _ _) normalized,
    SourceCursor.proof_mono (Nat.le_max_left _ _) derived⟩

/-- A successful program cannot be relabelled with a different canonical
conclusion. This retains the target's admitted beta/eta conversion rather
than demanding literal equality of the authored source formulas. -/
theorem refuses_other_normal_form {depth : Nat}
    {assumptions : List (Formula (Constant environment) gamma)}
    {program : Pf} {conclusion other : Formula (Constant environment) gamma}
    (inferred : Infers depth assumptions program conclusion)
    (otherNormal : DeltaNormalInvariant.Normal environment (native other))
    (different : normalFormCode conclusion ≠ normalFormCode other) (fuel : Nat) :
    checkProof environment fuel depth (gamma.map reifyType) (assumptions.map normalFormCode)
      program (native other) = false := by
  cases accepted : checkProof environment fuel depth (gamma.map reifyType)
      (assumptions.map normalFormCode) program (native other) with
  | false => rfl
  | true =>
      obtain ⟨proofFuel, sourceDerived⟩ := inferred
      obtain ⟨output, normalized, otherDerived⟩ :=
        (ProofJudgment.check_iff environment fuel (context depth assumptions) program (native other)).mp accepted
      have betaNormalized : Tm.normalize fuel (native other) = some output := by
        simpa [MathdataKernel.normalize, DeltaNormalInvariant.fixed otherNormal fuel] using normalized
      have goalCode := normalFormCode_of_normalizes other betaNormalized
      have sourceInferred := (SourceCursor.proof_mono (Nat.le_max_left proofFuel fuel) sourceDerived).infer
      have otherInferred := (SourceCursor.proof_mono (Nat.le_max_right proofFuel fuel) otherDerived).infer
      have same : normalFormCode conclusion = output :=
        Option.some.inj (sourceInferred.symm.trans otherInferred)
      exact (different (same.trans goalCode.symm)).elim

#print axioms context_weaken
#print axioms of_conversion
#print axioms hyp
#print axioms topI
#print axioms impE
#print axioms impI
#print axioms allI
#print axioms allE
#print axioms checked_of_inferred

end Mettapedia.Languages.Megalodon.HOLProofInference
