import Mettapedia.Languages.HOLLight.OpenVectorCompilation

/-!
# Compound constant images and the native compilation boundary

The small beta control uses the same primitive source alphabet as the vector
proofs. Its zero image is an application, so symbol renaming alone would not
cover it. A retained eta proof remains outside the eta-free compilation path.
The full vector export uses the registered source cohort separately.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.OpenVectorCompilation.Controls
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
local infixr:60 " ⇒ " => HOL.Ty.arr

def number : HOL.Ty AtomicTy := (Ty.var (Name.global "ControlNumber")).toHOL
def space : HOL.Ty AtomicTy := (Ty.var (Name.global "ControlVector")).toHOL

def constant (name : String) (type : HOL.Ty AtomicTy) : HOL.ClosedTerm Symbol type :=
  .const (.constant (.mk (Name.global name) .undefined) (reverseTy type) (toHOL_reverseTy type))

def raw : HOL.RawVectorConstructors.Signature AtomicTy Symbol where
  number := number
  element := .prop
  space := space
  zero := .app (constant "NUMERAL" (number ⇒ number)) (constant "_0" number)
  successor := constant "SUC" (number ⇒ number)
  bottom := constant "BOTTOM" space
  construct := constant "CONSTR" (number ⇒ HOL.FiniteConstructorEncoding.payloadType
    (HOL.RawVectorConstructors.fields number .prop) ⇒ (number ⇒ space) ⇒ space)
  selection := OpenVectorCompilation.selection (number ⇒ space)

def sourceBeta : HOL.ProofSyntax SourceConst (Γ := []) []
    (.eq (.app (.lam (.var .vz)) (.const NativeVectorComputationRows.EncodedConstructor.Controls.Const.zero)) (.const NativeVectorComputationRows.EncodedConstructor.Controls.Const.zero)) :=
  .beta (.const NativeVectorComputationRows.EncodedConstructor.Controls.Const.zero) (.var .vz)

def mappedBeta := (interpretation raw).proof sourceBeta

theorem beta_steps_preserved : mappedBeta.nodeCount = sourceBeta.nodeCount :=
  HOL.TermInterpretation.proof_nodeCount (interpretation raw) sourceBeta

theorem beta_free : mappedBeta.FunctionExtensionalityFree :=
  HOL.TermInterpretation.proof_free (interpretation raw) sourceBeta True.intro

def betaCompiled := InterpretedCompilation.compile (interpretation raw) sourceBeta True.intro Naming.empty ("compound-zero-beta", 0)

theorem beta_accepted : (ProofSystem.checker emptyAxiomPolicy).check betaCompiled.proof.result betaCompiled.proof.certificate = true :=
  InterpretedCompilation.accepted (interpretation raw) sourceBeta True.intro Naming.empty ("compound-zero-beta", 0)

theorem compound_zero_readback : (interpretation raw).term (Γ := []) (.const (NativeVectorComputationRows.EncodedConstructor.Controls.Const.zero)) =
    .app (constant "NUMERAL" (number ⇒ number)) (constant "_0" number) := rfl

def sourceEta : HOL.ProofSyntax SourceConst (Γ := []) []
    (.eq (.lam (.app (HOL.weaken (.const NativeVectorComputationRows.EncodedConstructor.Controls.Const.successor)) (.var .vz))) (.const NativeVectorComputationRows.EncodedConstructor.Controls.Const.successor)) :=
  .eta (.const NativeVectorComputationRows.EncodedConstructor.Controls.Const.successor)

theorem eta_not_free : ¬ ((interpretation raw).proof sourceEta).FunctionExtensionalityFree := by
  simp only [HOL.TermInterpretation.proof, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_substConst, HOL.ProofSyntax.functionExtensionalityFree_mapTypes,
    sourceEta, HOL.ProofSyntax.FunctionExtensionalityFree, not_false_eq_true]

def wrongClaim : Theorem := Theorem.emptyResult ∅
  (CanonicalTerm.free ⟨Name.global "wrong_compound_zero_claim", Ty.bool⟩)

theorem wrong_beta_refused : (ProofSystem.checker emptyAxiomPolicy).check wrongClaim betaCompiled.proof.certificate = false := by
  apply InterpretedCompilation.refuses_changed_conclusion
  decide +kernel

#print axioms beta_steps_preserved
#print axioms beta_free
#print axioms beta_accepted
#print axioms eta_not_free
#print axioms wrong_beta_refused
end Mettapedia.Languages.HOLLight.OpenVectorCompilation.Controls
