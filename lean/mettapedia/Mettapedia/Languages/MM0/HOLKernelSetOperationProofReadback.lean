import Mettapedia.Languages.MM0.HOLKernelProofReadback
import Mettapedia.Languages.MM0.HOLKernelLogicalFunctionReadback
import Mettapedia.Languages.MM0.HOLKernelSetOperationSequentReadback
import Mettapedia.Languages.MM0.HOLKernelSetOperationInterpretation

/-!
# Source derivations reconstructed from the maintained material HOL profile

The decoder first reconstructs the logical reading of a checked native proof
tree. It independently reads the native conclusion as an exact source
sequent, constructs its explicit antecedent from the source assumptions, and
applies the reconstructed implication. The result is ordinary HOL proof
syntax at the original ordered assumptions and conclusion.

The proof-tree decoder admits licensed binding and nonbinding rules and
conversions that preserve its source reading. Source typing is reconstructed
separately. Its independent admission grammar implies total constructive
readback at the exact source sequent. Forward compilation and this admitted
reflection concern explicitly distinguished certificate classes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadback

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelProofReadback
open Embedding.ZFSetHenkinInterpretation (Symbol)

universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable [∀ type, DecidableEq (Const type)]

/-- Finite occurrence lookup, rather than proof search or a membership
choice. The requested ordered context remains unchanged. -/
def hypothesisProof (formula : Formula Const gamma) :
    (assumptions : List (Formula Const gamma)) → Option (ProofSyntax Const assumptions formula)
  | [] => none
  | first :: rest =>
      if same : first = formula then some (same ▸ ProofSyntax.hyp 0)
      else (hypothesisProof formula rest).map (ProofSyntax.prepend first)

def contextProof (assumptions : List (Formula Const gamma)) :
    (judgment : Judgment Const gamma) → Option (ProofSyntax Const assumptions judgment.formula)
  | .typing _ => some .topI
  | .assertion formula =>
      if same : formula = .top then some (same.symm ▸ ProofSyntax.topI)
      else hypothesisProof formula assumptions
  | .conjunction first second => do
      pure (.andI (← contextProof assumptions first) (← contextProof assumptions second))
  | .consequence _ _ => none

variable {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

structure SourceProofReadback
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context) (witness : ProofWitness) where
  sequent : HOLKernelSetOperationReadback.SourceSequent
  native : Preterm
  accepted : witness.proof? terms definitions theorems context [] = some native
  statement : HOLKernelSetOperationInterpretation.statement references sequent.1 sequent.2 = native
  proof : ProofSyntax Symbol sequent.1 sequent.2

def readSourceProof {sorts : SortSignature} (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (theorems : TheoremSignature)
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (context : Context)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (fuel : Nat) (witness : ProofWitness) :
    Option (SourceProofReadback abbreviation theorems context witness) := do
  let reader : TermReader Symbol :=
    HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7
  let reconstructed ← readProof abbreviation theorems context
    reader 7 NamedElaboration.BinderNames.nil ruleAt bindingAt fuel witness
  match sequentRead : HOLKernelSetOperationReadback.readSequent signature.symbol reconstructed.native with
  | none => none
  | some sequent => do
      let .app (.app (.term _) antecedent) _ := reconstructed.native | none
      let contextReading ← readJudgmentWith reader signature.symbol
        NamedElaboration.BinderNames.nil (expandEquivalence signature.symbol abbreviation.reference antecedent)
      let antecedentProof ← contextProof sequent.1 contextReading
      if same : reconstructed.source.formula = .imp contextReading.formula sequent.2 then
        let implication : ProofSyntax Symbol [] (.imp contextReading.formula sequent.2) :=
          same ▸ reconstructed.source.proof
        pure ⟨sequent, reconstructed.native, reconstructed.accepted,
          HOLKernelSetOperationReadback.readSequent_sound signature.symbol reconstructed.native sequent sequentRead,
          .impE (ProofSyntax.mono (ProofSyntax.emptyOccurrenceMap sequent.1) implication) antecedentProof⟩
      else none

omit [∀ type, DecidableEq (Const type)] in
theorem SourceProofReadback.native_checked
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {context : Context} {witness : ProofWitness}
    (reconstructed : SourceProofReadback abbreviation theorems context witness) :
    witness.check terms definitions theorems context []
      (HOLKernelSetOperationInterpretation.statement references reconstructed.sequent.1 reconstructed.sequent.2) =
      true := by
  rw [reconstructed.statement]
  exact (ProofWitness.check_iff _ _ _ _ _ _ _).mpr
    (ProofWitness.proof_sound reconstructed.accepted)

omit [∀ type, DecidableEq (Const type)] in
theorem SourceProofReadback.source_derivation
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {context : Context} {witness : ProofWitness}
    (reconstructed : SourceProofReadback abbreviation theorems context witness) :
    ExtDerivation Symbol reconstructed.sequent.1 reconstructed.sequent.2 := reconstructed.proof.erase

theorem hypothesisProof_of_mem {formula : Formula Const gamma}
    {assumptions : List (Formula Const gamma)} (mem : formula ∈ assumptions) :
    ∃ proof, hypothesisProof formula assumptions = some proof := by
  induction assumptions with
  | nil => cases mem
  | cons first rest ih =>
      unfold hypothesisProof
      split
      · exact ⟨_, rfl⟩
      next hne =>
        cases List.mem_cons.mp mem with
        | inl h => exact False.elim (hne h.symm)
        | inr hrest =>
            obtain ⟨proof, hproof⟩ := ih hrest
            simp only [hproof, Option.map_some]
            exact ⟨_, rfl⟩

/-- Proof-free admission of a decoded native antecedent judgment against
ordered source assumptions. -/
inductive AdmittedContext (assumptions : List (Formula Const gamma)) :
    Judgment Const gamma → Prop where
  | typing {type : Ty Unit} (term : Term Const gamma type) :
      AdmittedContext assumptions (.typing term)
  | top :
      AdmittedContext assumptions (.assertion .top)
  | assumption {formula : Formula Const gamma} (mem : formula ∈ assumptions) :
      AdmittedContext assumptions (.assertion formula)
  | conjunction {first second : Judgment Const gamma}
      (firstAdmitted : AdmittedContext assumptions first)
      (secondAdmitted : AdmittedContext assumptions second) :
      AdmittedContext assumptions (.conjunction first second)

theorem contextProof_of_admitted {assumptions : List (Formula Const gamma)}
    {judgment : Judgment Const gamma}
    (admitted : AdmittedContext assumptions judgment) :
    ∃ proof, contextProof assumptions judgment = some proof := by
  induction admitted with
  | typing _ =>
      exact ⟨.topI, rfl⟩
  | top =>
      unfold contextProof
      simp only [↓reduceDIte]
      exact ⟨_, rfl⟩
  | @assumption formula mem =>
      unfold contextProof
      by_cases same : formula = .top
      · simp only [same, ↓reduceDIte]
        exact ⟨_, rfl⟩
      · simp only [same, ↓reduceDIte]
        exact hypothesisProof_of_mem mem
  | conjunction _ _ ih1 ih2 =>
      obtain ⟨p1, hp1⟩ := ih1
      obtain ⟨p2, hp2⟩ := ih2
      unfold contextProof
      simp only [hp1, hp2, Option.bind_eq_bind, Option.bind_some]
      exact ⟨_, rfl⟩

/-- Proof-free admission of a native MM0 proof certificate for a closed
set-operation sequent. -/
structure AdmittedSourceProof {sorts : SortSignature} (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (theorems : TheoremSignature)
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (context : Context)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (fuel : Nat) (witness : ProofWitness)
    (sequent : HOLKernelSetOperationReadback.SourceSequent) where
  contextReading : Judgment Symbol []
  antecedent_read :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol NamedElaboration.BinderNames.nil
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelAssumptions.antecedent signature.symbol
          (HOLKernelSetOperationInterpretation.formation signature.symbol)
          (sequent.1.map (fun source =>
            HOLKernelJudgment.holds signature.symbol
              (HOLKernelSetOperationInterpretation.term signature.symbol source))))) =
      some contextReading
  context_admitted : AdmittedContext sequent.1 contextReading
  native_accepted :
    witness.proof? terms definitions theorems context [] =
      some (HOLKernelSetOperationInterpretation.statement signature.symbol sequent.1 sequent.2)
  proof_admitted :
    AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel NamedElaboration.BinderNames.nil witness
      (.imp contextReading.formula sequent.2)

omit [∀ type, DecidableEq (Const type)] in
theorem readSourceProof_of_admitted {sorts : SortSignature} (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (theorems : TheoremSignature)
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (context : Context)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (fuel : Nat) (witness : ProofWitness)
    (sequent : HOLKernelSetOperationReadback.SourceSequent)
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent) :
    ∃ out : SourceProofReadback abbreviation theorems context witness,
      readSourceProof signature abbreviation theorems logical context ruleAt bindingAt fuel witness = some out ∧
      out.sequent = sequent := by
  obtain ⟨reconstructed, hproof, hform⟩ := readProof_of_admitted admitted.proof_admitted
  have sameNative : reconstructed.native =
      HOLKernelSetOperationInterpretation.statement signature.symbol sequent.1 sequent.2 :=
    Option.some.inj (reconstructed.accepted.symm.trans admitted.native_accepted)
  have hseq : HOLKernelSetOperationReadback.readSequent signature.symbol reconstructed.native = some sequent := by
    rw [sameNative]
    exact HOLKernelSetOperationReadback.readSequent_statement
      signature.symbol signature.symbol_injective sequent.1 sequent.2
  obtain ⟨antecedentProof, hctx⟩ := contextProof_of_admitted admitted.context_admitted
  unfold readSourceProof
  simp only [hproof, Option.bind_eq_bind, Option.bind_some]
  split
  next refused =>
    rw [hseq] at refused
    contradiction
  next decoded hdecoded =>
    have sameSeq : decoded = sequent := Option.some.inj (hdecoded.symm.trans hseq)
    subst sameSeq
    have hshape : reconstructed.native =
        .app (.app (.term (signature.symbol .im))
          (HOLKernelAssumptions.antecedent signature.symbol
            (HOLKernelSetOperationInterpretation.formation signature.symbol)
            (decoded.1.map (fun source =>
              HOLKernelJudgment.holds signature.symbol
                (HOLKernelSetOperationInterpretation.term signature.symbol source)))))
          (HOLKernelJudgment.holds signature.symbol
            (HOLKernelSetOperationInterpretation.term signature.symbol decoded.2)) :=
      sameNative
    simp only [hshape, admitted.antecedent_read, Option.bind_some,
      hctx, hform, ↓reduceDIte]
    exact ⟨_, rfl, rfl⟩

omit [∀ type, DecidableEq (Const type)] in
theorem admitted_source_derivation {sorts : SortSignature} (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (theorems : TheoremSignature)
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (context : Context)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (fuel : Nat) (witness : ProofWitness)
    (assumptions : List (ClosedFormula Symbol)) (conclusion : ClosedFormula Symbol)
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness (assumptions, conclusion)) :
    ExtDerivation Symbol assumptions conclusion := by
  obtain ⟨out, _, hseq⟩ :=
    readSourceProof_of_admitted signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness (assumptions, conclusion) admitted
  have derived := out.source_derivation
  rw [hseq] at derived
  exact derived

omit [∀ type, DecidableEq (Const type)] in
/-- Totalize the executable reader on its independently admitted domain.
The returned proof is computed by `readSourceProof`, rather than supplied
by the admission evidence. -/
def AdmittedSourceProof.readback {sorts : SortSignature} {signature : Signature sorts terms}
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
    {logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
    {context : Context} {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {fuel : Nat} {witness : ProofWitness} {sequent : HOLKernelSetOperationReadback.SourceSequent}
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent) :
    SourceProofReadback abbreviation theorems context witness :=
  (readSourceProof signature abbreviation theorems logical context ruleAt bindingAt fuel witness).get (by
    obtain ⟨out, accepted, _⟩ := readSourceProof_of_admitted signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent admitted
    rw [accepted]
    rfl)

omit [∀ type, DecidableEq (Const type)] in
theorem AdmittedSourceProof.readback_read {sorts : SortSignature} {signature : Signature sorts terms}
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
    {logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
    {context : Context} {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {fuel : Nat} {witness : ProofWitness} {sequent : HOLKernelSetOperationReadback.SourceSequent}
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent) :
    readSourceProof signature abbreviation theorems logical context ruleAt bindingAt fuel witness =
      some admitted.readback := by
  exact (Option.some_get _).symm

omit [∀ type, DecidableEq (Const type)] in
theorem AdmittedSourceProof.readback_sequent {sorts : SortSignature} {signature : Signature sorts terms}
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
    {logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
    {context : Context} {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {fuel : Nat} {witness : ProofWitness} {sequent : HOLKernelSetOperationReadback.SourceSequent}
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent) :
    admitted.readback.sequent = sequent := by
  obtain ⟨out, accepted, sameSequent⟩ := readSourceProof_of_admitted signature abbreviation theorems logical context
    ruleAt bindingAt fuel witness sequent admitted
  have same : admitted.readback = out := Option.some.inj (admitted.readback_read.symm.trans accepted)
  rw [same]
  exact sameSequent

omit [∀ type, DecidableEq (Const type)] in
/-- The computed HOL proof at the submitted sequent, including its ordered
assumption occurrences. -/
def AdmittedSourceProof.sourceProof {sorts : SortSignature} {signature : Signature sorts terms}
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
    {logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
    {context : Context} {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {fuel : Nat} {witness : ProofWitness} {sequent : HOLKernelSetOperationReadback.SourceSequent}
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent) :
    ProofSyntax Symbol sequent.1 sequent.2 :=
  admitted.readback_sequent ▸ admitted.readback.proof

omit [∀ type, DecidableEq (Const type)] in
theorem compilation_and_admitted_reflection {sorts : SortSignature} (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (assumptions : List (ClosedFormula Symbol)) (conclusion : ClosedFormula Symbol) :
    (ExtDerivation Symbol assumptions conclusion →
      ∃ (context : Context) (witness : ProofWitness),
        witness.check terms definitions theorems context []
          (HOLKernelSetOperationInterpretation.statement signature.symbol assumptions conclusion) = true) ∧
    ((∃ (context : Context) (fuel : Nat) (witness : ProofWitness),
        Nonempty (AdmittedSourceProof signature abbreviation theorems profile context
          ruleAt bindingAt fuel witness (assumptions, conclusion))) →
      ExtDerivation Symbol assumptions conclusion) := by
  constructor
  · intro derivation
    obtain ⟨source⟩ := ProofSyntax.nonempty_of_derivation derivation
    refine ⟨_, (HOLKernelSetOperationInterpretation.compile
      signature abbreviation profile structural typing rules binding source).val,
      HOLKernelSetOperationInterpretation.compile_accepted
        signature abbreviation profile structural typing rules binding source⟩
  · rintro ⟨context, fuel, witness, ⟨admitted⟩⟩
    exact admitted_source_derivation signature abbreviation theorems profile context
      ruleAt bindingAt fuel witness assumptions conclusion admitted

#print axioms readSourceProof
#print axioms SourceProofReadback.native_checked
#print axioms SourceProofReadback.source_derivation
#print axioms readSourceProof_of_admitted
#print axioms admitted_source_derivation
#print axioms AdmittedSourceProof.readback
#print axioms AdmittedSourceProof.readback_read
#print axioms AdmittedSourceProof.readback_sequent
#print axioms AdmittedSourceProof.sourceProof
#print axioms compilation_and_admitted_reflection

end Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadback
