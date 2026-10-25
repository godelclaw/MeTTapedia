import Mettapedia.Languages.HOLLight.EqualityExpansion

/-!
# Constructive hypothesis management in HOL Light certificates

Assumption, deduction antisymmetry, premise discharge and addition of an
assumption are expanded into actual primitive request graphs. Their outputs
retain the complete axiom set and the exact finite hypothesis set. The two
premise occurrences remain separate references, even when their theorem
values agree. These blocks are data for the existing replay checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.HypothesisExpansion

open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.DerivationGraph
open GraphExpansion EqualityExpansion
open ProofExecution (Origin Receipt)

def assumption (term : CanonicalTerm) : Theorem :=
  Theorem.emptyResult {term} term

theorem assumption_checked (term : CanonicalTerm) (boolean : term.IsBool) :
    checkAssume term = some (assumption term) :=
  (checkAssume_eq_some_iff _ _).mpr ⟨boolean, rfl, rfl, rfl⟩

def assumptionBlock (term : CanonicalTerm) (origin : Origin) : ProofSystem.Certificate :=
  primitiveBlock (.inference (.assume term)) (assumption term) origin

theorem assumptionBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (term : CanonicalTerm) (boolean : term.IsBool) (origin : Origin) :
    BlockChecked policy [] (assumption term) (assumptionBlock term origin) :=
  primitiveBlock_checked (.inference (.assume term)) (assumption term) origin
    (assumption_checked term boolean)

def deductionResult (left right : Theorem)
    (sameType : left.sequent.concl.ty = right.sequent.concl.ty) : Theorem :=
  Theorem.unionResult left right
    (left.sequent.hyp.erase right.sequent.concl ∪ right.sequent.hyp.erase left.sequent.concl)
    (CanonicalTerm.equalityOfSameType left.sequent.concl right.sequent.concl sameType)

theorem deductionResult_checked (left right : Theorem)
    (sameType : left.sequent.concl.ty = right.sequent.concl.ty) :
    checkDeductAntisym left right = some (deductionResult left right sameType) :=
  (checkDeductAntisym_eq_some_iff _ _ _).mpr
    ⟨_, CanonicalTerm.equalityOfSameType_semantics _ _ sameType, rfl, rfl, rfl⟩

def deductionBlock (left right : Theorem)
    (sameType : left.sequent.concl.ty = right.sequent.concl.ty) (origin : Origin) :
    ProofSystem.Certificate :=
  primitiveBlock (.inference (.deductAntisym left right)) (deductionResult left right sameType) origin

theorem deductionBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (left right : Theorem) (sameType : left.sequent.concl.ty = right.sequent.concl.ty)
    (origin : Origin) :
    BlockChecked policy [left, right] (deductionResult left right sameType)
      (deductionBlock left right sameType origin) :=
  primitiveBlock_checked (.inference (.deductAntisym left right))
    (deductionResult left right sameType) origin (deductionResult_checked left right sameType)

/-- Abstract the same typed variable on both sides, preserving all provenance. -/
def abstractionResult (binder : SourceVar) (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) : Theorem :=
  Theorem.preserveAxiomsResult input input.sequent.hyp
    (CanonicalTerm.equalityOfSameType (left.abstractFree binder) (right.abstractFree binder)
      (congrArg (Ty.function binder.ty) sameType))

theorem abstractionResult_checked (binder : SourceVar) (input : Theorem)
    (left right : CanonicalTerm) (sameType : left.ty = right.ty)
    (view : CanonicalTerm.EqualityViewSemantics input.sequent.concl left right)
    (fresh : ¬ FreeInHypotheses binder input.sequent.hyp) :
    checkAbs binder input = some (abstractionResult binder input left right sameType) :=
  (checkAbs_eq_some_iff _ _ _).mpr ⟨fresh, left, right,
    left.abstractFree binder, right.abstractFree binder,
    CanonicalTerm.equalityOfSameType (left.abstractFree binder) (right.abstractFree binder)
      (congrArg (Ty.function binder.ty) sameType), view, rfl, rfl,
    CanonicalTerm.equalityOfSameType_semantics _ _
      (congrArg (Ty.function binder.ty) sameType), rfl, rfl, rfl⟩

def abstractionBlock (binder : SourceVar) (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) (origin : Origin) : ProofSystem.Certificate :=
  primitiveBlock (.inference (.abs binder input))
    (abstractionResult binder input left right sameType) origin

theorem abstractionBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (binder : SourceVar) (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty)
    (view : CanonicalTerm.EqualityViewSemantics input.sequent.concl left right)
    (fresh : ¬ FreeInHypotheses binder input.sequent.hyp) (origin : Origin) :
    BlockChecked policy [input] (abstractionResult binder input left right sameType)
      (abstractionBlock binder input left right sameType origin) :=
  primitiveBlock_checked (.inference (.abs binder input)) _ origin
    (abstractionResult_checked binder input left right sameType view fresh)

/-- Discharge the second input's use of the first input's conclusion. -/
def proveHypResult (proved input : Theorem) : Theorem :=
  Theorem.unionResult proved input
    (proved.sequent.hyp ∪ input.sequent.hyp.erase proved.sequent.concl) input.sequent.concl

theorem proveHypResult_checked (proved input : Theorem)
    (sameType : proved.sequent.concl.ty = input.sequent.concl.ty) :
    checkEqMp (deductionResult proved input sameType) proved = some (proveHypResult proved input) := by
  apply (checkEqMp_eq_some_iff _ _ _).mpr
  refine ⟨proved.sequent.concl, input.sequent.concl, equality_view _ _ sameType, rfl, ?_⟩
  refine ⟨?_, ?_, rfl⟩
  · simp only [proveHypResult, deductionResult, Theorem.unionResult]
    ext dependency
    simp only [Finset.mem_union]
    tauto
  · simp only [proveHypResult, deductionResult, Theorem.unionResult]
    ext hypothesis
    simp only [Finset.mem_union, Finset.mem_erase]
    tauto

/-- Two native inferences, with the original proof root used twice. -/
def proveHypBlock (proved input : Theorem)
    (sameType : proved.sequent.concl.ty = input.sequent.concl.ty) (origin : Origin) :
    ProofSystem.Certificate :=
  ([⟨deductionResult proved input sameType, .inference (.deductAntisym proved input), [0, 1], origin⟩,
    ⟨proveHypResult proved input, .inference (.eqMp (deductionResult proved input sameType) proved),
      [2, 0], origin⟩], 3)

theorem proveHypBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (proved input : Theorem) (sameType : proved.sequent.concl.ty = input.sequent.concl.ty)
    (origin : Origin) :
    BlockChecked policy [proved, input] (proveHypResult proved input)
      (proveHypBlock proved input sameType origin) := by
  let nodes := (proveHypBlock proved input sameType origin).1
  have nodeCount : nodes.length = 2 := rfl
  let first := #[proved, input]
  let middle := first.push (deductionResult proved input sameType)
  let final := middle.push (proveHypResult proved input)
  have head : nodes[0].replay (ruleWitness policy) first = some middle := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, deductionResult_checked proved input sameType, rfl⟩
  have tail : nodes[1].replay (ruleWitness policy) middle = some final := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, proveHypResult_checked proved input sameType, rfl⟩
  refine ⟨final, ?_, rfl⟩
  change replayFrom (ruleWitness policy) first [nodes[0], nodes[1]] = some final
  simp [replayFrom, head, tail]

def addAssumptionResult (term : CanonicalTerm) (input : Theorem) : Theorem :=
  Theorem.preserveAxiomsResult input (insert term input.sequent.hyp) input.sequent.concl

theorem proveHyp_assumption (term : CanonicalTerm) (input : Theorem) :
    proveHypResult (assumption term) input = addAssumptionResult term input := by
  apply HasParts.eq
  refine ⟨?_, ?_, rfl⟩
  · simp [proveHypResult, assumption, addAssumptionResult, Theorem.unionResult,
      Theorem.emptyResult, Theorem.preserveAxiomsResult]
  · simp only [proveHypResult, assumption, addAssumptionResult, Theorem.unionResult,
      Theorem.emptyResult, Theorem.preserveAxiomsResult]
    ext hypothesis
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_insert]
    tauto

/-- Addition of an assumption uses ASSUME followed by the two discharge
inferences. No weakening primitive is added to the kernel. -/
def addAssumptionBlock (term : CanonicalTerm) (input : Theorem)
    (sameType : term.ty = input.sequent.concl.ty) (origin : Origin) : ProofSystem.Certificate :=
  ([⟨assumption term, .inference (.assume term), [], origin⟩,
    ⟨deductionResult (assumption term) input sameType,
      .inference (.deductAntisym (assumption term) input), [1, 0], origin⟩,
    ⟨addAssumptionResult term input,
      .inference (.eqMp (deductionResult (assumption term) input sameType) (assumption term)),
      [2, 1], origin⟩], 3)

theorem addAssumptionBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (term : CanonicalTerm) (input : Theorem) (sameType : term.ty = input.sequent.concl.ty)
    (boolean : term.IsBool) (origin : Origin) :
    BlockChecked policy [input] (addAssumptionResult term input)
      (addAssumptionBlock term input sameType origin) := by
  let nodes := (addAssumptionBlock term input sameType origin).1
  have nodeCount : nodes.length = 3 := rfl
  let initial := #[input]
  let first := initial.push (assumption term)
  let middle := first.push (deductionResult (assumption term) input sameType)
  let final := middle.push (addAssumptionResult term input)
  have assumeStep : nodes[0].replay (ruleWitness policy) initial = some first := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, assumption_checked term boolean, rfl⟩
  have deductionStep : nodes[1].replay (ruleWitness policy) first = some middle := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, deductionResult_checked (assumption term) input sameType, rfl⟩
  have eliminationStep : nodes[2].replay (ruleWitness policy) middle = some final := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    refine ⟨rfl, ?_, rfl⟩
    change checkEqMp (deductionResult (assumption term) input sameType) (assumption term) =
      some (addAssumptionResult term input)
    rw [← proveHyp_assumption]
    exact proveHypResult_checked (assumption term) input sameType
  refine ⟨final, ?_, rfl⟩
  change replayFrom (ruleWitness policy) initial [nodes[0], nodes[1], nodes[2]] = some final
  simp [replayFrom, assumeStep, deductionStep, eliminationStep]

/-! ## Truth equality with exact hypotheses -/

def booleanIdentity : CanonicalTerm :=
  ⟨PrimitiveSentences.identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩

def truthTheorem : Theorem := Theorem.emptyResult ∅ DerivedRules.truthTerm

theorem truthTheorem_checked : checkRefl booleanIdentity = some truthTheorem :=
  reflexivity_checked booleanIdentity

def truthEqualityResult (input : Theorem) (boolean : input.sequent.concl.IsBool) : Theorem :=
  Theorem.preserveAxiomsResult input input.sequent.hyp
    (CanonicalTerm.equalityOfSameType input.sequent.concl DerivedRules.truthTerm boolean)

private def truthEqualityPrefix (input : Theorem) (boolean : input.sequent.concl.IsBool)
    (origin : Origin) : List Receipt :=
  [⟨truthTheorem, .inference (.refl booleanIdentity), [], origin⟩,
    ⟨deductionResult input truthTheorem boolean,
      .inference (.deductAntisym input truthTheorem), [0, 1], origin⟩]

private theorem truthEqualityPrefix_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (boolean : input.sequent.concl.IsBool) (origin : Origin) :
    replayFrom (ruleWitness policy) #[input] (truthEqualityPrefix input boolean origin) =
      some (#[input, truthTheorem].push (deductionResult input truthTheorem boolean)) := by
  let nodes := truthEqualityPrefix input boolean origin
  have nodeCount : nodes.length = 2 := rfl
  have first : nodes[0].replay (ruleWitness policy) #[input] = some #[input, truthTheorem] := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, truthTheorem_checked, rfl⟩
  have second : nodes[1].replay (ruleWitness policy) #[input, truthTheorem] =
      some (#[input, truthTheorem].push (deductionResult input truthTheorem boolean)) := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨rfl, deductionResult_checked input truthTheorem boolean, rfl⟩
  change replayFrom (ruleWitness policy) #[input] [nodes[0], nodes[1]] = _
  simp [replayFrom, first, second]

private theorem truthEquality_without_truth (input : Theorem) (boolean : input.sequent.concl.IsBool)
    (absent : DerivedRules.truthTerm ∉ input.sequent.hyp) :
    deductionResult input truthTheorem boolean = truthEqualityResult input boolean := by
  apply HasParts.eq
  simp [HasParts, deductionResult, truthTheorem, truthEqualityResult, Theorem.unionResult,
    Theorem.emptyResult, Theorem.preserveAxiomsResult, absent]

private theorem truthEquality_with_truth (input : Theorem) (boolean : input.sequent.concl.IsBool)
    (present : DerivedRules.truthTerm ∈ input.sequent.hyp) :
    addAssumptionResult DerivedRules.truthTerm (deductionResult input truthTheorem boolean) =
      truthEqualityResult input boolean := by
  apply HasParts.eq
  simp [HasParts, deductionResult, truthTheorem, truthEqualityResult, addAssumptionResult,
    Theorem.unionResult, Theorem.emptyResult, Theorem.preserveAxiomsResult,
    Finset.insert_erase present]

/-- EQT_INTRO retains the input's exact hypotheses. DEDUCT_ANTISYM can
remove a truth assumption; the computed branch restores it when necessary. -/
def truthEqualityBlock (input : Theorem) (boolean : input.sequent.concl.IsBool)
    (origin : Origin) : ProofSystem.Certificate :=
  if DerivedRules.truthTerm ∈ input.sequent.hyp then
    let continuation := expandBlock [2] 3
      (addAssumptionBlock DerivedRules.truthTerm
        (deductionResult input truthTheorem boolean) rfl origin)
    (truthEqualityPrefix input boolean origin ++ continuation.1, continuation.2)
  else
    (truthEqualityPrefix input boolean origin, 2)

set_option backward.isDefEq.respectTransparency false in
theorem truthEqualityBlock_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (boolean : input.sequent.concl.IsBool) (origin : Origin) :
    BlockChecked policy [input] (truthEqualityResult input boolean)
      (truthEqualityBlock input boolean origin) := by
  have initialReplay := truthEqualityPrefix_checked policy input boolean origin
  by_cases present : DerivedRules.truthTerm ∈ input.sequent.hyp
  · let middle := #[input, truthTheorem].push (deductionResult input truthTheorem boolean)
    have found : lookupPremises middle [2] = some [deductionResult input truthTheorem boolean] := rfl
    have block := addAssumptionBlock_checked policy DerivedRules.truthTerm
      (deductionResult input truthTheorem boolean) rfl rfl origin
    obtain ⟨final, replayed, root⟩ := expandBlock_checked found block
    have size : middle.size = 3 := rfl
    rw [size] at replayed root
    refine ⟨final, ?_, ?_⟩
    · simpa only [truthEqualityBlock, if_pos present] using
        replayFrom_append (ruleWitness policy) initialReplay replayed
    · simpa only [truthEqualityBlock, if_pos present, truthEquality_with_truth input boolean present]
        using root
  · refine ⟨#[input, truthTheorem].push (deductionResult input truthTheorem boolean), ?_, ?_⟩
    · simpa only [truthEqualityBlock, if_neg present] using initialReplay
    · simp only [truthEqualityBlock, if_neg present]
      change some (deductionResult input truthTheorem boolean) =
        some (truthEqualityResult input boolean)
      exact congrArg some (truthEquality_without_truth input boolean present)

end Mettapedia.Languages.HOLLight.HypothesisExpansion
