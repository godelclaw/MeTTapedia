import Mettapedia.Languages.HOLLight.ImplicationIntroduction
import Mettapedia.Languages.HOLLight.ExtensionalityExpansion
import Mettapedia.Languages.OpenTheory.EtaCompletenessRules
import Mettapedia.Logic.HOL.ImpredicativeProofTranslation

/-!
# Constructive assembly of retained HOL proofs into native certificates

The compiler assembles existing primitive graph blocks through the original
HOL Light replay. Source hypotheses are ordered occurrences; target theorem
hypotheses are finite sets. The explicit hypothesis-padding construction
retains exactly the target set while making no claim of proof-identity or
occurrence-multiplicity reflection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RetainedCompilation

open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic
open GraphExpansion EqualityExpansion HypothesisExpansion PrimitiveTransport
open ReverseTranslation
open ProofExecution (Origin)

/-- A constructed theorem and its actual closed native proof graph. -/
structure CheckedProof (policy : AxiomPolicy) [DecidablePred policy] where
  result : Theorem
  certificate : ProofSystem.Certificate
  accepted : (ProofSystem.checker policy).check result certificate = true

namespace CheckedProof

variable {policy : AxiomPolicy} [DecidablePred policy]

theorem blockChecked (proof : CheckedProof policy) :
    BlockChecked policy [] proof.result proof.certificate :=
  (ProofSystem.checker_check_iff policy _ _).mp proof.accepted

def ofBlock (result : Theorem) (certificate : ProofSystem.Certificate)
    (checked : BlockChecked policy [] result certificate) : CheckedProof policy :=
  ⟨result, certificate, (ProofSystem.checker_check_iff policy _ _).mpr checked⟩

/-- Select the result of a proved-total computation. The proof certifies
availability; the certificate itself is returned by the executable Option. -/
def ofOption (result : Theorem) (candidate : Option ProofSystem.Certificate)
    (available : ∃ certificate, candidate = some certificate ∧ BlockChecked policy [] result certificate) :
    CheckedProof policy := by
  have present : candidate.isSome := by
    obtain ⟨certificate, computed, _⟩ := available
    exact Option.isSome_iff_exists.mpr ⟨certificate, computed⟩
  refine ⟨result, candidate.get present, ?_⟩
  obtain ⟨certificate, computed, checked⟩ := available
  have same : candidate.get present = certificate :=
    Option.some.inj ((Option.some_get present).trans computed)
  rw [same]
  exact (ProofSystem.checker_check_iff policy _ _).mpr checked

/-- Assemble blocks whose local checks are already proved. The executable
path performs address relocation and root selection; the existing checked-plan
theorem supplies validity without replaying every child graph at each join. -/
def assemble (requests : List BlockRequest) (index : Nat) (result : Theorem)
    (localChecks : LocallyChecked policy #[] requests)
    (selected : (requests.map (·.conclusion))[index]? = some result) : CheckedProof policy :=
  ofOption result
    (do let (nodes,roots) ← expandFrom [] #[] requests
        let root ← roots[index]?
        pure (nodes,root)) (by
      obtain ⟨block,computed,checked⟩ :=
        finishPlan_checked (outputs := #[]) (roots := #[]) (start_checked policy []) rfl
          localChecks (index := index) (conclusion := result) (by simpa using selected)
      exact ⟨block,finishPlan_expanded (start_checked policy []) computed,checked⟩)

/-- Certified structural assembly returns exactly the certificate returned
by the replaying builder, including receipt order, origins and multiplicity. -/
theorem assemble_matches_replayed_plan (requests : List BlockRequest) (index : Nat) (result : Theorem)
    (localChecks : LocallyChecked policy #[] requests)
    (selected : (requests.map (·.conclusion))[index]? = some result) :
    finishPlan policy (start []) #[] requests index =
      some (assemble requests index result localChecks selected).certificate := by
  obtain ⟨block,computed,checked⟩ :=
    finishPlan_checked (outputs := #[]) (roots := #[]) (start_checked policy []) rfl
      localChecks (index := index) (conclusion := result) (by simpa using selected)
  have expanded := finishPlan_expanded (start_checked policy []) computed
  have same : (assemble requests index result localChecks selected).certificate = block := by
    change (Option.get _ _) = block
    exact Option.some.inj ((Option.some_get _).trans expanded)
  rw [same]
  exact computed

/-- One child is shared as a root of the assembled primitive graph. -/
def unary (input : CheckedProof policy) (result : Theorem)
    (block : ProofSystem.Certificate) (checked : BlockChecked policy [input.result] result block)
    (origin : Origin) : CheckedProof policy := by
  let requests : List BlockRequest :=
    [⟨input.result, input.certificate, [], origin⟩, ⟨result, block, [0], origin⟩]
  have localChecks : LocallyChecked policy #[] requests := by
    apply LocallyChecked.cons (premises := []) rfl input.blockChecked
    apply LocallyChecked.cons (premises := [input.result]) rfl checked
    exact .nil _
  exact assemble requests 1 result localChecks rfl

/-- Two child graphs retain their separate occurrences and ordered uses. -/
def binary (left right : CheckedProof policy) (result : Theorem)
    (block : ProofSystem.Certificate) (checked : BlockChecked policy [left.result, right.result] result block)
    (origin : Origin) : CheckedProof policy := by
  let requests : List BlockRequest :=
    [⟨left.result, left.certificate, [], origin⟩, ⟨right.result, right.certificate, [], origin⟩,
     ⟨result, block, [0, 1], origin⟩]
  have localChecks : LocallyChecked policy #[] requests := by
    apply LocallyChecked.cons (premises := []) rfl left.blockChecked
    apply LocallyChecked.cons (premises := []) rfl right.blockChecked
    apply LocallyChecked.cons (premises := [left.result, right.result]) rfl checked
    exact .nil _
  exact assemble requests 2 result localChecks rfl

/-- A local macro's computed certificate is selected before graph composition. -/
def unaryOption (input : CheckedProof policy) (result : Theorem)
    (candidate : Option ProofSystem.Certificate)
    (available : ∃ block, candidate = some block ∧ BlockChecked policy [input.result] result block)
    (origin : Origin) : CheckedProof policy := by
  have present : candidate.isSome := by
    obtain ⟨block, computed, _⟩ := available
    exact Option.isSome_iff_exists.mpr ⟨block, computed⟩
  have checked : BlockChecked policy [input.result] result (candidate.get present) := by
    obtain ⟨block, computed, checked⟩ := available
    have same : candidate.get present = block := Option.some.inj ((Option.some_get present).trans computed)
    exact same.symm ▸ checked
  exact unary input result (candidate.get present) checked origin


def binaryOption (left right : CheckedProof policy) (result : Theorem)
    (candidate : Option ProofSystem.Certificate)
    (available : ∃ block, candidate = some block ∧ BlockChecked policy [left.result, right.result] result block)
    (origin : Origin) : CheckedProof policy := by
  have present : candidate.isSome := by
    obtain ⟨block, computed, _⟩ := available
    exact Option.isSome_iff_exists.mpr ⟨block, computed⟩
  have checked : BlockChecked policy [left.result, right.result] result (candidate.get present) := by
    obtain ⟨block, computed, checked⟩ := available
    have same : candidate.get present = block := Option.some.inj ((Option.some_get present).trans computed)
    exact same.symm ▸ checked
  exact binary left right result (candidate.get present) checked origin

/-- Add the listed hypotheses through actual ASSUME/DEDUCT_ANTISYM/EQ_MP
requests, leaving the supplied theorem's conclusion and dependencies intact. -/
def pad (input : CheckedProof policy) (boolean : input.result.sequent.concl.IsBool)
    (hypotheses : List CanonicalTerm) (formed : ∀ term ∈ hypotheses, term.IsBool)
    (origin : Origin) : CheckedProof policy :=
  match hypotheses with
  | [] => input
  | term :: rest =>
      let termBool := formed term List.mem_cons_self
      let next := unary input (addAssumptionResult term input.result)
        (addAssumptionBlock term input.result (termBool.trans boolean.symm) origin)
        (addAssumptionBlock_checked policy term input.result (termBool.trans boolean.symm) termBool origin) origin
      pad next boolean rest (fun term member => formed term (List.mem_cons_of_mem _ member)) origin

set_option backward.isDefEq.respectTransparency false in
theorem pad_parts (input : CheckedProof policy) (boolean : input.result.sequent.concl.IsBool)
    (hypotheses : List CanonicalTerm) (formed : ∀ term ∈ hypotheses, term.IsBool) (origin : Origin) :
    (pad input boolean hypotheses formed origin).result.axioms = input.result.axioms ∧
      (pad input boolean hypotheses formed origin).result.sequent.hyp = hypotheses.toFinset ∪ input.result.sequent.hyp ∧
      (pad input boolean hypotheses formed origin).result.sequent.concl = input.result.sequent.concl := by
  induction hypotheses generalizing input with
  | nil => simp [pad]
  | cons term rest ih =>
      let termBool := formed term List.mem_cons_self
      let next := unary input (addAssumptionResult term input.result)
        (addAssumptionBlock term input.result (termBool.trans boolean.symm) origin)
        (addAssumptionBlock_checked policy term input.result (termBool.trans boolean.symm) termBool origin) origin
      have parts := ih next boolean (fun term member => formed term (List.mem_cons_of_mem _ member))
      refine ⟨parts.1, parts.2.1.trans ?_, parts.2.2⟩
      change rest.toFinset ∪ insert term input.result.sequent.hyp =
        (term :: rest).toFinset ∪ input.result.sequent.hyp
      ext hypothesis
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto

/-- One physical certificate has one exact selected theorem, including its
assumptions and axiom dependencies. -/
theorem checked_claim_eq (proof : CheckedProof policy) (claim : Theorem)
    (accepted : (ProofSystem.checker policy).check claim proof.certificate = true) :
    claim = proof.result := by
  obtain ⟨first, replayFirst, foundFirst⟩ :=
    (ProofSystem.checker_check_iff policy _ _).mp proof.accepted
  obtain ⟨second, replaySecond, foundSecond⟩ :=
    (ProofSystem.checker_check_iff policy _ _).mp accepted
  have sameCache := Option.some.inj (replayFirst.symm.trans replaySecond)
  subst second
  exact Option.some.inj (foundSecond.symm.trans foundFirst)

/-- Changing the conclusion cannot reuse the same accepted certificate. -/
theorem refuses_changed_conclusion (proof : CheckedProof policy) (claim : Theorem)
    (different : claim.sequent.concl ≠ proof.result.sequent.concl) :
    (ProofSystem.checker policy).check claim proof.certificate = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact different (congrArg (fun value : Theorem => value.sequent.concl)
    (proof.checked_claim_eq claim accepted))

end CheckedProof

/-- Exact conclusion and hypothesis-set indices for one source naming. -/
structure Compiled (policy : AxiomPolicy) [DecidablePred policy]
    {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    (hypotheses : List (HOL.Formula Symbol Γ)) (conclusion : HOL.Formula Symbol Γ) where
  proof : CheckedProof policy
  hypotheses_exact : proof.result.sequent.hyp = reverseHypotheses names hypotheses
  conclusion_exact : proof.result.sequent.concl = reverseCanonical names conclusion

/-- Complete a subset of the requested assumptions without changing the
actual computed conclusion. -/
def align {policy : AxiomPolicy} [DecidablePred policy]
    {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) (hypotheses : List (HOL.Formula Symbol Γ))
    (conclusion : HOL.Formula Symbol Γ) (proof : CheckedProof policy)
    (exactConclusion : proof.result.sequent.concl = reverseCanonical names conclusion)
    (contained : proof.result.sequent.hyp ⊆ reverseHypotheses names hypotheses) (origin : Origin) :
    Compiled policy names hypotheses conclusion := by
  let terms := hypotheses.map (reverseCanonical names)
  have formed : ∀ term ∈ terms, term.IsBool := by
    intro term member
    obtain ⟨formula, _, rfl⟩ := List.mem_map.mp member
    exact reverseCanonical_isBool names formula
  have boolean : proof.result.sequent.concl.IsBool := exactConclusion ▸ reverseCanonical_isBool names conclusion
  let padded := CheckedProof.pad proof boolean terms formed origin
  have parts := CheckedProof.pad_parts proof boolean terms formed origin
  exact ⟨padded, parts.2.1.trans (Finset.union_eq_left.mpr contained), parts.2.2.trans exactConclusion⟩



private theorem freeNames_toFinset (term : DBTerm) :
    (PrimitiveTransport.freeNames term).toFinset = term.freeNames := by
  induction term <;> simp_all [PrimitiveTransport.freeNames, DBTerm.freeNames]

private def freshTermName (terms : List CanonicalTerm) : Name :=
  freshName (terms.flatMap (fun term => PrimitiveTransport.freeNames term.term))

private theorem freshTermName_absent (terms : List CanonicalTerm) (type : Ty)
    (term : CanonicalTerm) (member : term ∈ terms) :
    ¬ DBTerm.FreeOccurrence ⟨freshTermName terms, type⟩ term.term := by
  intro occurs
  have listed := DBTerm.name_mem_freeNames occurs
  rw [← freeNames_toFinset] at listed
  exact freshName_not_mem _ (List.mem_flatMap.mpr ⟨term, member, List.mem_toFinset.mp listed⟩)

private theorem reverseBinder_checked {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {σ τ : HOL.Ty AtomicTy} (body : HOL.Term Symbol (σ :: Γ) τ) :
    (reverseTermWith (VarEnv.lift (Naming.env names)) body).inferType [reverseTy σ] = some (reverseTy τ) := by
  have typed := inferType_reverseTerm names [] (.lam body)
  obtain ⟨actual, typedBody, same⟩ := DBTerm.inferType_abs_eq_some_iff.mp typed
  have equal := (Ty.function_inj same).2
  exact equal ▸ typedBody

namespace Compiled

variable {policy : AxiomPolicy} [DecidablePred policy]
variable {Γ : HOL.Ctx AtomicTy} {names : Naming Γ}
variable {Δ : List (HOL.Formula Symbol Γ)}

theorem boolean {φ : HOL.Formula Symbol Γ} (proof : Compiled policy names Δ φ) :
    proof.proof.result.sequent.concl.IsBool := by
  rw [proof.conclusion_exact]
  exact reverseCanonical_isBool names φ

theorem equalityView {τ : HOL.Ty AtomicTy} {left right : HOL.Term Symbol Γ τ}
    (proof : Compiled policy names Δ (.eq left right)) :
    CanonicalTerm.EqualityViewSemantics proof.proof.result.sequent.concl
      (reverseCanonical names left) (reverseCanonical names right) := by
  rw [proof.conclusion_exact]
  exact ⟨rfl, rfl⟩

/-- A source occurrence selects its actual formula; the target stores its
finite-set assumption. The source occurrence index is not recovered from it. -/
def hypothesis (occurrence : Fin Δ.length) (origin : Origin) :
    Compiled policy names Δ (Δ.get occurrence) :=
  align names Δ _
    (CheckedProof.ofBlock (assumption (reverseCanonical names (Δ.get occurrence)))
      (assumptionBlock (reverseCanonical names (Δ.get occurrence)) origin)
      (assumptionBlock_checked policy _ (reverseCanonical_isBool names _) origin))
    rfl (Finset.singleton_subset_iff.mpr
      (reverseCanonical_mem_reverseHypotheses names (List.get_mem _ occurrence))) origin

def reflexive {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) (origin : Origin) :
    Compiled policy names Δ (.eq term term) :=
  align names Δ _
    (CheckedProof.ofBlock (reflexivity (reverseCanonical names term))
      (primitiveBlock (.inference (.refl (reverseCanonical names term)))
        (reflexivity (reverseCanonical names term)) origin)
      (primitiveBlock_checked (.inference (.refl (reverseCanonical names term))) _ origin
        (reflexivity_checked (reverseCanonical names term))))
    rfl (Finset.empty_subset _) origin

def symmetric {τ : HOL.Ty AtomicTy} {left right : HOL.Term Symbol Γ τ}
    (proof : Compiled policy names Δ (.eq left right)) (origin : Origin) :
    Compiled policy names Δ (.eq right left) :=
  align names Δ _
    (CheckedProof.unary proof.proof
      (symmetryResult proof.proof.result (reverseCanonical names left) (reverseCanonical names right) rfl)
      (symmetryBlock proof.proof.result (reverseCanonical names left) (reverseCanonical names right) rfl origin)
      (symmetryBlock_checked policy proof.proof.result (reverseCanonical names left)
        (reverseCanonical names right) rfl proof.equalityView origin) origin)
    rfl (by
      change proof.proof.result.sequent.hyp ⊆ reverseHypotheses names Δ
      simp only [proof.hypotheses_exact, Finset.Subset.refl]) origin

def transitive {τ : HOL.Ty AtomicTy} {left middle right : HOL.Term Symbol Γ τ}
    (first : Compiled policy names Δ (.eq left middle))
    (second : Compiled policy names Δ (.eq middle right)) (origin : Origin) :
    Compiled policy names Δ (.eq left right) := by
  let result := transResult first.proof.result second.proof.result
    (reverseCanonical names left) (reverseCanonical names right) rfl
  have checked : checkTrans first.proof.result second.proof.result = some result :=
    transResult_checked _ _ (reverseCanonical names left) (reverseCanonical names middle)
      (reverseCanonical names right) rfl first.equalityView second.equalityView
  exact align names Δ _
    (CheckedProof.binary first.proof second.proof result
      (primitiveBlock (.inference (.trans first.proof.result second.proof.result)) result origin)
      (primitiveBlock_checked (.inference (.trans first.proof.result second.proof.result)) result origin checked) origin)
    rfl (by
      change first.proof.result.sequent.hyp ∪ second.proof.result.sequent.hyp ⊆ reverseHypotheses names Δ
      simp [first.hypotheses_exact, second.hypotheses_exact]) origin

def modusPonens {premise conclusion : HOL.Formula Symbol Γ}
    (function : Compiled policy names Δ (.imp premise conclusion))
    (argument : Compiled policy names Δ premise) (origin : Origin) :
    Compiled policy names Δ conclusion := by
  let p := reverseCanonical names premise
  let q := reverseCanonical names conclusion
  have shape : function.proof.result.sequent.concl.term = ExcludedMiddle.impAppDB p.term q.term := by
    rw [function.conclusion_exact]
    rfl
  let result := ImplicationExpansion.mpResult function.proof.result argument.proof.result q
  let compiled := CheckedProof.binaryOption function.proof argument.proof result
    (ImplicationExpansion.mpTypedBlock? policy function.proof.result argument.proof.result p q
      (reverseCanonical_isBool names premise) (reverseCanonical_isBool names conclusion)
      shape argument.conclusion_exact origin)
    (ImplicationExpansion.mpTypedBlock?_checked policy function.proof.result argument.proof.result p q
      (reverseCanonical_isBool names premise) (reverseCanonical_isBool names conclusion)
      shape argument.conclusion_exact origin) origin
  exact align names Δ conclusion compiled rfl
    (by simp [compiled, CheckedProof.binaryOption, CheckedProof.binary, CheckedProof.assemble, CheckedProof.ofOption,
      result, ImplicationExpansion.mpResult, Theorem.unionResult,
      function.hypotheses_exact, argument.hypotheses_exact]) origin

def discharge {premise conclusion : HOL.Formula Symbol Γ}
    (proof : Compiled policy names (premise :: Δ) conclusion) (origin : Origin) :
    Compiled policy names Δ (.imp premise conclusion) := by
  let p := reverseCanonical names premise
  let q := reverseCanonical names conclusion
  let terms := p :: q :: Δ.map (reverseCanonical names)
  let name := freshTermName terms
  have absentP := freshTermName_absent terms ExcludedMiddle.boolBinaryTy p (by simp [terms])
  have absentQ := freshTermName_absent terms ExcludedMiddle.boolBinaryTy q (by simp [terms])
  have fresh : ¬ FreeInHypotheses ⟨name, ExcludedMiddle.boolBinaryTy⟩ ({p} ∪ proof.proof.result.sequent.hyp) := by
    rintro ⟨term, member, occurs⟩
    have inHyp : term ∈ insert p (reverseHypotheses names Δ) := by
      simpa only [p, proof.hypotheses_exact, reverseHypotheses_cons, Finset.singleton_union,
        Finset.insert_idem] using member
    have inList : term ∈ terms := by
      rcases Finset.mem_insert.mp inHyp with same | old
      · simp [terms, same]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_toFinset.mp old))
    exact freshTermName_absent terms _ term inList occurs
  let result := ImplicationIntroduction.dischResult p proof.proof.result
    (reverseCanonical_isBool names premise) proof.boolean
  let native := CheckedProof.unaryOption proof.proof result
    (ImplicationIntroduction.dischBlock? policy p proof.proof.result
      (reverseCanonical_isBool names premise) proof.boolean name fresh absentP
      (by simpa only [proof.conclusion_exact] using absentQ) origin)
    (ImplicationIntroduction.dischBlock?_checked policy p proof.proof.result
      (reverseCanonical_isBool names premise) proof.boolean name fresh absentP
      (by simpa only [proof.conclusion_exact] using absentQ) origin) origin
  apply align names Δ _ native ?_ ?_ origin
  · apply CanonicalTerm.ext_term
    change ExcludedMiddle.impAppDB p.term proof.proof.result.sequent.concl.term = _
    rw [proof.conclusion_exact]
    rfl
  · change proof.proof.result.sequent.hyp.erase p ⊆ reverseHypotheses names Δ
    rw [proof.hypotheses_exact, reverseHypotheses_cons]
    exact Finset.erase_insert_subset _ _

def universalIntro {σ : HOL.Ty AtomicTy} {body : HOL.Formula Symbol (σ :: Γ)}
    (proof : Compiled policy (Naming.cons (freshBinderName names body Δ) names)
      (HOL.weakenHyps (σ := σ) Δ) body) (origin : Origin) :
    Compiled policy names Δ (.all body) := by
  let name := freshBinderName names body Δ
  let binder : SourceVar := ⟨name, reverseTy σ⟩
  have freshFacts := freshBinderName_spec names body Δ
  have fresh : ¬ FreeInHypotheses binder proof.proof.result.sequent.hyp := by
    rw [proof.hypotheses_exact, reverseHypotheses_weakenHyps]
    exact not_freeInHypotheses_reverseHypotheses freshFacts.1 freshFacts.2.2
  let result := QuantifierExpansion.genResult proof.proof.result binder proof.boolean
  let native := CheckedProof.unaryOption proof.proof result
    (QuantifierExpansion.genTypedBlock? policy proof.proof.result binder proof.boolean fresh origin)
    (QuantifierExpansion.genTypedBlock?_checked policy proof.proof.result binder proof.boolean fresh origin) origin
  refine ⟨native, ?_, ?_⟩
  · change proof.proof.result.sequent.hyp = reverseHypotheses names Δ
    rw [proof.hypotheses_exact, reverseHypotheses_weakenHyps]
  · apply CanonicalTerm.ext_term
    change DerivedRules.forallAppDB (reverseTy σ)
      (.abs (reverseTy σ) (DBTerm.closeFreeAt binder 0 proof.proof.result.sequent.concl.term)) = _
    rw [proof.conclusion_exact]
    change DerivedRules.forallAppDB (reverseTy σ)
      (.abs (reverseTy σ) (DBTerm.closeFreeAt binder 0 (reverseTerm (Naming.cons name names) body))) = _
    rw [closeFreeAt_reverseTerm_cons names name body freshFacts.1 freshFacts.2.1]
    rfl

def specialize {σ : HOL.Ty AtomicTy} {body : HOL.Formula Symbol (σ :: Γ)}
    (argument : HOL.Term Symbol Γ σ) (proof : Compiled policy names Δ (.all body)) (origin : Origin) :
    Compiled policy names Δ (HOL.instantiate argument body) := by
  let nativeBody := reverseTermWith (VarEnv.lift (Naming.env names)) body
  let term := reverseCanonical names argument
  have formed : nativeBody.inferType [reverseTy σ] = some Ty.bool := reverseBinder_checked names body
  have shape : proof.proof.result.sequent.concl.term =
      DerivedRules.forallAppDB (reverseTy σ) (.abs (reverseTy σ) nativeBody) := by
    rw [proof.conclusion_exact]
    rfl
  let result := QuantifierExpansion.specResult proof.proof.result (reverseTy σ) nativeBody formed term rfl
  let native := CheckedProof.unaryOption proof.proof result
    (QuantifierExpansion.specTypedBlock? policy proof.proof.result (reverseTy σ) nativeBody formed term rfl shape origin)
    (QuantifierExpansion.specTypedBlock?_checked policy proof.proof.result (reverseTy σ) nativeBody formed term rfl shape origin) origin
  refine ⟨native, proof.hypotheses_exact, ?_⟩
  apply CanonicalTerm.ext_term
  exact (reverseTerm_instantiate names argument body).symm

def betaRule {σ τ : HOL.Ty AtomicTy} (argument : HOL.Term Symbol Γ σ)
    (body : HOL.Term Symbol (σ :: Γ) τ) (origin : Origin) :
    Compiled policy names Δ (.eq (.app (.lam body) argument) (HOL.instantiate argument body)) := by
  let nativeBody := reverseTermWith (VarEnv.lift (Naming.env names)) body
  let term := reverseCanonical names argument
  let expansion := betaExpansion (reverseTy σ) nativeBody (reverseTy τ)
    (reverseBinder_checked names body) term rfl
  let native := CheckedProof.ofBlock expansion.conclusion (betaBlock expansion origin)
    (betaBlock_checked policy expansion origin)
  apply align names Δ _ native ?_ ?_ origin
  · apply CanonicalTerm.ext_term
    change expansion.conclusion.sequent.concl.term = _
    rw [show expansion.conclusion = _ from betaExpansion_conclusion (reverseTy σ) nativeBody
      (reverseTy τ) (reverseBinder_checked names body) term rfl]
    change CanonicalTerm.equalityDB (reverseTy τ) _ _ = _
    rw [show (betaReduced (reverseTy σ) nativeBody (reverseTy τ)
      (reverseBinder_checked names body) term rfl).term = reverseTerm names (HOL.instantiate argument body)
      from (reverseTerm_instantiate names argument body).symm]
    rfl
  · change expansion.conclusion.sequent.hyp ⊆ reverseHypotheses names Δ
    rw [show expansion.conclusion = _ from betaExpansion_conclusion (reverseTy σ) nativeBody
      (reverseTy τ) (reverseBinder_checked names body) term rfl]
    exact Finset.empty_subset _

def etaRule (admitted : policy EtaAxiom.sequent) {σ τ : HOL.Ty AtomicTy}
    (function : HOL.Term Symbol Γ (.arr σ τ)) (origin : Origin) :
    Compiled policy names Δ (.eq (.lam (.app (HOL.weaken (σ := σ) function) (.var .vz))) function) := by
  let term := reverseCanonical names function
  let native := CheckedProof.ofBlock
    (ExtensionalityExpansion.etaResult (reverseTy σ) (reverseTy τ) term rfl)
    (ExtensionalityExpansion.etaBlock (reverseTy σ) (reverseTy τ) term rfl origin)
    (ExtensionalityExpansion.etaBlock_checked policy admitted (reverseTy σ) (reverseTy τ) term rfl origin)
  apply align names Δ _ native ?_ (Finset.empty_subset _) origin
  apply CanonicalTerm.ext_term
  change CanonicalTerm.equalityDB (Ty.function (reverseTy σ) (reverseTy τ))
    (.abs (reverseTy σ) (.app (reverseTerm names function) (.bound 0))) (reverseTerm names function) = _
  have weakened := EtaCompleteness.reverseTermWith_lift_env_weaken (σ := σ) names function
  simp only [reverseCanonical, reverseTerm, reverseTermWith, reverseTy_arr, weakened, VarEnv.lift]


def weaken {conclusion : HOL.Formula Symbol Γ} (proof : Compiled policy names Δ conclusion)
    (premise : HOL.Formula Symbol Γ) (origin : Origin) :
    Compiled policy names (premise :: Δ) conclusion :=
  align names (premise :: Δ) conclusion proof.proof proof.conclusion_exact
    (by rw [proof.hypotheses_exact, reverseHypotheses_cons]; exact Finset.subset_insert _ _) origin

def equalityEliminate {premise conclusion : HOL.Formula Symbol Γ}
    (equation : Compiled policy names Δ (.eq premise conclusion))
    (argument : Compiled policy names Δ premise) (origin : Origin) :
    Compiled policy names Δ conclusion := by
  let result := eqMpResult equation.proof.result argument.proof.result (reverseCanonical names conclusion)
  have checked : checkEqMp equation.proof.result argument.proof.result = some result :=
    eqMpResult_checked _ _ (reverseCanonical names premise) (reverseCanonical names conclusion)
      equation.equalityView argument.conclusion_exact.symm
  let native := CheckedProof.binary equation.proof argument.proof result
    (primitiveBlock (.inference (.eqMp equation.proof.result argument.proof.result)) result origin)
    (primitiveBlock_checked (.inference (.eqMp equation.proof.result argument.proof.result)) result origin checked) origin
  refine ⟨native, ?_, rfl⟩
  change equation.proof.result.sequent.hyp ∪ argument.proof.result.sequent.hyp = reverseHypotheses names Δ
  simp [equation.hypotheses_exact, argument.hypotheses_exact]

def propositionForward {premise conclusion : HOL.Formula Symbol Γ}
    (equation : Compiled policy names Δ (.eq premise conclusion)) (origin : Origin) :
    Compiled policy names Δ (.imp premise conclusion) :=
  discharge (equalityEliminate (equation.weaken premise origin) (hypothesis 0 origin) origin) origin

def propositionBackward {premise conclusion : HOL.Formula Symbol Γ}
    (equation : Compiled policy names Δ (.eq premise conclusion)) (origin : Origin) :
    Compiled policy names Δ (.imp conclusion premise) :=
  propositionForward (equation.symmetric origin) origin

def propositionExtensionality {left right : HOL.Formula Symbol Γ}
    (forward : Compiled policy names Δ (.imp left right))
    (backward : Compiled policy names Δ (.imp right left)) (origin : Origin) :
    Compiled policy names Δ (.eq left right) := by
  let leftProof := modusPonens (backward.weaken right origin) (hypothesis 0 origin) origin
  let rightProof := modusPonens (forward.weaken left origin) (hypothesis 0 origin) origin
  let sameType := leftProof.boolean.trans rightProof.boolean.symm
  let result := deductionResult leftProof.proof.result rightProof.proof.result sameType
  let native := CheckedProof.binary leftProof.proof rightProof.proof result
    (deductionBlock leftProof.proof.result rightProof.proof.result sameType origin)
    (deductionBlock_checked policy leftProof.proof.result rightProof.proof.result sameType origin) origin
  apply align names Δ _ native ?_ ?_ origin
  · apply CanonicalTerm.ext_term
    change CanonicalTerm.equalityDB leftProof.proof.result.sequent.concl.ty
      leftProof.proof.result.sequent.concl.term rightProof.proof.result.sequent.concl.term = _
    rw [leftProof.conclusion_exact, rightProof.conclusion_exact]
    rfl
  · change leftProof.proof.result.sequent.hyp.erase rightProof.proof.result.sequent.concl ∪
      rightProof.proof.result.sequent.hyp.erase leftProof.proof.result.sequent.concl ⊆ reverseHypotheses names Δ
    rw [leftProof.hypotheses_exact, rightProof.hypotheses_exact, leftProof.conclusion_exact,
      rightProof.conclusion_exact, reverseHypotheses_cons, reverseHypotheses_cons]
    exact Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.erase_insert_subset _ _)

def functionCongruence {σ τ : HOL.Ty AtomicTy} {left right : HOL.Term Symbol Γ (.arr σ τ)}
    (argument : HOL.Term Symbol Γ σ) (proof : Compiled policy names Δ (.eq left right)) (origin : Origin) :
    Compiled policy names Δ (.eq (.app left argument) (.app right argument)) := by
  let functionLeft := reverseCanonical names left
  let functionRight := reverseCanonical names right
  let term := reverseCanonical names argument
  let appliedLeft := reverseCanonical names (.app left argument)
  let appliedRight := reverseCanonical names (.app right argument)
  let reflProof := CheckedProof.ofBlock (policy := policy) (reflexivity term)
    (primitiveBlock (.inference (.refl term)) (reflexivity term) origin)
    (primitiveBlock_checked (.inference (.refl term)) _ origin (reflexivity_checked term))
  let result := appResult proof.proof.result reflProof.result appliedLeft appliedRight rfl
  have checked : checkApp proof.proof.result reflProof.result = some result := by
    apply appResult_checked _ _ functionLeft functionRight term term appliedLeft appliedRight rfl
    · exact proof.equalityView
    · exact equality_view term term rfl
    · exact ⟨reverseTy σ, reverseTy τ, by simp [functionLeft, reverseCanonical], rfl, rfl⟩
    · exact ⟨reverseTy σ, reverseTy τ, by simp [functionRight, reverseCanonical], rfl, rfl⟩
  let native := CheckedProof.binary proof.proof reflProof result
    (primitiveBlock (.inference (.mkComb proof.proof.result reflProof.result)) result origin)
    (primitiveBlock_checked (.inference (.mkComb proof.proof.result reflProof.result)) result origin checked) origin
  refine ⟨native, ?_, rfl⟩
  change proof.proof.result.sequent.hyp ∪ ∅ = reverseHypotheses names Δ
  simp [proof.hypotheses_exact]

def argumentCongruence {σ τ : HOL.Ty AtomicTy} (function : HOL.Term Symbol Γ (.arr σ τ))
    {left right : HOL.Term Symbol Γ σ} (proof : Compiled policy names Δ (.eq left right)) (origin : Origin) :
    Compiled policy names Δ (.eq (.app function left) (.app function right)) := by
  let term := reverseCanonical names function
  let argumentLeft := reverseCanonical names left
  let argumentRight := reverseCanonical names right
  let appliedLeft := reverseCanonical names (.app function left)
  let appliedRight := reverseCanonical names (.app function right)
  let reflProof := CheckedProof.ofBlock (policy := policy) (reflexivity term)
    (primitiveBlock (.inference (.refl term)) (reflexivity term) origin)
    (primitiveBlock_checked (.inference (.refl term)) _ origin (reflexivity_checked term))
  let result := appResult reflProof.result proof.proof.result appliedLeft appliedRight rfl
  have checked : checkApp reflProof.result proof.proof.result = some result := by
    apply appResult_checked _ _ term term argumentLeft argumentRight appliedLeft appliedRight rfl
    · exact equality_view term term rfl
    · exact proof.equalityView
    · exact ⟨reverseTy σ, reverseTy τ, by simp [term, reverseCanonical], rfl, rfl⟩
    · exact ⟨reverseTy σ, reverseTy τ, by simp [term, reverseCanonical], rfl, rfl⟩
  let native := CheckedProof.binary reflProof proof.proof result
    (primitiveBlock (.inference (.mkComb reflProof.result proof.proof.result)) result origin)
    (primitiveBlock_checked (.inference (.mkComb reflProof.result proof.proof.result)) result origin checked) origin
  refine ⟨native, ?_, rfl⟩
  change ∅ ∪ proof.proof.result.sequent.hyp = reverseHypotheses names Δ
  simp [proof.hypotheses_exact]

def abstractionCongruence {σ τ : HOL.Ty AtomicTy} {left right : HOL.Term Symbol (σ :: Γ) τ}
    (proof : Compiled policy (Naming.cons (freshBinderName names (.eq left right) Δ) names)
      (HOL.weakenHyps (σ := σ) Δ) (.eq left right)) (origin : Origin) :
    Compiled policy names Δ (.eq (.lam left) (.lam right)) := by
  let name := freshBinderName names (.eq left right) Δ
  let binder : SourceVar := ⟨name, reverseTy σ⟩
  have freshFacts := freshBinderName_spec names (.eq left right) Δ
  have fresh : ¬ FreeInHypotheses binder proof.proof.result.sequent.hyp := by
    rw [proof.hypotheses_exact, reverseHypotheses_weakenHyps]
    exact not_freeInHypotheses_reverseHypotheses freshFacts.1 freshFacts.2.2
  have absentLeft : HOL.NoConstOccurrence (Symbol.ofVar binder) left := by
    exact (noConstOccurrence_eq_inv freshFacts.2.1).1
  have absentRight : HOL.NoConstOccurrence (Symbol.ofVar binder) right := by
    exact (noConstOccurrence_eq_inv freshFacts.2.1).2
  let nativeLeft := reverseCanonical (Naming.cons name names) left
  let nativeRight := reverseCanonical (Naming.cons name names) right
  let result := abstractionResult binder proof.proof.result nativeLeft nativeRight rfl
  let native := CheckedProof.unary proof.proof result
    (abstractionBlock binder proof.proof.result nativeLeft nativeRight rfl origin)
    (abstractionBlock_checked policy binder proof.proof.result nativeLeft nativeRight rfl proof.equalityView fresh origin) origin
  refine ⟨native, ?_, ?_⟩
  · change proof.proof.result.sequent.hyp = reverseHypotheses names Δ
    rw [proof.hypotheses_exact, reverseHypotheses_weakenHyps]
  · apply CanonicalTerm.ext_term
    change CanonicalTerm.equalityDB (Ty.function (reverseTy σ) (reverseTy τ))
      (nativeLeft.abstractFree binder).term (nativeRight.abstractFree binder).term = _
    rw [show nativeLeft.abstractFree binder = reverseCanonical names (.lam left) from
      abstractFree_reverseCanonical_cons names name left freshFacts.1 absentLeft,
      show nativeRight.abstractFree binder = reverseCanonical names (.lam right) from
      abstractFree_reverseCanonical_cons names name right freshFacts.1 absentRight]
    rfl

def functionExtensionality (admitted : policy EtaAxiom.sequent) {σ τ : HOL.Ty AtomicTy}
    {left right : HOL.Term Symbol Γ (.arr σ τ)}
    (proof : Compiled policy names Δ
      (.all (.eq (.app (HOL.weaken (σ := σ) left) (.var .vz))
        (.app (HOL.weaken (σ := σ) right) (.var .vz))))) (origin : Origin) :
    Compiled policy names Δ (.eq left right) := by
  let f := reverseCanonical names left
  let g := reverseCanonical names right
  let terms := f :: g :: Δ.map (reverseCanonical names)
  let binder : SourceVar := ⟨freshTermName terms, reverseTy σ⟩
  have absentF := freshTermName_absent terms (reverseTy σ) f (by simp [terms])
  have absentG := freshTermName_absent terms (reverseTy σ) g (by simp [terms])
  have fresh : ¬ FreeInHypotheses binder proof.proof.result.sequent.hyp := by
    rintro ⟨term, member, occurs⟩
    rw [proof.hypotheses_exact] at member
    have inList : term ∈ terms :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_toFinset.mp member))
    exact freshTermName_absent terms _ term inList occurs
  have shape : proof.proof.result.sequent.concl.term = DerivedRules.forallAppDB binder.ty
      (.abs binder.ty (ExtensionalityExpansion.pointwiseBody (reverseTy τ) f g)) := by
    rw [proof.conclusion_exact]
    change reverseTerm names (.all (.eq (.app (HOL.weaken (σ := σ) left) (.var .vz))
      (.app (HOL.weaken (σ := σ) right) (.var .vz)))) = _
    rw [EtaCompleteness.reverseTerm_all_eq_forallAppDB]
    simp only [reverseTermWith, EtaCompleteness.reverseTermWith_lift_env_weaken,
      VarEnv.lift, ExtensionalityExpansion.pointwiseBody, f, g, reverseCanonical, binder]
  let result := ExtensionalityExpansion.extResult proof.proof.result f g rfl
  let native := CheckedProof.unaryOption proof.proof result
    (ExtensionalityExpansion.extBlock? policy admitted proof.proof.result binder (reverseTy τ) f g rfl rfl
      shape fresh absentF absentG origin)
    (ExtensionalityExpansion.extBlock?_checked policy admitted proof.proof.result binder (reverseTy τ) f g rfl rfl
      shape fresh absentF absentG origin) origin
  exact ⟨native, proof.hypotheses_exact, rfl⟩


end Compiled


open HOL.ImpredicativeConnectives

/-- Structural compilation of the retained implication/quantifier/equality
core. The source proof is Type-valued; no proof is selected from derivability. -/
def compileCore (policy : AxiomPolicy) [DecidablePred policy] (origin : Origin)
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ) (core : IsCoreProof proof)
    (licensed : HOL.ProofSyntax.FunctionExtensionalityFree proof ∨ policy EtaAxiom.sequent)
    (names : Naming Γ) : Compiled policy names Δ φ :=
  match proof with
  | .hyp occurrence => Compiled.hypothesis occurrence origin
  | .impI body => Compiled.discharge (compileCore policy origin body core.2 licensed names) origin
  | .impE function argument =>
      Compiled.modusPonens
        (compileCore policy origin function core.1 (licensed.imp And.left id) names)
        (compileCore policy origin argument core.2 (licensed.imp And.right id) names) origin
  | @HOL.ProofSyntax.allI _ _ _ _ _ body bodyProof =>
      Compiled.universalIntro (compileCore policy origin bodyProof core licensed
        (Naming.cons (freshBinderName names body Δ) names)) origin
  | .allE argument body =>
      Compiled.specialize argument (compileCore policy origin body core.2 licensed names) origin
  | .eqRefl term => Compiled.reflexive term origin
  | .eqSymm body => Compiled.symmetric (compileCore policy origin body core.2.2 licensed names) origin
  | .eqTrans first second =>
      Compiled.transitive
        (compileCore policy origin first core.2.2.2.1 (licensed.imp And.left id) names)
        (compileCore policy origin second core.2.2.2.2 (licensed.imp And.right id) names) origin
  | .eqPropI forward backward =>
      Compiled.propositionExtensionality
        (compileCore policy origin forward core.2.2.1 (licensed.imp And.left id) names)
        (compileCore policy origin backward core.2.2.2 (licensed.imp And.right id) names) origin
  | .eqPropEL body => Compiled.propositionForward (compileCore policy origin body core.2.2 licensed names) origin
  | .eqPropER body => Compiled.propositionBackward (compileCore policy origin body core.2.2 licensed names) origin
  | .eqApp argument body => Compiled.functionCongruence argument (compileCore policy origin body core.2.2.2 licensed names) origin
  | .eqAppArg function body => Compiled.argumentCongruence function (compileCore policy origin body core.2.2.2 licensed names) origin
  | @HOL.ProofSyntax.eqLam _ _ _ _ _ _ left right body =>
      Compiled.abstractionCongruence (compileCore policy origin body core.2.2 licensed
        (Naming.cons (freshBinderName names (.eq left right) Δ) names)) origin
  | .funExt body =>
      let admitted := licensed.elim False.elim id
      Compiled.functionExtensionality admitted
        (compileCore policy origin body core.2.2 (.inr admitted) names) origin
  | .beta argument body => Compiled.betaRule argument body origin
  | .eta function => Compiled.etaRule (licensed.elim False.elim id) function origin
  | .topI | .botE _ | .andI _ _ | .andEL _ | .andER _ | .orIL _ | .orIR _ | .orE _ _ _ |
      .notI _ | .notE _ _ | .exI _ _ | .exE _ _ => False.elim core
termination_by structural proof

/-- All 29 source constructors enter through the existing constructive
impredicative expansion. Its exact translated hypotheses and conclusion are
then certified by the ten original HOL Light inference operations and the
explicit eta axiom. -/
def compile (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ) (names : Naming Γ) (origin : Origin) :
    Compiled policy names (Δ.map expand) (expand φ) :=
  compileCore policy origin (expandProof proof) (expandProof_isCore proof) (.inr admitted) names

/-- Compile an actually eta/function-extensionality-free source proof under
any axiom policy, including the empty policy. No eta permission is required. -/
def compileWithoutFunctionExtensionality (policy : AxiomPolicy) [DecidablePred policy]
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ)
    (free : HOL.ProofSyntax.FunctionExtensionalityFree proof)
    (names : Naming Γ) (origin : Origin) :
    Compiled policy names (Δ.map expand) (expand φ) :=
  compileCore policy origin (expandProof proof) (expandProof_isCore proof)
    (.inl ((expandProof_functionExtensionalityFree proof).mpr free)) names

theorem compileWithoutFunctionExtensionality_accepted
    (policy : AxiomPolicy) [DecidablePred policy]
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ)
    (free : HOL.ProofSyntax.FunctionExtensionalityFree proof)
    (names : Naming Γ) (origin : Origin) :
    (ProofSystem.checker policy).check
      (compileWithoutFunctionExtensionality policy proof free names origin).proof.result
      (compileWithoutFunctionExtensionality policy proof free names origin).proof.certificate = true :=
  (compileWithoutFunctionExtensionality policy proof free names origin).proof.accepted

/-- The policy-restricted compiler retains the exact translated sequent. -/
theorem compileWithoutFunctionExtensionality_sequent
    (policy : AxiomPolicy) [DecidablePred policy]
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ)
    (free : HOL.ProofSyntax.FunctionExtensionalityFree proof)
    (names : Naming Γ) (origin : Origin) :
    (compileWithoutFunctionExtensionality policy proof free names origin).proof.result.sequent.hyp =
        reverseHypotheses names (Δ.map expand) ∧
      (compileWithoutFunctionExtensionality policy proof free names origin).proof.result.sequent.concl =
        reverseCanonical names (expand φ) :=
  ⟨(compileWithoutFunctionExtensionality policy proof free names origin).hypotheses_exact,
    (compileWithoutFunctionExtensionality policy proof free names origin).conclusion_exact⟩

theorem compileWithoutFunctionExtensionality_refuses_changed_conclusion
    (policy : AxiomPolicy) [DecidablePred policy]
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ)
    (free : HOL.ProofSyntax.FunctionExtensionalityFree proof)
    (names : Naming Γ) (origin : Origin)
    (claim : Theorem) (different : claim.sequent.concl ≠ reverseCanonical names (expand φ)) :
    (ProofSystem.checker policy).check claim
      (compileWithoutFunctionExtensionality policy proof free names origin).proof.certificate = false := by
  apply CheckedProof.refuses_changed_conclusion
  simpa only [(compileWithoutFunctionExtensionality policy proof free names origin).conclusion_exact]
    using different

theorem compile_accepted (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ) (names : Naming Γ) (origin : Origin) :
    (ProofSystem.checker policy).check (compile policy admitted proof names origin).proof.result
      (compile policy admitted proof names origin).proof.certificate = true :=
  (compile policy admitted proof names origin).proof.accepted

/-- The theorem at the selected native root has precisely the translated
source conclusion and the finite-set image of its ordered assumptions. -/
theorem compile_sequent (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ) (names : Naming Γ) (origin : Origin) :
    (compile policy admitted proof names origin).proof.result.sequent.hyp = reverseHypotheses names (Δ.map expand) ∧
      (compile policy admitted proof names origin).proof.result.sequent.concl = reverseCanonical names (expand φ) :=
  ⟨(compile policy admitted proof names origin).hypotheses_exact,
    (compile policy admitted proof names origin).conclusion_exact⟩

/-- Reusing the graph with a different conclusion is rejected by the actual
root comparison, independently of the theorem name a caller supplies. -/
theorem compile_refuses_changed_conclusion (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : policy EtaAxiom.sequent)
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ) (names : Naming Γ) (origin : Origin)
    (claim : Theorem) (different : claim.sequent.concl ≠ reverseCanonical names (expand φ)) :
    (ProofSystem.checker policy).check claim (compile policy admitted proof names origin).proof.certificate = false := by
  apply CheckedProof.refuses_changed_conclusion
  simpa only [(compile policy admitted proof names origin).conclusion_exact] using different

end Mettapedia.Languages.HOLLight.RetainedCompilation
