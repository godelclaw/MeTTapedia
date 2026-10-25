import Mettapedia.Languages.Megalodon.HOLProofCompilationCorrectness
import Mettapedia.Languages.Megalodon.SetOperationExtensionality
import Mettapedia.Languages.Megalodon.HOLProofCompilationFragment
import Std.Data.String.ToNat

/-!
# All-constructor acceptance in the common material HOL profile

The six opaque material operations admit every simple type of their source
signature. Each function-extensionality pair used by a supplied proof has a
finite, explicit declaration. The compiler theorem is instantiated with these
actual lookups; no assumption of whole-program acceptance is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.SetOperationCompilerAcceptance

universe w

open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation
open MathdataKernel HenkinTermInterpretation HOLProofInference
open SetOperationProofCompilation (type)
open SetOperationExtensionality

theorem functionalName_injective : Function.Injective functionalName := by
  intro first second same
  apply Nat.repr_injective
  have text := (String.append_right_inj "func_ext_").mp same
  simpa only [Nat.toString_eq_repr] using text

theorem functionalName_ne_propositional (index : Nat) : functionalName index ≠ "prop_ext" := by
  intro same
  have first := congrArg (fun name : String => name.toList.head?) same
  simp [functionalName, String.toList_append] at first

private theorem lookup_of_consistent_member (entries : List KnownDecl) (fact : KnownDecl)
    (present : fact ∈ entries)
    (consistent : ∀ other ∈ entries, other.name = fact.name → other.proposition = fact.proposition) :
    lookupKnownList? entries fact.name = some fact.proposition := by
  induction entries with
  | nil => cases present
  | cons head tail ih =>
      by_cases same : head.name = fact.name
      · simp [lookupKnownList?, same, consistent head (List.mem_cons_self) same]
      · have inTail : fact ∈ tail := by
          rcases List.mem_cons.mp present with rfl | member
          · exact (same rfl).elim
          · exact member
        have found := ih inTail
          (fun other member equal => consistent other (List.mem_cons_of_mem _ member) equal)
        simpa [lookupKnownList?, same] using found

theorem functional_declared (instances : List (Ty Base × Ty Base))
    (domain result : Ty Base) (present : (domain, result) ∈ instances) :
    (environment instances).lookupKnown?
        (functionalInstanceName instances (reifyType domain) (reifyType result)) =
      some (ExtensionalityAxioms.Native.functional (reifyType domain) (reifyType result)) := by
  let nativeTypes := instances.map (fun pair => (reifyType pair.1, reifyType pair.2))
  let position := nativeTypes.idxOf (reifyType domain, reifyType result)
  have nativePresent : (reifyType domain, reifyType result) ∈ nativeTypes :=
    List.mem_map.mpr ⟨(domain, result), present, rfl⟩
  have bounded : position < instances.length := by
    simpa only [nativeTypes, List.length_map] using List.idxOf_lt_length_of_mem nativePresent
  let pair := instances[position]
  have sameTypes : (reifyType pair.1, reifyType pair.2) = (reifyType domain, reifyType result) := by
    have chosen : instances[position]? = some pair := by simp [pair, bounded]
    have mapped : nativeTypes[position]? = some (reifyType pair.1, reifyType pair.2) := by
      simp only [nativeTypes, List.getElem?_map, chosen, Option.map_some]
    exact Option.some.inj (mapped.symm.trans (List.getElem?_idxOf nativePresent))
  let selected : KnownDecl := ⟨functionalName position,
    ExtensionalityAxioms.Native.functional (reifyType pair.1) (reifyType pair.2)⟩
  have selectedPresent : selected ∈ facts instances := by
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨(pair, position), ?_, rfl⟩
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [pair, bounded])
  have consistent : ∀ other ∈ facts instances,
      other.name = selected.name → other.proposition = selected.proposition := by
    intro other member named
    rcases List.mem_cons.mp member with rfl | member
    · exact ((functionalName_ne_propositional position) named.symm).elim
    · obtain ⟨⟨otherPair, index⟩, indexed, rfl⟩ := List.mem_map.mp member
      have sameIndex : index = position := functionalName_injective named
      subst index
      have samePair : otherPair = pair := by
        have atIndex := List.mk_mem_zipIdx_iff_getElem?.mp indexed
        have chosen : instances[position]? = some pair := by simp [pair, bounded]
        exact Option.some.inj (atIndex.symm.trans chosen)
      subst otherPair
      rfl
  have found := lookup_of_consistent_member (facts instances) selected selectedPresent consistent
  have leftSame := congrArg Prod.fst sameTypes
  have rightSame := congrArg Prod.snd sameTypes
  dsimp only [Prod.fst] at leftSame
  dsimp only [Prod.snd] at rightSame
  simpa only [environment, Environment.lookupKnown?, functionalInstanceName,
    selected, position, nativeTypes, leftSame, rightSame] using found

theorem propositional_declared (instances : List (Ty Base × Ty Base)) :
    (environment instances).lookupKnown? "prop_ext" =
      some ExtensionalityAxioms.Native.propositional := by
  simp [environment, facts, Environment.lookupKnown?, lookupKnownList?]

theorem type_formed (source : Ty Unit) (depth : Nat) :
    (reifyType (type source)).plainWellFormed depth = true := by
  induction source with
  | prop => rfl
  | base value => cases value; rfl
  | arr domain result ihd ihr =>
      simpa only [type, Ty.substitute, reifyType, Tp.plainWellFormed, Bool.and_eq_true] using
        And.intro ihd ihr

theorem plainEnvironment (instances : List (Ty Base × Ty Base)) (depth : Nat) :
    PlainEnvironment (environment instances) depth where
  named name entry lookup := by
    have member := lookupTermList?_mem (environment instances).terms name lookup
    simp only [environment, SetOperationProofCompilation.environment,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  primitive index value lookup := by
    change ([] : List Tp)[index]? = some value at lookup
    simp at lookup

theorem compiled_fragment (instances : List (Ty Base × Ty Base))
    {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {conclusion : Formula Symbol gamma}
    (source : ProofSyntax Symbol assumptions conclusion) :
    NativeProof.Fragment (environment instances) 0 (compile instances source) := by
  exact HOLProofCompilationFragment.compile_fragment (functionalProof instances) (.known "prop_ext")
    (fun _ _ => rfl) rfl (plainEnvironment instances 0) (proof instances source)

theorem inferred (instances : List (Ty Base × Ty Base))
    {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {conclusion : Formula Symbol gamma}
    (source : ProofSyntax Symbol assumptions conclusion)
    (covered : ∀ domain result,
      (domain, result) ∈ HOLProofCompilationCorrectness.functionalTypes source →
        (type domain, type result) ∈ instances) :
    Infers 0 (assumptions.map (term instances)) (compile instances source) (term instances conclusion) := by
  exact HOLProofCompilationCorrectness.inferred SetOperationProofCompilation.base (symbol instances) 0
    (fun value => type_formed value 0)
    (fun name entry lookup => SetOperationSemantics.lookup_opaque name entry lookup)
    (functionalInstanceName instances) "prop_ext" (propositional_declared instances) source
    (fun domain result member => functional_declared instances (type domain) (type result)
      (covered domain result member))

/-- The finite declarations are computed from this proof's actual uses of
functional extensionality; duplicates do not change their meaning. -/
def requiredInstances {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)}
    {conclusion : Formula Symbol gamma} (source : ProofSyntax Symbol assumptions conclusion) :
    List (Ty Base × Ty Base) :=
  (HOLProofCompilationCorrectness.functionalTypes source).map
    (fun pair => (type pair.1, type pair.2))

theorem inferred_required {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)}
    {conclusion : Formula Symbol gamma} (source : ProofSyntax Symbol assumptions conclusion) :
    Infers 0 (assumptions.map (term (requiredInstances source)))
      (compile (requiredInstances source) source) (term (requiredInstances source) conclusion) := by
  apply inferred
  intro domain result member
  exact List.mem_map.mpr ⟨(domain, result), member, rfl⟩

theorem accepted (instances : List (Ty Base × Ty Base))
    {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {conclusion : Formula Symbol gamma}
    (source : ProofSyntax Symbol assumptions conclusion)
    (covered : ∀ domain result,
      (domain, result) ∈ HOLProofCompilationCorrectness.functionalTypes source →
        (type domain, type result) ∈ instances) :
    ∃ fuel, checkProof (environment instances) fuel 0 ((gamma.map type).map reifyType)
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (term instances formula)))
      (compile instances source) (HOLTermEncoding.native (term instances conclusion)) = true := by
  have normal : DeltaNormalInvariant.Normal (environment instances)
      (HOLTermEncoding.native (term instances conclusion)) :=
    fun name entry _ lookup => SetOperationSemantics.lookup_opaque name entry lookup
  simpa only [List.map_map, Function.comp_def] using HOLProofInference.checked_of_inferred
    normal (inferred instances source covered)

theorem accepted_required {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)}
    {conclusion : Formula Symbol gamma} (source : ProofSyntax Symbol assumptions conclusion) :
    ∃ fuel, checkProof (environment (requiredInstances source)) fuel 0 ((gamma.map type).map reifyType)
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (term (requiredInstances source) formula)))
      (compile (requiredInstances source) source)
      (HOLTermEncoding.native (term (requiredInstances source) conclusion)) = true := by
  apply accepted
  intro domain result member
  exact List.mem_map.mpr ⟨(domain, result), member, rfl⟩

theorem canonical_formula_meaning (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (full : source.FullDomains)
    {gamma : Ctx Unit} (formula : Formula Symbol gamma)
    (values : (model instances source).Valuation (gamma.map type)) :
    (model instances source).denote (HOLNormalForms.normalForm (term instances formula)) values =
      source.denote formula (SetOperationSemantics.sourceValuation source values) := by
  calc
    _ = (model instances source).denote (HOLTermEncoding.encode (term instances formula)) values :=
      (HOLNormalForms.denote_normalForm _ (fullDomains instances source) _ values).trans
        (HOLTermEncoding.denote_encode _ (fullDomains instances source) _ values).symm
    _ = _ := denote_encoded_formula instances source full formula values

/-- Soundness for the actual canonical hypothesis representation accepted by
the compiler. List positions are retained; normalization preserves their
interpreted propositions in either material model. -/
theorem accepted_canonical_material (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (full : source.FullDomains)
    {gamma : Ctx Unit} (assumptions : List (Formula Symbol gamma))
    (conclusion : Formula Symbol gamma) {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment (environment instances) depth program)
    (accepted : checkProof (environment instances) fuel depth ((gamma.map type).map reifyType)
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (term instances formula)))
      program (HOLTermEncoding.native (term instances conclusion)) = true)
    (values : (model instances source).Valuation (gamma.map type))
    (satisfied : Soundness.SatisfiesHyps source
      (SetOperationSemantics.sourceValuation source values) assumptions) :
    (source.denote conclusion (SetOperationSemantics.sourceValuation source values)).down := by
  have erased : NativeProof.ErasedHypotheses
      (assumptions.map (fun formula => HOLNormalForms.normalForm (term instances formula)))
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (term instances formula))) := by
    change (assumptions.map (fun formula => HOLNormalForms.normalForm (term instances formula))).map erase =
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (term instances formula))).map some
    simp only [List.map_map]
    apply List.map_congr_left
    intro formula _
    exact HOLNormalForms.normalForm_erased _
  have canonicalSatisfied : Soundness.SatisfiesHyps (model instances source) values
      (assumptions.map (fun formula => HOLNormalForms.normalForm (term instances formula))) := by
    intro formula member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [canonical_formula_meaning instances source full]
    exact satisfied original originalMember
  have valid := NativeProof.checkProof_sound (checkedDefinitions instances) (model instances source)
    (definitionEquations instances source) (knownValidity instances source) fragment erased
    (HOLTermEncoding.encode (term instances conclusion)) (HOLTermEncoding.native_erased _)
    accepted values (fun _ => fullDomains instances source _ _) canonicalSatisfied
  rwa [denote_encoded_formula instances source full] at valid

/-- The same compiled program is checked and then interpreted. The source
proof supplies no axiom-validity field: the declared guest schemas have
already been proved valid in the material interpretation. -/
theorem checked_material (instances : List (Ty Base × Ty Base))
    {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {conclusion : Formula Symbol gamma}
    (source : ProofSyntax Symbol assumptions conclusion)
    (covered : ∀ domain result,
      (domain, result) ∈ HOLProofCompilationCorrectness.functionalTypes source →
        (type domain, type result) ∈ instances) :
    ∃ fuel, checkProof (environment instances) fuel 0 ((gamma.map type).map reifyType)
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (term instances formula)))
      (compile instances source) (HOLTermEncoding.native (term instances conclusion)) = true ∧
      ∀ (interpretation : HenkinModel.{0, 0, w} Unit Symbol), interpretation.FullDomains →
        ∀ values : (model instances interpretation).Valuation (gamma.map type),
          Soundness.SatisfiesHyps interpretation
            (SetOperationSemantics.sourceValuation interpretation values) assumptions →
          (interpretation.denote conclusion
            (SetOperationSemantics.sourceValuation interpretation values)).down := by
  obtain ⟨fuel, checked⟩ := accepted instances source covered
  refine ⟨fuel, checked, ?_⟩
  intro interpretation full values satisfied
  exact accepted_canonical_material instances interpretation full assumptions conclusion
    (compiled_fragment instances source) checked values satisfied

#print axioms functional_declared
#print axioms propositional_declared
#print axioms type_formed
#print axioms plainEnvironment
#print axioms compiled_fragment
#print axioms inferred
#print axioms inferred_required
#print axioms accepted
#print axioms accepted_required
#print axioms canonical_formula_meaning
#print axioms accepted_canonical_material
#print axioms checked_material

end Mettapedia.Languages.Megalodon.SetOperationCompilerAcceptance
