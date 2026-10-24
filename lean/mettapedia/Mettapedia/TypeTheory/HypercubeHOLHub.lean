import Mettapedia.TypeTheory.HypercubeBubbles
import Mettapedia.GSLT.Dedukti.HOLHubPreservation
import Mettapedia.GSLT.Dedukti.Metatheory
import Mettapedia.GSLT.LanguageDef.LF.DTTBenchDemand
import Mettapedia.GSLT.LanguageDef.LF.ProfileChecker

/-!
# The HOL proof hub at the direct-dependency formation vertex

The typed STTfa proof hub uses `LFProfile.standardLF`.  Its product rules are
exactly the ordinary-function and value-to-type rules isolated by
`HypercubeBubbles` as the least basis for direct value-indexed universals.
This module makes that connection explicit without identifying formation
with the hub's conversion theory.

* `standardLF_subsumed_iff_directInterface` characterizes profile extension from
  the hub's formation profile by the direct same-value interface.
* `translate_typed_of_directInterface` and
  `theorem_typed_of_directInterface` transport object terms and compiled HOL
  evidence to every profile supporting that interface.  Context lookup and
  substitution use the existing source translation; the latter is joined to
  profiled typing by `translate_substitute_typed_of_directInterface`.
* The actual STTfa declarations, definitions and rewrite rules satisfy their
  formation and preservation obligations at the two-rule vertex.  The
  decoder declaration `eta : type → Type` cannot even be formed at the simple
  vertex, giving the negative control.

The results do not say that dependency alone supplies the STTfa declarations
or rules, that every dependent profile validates HOL, or that formation
chooses beta, eta or another conversion policy.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HypercubeHOLHub

open Mettapedia.Logic
open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.Dedukti.HOLHub
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.TypeTheory.HypercubeBubbles

universe u v

/-- The λΠ profile of the proof hub is the dependent vertex of the annotated
cube: the same sort axiom and exactly the two rules `F,D`. -/
theorem standardLF_eq_dependentVertex :
    LFProfile.standardLF = vertex dependentProducts := by
  rfl

/-- Among profiles with `Type : Kind`, extending the hub's λΠ formation
profile is equivalent to supporting the direct same-value universal
interface.  The conversion bubble remains arbitrary. -/
theorem standardLF_subsumed_iff_directInterface
    (profile : Profile) (sameAxiom : profile.sortAxiom = typeAxiom)
    (steps : PTerm → PTerm → Prop) :
    LFProfile.standardLF ⊑ profile ↔ DirectValueIndexedForall profile.products steps := by
  constructor
  · intro included
    apply (directValueIndexedForall_iff_contains_dependentProducts _ _).2
    intro rule member
    exact included.2 rule (by simpa [LFProfile.standardLF, dependentProducts] using member)
  · intro available
    refine ⟨?_, ?_⟩
    · intro source target holds
      change typeAxiom source = some target at holds
      rw [sameAxiom]
      exact holds
    · intro rule member
      have needed : rule ∈ dependentProducts := by
        simpa [LFProfile.standardLF, dependentProducts] using member
      exact (directValueIndexedForall_iff_contains_dependentProducts _ _).1 available needed

/-! ## The actual hub theory at the least formation profile -/

/-- Every STTfa hub declaration is formed at the dependent vertex. -/
theorem formedSignature_at_dependentVertex
    {Base : Type u} {Const : HOL.Ty Base → Type v} {e : Encoding Base Const}
    (names : SttfaNames e) :
    (sttfaProofTheory e).FormedSignature (vertex dependentProducts) := by
  simpa [standardLF_eq_dependentVertex] using formedSignature names

/-- The STTfa hub has no transparent body outside its declared type at the
same vertex. -/
theorem typedBodies_at_dependentVertex
    {Base : Type u} {Const : HOL.Ty Base → Type v} (e : Encoding Base Const) :
    (sttfaProofTheory e).TypedBodies (vertex dependentProducts) := by
  simpa [standardLF_eq_dependentVertex] using typedBodies e

/-- Every STTfa rewrite instance preserves its input type at the same
formation vertex. -/
theorem rulesPreserveTypes_at_dependentVertex
    {Base : Type u} {Const : HOL.Ty Base → Type v} {e : Encoding Base Const}
    (names : SttfaNames e) :
    (sttfaProofTheory e).RulesPreserveTypes (vertex dependentProducts) := by
  simpa [standardLF_eq_dependentVertex] using rulesPreserveTypes names

/-- Subject reduction for the typed hub, stated at the direct-dependency
vertex rather than through the `LambdaPiModulo` abbreviation. -/
theorem typePreservation_at_dependentVertex
    {Base : Type u} {Const : HOL.Ty Base → Type v} {e : Encoding Base Const}
    (names : SttfaNames e) {context : LFTyping.Ctx} {source target type : LF.Term}
    (wellFormed : WellFormedCtx (vertex dependentProducts) (sttfaProofTheory e) context)
    (typed : HasType (vertex dependentProducts) (sttfaProofTheory e) context source type)
    (reduces : Reduces (sttfaProofTheory e) source target) :
    HasType (vertex dependentProducts) (sttfaProofTheory e) context target type := by
  rw [← standardLF_eq_dependentVertex] at wellFormed typed ⊢
  exact sttfa_typePreservation names wellFormed typed reduces

/-! ## Contexts, substitution and compiled evidence above the vertex -/

/-- A declared HOL term remains typed after moving from the least formation
profile to any profile supporting the direct interface.  The target context
is the existing pointwise decoding of the source context. -/
theorem translate_typed_of_directInterface
    {Base : Type u} {Const : HOL.Ty Base → Type v} {e : Encoding Base Const}
    {theory : Theory} {codes : String} (declares : Declares e theory codes)
    (profile : Profile) (sameAxiom : profile.sortAxiom = typeAxiom)
    (steps : PTerm → PTerm → Prop)
    (available : DirectValueIndexedForall profile.products steps)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (term : HOL.Term Const Γ τ) :
    HasType profile theory (e.ctx Γ) (e.translate term) (e.El (e.code τ)) := by
  apply HasType.mono
    ((standardLF_subsumed_iff_directInterface profile sameAxiom steps).2 available)
    (Theory.Extends.refl _)
  exact declares.translate_typed term

/-- The existing capture-avoiding source substitution equation and profiled
typing hold together.  Its `image` premise states the selected one-variable
substitution on the translated de Bruijn context. -/
theorem translate_substitute_typed_of_directInterface
    {Base : Type u} {Const : HOL.Ty Base → Type v} {e : Encoding Base Const}
    {theory : Theory} {codes : String} (declares : Declares e theory codes)
    (profile : Profile) (sameAxiom : profile.sortAxiom = typeAxiom)
    (steps : PTerm → PTerm → Prop)
    (available : DirectValueIndexedForall profile.products steps)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (term : HOL.Term Const Γ τ)
    {Δ : HOL.Ctx Base} (index : Nat) (substitution : HOL.Subst Const Γ Δ)
    (replacement : LF.Term)
    (image : ∀ {σ : HOL.Ty Base} (sourceVar : HOL.Var Γ σ),
      e.translate (substitution sourceVar) =
        if varIndex sourceVar < index then .var (varIndex sourceVar)
        else if varIndex sourceVar = index then LFTyping.lift index 0 replacement
        else .var (varIndex sourceVar - 1)) :
    e.translate (HOL.subst substitution term) =
        LFTyping.subst index (LFTyping.lift index 0 replacement) (e.translate term) ∧
      HasType profile theory (e.ctx Δ) (e.translate (HOL.subst substitution term))
        (e.El (e.code τ)) :=
  ⟨e.translate_substitute term index substitution replacement image,
    translate_typed_of_directInterface declares profile sameAxiom steps available _⟩

/-- Every proof in the maintained implication/universal HOL calculus compiles
to typed STTfa evidence at every formation profile supporting the direct
interface.  The STTfa declarations and rewrite theory remain explicit
premises of the route. -/
theorem theorem_typed_of_directInterface
    {Base : Type u} {Const : HOL.Ty Base → Type v} {e : Encoding Base Const}
    (el : e.el = "eta") (arrow : e.name .arrow = "arrow")
    (imp : e.name .imp = "impl") (all : e.name .all = "forall")
    (fresh : ∀ s, e.name s ≠ "eta" ∧ e.name s ≠ "etap" ∧ e.name s ≠ "eps")
    (typeFresh : ∀ s, e.name s ≠ "type")
    (profile : Profile) (sameAxiom : profile.sortAxiom = typeAxiom)
    (steps : PTerm → PTerm → Prop)
    (available : DirectValueIndexedForall profile.products steps)
    {Γ : HOL.Ctx Base} {φ : HOL.Formula Const Γ}
    (proof : HOL.ProofSyntaxModulo [] [] φ) :
    HasType profile (sttfaProofTheory e) (e.ctx Γ)
      (compile e "eps" proof (.base Γ) Fin.elim0)
      (.app (.con "eps") (e.translate φ)) := by
  apply HasType.mono
    ((standardLF_subsumed_iff_directInterface profile sameAxiom steps).2 available)
    (Theory.Extends.refl _)
  exact sttfa_theorem_typed e el arrow imp all fresh typeFresh proof

/-! ## Positive and negative controls -/

/-- The compiled universal-elimination control is typed at the exact
two-rule dependency vertex. -/
theorem predInstance_typed_at_dependentVertex :
    HasType (vertex dependentProducts) (sttfaProofTheory sttfaControl)
      (sttfaControl.ctx [])
      (compile sttfaControl "eps" predInstanceProof (.base []) Fin.elim0)
      (.app (.con "eps") (sttfaControl.translate
        (.imp (.all predVar) (.app (.const ControlConst.pred) (.const ControlConst.point))))) := by
  rw [← standardLF_eq_dependentVertex]
  exact sttfa_predInstance_typed

/-- A product from a value to `Type` cannot be formed at the simple vertex,
regardless of the theory's conversion relation. -/
theorem eta_declaration_not_formed_at_simpleVertex
    {Base : Type u} {Const : HOL.Ty Base → Type v} {e : Encoding Base Const} :
    ¬ ∃ sort, HasType (vertex simplyTypedProducts) (sttfaProofTheory e) []
      (.pi (.con "type") (.srt .type)) (.srt sort) := by
  rintro ⟨sort, typed⟩
  obtain ⟨domainSort, codomainSort, resultSort, _, bodyTyped, member, _⟩ := typed.pi_inv
  have codomainIsType : codomainSort = .type := by
    simpa [vertex, simplyTypedProducts, LFProfile.typeTypeType] using congrArg ProductRule.codomain
      (List.mem_singleton.mp member)
  obtain ⟨target, sortAxiomHolds, converted⟩ := bodyTyped.sort_inv
  have targetIsKind : target = .kind := by
    have kindIsTarget : (Srt.kind : Srt) = target := by
      simpa [vertex, typeAxiom] using sortAxiomHolds
    exact kindIsTarget.symm
  have targetIsCodomain : target = codomainSort :=
    Conv.srt_injective (proofTheory_confluent e) (proofTheory_headed e) converted
  have impossible : (Srt.kind : Srt) = .type :=
    targetIsKind.symm.trans (targetIsCodomain.trans codomainIsType)
  cases impossible

/-- Consequently the actual STTfa signature is not formed at the simple
vertex: its `eta : type → Type` declaration already crosses the dependency
edge. -/
theorem signature_not_formed_at_simpleVertex
    {Base : Type u} {Const : HOL.Ty Base → Type v} {e : Encoding Base Const}
    (names : SttfaNames e) :
    ¬ (sttfaProofTheory e).FormedSignature (vertex simplyTypedProducts) := by
  intro formed
  exact eta_declaration_not_formed_at_simpleVertex
    (formed "eta" (.pi (.con "type") (.srt .type)) (constType_eta names))

/-! ## CoC and the MettaKernel kind-result prototype fork

The four-rule CoC formation profile and the source-extracted MettaKernel
kind-result prototype are distinct extensions of their shared three-rule fragment. CoC has
`(Kind, Type, Type)`, allowing the displayed polymorphic identity type. The
prototype has `(Kind, Type, Kind)`, demanded by the frozen DTTBench
statement corpus. Their indiscriminate union has both results for the same
domain/codomain pair and is therefore not functional.

This is a checked interaction law for the flower: two individually useful
upper profiles cannot be merged as a bag while retaining the standard
uniqueness-of-types hypothesis.
-/

open Mettapedia.GSLT.LanguageDef.LFDTTBenchDemand

/-- The product rules shared by CoC formation and the MettaKernel
kind-result prototype. -/
def sharedDependentOperatorProducts : List ProductRule :=
  [typeTypeType, typeKindKind, kindKindKind]

/-- Exact intersection of the two upper profiles' product rules. -/
theorem construction_mettaKernelPrototype_common_product_iff
    (rule : ProductRule) :
    (rule ∈ constructionProducts ∧ rule ∈ LFProfile.mettaKernelKindResultPrototype.products) ↔
      rule ∈ sharedDependentOperatorProducts := by
  simp [constructionProducts, constructions, LFProfile.mettaKernelKindResultPrototype,
    sharedDependentOperatorProducts, kindTypeType, kindTypeKind,
    typeTypeType, typeKindKind, kindKindKind]
  aesop

/-- CoC's polymorphic product is absent from the MettaKernel prototype. -/
theorem coc_polymorphism_not_mettaKernelPrototype :
    kindTypeType ∉ LFProfile.mettaKernelKindResultPrototype.products := by
  decide

/-- The prototype's unusual Type-parameter rule is absent from CoC. -/
theorem mettaKernelPrototype_parameterRule_not_construction :
    kindTypeKind ∉ constructionProducts := by
  decide

theorem constructions_not_subsumed_mettaKernelPrototype :
    ¬ constructions ⊑ LFProfile.mettaKernelKindResultPrototype := by
  intro included
  exact coc_polymorphism_not_mettaKernelPrototype
    (included.2 kindTypeType (by decide))

theorem mettaKernelPrototype_not_subsumed_constructions :
    ¬ LFProfile.mettaKernelKindResultPrototype ⊑ constructions := by
  intro included
  exact mettaKernelPrototype_parameterRule_not_construction
    (included.2 kindTypeKind (by decide))

/-- The literal union of the two branches. -/
def constructionMettaKernelPrototypeUnion : Profile where
  sortAxiom := typeAxiom
  products := constructionProducts ++ [kindTypeKind]

/-- The literal union is not functional: one product has both `Type` and
`Kind` as result sorts. -/
theorem constructionMettaKernelPrototypeUnion_not_functional :
    ¬ Functional constructionMettaKernelPrototypeUnion := by
  intro functional
  have impossible := functional kindTypeType (by decide) kindTypeKind (by decide) rfl rfl
  cases impossible

/-- The MettaKernel prototype does not support the three direct interfaces
whose relative minimum is CoC formation. -/
theorem mettaKernelPrototype_does_not_support_directFormationInterfaces
    (steps : PTerm → PTerm → Prop) :
    ¬ DirectFormationInterfaces LFProfile.mettaKernelKindResultPrototype.products steps := by
  intro available
  have contains :=
    (directFormationInterfaces_iff_contains_constructionProducts _ _).1 available
  exact coc_polymorphism_not_mettaKernelPrototype (contains (by decide))

/-- CoC formation does not contain the independently computed demand of the
frozen DTTBench statement corpus. -/
theorem constructions_do_not_contain_DTTBench : ¬ ContainsDTTBench constructions := by
  intro contains
  have demanded : kindTypeKind ∈ allDemandRules := by
    rw [allDemandRules_eq_mettaKernelPrototype]
    decide
  exact mettaKernelPrototype_parameterRule_not_construction
    (contains.2 kindTypeKind demanded)

/-- Both branches meet their own requirements, neither subsumes the other,
and their literal union loses functionality. -/
theorem coc_mettaKernelPrototype_fork (steps : PTerm → PTerm → Prop) :
    DirectFormationInterfaces constructionProducts steps ∧
      ContainsDTTBench LFProfile.mettaKernelKindResultPrototype ∧
      ¬ constructions ⊑ LFProfile.mettaKernelKindResultPrototype ∧
      ¬ LFProfile.mettaKernelKindResultPrototype ⊑ constructions ∧
      ¬ Functional constructionMettaKernelPrototypeUnion :=
  ⟨(directFormationInterfaces_iff_contains_constructionProducts _ _).2
      (fun _ member => member),
    mettaKernelPrototype_contains_DTTBench,
    constructions_not_subsumed_mettaKernelPrototype,
    mettaKernelPrototype_not_subsumed_constructions,
    constructionMettaKernelPrototypeUnion_not_functional⟩

/-! ## Executable formation-profile join admission

Formation rules can be joined mechanically only after checking that every
domain/codomain pair still has one result sort. This gate concerns formation
profiles. It does not admit the union of conversion rules, whose normalization
and interaction laws remain separate obligations.
-/

/-- Two rules are compatible when different premises distinguish them, or
their result sorts agree. -/
def compatibleResults (first second : ProductRule) : Prop :=
  first.domain ≠ second.domain ∨
    first.codomain ≠ second.codomain ∨ first.result = second.result

def compatibleResultsCheck (first second : ProductRule) : Bool :=
  (first.domain != second.domain) ||
    (first.codomain != second.codomain) || (first.result == second.result)

theorem compatibleResultsCheck_eq_true_iff (first second : ProductRule) :
    compatibleResultsCheck first second = true ↔ compatibleResults first second := by
  simp [compatibleResultsCheck, compatibleResults]
  tauto

/-- Functionality stated on a finite list of product rules. -/
def functionalProducts (products : List ProductRule) : Prop :=
  ∀ first ∈ products, ∀ second ∈ products, compatibleResults first second

def functionalProductsCheck (products : List ProductRule) : Bool :=
  products.all fun first =>
    products.all fun second => compatibleResultsCheck first second

theorem functionalProductsCheck_eq_true_iff (products : List ProductRule) :
    functionalProductsCheck products = true ↔ functionalProducts products := by
  simp [functionalProductsCheck, functionalProducts, compatibleResultsCheck_eq_true_iff]

/-- The finite check is exactly the functionality premise used by the
uniqueness-of-types theorem. -/
theorem functionalProducts_iff_profileFunctional (products : List ProductRule) :
    functionalProducts products ↔
      Functional ({ sortAxiom := typeAxiom, products := products } : Profile) := by
  constructor
  · intro functional first firstMember second secondMember domains codomains
    rcases functional first firstMember second secondMember with differentDomains |
      differentCodomains | sameResult
    · exact absurd domains differentDomains
    · exact absurd codomains differentCodomains
    · exact sameResult
  · intro functional first firstMember second secondMember
    by_cases domains : first.domain = second.domain
    · by_cases codomains : first.codomain = second.codomain
      · exact Or.inr (Or.inr
          (functional first firstMember second secondMember domains codomains))
      · exact Or.inr (Or.inl codomains)
    · exact Or.inl domains

def mergedProducts (first second : List ProductRule) : List ProductRule :=
  (first ++ second).eraseDups

/-- Join two finite formation-rule lists, refusing a nonfunctional union. -/
def admitProductJoin (first second : List ProductRule) : Option (List ProductRule) :=
  let merged := mergedProducts first second
  if functionalProductsCheck merged then some merged else none

theorem admitProductJoin_eq_some_iff (first second joined : List ProductRule) :
    admitProductJoin first second = some joined ↔
      joined = mergedProducts first second ∧ functionalProducts joined := by
  simp [admitProductJoin]
  constructor
  · rintro ⟨check, rfl⟩
    exact ⟨rfl, (functionalProductsCheck_eq_true_iff _).1 check⟩
  · rintro ⟨rfl, functional⟩
    exact ⟨(functionalProductsCheck_eq_true_iff _).2 functional, rfl⟩

theorem admitProductJoin_eq_none_iff (first second : List ProductRule) :
    admitProductJoin first second = none ↔
      ¬ functionalProducts (mergedProducts first second) := by
  simp [admitProductJoin, functionalProductsCheck_eq_true_iff]

theorem admitted_join_contains_left {first second joined : List ProductRule}
    (accepted : admitProductJoin first second = some joined) : first ⊆ joined := by
  rw [(admitProductJoin_eq_some_iff _ _ _).1 accepted |>.1]
  intro rule member
  apply List.mem_eraseDups.mpr
  exact List.mem_append_left _ member

theorem admitted_join_contains_right {first second joined : List ProductRule}
    (accepted : admitProductJoin first second = some joined) : second ⊆ joined := by
  rw [(admitProductJoin_eq_some_iff _ _ _).1 accepted |>.1]
  intro rule member
  apply List.mem_eraseDups.mpr
  exact List.mem_append_right _ member

/-- Positive admission: dependency plus type operators remains functional. -/
theorem dependent_operator_join_accepted :
    admitProductJoin dependentProducts [kindKindKind] =
      some sharedDependentOperatorProducts := by
  decide

/-- Negative admission: the blind CoC/prototype union is refused. -/
theorem coc_mettaKernelPrototype_join_refused :
    admitProductJoin constructionProducts LFProfile.mettaKernelKindResultPrototype.products = none := by
  decide

/-- A finite product list as a selectable formation profile with the shared
`Type : Kind` axiom. -/
def profileOfProducts (products : List ProductRule) : Profile where
  sortAxiom := typeAxiom
  products := products

theorem admitted_join_subsumes_left {first second joined : List ProductRule}
    (accepted : admitProductJoin first second = some joined) :
    profileOfProducts first ⊑ profileOfProducts joined :=
  ⟨fun _ _ known => known, fun _ member => admitted_join_contains_left accepted member⟩

theorem admitted_join_subsumes_right {first second joined : List ProductRule}
    (accepted : admitProductJoin first second = some joined) :
    profileOfProducts second ⊑ profileOfProducts joined :=
  ⟨fun _ _ known => known, fun _ member => admitted_join_contains_right accepted member⟩

/-- Every accepted proof under the left input profile has finite evidence
accepted under an admitted joined profile. -/
theorem admitted_join_rechecks_left
    {first second joined : List ProductRule}
    (accepted : admitProductJoin first second = some joined)
    {signature : LFTyping.Sig} {context : LFTyping.Ctx}
    {proof : LFProfileChecker.Proof} {term type : LF.Term}
    (checked : LFProfileChecker.checkProof (profileOfProducts first)
      signature context proof term type = true) :
    ∃ joinedProof, LFProfileChecker.checkProof (profileOfProducts joined)
      signature context joinedProof term type = true := by
  have derived := LFProfileChecker.checkProof_sound checked
  exact LFProfileChecker.exists_checkProof_of_deriv
    (derived.mono (admitted_join_subsumes_left accepted))

/-- The symmetric finite-evidence preservation result for the right input. -/
theorem admitted_join_rechecks_right
    {first second joined : List ProductRule}
    (accepted : admitProductJoin first second = some joined)
    {signature : LFTyping.Sig} {context : LFTyping.Ctx}
    {proof : LFProfileChecker.Proof} {term type : LF.Term}
    (checked : LFProfileChecker.checkProof (profileOfProducts second)
      signature context proof term type = true) :
    ∃ joinedProof, LFProfileChecker.checkProof (profileOfProducts joined)
      signature context joinedProof term type = true := by
  have derived := LFProfileChecker.checkProof_sound checked
  exact LFProfileChecker.exists_checkProof_of_deriv
    (derived.mono (admitted_join_subsumes_right accepted))

#print axioms standardLF_subsumed_iff_directInterface
#print axioms formedSignature_at_dependentVertex
#print axioms typedBodies_at_dependentVertex
#print axioms rulesPreserveTypes_at_dependentVertex
#print axioms typePreservation_at_dependentVertex
#print axioms translate_typed_of_directInterface
#print axioms translate_substitute_typed_of_directInterface
#print axioms theorem_typed_of_directInterface
#print axioms predInstance_typed_at_dependentVertex
#print axioms eta_declaration_not_formed_at_simpleVertex
#print axioms signature_not_formed_at_simpleVertex
#print axioms construction_mettaKernelPrototype_common_product_iff
#print axioms constructions_not_subsumed_mettaKernelPrototype
#print axioms mettaKernelPrototype_not_subsumed_constructions
#print axioms constructionMettaKernelPrototypeUnion_not_functional
#print axioms mettaKernelPrototype_does_not_support_directFormationInterfaces
#print axioms constructions_do_not_contain_DTTBench
#print axioms coc_mettaKernelPrototype_fork
#print axioms compatibleResultsCheck_eq_true_iff
#print axioms functionalProductsCheck_eq_true_iff
#print axioms functionalProducts_iff_profileFunctional
#print axioms admitProductJoin_eq_some_iff
#print axioms admitProductJoin_eq_none_iff
#print axioms admitted_join_contains_left
#print axioms admitted_join_contains_right
#print axioms dependent_operator_join_accepted
#print axioms coc_mettaKernelPrototype_join_refused
#print axioms admitted_join_subsumes_left
#print axioms admitted_join_subsumes_right
#print axioms admitted_join_rechecks_left
#print axioms admitted_join_rechecks_right

end Mettapedia.TypeTheory.HypercubeHOLHub
