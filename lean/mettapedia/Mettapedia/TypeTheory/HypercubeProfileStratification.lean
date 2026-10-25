import Mettapedia.TypeTheory.HypercubeHOLHub

/-!
# A mode-stratified upper interface for incompatible formation profiles

The CoC-style formation profile and the historical MettaKernel kind-result prototype
cannot have a functional common upper profile on the current two-sort syntax:
every common upper would contain two rules with the same premise sorts and
different result sorts.  This strengthens the earlier observation about their
literal list union.

One honest common service therefore retains the selected branch as a mode.
Each fibre has its own functional profile and exact proof checker.  The shared
`F,D,O` fragment embeds in both fibres, so proof evidence from that fragment
can be rechecked in either one.  Branch-specific evidence is not silently
retagged.

This construction is a dispatch interface, not a merged calculus.  A future
single upper calculus would still need a larger sort syntax, a resolution of
the conflicting result sort, or a different uniqueness metatheory.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HypercubeProfileStratification

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.LanguageDef.LFProfileChecker
open Mettapedia.GSLT.LanguageDef.LFDTTBenchDemand
open Mettapedia.GSLT.Dedukti
open Mettapedia.TypeTheory.HypercubeBubbles
open Mettapedia.TypeTheory.HypercubeHOLHub

universe u

/-- No functional profile over the existing two sorts can contain both upper
branches.  The obstacle is inherited by every alleged common upper profile. -/
theorem no_functional_common_upper :
    ¬ ∃ upper : Profile,
      profileOfProducts constructionProducts ⊑ upper ∧
      mettaKernelKindResultPrototype ⊑ upper ∧ Functional upper := by
  rintro ⟨upper, fromConstruction, fromPrototype, functional⟩
  have constructionRule : kindTypeType ∈ constructionProducts := by
    simp [constructionProducts, constructions, kindTypeType]
  have prototypeRule : kindTypeKind ∈ mettaKernelKindResultPrototype.products := by
    simp [mettaKernelKindResultPrototype, kindTypeKind]
  have impossible : Srt.type = Srt.kind :=
    functional kindTypeType (fromConstruction.2 _ constructionRule)
      kindTypeKind (fromPrototype.2 _ prototypeRule) rfl rfl
  exact Srt.noConfusion impossible

/-! ## Coarse semantic reconciliation

A semantic observation may forget the distinction between result sorts even
when the source PTS cannot.  The following intentionally weak notion records
only the result-sort observation; it is not a model of typing or conversion.
-/

/-- Product formation is functional after observing its result sorts. -/
def ResultFunctionalUnder {Meaning : Type u} (observe : Srt → Meaning)
    (profile : Profile) : Prop :=
  ∀ first ∈ profile.products, ∀ second ∈ profile.products,
    first.domain = second.domain → first.codomain = second.codomain →
      observe first.result = observe second.result

/-- The CoC/prototype union is result-functional under an observation exactly
when that observation identifies `Type` and `Kind`. -/
theorem constructionMettaKernelPrototypeUnion_resultFunctionalUnder_iff
    {Meaning : Type u} (observe : Srt → Meaning) :
    ResultFunctionalUnder observe constructionMettaKernelPrototypeUnion ↔
      observe .type = observe .kind := by
  constructor
  · intro functional
    exact functional kindTypeType (by decide) kindTypeKind (by decide) rfl rfl
  · intro sortsEqual first firstMember second secondMember domains codomains
    simp [constructionMettaKernelPrototypeUnion, constructionProducts,
      constructions] at firstMember secondMember
    rcases firstMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases secondMember with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [typeTypeType, typeKindKind, kindTypeType, kindTypeKind,
        kindKindKind]

/-- A one-point observation reconciles the two result sorts, while proving no
typing or consistency fact. -/
theorem constant_observation_reconciles
    {Meaning : Type u} (point : Meaning) :
    ResultFunctionalUnder (fun _ => point)
      constructionMettaKernelPrototypeUnion :=
  (constructionMettaKernelPrototypeUnion_resultFunctionalUnder_iff _).2 rfl

/-- A faithful observation cannot reconcile the conflicting result sorts. -/
theorem injective_observation_does_not_reconcile
    {Meaning : Type u} {observe : Srt → Meaning}
    (faithful : Function.Injective observe) :
    ¬ ResultFunctionalUnder observe constructionMettaKernelPrototypeUnion := by
  intro functional
  have observed :=
    (constructionMettaKernelPrototypeUnion_resultFunctionalUnder_iff observe).1
      functional
  exact Srt.noConfusion (faithful observed)

/-- The two retained upper fibres. -/
inductive Branch where
  | construction
  | mettaKernelPrototype
  deriving DecidableEq, Repr

def branchProfile : Branch → Profile
  | .construction => profileOfProducts constructionProducts
  | .mettaKernelPrototype => mettaKernelKindResultPrototype

theorem branchProfile_functional (branch : Branch) :
    Functional (branchProfile branch) := by
  cases branch with
  | construction =>
      unfold Functional branchProfile profileOfProducts constructionProducts
      exact Mettapedia.GSLT.Dedukti.ConstructionsModel.functional
  | mettaKernelPrototype =>
      unfold branchProfile Functional
      decide

/-- Exact common formation fragment of the two branches. -/
def sharedProfile : Profile :=
  profileOfProducts sharedDependentOperatorProducts

theorem shared_subsumed_branch (branch : Branch) :
    sharedProfile ⊑ branchProfile branch := by
  cases branch <;> constructor
  · intro source target known
    exact known
  · intro rule member
    exact (construction_mettaKernelPrototype_common_product_iff rule).2 member |>.1
  · intro source target known
    exact known
  · intro rule member
    exact (construction_mettaKernelPrototype_common_product_iff rule).2 member |>.2

/-- The existing exact checker selected by the branch index. -/
def checkProof (branch : Branch) (signature : Signature) (context : Context) :
    Proof → Term → Term → Bool :=
  Mettapedia.GSLT.LanguageDef.LFProfileChecker.checkProof
    (branchProfile branch) signature context

theorem exists_checkProof_iff_deriv {branch : Branch} {signature : Signature}
    {context : Context} {term type : Term} :
    (∃ proof, checkProof branch signature context proof term type = true) ↔
      Deriv (branchProfile branch) signature context term type :=
  Mettapedia.GSLT.LanguageDef.LFProfileChecker.exists_checkProof_iff_deriv

/-- Any finite proof accepted in the exact common fragment has accepted proof
evidence in both upper fibres. -/
theorem shared_evidence_rechecks_both
    {signature : Signature} {context : Context}
    {proof : Proof} {term type : Term}
    (checked : Mettapedia.GSLT.LanguageDef.LFProfileChecker.checkProof
      sharedProfile signature context
      proof term type = true) :
    (∃ constructionProof,
        checkProof .construction signature context constructionProof term type = true) ∧
      ∃ prototypeProof,
        checkProof .mettaKernelPrototype signature context prototypeProof term type = true := by
  have derived :=
    Mettapedia.GSLT.LanguageDef.LFProfileChecker.checkProof_sound checked
  constructor
  · exact Mettapedia.GSLT.LanguageDef.LFProfileChecker.exists_checkProof_of_deriv
      (derived.mono (shared_subsumed_branch .construction))
  · exact Mettapedia.GSLT.LanguageDef.LFProfileChecker.exists_checkProof_of_deriv
      (derived.mono (shared_subsumed_branch .mettaKernelPrototype))

/-- The two modes remain observably different: the CoC branch supports the
selected direct interfaces, while the MettaKernel prototype does not. -/
theorem construction_interface_separates_branches
    (steps : Mettapedia.GSLT.Dedukti.PTerm →
      Mettapedia.GSLT.Dedukti.PTerm → Prop) :
    DirectFormationInterfaces (branchProfile .construction).products steps ∧
      ¬ DirectFormationInterfaces (branchProfile .mettaKernelPrototype).products steps := by
  exact ⟨(directFormationInterfaces_iff_contains_constructionProducts _ _).2
      (fun _ known => known),
    mettaKernelPrototype_does_not_support_directFormationInterfaces steps⟩

/-- The prototype contains the rule list computed while inferring the corpus
at that prototype, whereas CoC does not contain that list.  This separates
profile-specific demand records, not typability of the raw statements. -/
theorem prototype_computedDemand_separates_profiles :
    ContainsDTTBench (branchProfile .mettaKernelPrototype) ∧
      ¬ ContainsDTTBench (branchProfile .construction) :=
  ⟨mettaKernelPrototype_contains_DTTBench, constructions_do_not_contain_DTTBench⟩

#print axioms no_functional_common_upper
#print axioms constructionMettaKernelPrototypeUnion_resultFunctionalUnder_iff
#print axioms constant_observation_reconciles
#print axioms injective_observation_does_not_reconcile
#print axioms branchProfile_functional
#print axioms shared_subsumed_branch
#print axioms exists_checkProof_iff_deriv
#print axioms shared_evidence_rechecks_both
#print axioms construction_interface_separates_branches
#print axioms prototype_computedDemand_separates_profiles

end Mettapedia.TypeTheory.HypercubeProfileStratification
