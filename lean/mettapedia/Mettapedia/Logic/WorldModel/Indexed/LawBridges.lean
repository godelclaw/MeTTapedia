import Mettapedia.Logic.WorldModel.Indexed.Survival
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Core.GradedSelectionIrreducibility
import Mettapedia.PLN.TruthValues.PLNForcedQueries
import Mettapedia.PLN.Bridges.GSLT.EvidenceRevisionSufficiency
import Mettapedia.PLN.WorldModel.GenericWorldModelForgetting
import Mettapedia.Logic.EvidenceStateInsufficiency
import Mettapedia.TypeTheory.UniversalDependentFamilyDescent
import Mettapedia.TypeTheory.MaterialSets.MembershipEvidence
import Mettapedia.TypeTheory.IdentityNotions
import Mettapedia.Computability.ComputationalTrinityDependentDescent

/-!
# Local statements of the survival law are the general one

Each section takes one local definition of "a consumer survives a lossy map
exactly when it factors through what the map keeps", or of "every family
descends exactly when nothing is lost", and proves it equal to the general
statement in `Survival`, or derives the local theorem from the general one.

* `NonFactorization.ConstantOnFibers` and `Factors` (`constantOnFibers_iff`,
  `factors_iff_perm_invariant`).
* `GradedSelectionIrreducibility.WeightFactorsThrough`
  (`weightFactorsThrough_iff`).
* `PLNForcedQueries.FactorsThrough` (`forcedFactorsThrough_iff`).
* `EvidenceRevisionSufficiency.RevisionObservation`: the kernel-stability
  condition, stated there as necessary, is also sufficient
  (`revisionFactorsThrough_iff_kernelStable`).
* `EvidenceStateInsufficiency`: the strength-only no-go is derived from the
  failure of the revised strength to factor through strength
  (`no_strength_only_state_implements_revision_of_law`).
* `GenericWorldModelForgetting.ForgettingLayer`: every consumer of the
  out-of-scope answers is invariant under forgetting
  (`forget_preserves_outOfScope_consumers`).
* `UniversalDependentFamilyDescent.exact_iff_allFamiliesDescend` is derived
  from the general family law (`exact_iff_allFamiliesDescend_of_law`).
* `ComputationalTrinityDependentDescent`: no program-information loss is
  universal family descent, without the splitting hypothesis
  (`not_losesProgramInformation_iff_allFamiliesFactor`).
* `IdentityNotions.DescendsThrough`: all families descend through behavioural
  classes exactly when bisimilarity is equality
  (`allFamiliesDescendThrough_iff`).
* `MembershipEvidence.Descends`: universal descent is injectivity of the first
  projection (`forall_descends_iff_of_law`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Logic.WorldModel.Indexed.LawBridges

universe u v w

/-! ## `NonFactorization` -/

section NonFactorization

open Mettapedia.GSLT.Core.NonFactorization

variable {A : Type u} {S : Type v} {V : Type w}

/-- Fibre constancy is Mathlib's `Function.FactorsThrough`. -/
theorem constantOnFibers_iff (shadow : A → S) (invariant : A → V) :
    ConstantOnFibers shadow invariant ↔ invariant.FactorsThrough shadow :=
  ⟨fun h _ _ same => h _ _ same, fun h _ _ same => h same⟩

/-- Recovery from the shadow is invariance under every shadow-preserving
permutation. -/
theorem factors_iff_perm_invariant [Nonempty V] (shadow : A → S) (invariant : A → V) :
    Factors shadow invariant ↔
      ∀ σ : Equiv.Perm A, shadow ∘ σ = shadow → invariant ∘ σ = invariant :=
  (factorsThrough_iff_exists_recover shadow invariant).symm.trans
    (factorsThrough_iff_perm_invariant shadow invariant)

end NonFactorization

/-! ## `GradedSelectionIrreducibility` -/

/-- The ranking criterion is the general factorization. -/
theorem weightFactorsThrough_iff {Candidate : Type u} {Value : Type v}
    (observe : Candidate → Value) (weight : Candidate → ℕ) :
    Mettapedia.GSLT.Core.WeightFactorsThrough observe weight ↔
      weight.FactorsThrough observe :=
  Iff.rfl

/-! ## `PLNForcedQueries` -/

/-- A query forced by a statistic is a consumer factoring through it. -/
theorem forcedFactorsThrough_iff {World : Type u} {Stat : Type v} {Val : Type w} [Nonempty Val]
    (stat : World → Stat) (eval : World → Val) :
    Mettapedia.PLN.TruthValues.PLNForcedQueries.ForcedByStatistic.FactorsThrough stat eval ↔
      eval.FactorsThrough stat := by
  rw [factorsThrough_iff_exists_recover]
  exact ⟨fun ⟨p, hp⟩ => ⟨p, fun W => (hp W).symm⟩, fun ⟨p, hp⟩ => ⟨p, fun W => (hp W).symm⟩⟩

/-! ## `EvidenceRevisionSufficiency` -/

section Revision

open Mettapedia.PLN.Bridges.GSLT.EvidenceRevisionSufficiency

variable {State : Type u} {Observation : Type v} {Value : Type w}

/-- Kernel stability says that every revised readout is a consumer factoring
through the readout. -/
theorem kernelStable_iff (system : RevisionObservation State Observation Value) :
    system.KernelStable ↔
      ∀ o, (fun s => system.observe (system.revise s o)).FactorsThrough system.observe :=
  ⟨fun h o _ _ same => h _ _ o same, fun h _ _ o same => h o same⟩

/-- **The necessary condition is sufficient.** A value-level update exists
exactly when the readout's kernel is stable under revision. -/
theorem revisionFactorsThrough_iff_kernelStable
    (system : RevisionObservation State Observation Value) :
    system.FactorsThrough ↔ system.KernelStable := by
  refine ⟨RevisionObservation.kernelStable_of_factorsThrough system, fun stable => ?_⟩
  have factors := (kernelStable_iff system).1 stable
  refine ⟨fun v o => Function.extend system.observe
    (fun s => system.observe (system.revise s o)) id v, fun s o => ?_⟩
  exact (factors o).extend_apply id s

end Revision

/-! ## `EvidenceStateInsufficiency` -/

section Insufficiency

open Mettapedia.Logic.EvidenceStateInsufficiency

/-- The revised strength is a consumer of counts that does not factor through
strength: the light and heavy states collide. -/
theorem revisedStrength_not_factorsThrough :
    ¬ (fun counts : Counts => (counts.revise true).strength).FactorsThrough Counts.strength := by
  intro factors
  have same := factors (light_strength.trans heavy_strength.symm)
  simp only [light_revised_strength, heavy_revised_strength] at same
  norm_num at same

/-- The local no-go, derived from the general law: any learner whose state is
a function of strength would make the revised strength factor through
strength. -/
theorem no_strength_only_state_implements_revision_of_law
    {State : Type} (encode : ℚ → State) (step : State → State) (read : State → ℚ) :
    ¬ ∀ counts : Counts,
        read (step (encode counts.strength)) = (counts.revise true).strength := by
  intro law
  apply revisedStrength_not_factorsThrough
  intro a b same
  show (a.revise true).strength = (b.revise true).strength
  rw [← law a, ← law b, same]

end Insufficiency

/-! ## `GenericWorldModelForgetting` -/

section Forgetting

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting

variable {State Scope Query Ev : Type u}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- The answers to the questions outside a scope. -/
def outOfScopeView (F : ForgettingLayer State Scope Query Ev) (S : Scope)
    (W : State) : {q // ¬ F.inScope S q} → Ev :=
  fun q => AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q.1

/-- Forgetting a scope preserves the out-of-scope view. -/
theorem outOfScopeView_forget (F : ForgettingLayer State Scope Query Ev) (S : Scope) :
    outOfScopeView F S ∘ F.forget S = outOfScopeView F S := by
  funext W
  funext q
  exact F.outsideInvariant q.2

/-- Every consumer of the out-of-scope answers is invariant under forgetting:
forgetting is a view-equality arrow for the out-of-scope view. -/
theorem forget_preserves_outOfScope_consumers {Z : Sort v}
    (F : ForgettingLayer State Scope Query Ev) (S : Scope) (c : State → Z)
    (factors : c.FactorsThrough (outOfScopeView F S)) :
    c ∘ F.forget S = c :=
  (factorsThrough_iff_endo_invariant _ c).1 factors _ (outOfScopeView_forget F S)

end Forgetting

/-! ## `UniversalDependentFamilyDescent` -/

section SplitReadout

open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.UniversalDependentFamilyDescent

/-- The local split-readout theorem, derived from the general family law. -/
theorem exact_iff_allFamiliesDescend_of_law {Source : Type u} {Target : Type v}
    (readout : SplitReadout Source Target) :
    readout.Exact ↔ AllFamiliesDescend.{u, v, w} readout :=
  readout.exact_iff_faithful.trans (allFamiliesFactor_iff_injective.{u, v, w} readout.observe).symm

end SplitReadout

/-! ## `ComputationalTrinityDependentDescent` -/

section Trinity

open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.ComputationalTrinityDependentDescent

variable {Context : Type u} [Category.{v} Context]

/-- **No splitting needed.** A trinity comparison loses no program information
exactly when every dependent family on programs, at every context, descends
along the spatial interpretation. -/
theorem not_losesProgramInformation_iff_allFamiliesFactor
    (comparison : Comparison.{u, v, w} Context) :
    ¬ comparison.LosesProgramInformation ↔
      ∀ (context : Contextᵒᵖ) (F : comparison.program.obj context → Type w),
        Nonempty (Mettapedia.TypeTheory.DependentFamilyObserverFactorization.FamilyFactorization
          (comparison.programToSpace.app context) F) := by
  rw [not_losesProgramInformation_iff_pointwiseInjective]
  exact ⟨fun injective context => (allFamiliesFactor_iff_injective _).2 (injective context),
    fun factor context => (allFamiliesFactor_iff_injective _).1 (factor context)⟩

end Trinity

/-! ## `IdentityNotions` -/

section Identity

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner

/-- Every family of types over terms descends through the behavioural classes
of an observer exactly when the behavioural class map is injective. -/
theorem allFamiliesDescendThrough_iff {S : GSLT.{u}} (M : System.{v, w} S) :
    (∀ family : S.Term → Type u, Mettapedia.TypeTheory.IdentityNotions.DescendsThrough M family) ↔
      Function.Injective M.toBehavioralClass :=
  allFamiliesDescend_iff_injective.{u, u, u} M.toBehavioralClass

end Identity

/-! ## `MembershipEvidence` -/

section Membership

open Mettapedia.TypeTheory.MaterialSets

variable {S : Type u} {Mem : S → S → Sort v}

/-- Descent of a family on members-with-evidence is factoring through the
member. -/
theorem descends_iff_factorsThrough {X : S} {B : Sort w} (F : El Mem X → B) :
    Descends F ↔ F.FactorsThrough (PSigma.fst : El Mem X → S) :=
  ⟨fun h _ _ same => h _ _ same, fun h _ _ same => h same⟩

/-- The local universal-descent theorem, derived from the general predicate
law. -/
theorem forall_descends_iff_of_law {X : S} :
    (∀ F : El Mem X → Prop, Descends F) ↔ Function.Injective (PSigma.fst : El Mem X → S) :=
  (forall_congr' fun F => descends_iff_factorsThrough F).trans
    (allPredicatesFactor_iff_injective _)

end Membership

end Mettapedia.Logic.WorldModel.Indexed.LawBridges
