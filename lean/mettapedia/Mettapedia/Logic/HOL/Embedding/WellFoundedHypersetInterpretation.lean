import Mettapedia.Logic.HOL.Semantics.StandardTransport
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSetModel

/-!
# Full HOL interpretation in well-founded hypersets

Membership, empty set, union, power set, separation and replacement are
interpreted by operations on actual well-founded hypersets. Their comparison
with the existing `ZFSet` model preserves every HOL term, including functions
and higher-order quantifiers, and is natural in typed simultaneous substitution.

The hyperset operations are constructed independently of the set interpretation.
Replacement uses an explicit graph presentation. The comparison with Mathlib's
replacement retains that model's classical host dependency. Neither this model
nor its full-domain semantics selects a conversion policy or an axiom package
for a source calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.WellFoundedHypersetInterpretation

open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ZFSetHenkinInterpretation (Symbol set predicate mapping)

universe u

abbrev carrier (_ : Unit) : Type (u + 1) := WellFoundedPart.{u}

/-- Separation applies the predicate only to well-founded elements. -/
def separation (X : WellFoundedPart.{u}) (P : WellFoundedPart.{u} → Prop) :
    WellFoundedPart.{u} :=
  ⟨HSet.sep (fun x => ∃ h : x.WF, P ⟨x, h⟩) X.1, X.2.sep _⟩

theorem mem_separation (X x : WellFoundedPart.{u}) (P : WellFoundedPart.{u} → Prop) :
    WellFoundedPart.Mem x (separation X P) ↔ WellFoundedPart.Mem x X ∧ P x := by
  simp only [WellFoundedPart.Mem, separation, HSet.mem_sep]
  constructor
  · rintro ⟨member, _, holds⟩
    exact ⟨member, holds⟩
  · rintro ⟨member, holds⟩
    exact ⟨member, x.2, holds⟩

/-- Replacement acts on the original members, retaining their full values. -/
def replacement (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (f : WellFoundedPart.{u} → WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  (WellFoundedPart.dependentReplacement p).repl X f

def denoteSymbol (p : HSet.Presentation.{u}) :
    {A : Ty Unit} → Symbol A → Ty.denote.{0, u + 1} carrier.{u} A
  | _, .member => fun x X => .up (WellFoundedPart.Mem x X)
  | _, .empty => WellFoundedPart.empty
  | _, .union => WellFoundedPart.union.union
  | _, .power => fun X => ⟨HSet.powerset X.1, X.2.powerset⟩
  | _, .separate => fun X P => separation X (fun x => (P x).down)
  | _, .replace => replacement p

def model (p : HSet.Presentation.{u}) : HenkinModel.{0, 0, u + 1} Unit Symbol :=
  HenkinModel.standard carrier (denoteSymbol p)

theorem fullDomains (p : HSet.Presentation.{u}) : (model p).FullDomains :=
  HenkinModel.fullDomains_standard carrier (denoteSymbol p)

theorem functionsRespectEqv (p : HSet.Presentation.{u}) :
    (model p).FunctionsRespectEqv :=
  (model p).functionsRespectEqv_of_fullDomains (fullDomains p)

def baseEquiv (_ : Unit) : carrier.{u} () ≃ ZFSetHenkinInterpretation.carrier.{u} () :=
  HSet.wellFoundedPartEquivZFSet

private abbrev toSet : WellFoundedPart.{u} ≃ ZFSet.{u} :=
  HSet.wellFoundedPartEquivZFSet

theorem toSet_empty : toSet WellFoundedPart.empty = (∅ : ZFSet.{u}) := by
  apply HSet.ofZFSet_injective
  rw [WellFoundedPart.ofZFSet_equiv, HSet.ofZFSet_empty]
  rfl

theorem toSet_power (X : WellFoundedPart.{u}) :
    toSet ⟨HSet.powerset X.1, X.2.powerset⟩ = ZFSet.powerset (toSet X) := by
  apply HSet.ofZFSet_injective
  rw [WellFoundedPart.ofZFSet_equiv, HSet.ofZFSet_powerset,
    WellFoundedPart.ofZFSet_equiv]

theorem toSet_separation (X : WellFoundedPart.{u}) (P : WellFoundedPart.{u} → Prop) :
    toSet (separation X P) = ZFSet.sep (fun x => P (toSet.symm x)) (toSet X) := by
  apply ZFSet.ext
  intro z
  have read (Y : WellFoundedPart.{u}) :
      WellFoundedPart.Mem (toSet.symm z) Y ↔ z ∈ toSet Y := by
    simpa only [Equiv.apply_symm_apply] using
      (WellFoundedPart.mem_iff_zfSetModel (x := toSet.symm z) (X := Y))
  rw [← read, mem_separation, ZFSet.mem_sep, read]

theorem toSet_replacement (p : HSet.Presentation.{u}) (X : WellFoundedPart.{u})
    (f : WellFoundedPart.{u} → WellFoundedPart.{u}) :
    toSet (replacement p X f) =
      ZFSetHenkinInterpretation.replacement (toSet X) (fun z => toSet (f (toSet.symm z))) := by
  unfold replacement DependentReplacement.repl
  rw [WellFoundedPart.equiv_image]
  exact Instances.ZFSetModel.repl_eq_replacement (toSet X)
    (fun z => toSet (f (toSet.symm z)))

/-- Every set-operation constant commutes with the actual model comparison. -/
theorem constants_transport (p : HSet.Presentation.{u}) {A : Ty Unit} (constant : Symbol A) :
    StandardTransport.liftEquiv baseEquiv A ((model p).constDen constant) =
      ZFSetHenkinInterpretation.model.constDen constant := by
  cases constant with
  | member =>
      funext x X
      apply ULift.ext
      apply propext
      exact HSet.mem_wellFoundedPartEquivZFSet_symm_iff
  | empty => exact toSet_empty
  | union =>
      funext X
      exact (WellFoundedPart.equiv_union (toSet.symm X)).trans
        (congrArg ZFSet.sUnion (toSet.apply_symm_apply X))
  | power =>
      funext X
      exact (toSet_power (toSet.symm X)).trans
        (congrArg ZFSet.powerset (toSet.apply_symm_apply X))
  | separate =>
      funext X P
      change toSet (separation (toSet.symm X) (fun x => (P (toSet x)).down)) =
        ZFSet.sep (fun x => (P x).down) X
      rw [toSet_separation, toSet.apply_symm_apply X]
      congr 1
      funext x
      rw [toSet.apply_symm_apply x]
  | replace =>
      funext X f
      change toSet (replacement p (toSet.symm X) (fun x => toSet.symm (f (toSet x)))) =
        ZFSetHenkinInterpretation.replacement X f
      rw [toSet_replacement p, toSet.apply_symm_apply X]
      congr 1
      funext x
      rw [toSet.apply_symm_apply x, toSet.apply_symm_apply (f x)]

/-- The comparison covers all open HOL terms, not only closed set expressions. -/
theorem denote_transport (p : HSet.Presentation.{u}) {Γ : Ctx Unit} {A : Ty Unit}
    (term : Term Symbol Γ A) (valuation : (model p).Valuation Γ) :
    ZFSetHenkinInterpretation.model.denote term
      (StandardTransport.valuationEquiv (model p) ZFSetHenkinInterpretation.model baseEquiv Γ
        valuation) =
      StandardTransport.liftEquiv baseEquiv A ((model p).denote term valuation) :=
  StandardTransport.denote_transport _ _ (fullDomains p)
    ZFSetHenkinInterpretation.fullDomains baseEquiv (constants_transport p) term valuation

/-- Full higher-order quantification sees the same theory on both carriers. -/
theorem models_iff (p : HSet.Presentation.{u}) (formula : ClosedFormula Symbol) :
    (model p).models formula ↔ ZFSetHenkinInterpretation.model.{u}.models formula :=
  (StandardTransport.models_transport _ _ (fullDomains p)
    ZFSetHenkinInterpretation.fullDomains baseEquiv (constants_transport p) formula).symm

/-- This is a contextual comparison over every source substitution. -/
noncomputable def valuationNaturalIso (p : HSet.Presentation.{u}) :
    ContextualHenkinSemantics.valuationFunctor (model p) ≅
      ContextualHenkinSemantics.valuationFunctor ZFSetHenkinInterpretation.model :=
  StandardTransport.valuationNaturalIso _ _ baseEquiv (fullDomains p)
    ZFSetHenkinInterpretation.fullDomains (constants_transport p)

theorem setInduction_valid (p : HSet.Presentation.{u}) :
    (model p).models ZFSetHenkinInterpretation.setInduction :=
  (models_iff p _).mpr ZFSetHenkinInterpretation.setInduction_valid

/-- All rules of the retained HOL proof syntax are sound in this actual model. -/
theorem proof_sound (p : HSet.Presentation.{u}) {Γ : Ctx Unit}
    {hypotheses : List (Formula Symbol Γ)} {conclusion : Formula Symbol Γ}
    (proof : ProofSyntax Symbol hypotheses conclusion) (valuation : (model p).Valuation Γ)
    (satisfied : Soundness.SatisfiesHyps (model p) valuation hypotheses) :
    ((model p).denote conclusion valuation).down :=
  Soundness.extDerivation_sound proof.erase (functionsRespectEqv p)
    (fun _ => fullDomains p _ _) satisfied

/-- The comparison cannot be extended to identify all hypersets with this
well-founded carrier while preserving their underlying values. -/
theorem quine_not_in_carrier :
    ¬ ∃ value : carrier.{u} (), value.1 = HSet.quineAtom := by
  rintro ⟨value, same⟩
  exact WellFoundedPart.ne_quineAtom value same

end Mettapedia.Logic.HOL.Embedding.WellFoundedHypersetInterpretation
