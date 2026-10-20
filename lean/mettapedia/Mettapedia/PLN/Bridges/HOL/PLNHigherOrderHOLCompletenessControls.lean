import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
import Mettapedia.Logic.HOL.TermModel.HenkinCompletenessControls
import Mettapedia.PLN.Bridges.HOL.PLNHeytingHOLWorldModelBridge

/-!
# Controls for the classical HO-PLN completeness bridges

Concrete instances of the classical HOL theorems of `PLNWorldModelHOLCompleteness`,
`PLNHigherOrderHOLCompletenessTightness` and `DefinableCuts.Core`. Every one takes the same
hypotheses: a surjective body enumeration, consistency, parameter-freeness of the theory and
of the query, and provability of the excluded-middle schema. The theory used here is
`HenkinCompletenessControls.excludedMiddleTheory`, the single axiom `∀ p : prop, p ∨ ¬ p`
over the propositional signature with parameters, which meets all of them.

Positive:
* a theory member gets singleton strength `1` (`member_strength_one`);
* the proof-tight interval of `⊤` collapses to a point (`top_width_zero`), and the interval
  of `p₀ ∨ ¬ p₀` has lower endpoint `1` (`excludedMiddle_atom_lower_one`);
* semantic implication on theory models gives provability (`atom_imp_self_provable`).

Positive, original signature: the bridge over `Const` through `SevenVirtues` applies to the
theory `{p₀}` over the propositional signature (`orig_extensional_model`,
`orig_readout_atom`, `orig_member_strength_one`).

Positive, every other theorem with hypotheses in `PLNWorldModelHOLCompleteness` and
`PLNHigherOrderHOLCompletenessTightness`: each is applied to `excludedMiddleTheory` with the
undecided atom `p₀`, the provable `⊤` or the refutable `⊥` as query, or to the standard
model in which every atom is true (from `atom_imp_self_pointwise` to
`top_decided_of_theoryInterval`).

Positive, intuitionistic: the Heyting world-model readout of EM-free derivability applies
at the empty theory (`heyting_readout_atom`).

Negative:
* the theory proves neither `p₀` nor `¬ p₀`, so completeness supplies a countermodel
  (`atom_countermodel`), the interval of `p₀` has full width `1` (`atom_width_one`), and the
  indicator cut of `p₀` does not collapse (`atom_indicatorCut_width_ne_zero`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessControls

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.Logic.HOL.PropositionalSlice
open Mettapedia.Logic.HOL.HenkinCompletenessControls
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
open Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets

/-! ## World-model completeness -/

/-- **Positive control.** The excluded-middle axiom gets strength `1` in the singleton
state that completeness supplies. -/
theorem member_strength_one :
    ∃ W : ClassicalHOLState (Base := AtomBase) (Const := Atom),
      stateModelsTheory excludedMiddleTheory W ∧
        BinaryWorldModel.queryStrength
            (State := ClassicalHOLState (Base := AtomBase) (Const := Atom))
            (Query := HOLQuery (Base := AtomBase) (WithParams Atom))
            W SevenVirtues.excludedMiddle = 1 :=
  exists_singletonState_with_member_strength_one_of_consistent_classicalTheory
    atomEnum atomEnum_surjective excludedMiddleTheory_consistent
    excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema
    (Set.mem_singleton _)

/-- **Negative control.** The theory does not prove `p₀`, so completeness supplies a model
of the theory in which `p₀` is false. -/
theorem atom_countermodel :
    ∃ M : ClassicalHOLPointed (Base := AtomBase) (Const := Atom),
      (∀ ψ ∈ excludedMiddleTheory, HenkinModel.models M ψ) ∧ ¬ HenkinModel.models M atom0 :=
  exists_model_not_models_of_not_provable_classical atomEnum atomEnum_surjective
    excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema atom0_paramFree
    excludedMiddleTheory_not_provable_atom

theorem atom_imp_self_paramFree (σ : Ty AtomBase) (k : Nat) :
    NoConstOccurrence (param σ k) (.imp atom0 atom0 : ClosedFormula (WithParams Atom)) :=
  .imp (atom0_paramFree σ k) (atom0_paramFree σ k)

/-- **Positive control.** Semantic implication on the theory models gives provability. -/
theorem atom_imp_self_provable :
    ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory
      (.imp atom0 atom0) :=
  provable_imp_onTheory_of_pointwiseImpliesOn_classical atomEnum atomEnum_surjective
    excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema
    atom_imp_self_paramFree (fun _ _ h => h)

/-! ## Proof-tight credal intervals -/

/-- **Positive control.** The interval of `⊤` collapses to a point. -/
theorem top_width_zero :
    (extensionalTheoryCredalHOLFormulaIntervalOfConsistent
      (Base := AtomBase) (Const := Atom) excludedMiddleTheory atomEnum atomEnum_surjective
      excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema .top).width = 0 :=
  extensionalTheoryCredalHOLFormulaInterval_top_width_eq_zero atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema

/-- **Positive control.** The interval of `p₀ ∨ ¬ p₀` has lower endpoint `1`. -/
theorem excludedMiddle_atom_lower_one :
    (extensionalTheoryCredalHOLFormulaIntervalOfConsistent
      (Base := AtomBase) (Const := Atom) excludedMiddleTheory atomEnum atomEnum_surjective
      excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema (.or atom0 (.not atom0))).lower = 1 :=
  (extensionalTheoryCredalHOLFormulaInterval_lower_eq_one_iff_provable atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema
    (fun σ k => .or (atom0_paramFree σ k) (.not (atom0_paramFree σ k)))).mpr
    (excludedMiddleTheory_proves_emSchema _ (emClosed_mem atom0))

/-- **Negative control.** The interval of the undecided atom `p₀` is all of `[0, 1]`. -/
theorem atom_width_one :
    (extensionalTheoryCredalHOLFormulaIntervalOfConsistent
      (Base := AtomBase) (Const := Atom) excludedMiddleTheory atomEnum atomEnum_surjective
      excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema atom0).width = 1 :=
  extensionalTheoryCredalHOLFormulaInterval_width_eq_one_of_undecided atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema atom0_paramFree
    excludedMiddleTheory_not_provable_atom excludedMiddleTheory_not_provable_not_atom

/-! ## Definable cuts -/

/-- The indicator score of `p₀`, cut at threshold `1`. -/
noncomputable def atomIndicatorCut :
    ExtensionalDefinableCut (Base := AtomBase) (Const := Atom) excludedMiddleTheory :=
  formulaIndicatorGeOneCut atom0 atom0_paramFree

/-- **Negative control.** The indicator cut of the undecided atom does not collapse. -/
theorem atom_indicatorCut_width_ne_zero :
    (atomIndicatorCut.intervalOfConsistent atomEnum atomEnum_surjective
      excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema).width ≠ 0 := fun hWidth =>
  ((ExtensionalDefinableCut.width_eq_zero_iff_decides atomIndicatorCut atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema).mp hWidth).elim
    excludedMiddleTheory_not_provable_atom excludedMiddleTheory_not_provable_not_atom

/-! ## The original-signature bridge -/

/-- **Positive control.** An extensional model of `{p₀}` over the propositional signature
itself, through `SevenVirtues.exists_model_of_consistent`. -/
theorem orig_extensional_model :
    ∃ M : HenkinModel.{0, 0, 0} AtomBase Atom, modelsExtTheoryOrig atomTheory M :=
  exists_extensional_model_of_consistent_orig atomInhabitants atomTheory_consistent

/-- **Positive control.** The original-signature readout of classical provability. -/
theorem orig_readout_atom :
    type_of% (provable_imp_iff_singletonStrengthLEOn_orig (Base := AtomBase) (Const := Atom)
      atomInhabitants atomTheory (PropositionalSlice.embed (.atom 0))
      (PropositionalSlice.embed (.atom 0))) :=
  provable_imp_iff_singletonStrengthLEOn_orig atomInhabitants atomTheory
    (PropositionalSlice.embed (.atom 0)) (PropositionalSlice.embed (.atom 0))

/-- **Positive control.** The member `p₀` of `{p₀}` gets strength `1` in a singleton state
over the original signature. -/
theorem orig_member_strength_one :
    type_of% (exists_singletonState_with_member_strength_one_of_consistent_orig
      (Base := AtomBase) (Const := Atom) atomInhabitants atomTheory_consistent
      (Set.mem_singleton _)) :=
  exists_singletonState_with_member_strength_one_of_consistent_orig atomInhabitants
    atomTheory_consistent (Set.mem_singleton _)

/-! ## The intuitionistic readout -/

/-- **Positive control.** The Heyting world-model readout of EM-free derivability, at the
empty theory and the implication `p₀ → p₀`. -/
theorem heyting_readout_atom :
    type_of% (PLNHeytingHOLWorldModelBridge.provable_imp_iff_singletonStrengthLEOn
      (Base := AtomBase) (Const := Atom) (T := ∅) (fun _ h => h.elim) atom0 atom0) :=
  PLNHeytingHOLWorldModelBridge.provable_imp_iff_singletonStrengthLEOn
    (Base := AtomBase) (Const := Atom) (T := ∅) (fun _ h => h.elim) atom0 atom0

/-! ## The remaining theorems of the two completeness modules

Each remaining theorem of `PLNWorldModelHOLCompleteness` and
`PLNHigherOrderHOLCompletenessTightness` with hypotheses, applied to `excludedMiddleTheory`
with the undecided atom `p₀`, the provable `⊤` or the refutable `⊥` as query, or to the
standard model in which every atom is true. -/

theorem top_paramFree (σ : Ty AtomBase) (k : Nat) :
    NoConstOccurrence (param σ k) (.top : ClosedFormula (WithParams Atom)) := .top

theorem bot_paramFree (σ : Ty AtomBase) (k : Nat) :
    NoConstOccurrence (param σ k) (.bot : ClosedFormula (WithParams Atom)) := .bot

/-- `¬ ⊥` is provable from any theory. -/
theorem provable_not_bot :
    ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory (.not .bot) :=
  ⟨[], by simp, .notI (.hyp (by simp))⟩

/-- The standard model in which every atom is true. -/
noncomputable abbrev trueModel : ClassicalHOLPointed (Base := AtomBase) (Const := Atom) :=
  standardModel fun _ => True

theorem trueModel_models_theory : ∀ ψ ∈ excludedMiddleTheory, HenkinModel.models trueModel ψ := by
  intro ψ hψ
  rw [excludedMiddleTheory, Set.mem_singleton_iff] at hψ
  subst hψ
  exact SevenVirtues.models_excludedMiddle _

theorem theoryModel_nonempty :
    Nonempty (TheoryModel (Base := AtomBase) (Const := Atom) excludedMiddleTheory) :=
  nonempty_theoryModel_of_consistent_classical atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema

theorem extensionalTheoryModel_nonempty :
    Nonempty (ExtensionalTheoryModel (Base := AtomBase) (Const := Atom) excludedMiddleTheory) :=
  nonempty_extensionalTheoryModel_of_consistent_classical atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema

/-- `p₀ → p₀` is derivable from no assumption. -/
theorem atom_imp_self_derivable :
    derivableImpOnTheory (Base := AtomBase) (Const := Atom) excludedMiddleTheory atom0 atom0 :=
  ⟨[], by simp, .impI (.hyp (by simp))⟩

theorem atom_imp_self_pointwise :
    type_of% (derivableImpOnTheory_implies_pointwiseImpliesOn atom_imp_self_derivable) :=
  derivableImpOnTheory_implies_pointwiseImpliesOn atom_imp_self_derivable

theorem atom_imp_self_strengthLE :
    type_of% (derivableImpOnTheory_implies_singletonStrengthLEOn atom_imp_self_derivable) :=
  derivableImpOnTheory_implies_singletonStrengthLEOn atom_imp_self_derivable

theorem atom_imp_self_of_strengthLE :
    ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory
      (.imp atom0 atom0) :=
  provable_imp_onTheory_of_singletonStrengthLEOn_classical atomEnum atomEnum_surjective
    excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema
    atom_imp_self_paramFree atom_imp_self_strengthLE

/-- The theory does not prove `¬ p₀`, so completeness supplies a model of `p₀`. -/
theorem atom_model :
    ∃ M : ClassicalHOLPointed (Base := AtomBase) (Const := Atom),
      (∀ ψ ∈ excludedMiddleTheory, HenkinModel.models M ψ) ∧ HenkinModel.models M atom0 :=
  exists_model_models_of_not_provable_not_classical atomEnum atomEnum_surjective
    excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema atom0_paramFree
    excludedMiddleTheory_not_provable_not_atom

theorem excludedMiddle_state :
    ∃ W : ClassicalHOLState (Base := AtomBase) (Const := Atom),
      stateModelsTheory excludedMiddleTheory W :=
  exists_singletonStateModelsTheory_of_consistent_classicalTheory atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema

theorem top_sentenceProb_one :
    type_of% (sentenceProb_singletonModelSpace_eq_one_of_models trueModel
      (HenkinModel.models_top trueModel)) :=
  sentenceProb_singletonModelSpace_eq_one_of_models trueModel (HenkinModel.models_top trueModel)

theorem bot_sentenceProb_zero :
    type_of% (sentenceProb_singletonModelSpace_eq_zero_of_not_models trueModel
      (HenkinModel.models_bot trueModel)) :=
  sentenceProb_singletonModelSpace_eq_zero_of_not_models trueModel
    (HenkinModel.models_bot trueModel)

theorem top_value_one :
    type_of% (credalHOLFormulaValue_dirac_eq_one_of_models trueModel
      (HenkinModel.models_top trueModel)) :=
  credalHOLFormulaValue_dirac_eq_one_of_models trueModel (HenkinModel.models_top trueModel)

theorem bot_value_zero :
    type_of% (credalHOLFormulaValue_dirac_eq_zero_of_not_models trueModel
      (HenkinModel.models_bot trueModel)) :=
  credalHOLFormulaValue_dirac_eq_zero_of_not_models trueModel (HenkinModel.models_bot trueModel)

theorem bot_interval_lower_zero :
    type_of% (credalHOLFormulaInterval_lower_eq_zero_of_exists_value_zero
      (ι := Unit) (fun _ => diracHierarchicalStateOfModel trueModel) .bot ⟨(), bot_value_zero⟩) :=
  credalHOLFormulaInterval_lower_eq_zero_of_exists_value_zero
    (ι := Unit) (fun _ => diracHierarchicalStateOfModel trueModel) .bot ⟨(), bot_value_zero⟩

theorem top_interval_upper_one :
    type_of% (credalHOLFormulaInterval_upper_eq_one_of_exists_value_one
      (ι := Unit) (fun _ => diracHierarchicalStateOfModel trueModel) .top ⟨(), top_value_one⟩) :=
  credalHOLFormulaInterval_upper_eq_one_of_exists_value_one
    (ι := Unit) (fun _ => diracHierarchicalStateOfModel trueModel) .top ⟨(), top_value_one⟩

theorem theoryInterval_top :
    type_of% (@theoryCredalHOLFormulaInterval_eq_const_one_of_all_models AtomBase Atom
      excludedMiddleTheory theoryModel_nonempty .top (fun M => HenkinModel.models_top M.1)) :=
  @theoryCredalHOLFormulaInterval_eq_const_one_of_all_models AtomBase Atom excludedMiddleTheory
    theoryModel_nonempty .top (fun M => HenkinModel.models_top M.1)

theorem theoryInterval_bot :
    type_of% (@theoryCredalHOLFormulaInterval_eq_const_zero_of_all_not_models AtomBase Atom
      excludedMiddleTheory theoryModel_nonempty .bot (fun M => HenkinModel.models_bot M.1)) :=
  @theoryCredalHOLFormulaInterval_eq_const_zero_of_all_not_models AtomBase Atom
    excludedMiddleTheory theoryModel_nonempty .bot (fun M => HenkinModel.models_bot M.1)

theorem extensionalInterval_member :
    type_of% (@extensionalTheoryCredalHOLFormulaInterval_eq_const_one_of_all_models AtomBase
      Atom excludedMiddleTheory extensionalTheoryModel_nonempty SevenVirtues.excludedMiddle
      (fun M => M.2.1 _ (Set.mem_singleton _))) :=
  @extensionalTheoryCredalHOLFormulaInterval_eq_const_one_of_all_models AtomBase Atom
    excludedMiddleTheory extensionalTheoryModel_nonempty SevenVirtues.excludedMiddle
    (fun M => M.2.1 _ (Set.mem_singleton _))

theorem extensionalInterval_bot :
    type_of% (@extensionalTheoryCredalHOLFormulaInterval_eq_const_zero_of_all_not_models
      AtomBase Atom excludedMiddleTheory extensionalTheoryModel_nonempty .bot
      (fun M => HenkinModel.models_bot M.1)) :=
  @extensionalTheoryCredalHOLFormulaInterval_eq_const_zero_of_all_not_models AtomBase Atom
    excludedMiddleTheory extensionalTheoryModel_nonempty .bot
    (fun M => HenkinModel.models_bot M.1)

theorem extensionalInterval_top_of_provable :
    type_of% (@extensionalTheoryCredalHOLFormulaInterval_eq_const_one_of_provable AtomBase Atom
      excludedMiddleTheory extensionalTheoryModel_nonempty .top
      (ClosedTheorySet.provable_top _)) :=
  @extensionalTheoryCredalHOLFormulaInterval_eq_const_one_of_provable AtomBase Atom
    excludedMiddleTheory extensionalTheoryModel_nonempty .top (ClosedTheorySet.provable_top _)

theorem extensionalInterval_bot_of_provable_not :
    type_of% (@extensionalTheoryCredalHOLFormulaInterval_eq_const_zero_of_provable_not AtomBase
      Atom excludedMiddleTheory extensionalTheoryModel_nonempty .bot provable_not_bot) :=
  @extensionalTheoryCredalHOLFormulaInterval_eq_const_zero_of_provable_not AtomBase Atom
    excludedMiddleTheory extensionalTheoryModel_nonempty .bot provable_not_bot

theorem trueModel_models_member :
    type_of% (models_of_provable_of_functionsRespectEqv
      (ClosedTheorySet.provable_of_mem (Set.mem_singleton SevenVirtues.excludedMiddle) :
        ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory _)
      trueModel trueModel_models_theory (standardModel_extensional _)) :=
  models_of_provable_of_functionsRespectEqv
    (ClosedTheorySet.provable_of_mem (Set.mem_singleton SevenVirtues.excludedMiddle) :
      ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory _)
    trueModel trueModel_models_theory (standardModel_extensional _)

theorem atom_theoryModel_value_zero :
    type_of% (exists_theoryModel_dirac_value_zero_of_not_provable atomEnum atomEnum_surjective
      excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema atom0_paramFree
      excludedMiddleTheory_not_provable_atom) :=
  exists_theoryModel_dirac_value_zero_of_not_provable atomEnum atomEnum_surjective
    excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema atom0_paramFree
    excludedMiddleTheory_not_provable_atom

theorem atom_theoryModel_value_one :
    type_of% (exists_theoryModel_dirac_value_one_of_not_provable_not atomEnum
      atomEnum_surjective excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema
      atom0_paramFree excludedMiddleTheory_not_provable_not_atom) :=
  exists_theoryModel_dirac_value_one_of_not_provable_not atomEnum atomEnum_surjective
    excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema atom0_paramFree
    excludedMiddleTheory_not_provable_not_atom

theorem atom_theoryInterval_lower_zero :
    type_of% (theoryCredalHOLFormulaInterval_lower_eq_zero_of_not_provable atomEnum
      atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema atom0_paramFree
      excludedMiddleTheory_not_provable_atom) :=
  theoryCredalHOLFormulaInterval_lower_eq_zero_of_not_provable atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema atom0_paramFree excludedMiddleTheory_not_provable_atom

theorem atom_theoryInterval_upper_one :
    type_of% (theoryCredalHOLFormulaInterval_upper_eq_one_of_not_provable_not atomEnum
      atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema atom0_paramFree
      excludedMiddleTheory_not_provable_not_atom) :=
  theoryCredalHOLFormulaInterval_upper_eq_one_of_not_provable_not atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema atom0_paramFree
    excludedMiddleTheory_not_provable_not_atom

theorem top_extensionalInterval_lower_one :
    type_of% (extensionalTheoryCredalHOLFormulaInterval_lower_eq_one_of_provable atomEnum
      atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema (ClosedTheorySet.provable_top _)) :=
  extensionalTheoryCredalHOLFormulaInterval_lower_eq_one_of_provable atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema (ClosedTheorySet.provable_top _)

theorem bot_extensionalInterval_upper_zero :
    type_of% (extensionalTheoryCredalHOLFormulaInterval_upper_eq_zero_of_provable_not atomEnum
      atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema provable_not_bot) :=
  extensionalTheoryCredalHOLFormulaInterval_upper_eq_zero_of_provable_not atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema provable_not_bot

theorem atom_extensionalInterval_lower_zero_iff :
    type_of% (extensionalTheoryCredalHOLFormulaInterval_lower_eq_zero_iff_not_provable atomEnum
      atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema atom0_paramFree) :=
  extensionalTheoryCredalHOLFormulaInterval_lower_eq_zero_iff_not_provable atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema atom0_paramFree

theorem atom_extensionalInterval_upper_one_iff :
    type_of% (extensionalTheoryCredalHOLFormulaInterval_upper_eq_one_iff_not_provable_not
      atomEnum atomEnum_surjective excludedMiddleTheory_consistent
      excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema atom0_paramFree) :=
  extensionalTheoryCredalHOLFormulaInterval_upper_eq_one_iff_not_provable_not atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema atom0_paramFree

theorem atom_extensionalInterval_upper_zero_iff :
    type_of% (extensionalTheoryCredalHOLFormulaInterval_upper_eq_zero_iff_provable_not atomEnum
      atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
      excludedMiddleTheory_proves_emSchema atom0_paramFree) :=
  extensionalTheoryCredalHOLFormulaInterval_upper_eq_zero_iff_provable_not atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema atom0_paramFree

theorem top_provable_of_extensionalInterval :
    ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory .top :=
  provable_of_extensionalTheoryCredalHOLFormulaInterval_lower_eq_one atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema top_paramFree top_extensionalInterval_lower_one

theorem bot_refutable_of_extensionalInterval :
    ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory (.not .bot) :=
  provable_not_of_extensionalTheoryCredalHOLFormulaInterval_upper_eq_zero atomEnum
    atomEnum_surjective excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema bot_paramFree bot_extensionalInterval_upper_zero

theorem top_theoryInterval_lower_one :
    (theoryCredalHOLFormulaIntervalOfConsistent (Base := AtomBase) (Const := Atom)
      excludedMiddleTheory atomEnum atomEnum_surjective excludedMiddleTheory_consistent
      excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema .top).lower = 1 :=
  congrArg Interval.lower theoryInterval_top

theorem bot_theoryInterval_upper_zero :
    (theoryCredalHOLFormulaIntervalOfConsistent (Base := AtomBase) (Const := Atom)
      excludedMiddleTheory atomEnum atomEnum_surjective excludedMiddleTheory_consistent
      excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema .bot).upper = 0 :=
  congrArg Interval.upper theoryInterval_bot

theorem top_theoryInterval_width_zero :
    (theoryCredalHOLFormulaIntervalOfConsistent (Base := AtomBase) (Const := Atom)
      excludedMiddleTheory atomEnum atomEnum_surjective excludedMiddleTheory_consistent
      excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema .top).width = 0 :=
  (congrArg Interval.width theoryInterval_top).trans (sub_self (1 : ℝ))

theorem top_provable_of_theoryInterval :
    ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory .top :=
  provable_of_theoryCredalHOLFormulaInterval_lower_eq_one atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema top_paramFree top_theoryInterval_lower_one

theorem bot_refutable_of_theoryInterval :
    ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory (.not .bot) :=
  provable_not_of_theoryCredalHOLFormulaInterval_upper_eq_zero atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema bot_paramFree bot_theoryInterval_upper_zero

theorem top_decided_of_theoryInterval :
    ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory .top ∨
      ClosedTheorySet.Provable (Const := WithParams Atom) excludedMiddleTheory (.not .top) :=
  decides_of_theoryCredalHOLFormulaInterval_width_eq_zero atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema top_paramFree top_theoryInterval_width_zero

#print axioms atom_imp_self_of_strengthLE
#print axioms trueModel_models_member
#print axioms top_provable_of_theoryInterval
#print axioms top_decided_of_theoryInterval
#print axioms extensionalInterval_member
#print axioms heyting_readout_atom
#print axioms orig_extensional_model
#print axioms orig_readout_atom
#print axioms orig_member_strength_one
#print axioms member_strength_one
#print axioms atom_countermodel
#print axioms atom_imp_self_provable
#print axioms top_width_zero
#print axioms excludedMiddle_atom_lower_one
#print axioms atom_width_one
#print axioms atom_indicatorCut_width_ne_zero

end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessControls
