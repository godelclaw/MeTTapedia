import Mettapedia.Logic.HOL.TermModel.HenkinCompletenessControls
import Mettapedia.Logic.HOL.Semantics.GoedelDummett
import Mettapedia.Logic.HOL.CanonicalQuantifierBridges
import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.SevenVirtues.Peano
import Mettapedia.Logic.HOL.SevenVirtues.OrderedField
import Mettapedia.Logic.HOL.SevenVirtues.StandardModels

/-!
# Witnesses for the headline HOL theorems

Each theorem below applies a published HOL theorem with every hypothesis argument a
closed term, so the hypotheses of that theorem hold together at the given data. The
theorems covered are the ones cited by the HOL completeness tower and advertised as main
results in module documentation:

* Heyting-valued and Gödel–Dummett completeness for parameter-free theories
  (`HeytingSem.provable_iff_heytingConsequence_param_free`,
  `HeytingSem.GoedelDummett.provableLC_iff_prelinearHeytingConsequence_param_free`), the
  soundness of the Heyting-valued semantics and the derivation lemmas the tower uses;
* the fresh-constant generalization `ClosedTheorySet.provable_all_intro_fresh` and the
  constant abstraction `ExtDerivation.abstractConstAt_deriv`;
* the term-model truth lemma `ClosedTheorySet.models_iff_mem` on a classical world built by
  `exists_classical_world`, and the witness-axiom existence `exists_witnessAxiom`;
* Dedekind and Huntington categoricity (`SevenVirtues.Peano.categorical`,
  `SevenVirtues.OrderedField.categorical`, `SevenVirtues.OrderedField.full_model_is_real`),
  infinity of Peano models and the transport of truth between isomorphic standard models
  (`SevenVirtues.standard_models_iff`).

The registry of these pairs is `scripts/headline_witnesses.toml`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HeadlineWitnesses

open ClosedTheorySet WithParams PropositionalSlice HenkinCompletenessControls

/-! ## Heyting-valued and Gödel–Dummett completeness -/

/-- Heyting-valued completeness at the empty theory and the atom `p₀`. -/
theorem heyting_completeness_atom :
    Provable (Const := WithParams Atom) ∅ atom0 ↔
      HeytingSem.HeytingConsequence (Base := AtomBase) ∅ atom0 :=
  HeytingSem.provable_iff_heytingConsequence_param_free (fun _ h => h.elim)

/-- Gödel–Dummett completeness at the empty theory and the atom `p₀`. -/
theorem goedelDummett_completeness_atom :
    HeytingSem.GoedelDummett.ProvableLC (Base := AtomBase) ∅ atom0 ↔
      HeytingSem.GoedelDummett.PrelinearHeytingConsequence (Base := AtomBase) ∅ atom0 :=
  HeytingSem.GoedelDummett.provableLC_iff_prelinearHeytingConsequence_param_free
    (fun _ h => h.elim)

/-- Soundness of the Heyting-valued semantics, at the Lindenbaum model of the empty
theory. -/
theorem heyting_sound_top :
    type_of% (HeytingSem.sound (Base := AtomBase) (Const := WithParams Atom) (Γ := [])
      (Δ := []) (φ := .top) .topI
      (HeytingSem.Lindenbaum.lindenbaumModel (Base := AtomBase) ∅ (fun _ h => h.elim))
      (HeytingSem.emptySubst (Base := AtomBase))) :=
  HeytingSem.sound (Δ := []) (φ := .top) .topI
    (HeytingSem.Lindenbaum.lindenbaumModel (Base := AtomBase) ∅ (fun _ h => h.elim))
    (HeytingSem.emptySubst (Base := AtomBase))

/-- The cut lemma of the Gödel–Dummett development, with one cut formula. -/
theorem goedelDummett_cut_top :
    ExtDerivation (WithParams Atom) ([] : List (ClosedFormula (WithParams Atom))) .top :=
  HeytingSem.GoedelDummett.ExtDerivation.cut_hyps (Δ₁ := [.top]) (.hyp (List.mem_singleton.mpr rfl))
    (fun _ h => by
      rw [List.mem_singleton] at h
      subst h
      exact .topI)

/-- Gödel–Dummett generalization from instances, for the body `⊤`. -/
theorem goedelDummett_all_intro_top :
    Provable (Const := WithParams Atom)
      (insert (.top : ClosedFormula (WithParams Atom))
        (∅ ∪ HeytingSem.GoedelDummett.lcSchema (Base := AtomBase) Atom))
      (.all (.top : Formula (WithParams Atom) [propTy])) :=
  HeytingSem.GoedelDummett.lc_all_intro_of_instances (fun _ h => h.elim)
    (fun _ => provable_top _)

/-! ## Fresh constants -/

/-- Generalization over a constant absent from the theory and the body. -/
theorem all_intro_fresh_top :
    Provable (Const := Atom) ∅ (.all (.top : Formula Atom [propTy])) :=
  provable_all_intro_fresh (Atom.atom 0) (fun _ h => h.elim) .top (provable_top _)

/-- Abstraction of a constant in a derivation. -/
theorem abstractConst_top :
    ExtDerivation Atom
      (([] : List (Formula Atom ([] ++ []))).map
        (abstractConstAt (Base := AtomBase) (Γ := []) (Atom.atom 0) []))
      (abstractConstAt (Base := AtomBase) (Γ := []) (Atom.atom 0) [] .top) :=
  ExtDerivation.abstractConstAt_deriv (Atom.atom 0) .topI

/-! ## The term model and witness axioms -/

/-- A classical world over `excludedMiddleTheory`. -/
theorem classicalWorld_exists :
    ∃ W : World (WithParams Atom),
      (∀ ψ ∈ witnessLimit excludedMiddleTheory atomEnum ∪ EMSchema Atom, ψ ∈ W.carrier) ∧
      (∀ χ : ClosedFormula (WithParams Atom),
        χ ∈ W.carrier ∨ (.not χ : ClosedFormula (WithParams Atom)) ∈ W.carrier) :=
  exists_classical_world atomEnum atomEnum_surjective
    (consistent_witnessLimit_union_emSchema atomEnum excludedMiddleTheory_consistent
      excludedMiddleTheory_paramFree excludedMiddleTheory_proves_emSchema)

/-- The truth lemma of the term model at that world. -/
theorem termModel_truth_atom :
    (termPreModel (Classical.choose classicalWorld_exists)
        (Classical.choose_spec classicalWorld_exists).2).models atom0 ↔
      atom0 ∈ (Classical.choose classicalWorld_exists).carrier :=
  models_iff_mem _ (Classical.choose_spec classicalWorld_exists).2 atom0

/-- The witness axiom of the body `⊤` occurs in the witnessed theory. -/
theorem witnessAxiom_top :
    ∃ k : Nat, witnessAxiom (param propTy k) (.top : Formula (WithParams Atom) [propTy]) ∈
      witnessLimit excludedMiddleTheory atomEnum :=
  exists_witnessAxiom excludedMiddleTheory atomEnum ⟨propTy, .top⟩
    (atomEnum_surjective ⟨propTy, .top⟩)

/-! ## Categoricity and standard models -/

open SevenVirtues

/-- Dedekind categoricity, between the standard model of `ℕ` and itself. -/
theorem peano_categorical_nat :
    ∃ e : (Peano.natModel.{0}).Carrier () ≃ (Peano.natModel.{0}).Carrier (),
      e (Peano.zeroOf Peano.PeanoConst.zero Peano.natModel.{0}) =
          Peano.zeroOf Peano.PeanoConst.zero Peano.natModel.{0} ∧
        ∀ x, e (Peano.succOf Peano.PeanoConst.succ Peano.natModel.{0} x) =
          Peano.succOf Peano.PeanoConst.succ Peano.natModel.{0} (e x) :=
  Peano.categorical Peano.natModel Peano.natModel (Peano.standardOf_fullDomains _)
    (Peano.standardOf_fullDomains _) Peano.natModel_models Peano.natModel_models

/-- The first two Peano axioms force an infinite carrier in the standard model. -/
theorem peano_infinite_nat : Infinite ((Peano.natModel.{0}).Carrier ()) :=
  Peano.infinite_of_models Peano.PeanoConst.zero Peano.PeanoConst.succ Peano.natModel
    (Peano.natModel_models _ (by simp [Peano.axioms]))
    (Peano.natModel_models _ (by simp [Peano.axioms]))

/-- Huntington categoricity, between the real model and itself. -/
theorem orderedField_categorical_real :
    type_of% (OrderedField.categorical OrderedField.realModel OrderedField.realModel
      OrderedField.realModel_fullDomains OrderedField.realModel_fullDomains
      OrderedField.realModel_models OrderedField.realModel_models) :=
  OrderedField.categorical OrderedField.realModel OrderedField.realModel
    OrderedField.realModel_fullDomains OrderedField.realModel_fullDomains
    OrderedField.realModel_models OrderedField.realModel_models

/-- Every full model of the ordered-field axioms is the real one, at the real model. -/
theorem orderedField_full_model_is_real_real :
    type_of% (OrderedField.full_model_is_real OrderedField.realModel
      OrderedField.realModel_fullDomains OrderedField.realModel_models) :=
  OrderedField.full_model_is_real OrderedField.realModel OrderedField.realModel_fullDomains
    OrderedField.realModel_models

/-- No constants: the signature of `standardTransport_top`. -/
abbrev NoConst : Ty Unit → Type := fun _ => Empty

/-- Isomorphic standard models agree on a sentence, at two copies of a two-element base. -/
theorem standardTransport_top.{w} :
    (HenkinModel.standard (Const := NoConst) (fun _ => ULift.{max 1 w} Bool)
        (fun {_} c => nomatch c)).models (.top : ClosedFormula NoConst) ↔
      (HenkinModel.standard (Const := NoConst) (fun _ => ULift.{max 1 w} Bool)
        (fun {_} c => nomatch c)).models (.top : ClosedFormula NoConst) :=
  standard_models_iff _ _ _ _ (fun _ => Equiv.refl _) (fun c => nomatch c) .top

#print axioms heyting_completeness_atom
#print axioms goedelDummett_completeness_atom
#print axioms heyting_sound_top
#print axioms goedelDummett_cut_top
#print axioms goedelDummett_all_intro_top
#print axioms all_intro_fresh_top
#print axioms abstractConst_top
#print axioms termModel_truth_atom
#print axioms witnessAxiom_top
#print axioms peano_categorical_nat
#print axioms peano_infinite_nat
#print axioms orderedField_categorical_real
#print axioms orderedField_full_model_is_real_real
#print axioms standardTransport_top

end Mettapedia.Logic.HOL.HeadlineWitnesses
