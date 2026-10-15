import Mettapedia.OSLF.Framework.ScopedBindingInstrumentComparison
import Mettapedia.OSLF.Framework.SortedInstrumentCongruenceLogic

/-!
# Structural and modal reconstruction for binding languages

Formulas retain the complete context at each interface. Satisfaction is
defined directly using authored binding steps, original argument lists and
the original binding equation relation. Its comparison with the sorted
interpretation yields reconstruction and the partial-instrument logical
characterization. Arbitrary conjunctions require no branching condition;
the finite-conjunction specialization retains both finite-cover hypotheses.

These are the explicitly presented instrument steps. Their realization as
least enabling contexts in an interactive language remains a separate
operational admission problem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ScopedInstruments

open ScopedEncoding
open Mettapedia.OSLF.Framework

universe uAtom uLabel

variable {S : Signature} {E : EquationTheory S}

abbrev Formula (S : Signature) (Atom : Type uAtom) (Proper : Type uLabel) :=
  SortedInstrumentCongruence.Formula (signature S) Atom Proper

/-- The interpretation uses original binding data at every node. -/
def Holds (base : BaseSystem.{uAtom,uLabel} E) : {scope : Scope S} →
    Formula S base.Atom base.Label scope → Term S scope.1 scope.2 → Prop
  | _, .conj parts, value => ∀ index, Holds base (parts index) value
  | _, .neg inner, value => ¬ Holds base inner value
  | _, .atom observation, value => base.observes observation value
  | _, .proper label next inner, value =>
      ∃ target : Term S next.1 next.2, base.act label value target ∧ Holds base inner target
  | _, .node constructor clauses, value =>
      ∃ arguments : Arguments constructor, E.relation value (buildTerm constructor arguments) ∧
        ∀ position, Holds base (clauses position) (readArguments constructor arguments position)

theorem holds_encode_iff (base : BaseSystem.{uAtom,uLabel} E) {scope : Scope S}
    (formula : Formula S base.Atom base.Label scope) (value : Term S scope.1 scope.2) :
    SortedInstrumentCongruence.Holds (sortedBase base) formula (encode value) ↔
      Holds base formula value := by
  refine @SortedInstrumentCongruence.Formula.rec (signature S) base.Atom base.Label
    (fun scope formula => ∀ value : Term S scope.1 scope.2,
      SortedInstrumentCongruence.Holds (sortedBase base) formula (encode value) ↔
        Holds base formula value) ?_ ?_ ?_ ?_ ?_ scope formula value
  · intro scope Index parts inductionHypothesis value
    exact forall_congr' (fun index => inductionHypothesis index value)
  · intro scope inner inductionHypothesis value
    exact not_congr (inductionHypothesis value)
  · intro scope atom value
    simp only [Holds, SortedInstrumentCongruence.Holds, sortedBase, decode_encode]
  · intro scope label next inner inductionHypothesis value
    constructor
    · rintro ⟨target, step, postcondition⟩
      refine ⟨decode target, ?_, ?_⟩
      · simpa only [sortedBase, decode_encode] using step
      · apply (inductionHypothesis (decode target)).mp
        simpa only [encode_decode] using postcondition
    · rintro ⟨target, step, postcondition⟩
      refine ⟨encode target, ?_, (inductionHypothesis target).mpr postcondition⟩
      simpa only [sortedBase, decode_encode] using step
  · intro constructor clauses inductionHypothesis value
    constructor
    · rintro ⟨children, decomposition, postconditions⟩
      refine ⟨assemble constructor (fun position => decode (children position)), ?_, ?_⟩
      · change E.relation (decode (encode value)) (decode _) at decomposition
        rw [decode_encode, decode_node] at decomposition
        exact decomposition
      · intro position
        have postcondition := (inductionHypothesis position (decode (children position))).mp
          (by simpa only [encode_decode] using postconditions position)
        simpa only [read_assemble] using postcondition
    · rintro ⟨arguments, decomposition, postconditions⟩
      refine ⟨fun position => encode (readArguments constructor arguments position), ?_, ?_⟩
      · rw [← encode_build]
        exact (sorted_relation_encode E _ _).mpr decomposition
      · intro position
        exact (inductionHypothesis position _).mpr (postconditions position)

def LogicallyEquivalent (base : BaseSystem.{uAtom,uLabel} E) (opened : Constructor S → Prop)
    {context : Ctx S} {sort : S.Srt} (first second : Term S context sort) : Prop :=
  ∀ formula : Formula S base.Atom base.Label (context, sort), formula.Allowed opened →
    (Holds base formula first ↔ Holds base formula second)

theorem logicallyEquivalent_encode_iff (base : BaseSystem.{uAtom,uLabel} E)
    (opened : Constructor S → Prop) {scope : Scope S}
    (first second : Term S scope.1 scope.2) :
    SortedInstrumentCongruence.LogicallyEquivalent (sortedBase base) opened
        (encode first) (encode second) ↔ LogicallyEquivalent base opened first second := by
  constructor
  · intro equivalent formula allowed
    exact (holds_encode_iff base formula first).symm.trans
      ((equivalent formula allowed).trans (holds_encode_iff base formula second))
  · intro equivalent formula allowed
    exact (holds_encode_iff base formula first).trans
      ((equivalent formula allowed).trans (holds_encode_iff base formula second).symm)

/-- Reconstruction for every binding substitution congruence. -/
theorem bisimilar_iff_equation (base : BaseSystem.{uAtom,uLabel} E)
    {opened : Constructor S → Prop} (complete : ∀ constructor, opened constructor)
    {context : Ctx S} {sort : S.Srt} (first second : Term S context sort) :
    Bisimilar base opened (.term first) (.term second) ↔ E.relation first second :=
  (bisimilar_encode_iff base opened (.term first) (.term second)).symm.trans
    ((SortedInstrumentCongruence.bisimilar_iff_rel complete (encode first) (encode second)).trans
      (sorted_relation_encode E first second))

/-- Every partial kit has its exact structural-modal logic. -/
theorem logicallyEquivalent_iff_bisimilar (base : BaseSystem.{uAtom,uLabel} E)
    (opened : Constructor S → Prop) {context : Ctx S} {sort : S.Srt}
    (first second : Term S context sort) :
    LogicallyEquivalent base opened first second ↔
      Bisimilar base opened (.term first) (.term second) :=
  (logicallyEquivalent_encode_iff base opened (scope := (context, sort)) first second).symm.trans
    ((SortedInstrumentCongruence.logicallyEquivalent_iff_bisimilar
      (sortedBase base) opened (encode first) (encode second)).trans
        (bisimilar_encode_iff base opened (.term first) (.term second)))

theorem bisimilar_mono (base : BaseSystem.{uAtom,uLabel} E)
    {smaller larger : Constructor S → Prop}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {first second : State S} (related : Bisimilar base larger first second) :
    Bisimilar base smaller first second :=
  (bisimilar_encode_iff base smaller first second).mp
    (SortedInstrumentCongruence.bisimilar_mono inclusion
      ((bisimilar_encode_iff base larger first second).mpr related))

/-- A finite structural formula recognizes the entire equation class,
including the original variable positions under every binder. -/
theorem characteristic_iff (base : BaseSystem.{uAtom,uLabel} E)
    {context : Ctx S} {sort : S.Srt} (pattern value : Term S context sort) :
    Holds base (SortedInstrumentCongruence.characteristic (encode pattern)) value ↔
      E.relation value pattern :=
  (holds_encode_iff base (scope := (context, sort)) _ value).symm.trans
    ((SortedInstrumentCongruence.holds_characteristic_iff (sortedBase base)
      (encode pattern) (encode value)).trans (sorted_relation_encode E value pattern))

def FinitaryEquivalent (base : BaseSystem.{uAtom,uLabel} E) (opened : Constructor S → Prop)
    {context : Ctx S} {sort : S.Srt} (first second : Term S context sort) : Prop :=
  ∀ formula : Formula S base.Atom base.Label (context, sort), formula.Allowed opened → formula.Finitary →
    (Holds base formula first ↔ Holds base formula second)

/-- Finite conjunctions retain the finite covers of authored successors and
of admitted equation decompositions in the complete scoped presentation. -/
theorem finitaryEquivalent_iff_bisimilar (base : BaseSystem.{uAtom,uLabel} E)
    {opened : Constructor S → Prop}
    (authored : SortedInstrumentCongruence.FiniteAuthoredBranching (sortedBase base))
    (decompositions : SortedInstrumentCongruence.FiniteDecompositions (sortedTheory E) opened)
    {context : Ctx S} {sort : S.Srt} (first second : Term S context sort) :
    FinitaryEquivalent base opened first second ↔
      Bisimilar base opened (.term first) (.term second) := by
  have adequate := (SortedInstrumentCongruence.finitaryEquivalent_iff_bisimilar
    authored decompositions (encode first) (encode second)).trans
      (bisimilar_encode_iff base opened (.term first) (.term second))
  constructor
  · intro equivalent
    apply adequate.mp
    intro formula allowed finitary
    exact (holds_encode_iff base formula first).trans
      ((equivalent formula allowed finitary).trans (holds_encode_iff base formula second).symm)
  · intro related formula allowed finitary
    exact (holds_encode_iff base formula first).symm.trans
      ((adequate.mpr related formula allowed finitary).trans (holds_encode_iff base formula second))

end Mettapedia.OSLF.Binding.ScopedInstruments
