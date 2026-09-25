import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizCommutatorSoundness

/-!
# OUR soundness of every row of the corrected relation operator

The integrated value of a relation row on a gauge background is the integral
of its value.  Every generator row of the Leibniz-corrected physical relation
operator has integrated value zero:

* field antisymmetry, from `F_νμ = -F_μν`;
* the innermost Bianchi row, from `D_λ F_μν + D_μ F_νλ + D_ν F_λμ = 0`;
* the integrated total derivative, from the covariant product rule and the
  vanishing of the integral on derivatives;
* the traceless one-letter trace, the adjacent trace anticommutator and the
  fundamental three-cut trace, from the `2 × 2` trace identities for traceless
  letters;
* the Leibniz-correct commutator, from
  `HypercubicDimension16LeibnizCommutatorSoundness`;
* on shell, the equation-of-motion row, from `∑_κ D_κ F_κν = 0`.

Each integrated evaluation therefore vanishes on the whole corrected relation
submodule, off shell on every background and on shell on every background
satisfying the Yang–Mills equations.  The four-field commutator row of the
earlier operator has integrated value `64` on a constant background, so it is
not in the off-shell corrected relation submodule, although it is a row of the
earlier operator.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationRowSoundness

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16DifferentialRelations
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16TraceEvaluation
open HypercubicDimension16BackgroundCalculus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16LeibnizCommutator
open HypercubicDimension16LeibnizRelationOperator
open HypercubicDimension16CommutatorRowEvaluation
open HypercubicDimension16LeibnizCommutatorSoundness

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-! ## Letters are traceless -/

theorem letterMatrix_traceless (bg : GaugeBackground S) {fieldCount d : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount d) (field : Fin fieldCount) :
    (letterMatrix bg sector field).trace = 0 := by
  unfold letterMatrix
  generalize (normalizedSectorData sector).derivativeFamily.1 field = word
  induction word with
  | nil => exact bg.curvature_traceless _ _
  | cons axis rest ih => exact bg.covDeriv_traceless axis _ ih

/-! ## The integrated value -/

/-- OUR integrated value of a relation row on a background. -/
def integratedValue (bg : GaugeBackground S) : RelationSpace →ₗ[ℚ] ℚ :=
  bg.scalars.integral.comp (relationValue bg)

theorem integratedValue_of_relationValue (bg : GaugeBackground S) (row : RelationSpace)
    (hrow : relationValue bg row = 0) : integratedValue bg row = 0 := by
  simp [integratedValue, hrow]

/-! ## Trace rewirings keep every letter -/

theorem letterMatrix_setTraceOrder (bg : GaugeBackground S) (carrier : RelationCarrier)
    (traceOrder : Equiv.Perm (Fin carrier.1.1)) :
    letterMatrix bg (setTraceOrder carrier traceOrder).2 = letterMatrix bg carrier.2 :=
  rfl

theorem relationValue_tracelessLetterRow (bg : GaugeBackground S)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (hsingleton : IsSingletonTrace carrier field) :
    relationValue bg (tracelessLetterRow carrier field) = 0 := by
  simp only [tracelessLetterRow, relationValue_single, one_smul]
  unfold carrierValue
  rw [tracePermutationContraction_fixedPoint _ _ field hsingleton,
    letterMatrix_traceless, zero_mul]

theorem relationValue_traceAnticommutatorRow (bg : GaugeBackground S)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    relationValue bg (traceAnticommutatorRow site) = 0 := by
  simp only [traceAnticommutatorRow, map_sub, map_add, relationValue_single, one_smul]
  exact tracePermutationContraction_traceAnticommutatorSite (letterMatrix bg carrier.2)
    (letterMatrix_traceless bg carrier.2) site

theorem relationValue_fundamentalTraceRow (bg : GaugeBackground S)
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    relationValue bg (fundamentalTraceRow site) = 0 := by
  simp only [fundamentalTraceRow, map_sub, map_add, relationValue_single, one_smul]
  exact tracePermutationContraction_fundamentalTraceSite (letterMatrix bg carrier.2) site

/-! ## Field antisymmetry -/

theorem letterMatrix_swapFieldAxes_apply (bg : GaugeBackground S) (carrier : RelationCarrier)
    (slot field : Fin carrier.1.1) :
    letterMatrix bg (swapExactFieldAxes carrier slot).2 field =
      Function.update (letterMatrix bg carrier.2) slot (-(letterMatrix bg carrier.2 slot))
        field := by
  by_cases hfield : field = slot
  · subst hfield
    rw [Function.update_self]
    refine (letterMatrix_eq_wordFold bg _ _).trans ?_
    rw [letterMatrix_eq_wordFold, ← map_neg, ← bg.curvature_antisymm]
    change wordFold bg carrier.2.derivativeWord.axisAtPosition _
        (bg.curvature (Function.update carrier.2.fieldFirst field (carrier.2.fieldSecond field) field)
          (Function.update carrier.2.fieldSecond field (carrier.2.fieldFirst field) field)) = _
    rw [Function.update_self, Function.update_self]
    rfl
  · rw [Function.update_of_ne hfield]
    refine (letterMatrix_eq_wordFold bg _ _).trans ?_
    refine Eq.trans ?_ (letterMatrix_eq_wordFold bg carrier.2 field).symm
    change wordFold bg carrier.2.derivativeWord.axisAtPosition _
        (bg.curvature (Function.update carrier.2.fieldFirst slot (carrier.2.fieldSecond slot) field)
          (Function.update carrier.2.fieldSecond slot (carrier.2.fieldFirst slot) field)) = _
    rw [Function.update_of_ne hfield, Function.update_of_ne hfield]
    rfl

theorem letterMatrix_swapFieldAxes (bg : GaugeBackground S) (carrier : RelationCarrier)
    (slot : Fin carrier.1.1) :
    letterMatrix bg (swapExactFieldAxes carrier slot).2 =
      Function.update (letterMatrix bg carrier.2) slot (-(letterMatrix bg carrier.2 slot)) :=
  funext (letterMatrix_swapFieldAxes_apply bg carrier slot)

theorem relationValue_fieldAntisymmetryRow (bg : GaugeBackground S)
    (carrier : RelationCarrier) (slot : Fin carrier.1.1) :
    relationValue bg (fieldAntisymmetryRow carrier slot) = 0 := by
  simp only [fieldAntisymmetryRow, map_add, relationValue_single, one_smul]
  unfold carrierValue
  rw [letterMatrix_swapFieldAxes]
  change tracePermutationContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder +
      tracePermutationContraction
        (Function.update (letterMatrix bg carrier.2) slot (-(letterMatrix bg carrier.2 slot)))
        carrier.2.trace.traceOrder = 0
  rw [contraction_update_neg, contraction_update_self, add_neg_cancel]

/-! ## Rows at an innermost derivative: Bianchi and the equation of motion -/

/-- OUR positions of a field before its innermost derivative. -/
def innermostPrefix (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    List (Fin (dimension16DerivativeCount carrier.1)) :=
  (List.finRange _).filter fun other =>
    carrier.2.derivativeWord.ownerAtPosition other = field ∧ other < position

theorem innermost_decompose (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (hinner : IsInnermostDerivative carrier field position) :
    (List.finRange _).filter (fun other =>
        carrier.2.derivativeWord.ownerAtPosition other = field) =
      innermostPrefix carrier field position ++ [position] := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact (List.pairwise_lt_finRange _).filter _
  · rw [List.pairwise_append]
    refine ⟨(List.pairwise_lt_finRange _).filter _, List.pairwise_singleton _ _, ?_⟩
    intro first hfirst second hsecond
    rw [List.mem_singleton] at hsecond
    subst second
    simp only [innermostPrefix, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hfirst
    exact hfirst.2
  · intro other
    simp only [innermostPrefix, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, List.mem_append, List.mem_singleton]
    constructor
    · intro howner
      rcases lt_trichotomy other position with hlt | heq | hgt
      · exact Or.inl ⟨howner, hlt⟩
      · exact Or.inr heq
      · exact absurd howner (hinner.2 other hgt)
    · rintro (⟨howner, _⟩ | rfl)
      · exact howner
      · exact hinner.1

theorem letterMatrix_innermost (bg : GaugeBackground S) (carrier : RelationCarrier)
    (field : Fin carrier.1.1) (position : Fin (dimension16DerivativeCount carrier.1))
    (hinner : IsInnermostDerivative carrier field position) :
    letterMatrix bg carrier.2 field =
      wordFold bg carrier.2.derivativeWord.axisAtPosition
        (innermostPrefix carrier field position)
        (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition position)
          (bg.curvature (carrier.2.fieldFirst field) (carrier.2.fieldSecond field))) := by
  rw [letterMatrix_eq_wordFold, innermost_decompose carrier field position hinner,
    wordFold_append, wordFold_cons, wordFold_nil]

theorem letterMatrix_setFieldDerivativeAxes_apply (bg : GaugeBackground S)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (hinner : IsInnermostDerivative carrier field position)
    (derivativeAxis first second : Fin 4) (other : Fin carrier.1.1) :
    letterMatrix bg (setFieldDerivativeAxes carrier field position derivativeAxis first second).2
        other =
      Function.update (letterMatrix bg carrier.2) field
        (wordFold bg carrier.2.derivativeWord.axisAtPosition
          (innermostPrefix carrier field position)
          (bg.covDeriv derivativeAxis (bg.curvature first second))) other := by
  by_cases hother : other = field
  · subst hother
    rw [Function.update_self]
    refine (letterMatrix_eq_wordFold bg _ _).trans ?_
    change wordFold bg
        (Function.update carrier.2.derivativeWord.axisAtPosition position derivativeAxis)
        ((List.finRange _).filter fun p =>
          decide (carrier.2.derivativeWord.ownerAtPosition p = other))
        (bg.curvature (Function.update carrier.2.fieldFirst other first other)
          (Function.update carrier.2.fieldSecond other second other)) = _
    rw [innermost_decompose carrier other position hinner, wordFold_append,
      wordFold_cons, wordFold_nil, Function.update_self, Function.update_self,
      Function.update_self]
    apply wordFold_congr
    intro p hp
    have hlt : p < position := by
      simp only [innermostPrefix, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq] at hp
      exact hp.2
    exact Function.update_of_ne (ne_of_lt hlt) _ _
  · rw [Function.update_of_ne hother]
    refine (letterMatrix_eq_wordFold bg _ _).trans ?_
    refine Eq.trans ?_ (letterMatrix_eq_wordFold bg carrier.2 other).symm
    change wordFold bg
        (Function.update carrier.2.derivativeWord.axisAtPosition position derivativeAxis)
        ((List.finRange _).filter fun p =>
          decide (carrier.2.derivativeWord.ownerAtPosition p = other))
        (bg.curvature (Function.update carrier.2.fieldFirst field first other)
          (Function.update carrier.2.fieldSecond field second other)) = _
    rw [Function.update_of_ne hother, Function.update_of_ne hother]
    apply wordFold_congr
    intro p hp
    have howner : carrier.2.derivativeWord.ownerAtPosition p = other := by
      simpa using hp
    have hne : p ≠ position := by
      rintro rfl
      exact hother (howner.symm.trans hinner.1)
    exact Function.update_of_ne hne _ _

theorem letterMatrix_setFieldDerivativeAxes (bg : GaugeBackground S)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (hinner : IsInnermostDerivative carrier field position)
    (derivativeAxis first second : Fin 4) :
    letterMatrix bg (setFieldDerivativeAxes carrier field position derivativeAxis first second).2 =
      Function.update (letterMatrix bg carrier.2) field
        (wordFold bg carrier.2.derivativeWord.axisAtPosition
          (innermostPrefix carrier field position)
          (bg.covDeriv derivativeAxis (bg.curvature first second))) :=
  funext (letterMatrix_setFieldDerivativeAxes_apply bg carrier field position hinner
    derivativeAxis first second)

theorem carrierValue_setFieldDerivativeAxes (bg : GaugeBackground S)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (hinner : IsInnermostDerivative carrier field position)
    (derivativeAxis first second : Fin 4) :
    carrierValue bg (setFieldDerivativeAxes carrier field position derivativeAxis first second) =
      slotContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder field
        (wordFold bg carrier.2.derivativeWord.axisAtPosition
          (innermostPrefix carrier field position)
          (bg.covDeriv derivativeAxis (bg.curvature first second))) := by
  unfold carrierValue
  rw [letterMatrix_setFieldDerivativeAxes bg carrier field position hinner]
  rfl

theorem relationValue_bianchiRow (bg : GaugeBackground S) (carrier : RelationCarrier)
    (field : Fin carrier.1.1) (position : Fin (dimension16DerivativeCount carrier.1))
    (hinner : IsInnermostDerivative carrier field position) :
    relationValue bg (bianchiRow carrier field position) = 0 := by
  simp only [bianchiRow, map_add, relationValue_single, one_smul]
  have hsource : carrierValue bg carrier =
      slotContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder field
        (letterMatrix bg carrier.2 field) := by
    rw [slotContraction_apply, Function.update_eq_self]
    rfl
  rw [hsource, bianchiRotateOne, bianchiRotateTwo,
    carrierValue_setFieldDerivativeAxes bg carrier field position hinner,
    carrierValue_setFieldDerivativeAxes bg carrier field position hinner,
    letterMatrix_innermost bg carrier field position hinner, ← map_add, ← map_add,
    ← map_add, ← map_add, bg.bianchi, map_zero, map_zero]

/-- OUR on-shell condition: the Euclidean Yang–Mills equations. -/
def IsOnShell (bg : GaugeBackground S) : Prop :=
  ∀ ν : Fin 4, ∑ κ : Fin 4, bg.covDeriv κ (bg.curvature κ ν) = 0

theorem relationValue_eomRow (bg : GaugeBackground S) (hshell : IsOnShell bg)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (hinner : IsInnermostDerivative carrier field position) :
    relationValue bg (eomRow carrier field position) = 0 := by
  simp only [eomRow, map_sum, relationValue_single, one_smul, eomTerm]
  simp only [carrierValue_setFieldDerivativeAxes bg carrier field position hinner]
  rw [← map_sum, ← map_sum, hshell, map_zero, map_zero]

/-! ## Integrated total derivatives -/

/-- OUR letters with the derivative at `position` removed from its owner. -/
def reducedLetters (bg : GaugeBackground S) (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1)) (field : Fin carrier.1.1) : Mat S :=
  wordFold bg carrier.2.derivativeWord.axisAtPosition
    ((List.finRange _).filter fun other =>
      carrier.2.derivativeWord.ownerAtPosition other = field ∧ other ≠ position)
    (bg.curvature (carrier.2.fieldFirst field) (carrier.2.fieldSecond field))

theorem letterMatrix_setDerivativeOwner_apply (bg : GaugeBackground S)
    (carrier : RelationCarrier) (position : Fin (dimension16DerivativeCount carrier.1))
    (houter : IsGloballyOutermostDerivative carrier position) (field other : Fin carrier.1.1) :
    letterMatrix bg (setDerivativeOwner carrier position field).2 other =
      Function.update (reducedLetters bg carrier position) field
        (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition position)
          (reducedLetters bg carrier position field)) other := by
  refine (letterMatrix_eq_wordFold bg _ _).trans ?_
  change wordFold bg carrier.2.derivativeWord.axisAtPosition
      ((List.finRange _).filter fun p =>
        decide (Function.update carrier.2.derivativeWord.ownerAtPosition position field p = other))
      (bg.curvature (carrier.2.fieldFirst other) (carrier.2.fieldSecond other)) = _
  by_cases hother : other = field
  · subst hother
    rw [Function.update_self]
    have hpositions :
        ((List.finRange (dimension16DerivativeCount carrier.1)).filter fun p =>
            decide (Function.update carrier.2.derivativeWord.ownerAtPosition position other p =
              other)) =
          position :: (List.finRange _).filter fun p =>
            decide (carrier.2.derivativeWord.ownerAtPosition p = other ∧ p ≠ position) := by
      apply eq_of_pairwise_lt_of_mem_iff
      · exact (List.pairwise_lt_finRange _).filter _
      · rw [List.pairwise_cons]
        refine ⟨?_, (List.pairwise_lt_finRange _).filter _⟩
        intro p hp
        simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hp
        exact lt_of_le_of_ne (houter p) (Ne.symm hp.2)
      · intro p
        simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
          List.mem_cons]
        by_cases hp : p = position
        · subst hp
          simp
        · simp [hp]
    rw [hpositions, wordFold_cons]
    rfl
  · rw [Function.update_of_ne hother]
    unfold reducedLetters
    congr 2
    apply List.filter_congr
    intro p _
    by_cases hp : p = position
    · subst hp
      simp [Ne.symm hother]
    · simp [hp]

theorem letterMatrix_setDerivativeOwner (bg : GaugeBackground S) (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (houter : IsGloballyOutermostDerivative carrier position) (field : Fin carrier.1.1) :
    letterMatrix bg (setDerivativeOwner carrier position field).2 =
      Function.update (reducedLetters bg carrier position) field
        (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition position)
          (reducedLetters bg carrier position field)) :=
  funext (letterMatrix_setDerivativeOwner_apply bg carrier position houter field)

theorem integratedValue_integrationByPartsRow (bg : GaugeBackground S)
    (carrier : RelationCarrier) (position : Fin (dimension16DerivativeCount carrier.1))
    (houter : IsGloballyOutermostDerivative carrier position) :
    integratedValue bg (integrationByPartsRow carrier position) = 0 := by
  unfold integratedValue
  rw [LinearMap.comp_apply]
  have hvalues : ∀ field : Fin carrier.1.1,
      carrierValue bg (setDerivativeOwner carrier position field) =
        tracePermutationContraction
          (Function.update (reducedLetters bg carrier position) field
            (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition position)
              (reducedLetters bg carrier position field)))
          carrier.2.trace.traceOrder := by
    intro field
    unfold carrierValue
    rw [letterMatrix_setDerivativeOwner bg carrier position houter field]
    rfl
  have hrow : relationValue bg (integrationByPartsRow carrier position) =
      ∑ field : Fin carrier.1.1,
        tracePermutationContraction
          (Function.update (reducedLetters bg carrier position) field
            (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition position)
              (reducedLetters bg carrier position field)))
          carrier.2.trace.traceOrder := by
    simp only [integrationByPartsRow, map_sum, relationValue_single, one_smul]
    exact Finset.sum_congr rfl (fun field _ => hvalues field)
  rw [hrow]
  exact bg.integral_sum_contraction_covDeriv (carrier.2.derivativeWord.axisAtPosition position)
    (reducedLetters bg carrier position) carrier.2.trace.traceOrder

/-! ## Every row of the corrected operator -/

theorem integratedValue_leibnizPhysicalRelationRow (bg : GaugeBackground S)
    {policy : PhysicalRelationPolicy} (hshell : policy = .onShell → IsOnShell bg)
    (generator : PhysicalRelationGenerator policy) :
    integratedValue bg (leibnizPhysicalRelationRow generator) = 0 := by
  cases generator with
  | antisymmetry carrier slot =>
      exact integratedValue_of_relationValue _ _
        (relationValue_fieldAntisymmetryRow bg carrier slot)
  | bianchi carrier field position hinner =>
      exact integratedValue_of_relationValue _ _
        (relationValue_bianchiRow bg carrier field position hinner)
  | eom enabled carrier field position hinner =>
      exact integratedValue_of_relationValue _ _
        (relationValue_eomRow bg (hshell enabled) carrier field position hinner)
  | integrationByParts carrier position houter =>
      exact integratedValue_integrationByPartsRow bg carrier position houter
  | traceless carrier field hsingleton =>
      exact integratedValue_of_relationValue _ _
        (relationValue_tracelessLetterRow bg carrier field hsingleton)
  | covariantCommutator carrier site =>
      exact integratedValue_of_relationValue _ _ (relationValue_leibnizCommutatorRow site bg)
  | traceAnticommutator carrier site =>
      exact integratedValue_of_relationValue _ _ (relationValue_traceAnticommutatorRow bg site)
  | fundamentalTrace carrier site =>
      exact integratedValue_of_relationValue _ _ (relationValue_fundamentalTraceRow bg site)

/-- Every integrated evaluation vanishes on the corrected relation submodule:
off shell on every background, on shell on every on-shell background. -/
theorem leibnizPhysicalRelationSubmodule_le_ker_integratedValue (bg : GaugeBackground S)
    {policy : PhysicalRelationPolicy} (hshell : policy = .onShell → IsOnShell bg) :
    leibnizPhysicalRelationSubmodule policy ≤ LinearMap.ker (integratedValue bg) := by
  rintro value ⟨source, rfl⟩
  rw [LinearMap.mem_ker]
  induction source using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond => simp [map_add, hfirst, hsecond]
  | single generator coefficient =>
      rw [leibnizPhysicalRelationOperator_single, map_smul,
        integratedValue_leibnizPhysicalRelationRow bg hshell generator, smul_zero]

/-! ## The earlier four-field row is outside the corrected relation span -/

theorem integratedValue_defect_covariantCommutatorRow :
    integratedValue defectBackground
        (covariantCommutatorRow HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourSite) =
      64 := by
  unfold integratedValue
  rw [LinearMap.comp_apply, relationValue_covariantCommutatorRow_fieldFour]
  rfl

/-- The earlier operator's four-field commutator row is a row of that operator
but lies outside the off-shell corrected relation submodule. -/
theorem covariantCommutatorRow_fieldFour_not_mem_leibnizPhysicalRelationSubmodule :
    covariantCommutatorRow HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourSite ∉
      leibnizPhysicalRelationSubmodule .offShell := by
  intro hmem
  have hzero := leibnizPhysicalRelationSubmodule_le_ker_integratedValue defectBackground
    (policy := .offShell) (fun h => nomatch h) hmem
  rw [LinearMap.mem_ker, integratedValue_defect_covariantCommutatorRow] at hzero
  norm_num at hzero

theorem covariantCommutatorRow_fieldFour_mem_physicalRelationSubmodule
    (policy : PhysicalRelationPolicy) :
    covariantCommutatorRow HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourSite ∈
      physicalRelationSubmodule policy :=
  ⟨Finsupp.single
      (HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourCommutatorGenerator policy) 1,
    by simp [HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourCommutatorGenerator,
      physicalRelationRow]⟩

#print axioms letterMatrix_traceless
#print axioms relationValue_bianchiRow
#print axioms integratedValue_integrationByPartsRow
#print axioms integratedValue_leibnizPhysicalRelationRow
#print axioms leibnizPhysicalRelationSubmodule_le_ker_integratedValue
#print axioms covariantCommutatorRow_fieldFour_not_mem_leibnizPhysicalRelationSubmodule

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationRowSoundness
