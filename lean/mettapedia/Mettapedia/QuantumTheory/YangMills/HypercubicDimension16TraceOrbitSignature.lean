import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16SignedOrbitCoinvariants

/-!
# An independent orbit signature for the derivative-free eight-field carrier

For every field label, record eight successive plane colors around its trace
orbit, together with the eight return-to-start bits.  Sorting the resulting
eight natural-number codes removes the field labels.  The construction is
proved invariant under the standard simultaneous field relabeling before it
is descended to the genuine orbit carrier.

The signature is only used as a separating invariant.  No completeness claim
is made, so later finite certificates cannot obtain a desired quotient by
definition.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitSignature

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants

abbrev FieldEightLabeledSector := LabeledLocalWordSector 8 0

/-- The trace permutation after relabeling intertwines the relabeling map. -/
theorem relabel_trace_apply (rename : Equiv.Perm (Fin 8))
    (sector : FieldEightLabeledSector) (field : Fin 8) :
    (sector.relabel rename).trace (rename field) =
      rename (sector.trace field) := by
  change rename
      (sector.trace (rename.symm (rename field))) =
    rename (sector.trace field)
  rw [rename.symm_apply_apply]

/-- The intertwining persists through every trace power. -/
theorem relabel_trace_pow_apply (rename : Equiv.Perm (Fin 8))
    (sector : FieldEightLabeledSector) (field : Fin 8) (power : ℕ) :
    ((sector.relabel rename).trace ^ power) (rename field) =
      rename ((sector.trace ^ power) field) := by
  induction power generalizing field with
  | zero => simp
  | succ power inductionHypothesis =>
      rw [pow_succ, Equiv.Perm.mul_apply, relabel_trace_apply,
        inductionHypothesis, pow_succ, Equiv.Perm.mul_apply]

/-- One base-twelve digit: plane color `0,...,5`, plus six precisely when the
chosen trace power returns to the starting field. -/
def fieldTraceDigit (sector : FieldEightLabeledSector)
    (field : Fin 8) (offset : Fin 8) : Nat :=
  (sector.decoration.1 ((sector.trace ^ offset.1) field)).plane.1 +
    if ((sector.trace ^ (offset.1 + 1)) field = field) then 6 else 0

/-- Fixed-width code of the colored trace orbit viewed from one field label. -/
irreducible_def fieldTraceCode (sector : FieldEightLabeledSector)
    (field : Fin 8) : Nat :=
  ∑ offset : Fin 8,
    fieldTraceDigit sector field offset * 12 ^ offset.1

theorem relabel_fieldTraceDigit (rename : Equiv.Perm (Fin 8))
    (sector : FieldEightLabeledSector) (field : Fin 8) (offset : Fin 8) :
    fieldTraceDigit (sector.relabel rename) (rename field) offset =
      fieldTraceDigit sector field offset := by
  unfold fieldTraceDigit
  rw [relabel_trace_pow_apply, relabel_trace_pow_apply]
  change
    (sector.decoration.1
        (rename.symm
          (rename ((sector.trace ^ offset.1) field)))).plane.1 +
        (if rename ((sector.trace ^ (offset.1 + 1)) field) = rename field
          then 6 else 0) = _
  rw [rename.symm_apply_apply]
  simp only [rename.injective.eq_iff]

theorem relabel_fieldTraceCode (rename : Equiv.Perm (Fin 8))
    (sector : FieldEightLabeledSector) (field : Fin 8) :
    fieldTraceCode (sector.relabel rename) (rename field) =
      fieldTraceCode sector field := by
  rw [fieldTraceCode_def, fieldTraceCode_def]
  apply Finset.sum_congr rfl
  intro offset _
  rw [relabel_fieldTraceDigit]

/-- Sorted multiset of the eight rooted trace-orbit codes. -/
irreducible_def labeledTraceSignature
    (sector : FieldEightLabeledSector) : List Nat :=
  (Finset.univ.val.map (fieldTraceCode sector)).sort (· ≤ ·)

theorem labeledTraceSignature_relabel (rename : Equiv.Perm (Fin 8))
    (sector : FieldEightLabeledSector) :
    labeledTraceSignature (sector.relabel rename) =
      labeledTraceSignature sector := by
  rw [labeledTraceSignature_def, labeledTraceSignature_def]
  apply congrArg (fun values : Multiset Nat => values.sort (· ≤ ·))
  calc
    Finset.univ.val.map (fieldTraceCode (sector.relabel rename)) =
        (Finset.univ.val.map rename).map
          (fieldTraceCode (sector.relabel rename)) := by
      rw [Multiset.map_univ_val_equiv]
    _ = Finset.univ.val.map
          (fieldTraceCode (sector.relabel rename) ∘ rename) := by
      rw [Multiset.map_map]
    _ = Finset.univ.val.map (fieldTraceCode sector) := by
      have hfunctions :
          fieldTraceCode (sector.relabel rename) ∘ rename =
            fieldTraceCode sector := by
        funext field
        exact relabel_fieldTraceCode rename sector field
      rw [hfunctions]

/-! ## A sorting-free symmetric signature -/

/-- One of the first eight power sums of the rooted trace codes.  These are
standard symmetric functions of the eight field-labelled codes. -/
def labeledTracePowerSum (sector : FieldEightLabeledSector)
    (moment : Fin 8) : Nat :=
  ∑ field : Fin 8, (fieldTraceCode sector field) ^ (moment.1 + 1)

theorem labeledTracePowerSum_relabel (rename : Equiv.Perm (Fin 8))
    (sector : FieldEightLabeledSector) (moment : Fin 8) :
    labeledTracePowerSum (sector.relabel rename) moment =
      labeledTracePowerSum sector moment := by
  unfold labeledTracePowerSum
  calc
    (∑ field : Fin 8,
        (fieldTraceCode (sector.relabel rename) field) ^ (moment.1 + 1)) =
        ∑ field : Fin 8,
          (fieldTraceCode (sector.relabel rename) (rename field)) ^
            (moment.1 + 1) :=
      (Equiv.sum_comp rename (fun field : Fin 8 =>
        (fieldTraceCode (sector.relabel rename) field) ^
          (moment.1 + 1))).symm
    _ = ∑ field : Fin 8,
          (fieldTraceCode sector field) ^ (moment.1 + 1) := by
      apply Finset.sum_congr rfl
      intro field _
      rw [relabel_fieldTraceCode]

/-- The first eight power sums of the rooted trace codes.  Over characteristic
zero they determine the underlying eight-element multiset, but only their
one-way separating property is used below. -/
def labeledTraceMomentSignature (sector : FieldEightLabeledSector) : List Nat :=
  List.ofFn fun moment : Fin 8 => labeledTracePowerSum sector moment

theorem labeledTraceMomentSignature_relabel
    (rename : Equiv.Perm (Fin 8)) (sector : FieldEightLabeledSector) :
    labeledTraceMomentSignature (sector.relabel rename) =
      labeledTraceMomentSignature sector := by
  unfold labeledTraceMomentSignature
  congr 1
  funext moment
  exact labeledTracePowerSum_relabel rename sector moment

theorem labeledTraceMomentSignature_respects_fieldRelabelOrbit
    (left right : FieldEightLabeledSector)
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin 8))
      FieldEightLabeledSector left right) :
    labeledTraceMomentSignature left =
      labeledTraceMomentSignature right := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrename⟩
  change right.relabel rename = left at hrename
  rw [← hrename, labeledTraceMomentSignature_relabel]

/-- The power-sum signature descended to the genuine field-relabel orbit
carrier. -/
def fieldEightOrbitMomentSignature : FieldEightOrbitCarrier → List Nat :=
  Quotient.lift labeledTraceMomentSignature
    labeledTraceMomentSignature_respects_fieldRelabelOrbit

@[simp] theorem fieldEightOrbitMomentSignature_mk
    (sector : FieldEightLabeledSector) :
    fieldEightOrbitMomentSignature (Quotient.mk _ sector) =
      labeledTraceMomentSignature sector :=
  rfl

/-- Reflections affect tensor signs but not the plane transport seen by the
derivative-free eight-field carrier. -/
theorem fieldEightLabeled_hypercubicAct_eq_unsigned (h : Hypercubic4)
    (sector : FieldEightLabeledSector) :
    sector.hypercubicAct h =
      sector.hypercubicAct (unsignedHypercubic h.perm) := by
  rfl

theorem fieldEightOrbit_hypercubicAct_eq_unsigned (h : Hypercubic4)
    (target : FieldEightOrbitCarrier) :
    target.hypercubicAct h =
      target.hypercubicAct (unsignedHypercubic h.perm) := by
  refine Quotient.inductionOn target ?_
  intro sector
  simp only [FieldRelabelOrbitCarrier.hypercubicAct_mk]
  exact congrArg (Quotient.mk _)
    (fieldEightLabeled_hypercubicAct_eq_unsigned h sector)

/-- The 24 unsigned axis-permutation images of the power-sum signature. -/
def unsignedMomentSignatureMultiset (target : FieldEightOrbitCarrier) :
    Multiset (List Nat) :=
  Finset.univ.val.map fun permutation : Equiv.Perm Axis =>
    fieldEightOrbitMomentSignature
      (target.hypercubicAct (unsignedHypercubic permutation))

theorem unsignedMomentSignatureMultiset_action (right : Hypercubic4)
    (target : FieldEightOrbitCarrier) :
    unsignedMomentSignatureMultiset (target.hypercubicAct right) =
      unsignedMomentSignatureMultiset target := by
  unfold unsignedMomentSignatureMultiset
  have hfunctions :
      (fun left : Equiv.Perm Axis =>
        fieldEightOrbitMomentSignature
          ((target.hypercubicAct right).hypercubicAct
            (unsignedHypercubic left))) =
        (fun combined : Equiv.Perm Axis =>
          fieldEightOrbitMomentSignature
            (target.hypercubicAct (unsignedHypercubic combined))) ∘
          Equiv.mulRight right.perm := by
    funext left
    calc
      fieldEightOrbitMomentSignature
          ((target.hypercubicAct right).hypercubicAct
            (unsignedHypercubic left)) =
          fieldEightOrbitMomentSignature
            (target.hypercubicAct (unsignedHypercubic left * right)) := by
        rw [FieldRelabelOrbitCarrier.hypercubicAct_mul]
      _ = fieldEightOrbitMomentSignature
          (target.hypercubicAct
            (unsignedHypercubic (left * right.perm))) := by
        rw [fieldEightOrbit_hypercubicAct_eq_unsigned]
        rfl
  rw [hfunctions, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

/-- Canonical minimum of the power-sum signature over the 24 unsigned axis
permutations.  Reflection-blindness makes it invariant under the full literal
hypercubic group. -/
def canonicalUnsignedMomentSignature
    (target : FieldEightOrbitCarrier) : List Nat :=
  (((unsignedMomentSignatureMultiset target).map
      (fun signature : List Nat =>
        (signature : WithTop (List Nat)))).fold min ⊤).untopD []

theorem canonicalUnsignedMomentSignature_action (right : Hypercubic4)
    (target : FieldEightOrbitCarrier) :
    canonicalUnsignedMomentSignature (target.hypercubicAct right) =
      canonicalUnsignedMomentSignature target := by
  unfold canonicalUnsignedMomentSignature
  rw [unsignedMomentSignatureMultiset_action]

/-- Unequal canonical power-sum signatures separate literal hypercubic
orbits.  No converse is built into the invariant. -/
theorem not_hypercubic_related_of_canonicalMomentSignature_ne
    (left right : FieldEightOrbitCarrier)
    (hdifferent : canonicalUnsignedMomentSignature left ≠
      canonicalUnsignedMomentSignature right) :
    ∀ h : Hypercubic4, left.hypercubicAct h ≠ right := by
  intro h hequal
  apply hdifferent
  rw [← hequal, canonicalUnsignedMomentSignature_action]

/-! ## A multiplicative symmetric fingerprint -/

/-- Evaluation at `X = 1` of the monic polynomial whose roots are the
negatives of the eight rooted trace codes.  This is a standard symmetric
polynomial of the field-labelled multiset. -/
def labeledTraceProductSignature (sector : FieldEightLabeledSector) : Nat :=
  ∏ field : Fin 8, (fieldTraceCode sector field + 1)

theorem labeledTraceProductSignature_relabel
    (rename : Equiv.Perm (Fin 8)) (sector : FieldEightLabeledSector) :
    labeledTraceProductSignature (sector.relabel rename) =
      labeledTraceProductSignature sector := by
  unfold labeledTraceProductSignature
  calc
    (∏ field : Fin 8,
        (fieldTraceCode (sector.relabel rename) field + 1)) =
        ∏ field : Fin 8,
          (fieldTraceCode (sector.relabel rename) (rename field) + 1) :=
      (Equiv.prod_comp rename (fun field : Fin 8 =>
        fieldTraceCode (sector.relabel rename) field + 1)).symm
    _ = ∏ field : Fin 8, (fieldTraceCode sector field + 1) := by
      apply Finset.prod_congr rfl
      intro field _
      rw [relabel_fieldTraceCode]

theorem labeledTraceProductSignature_respects_fieldRelabelOrbit
    (left right : FieldEightLabeledSector)
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin 8))
      FieldEightLabeledSector left right) :
    labeledTraceProductSignature left =
      labeledTraceProductSignature right := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrename⟩
  change right.relabel rename = left at hrename
  rw [← hrename, labeledTraceProductSignature_relabel]

/-- The product signature on the genuine field-relabel orbit carrier. -/
def fieldEightOrbitProductSignature : FieldEightOrbitCarrier → Nat :=
  Quotient.lift labeledTraceProductSignature
    labeledTraceProductSignature_respects_fieldRelabelOrbit

@[simp] theorem fieldEightOrbitProductSignature_mk
    (sector : FieldEightLabeledSector) :
    fieldEightOrbitProductSignature (Quotient.mk _ sector) =
      labeledTraceProductSignature sector :=
  rfl

/-- The 24 unsigned images of the multiplicative signature. -/
def unsignedProductSignatureMultiset (target : FieldEightOrbitCarrier) :
    Multiset Nat :=
  Finset.univ.val.map fun permutation : Equiv.Perm Axis =>
    fieldEightOrbitProductSignature
      (target.hypercubicAct (unsignedHypercubic permutation))

theorem unsignedProductSignatureMultiset_action (right : Hypercubic4)
    (target : FieldEightOrbitCarrier) :
    unsignedProductSignatureMultiset (target.hypercubicAct right) =
      unsignedProductSignatureMultiset target := by
  unfold unsignedProductSignatureMultiset
  have hfunctions :
      (fun left : Equiv.Perm Axis =>
        fieldEightOrbitProductSignature
          ((target.hypercubicAct right).hypercubicAct
            (unsignedHypercubic left))) =
        (fun combined : Equiv.Perm Axis =>
          fieldEightOrbitProductSignature
            (target.hypercubicAct (unsignedHypercubic combined))) ∘
          Equiv.mulRight right.perm := by
    funext left
    calc
      fieldEightOrbitProductSignature
          ((target.hypercubicAct right).hypercubicAct
            (unsignedHypercubic left)) =
          fieldEightOrbitProductSignature
            (target.hypercubicAct (unsignedHypercubic left * right)) := by
        rw [FieldRelabelOrbitCarrier.hypercubicAct_mul]
      _ = fieldEightOrbitProductSignature
          (target.hypercubicAct
            (unsignedHypercubic (left * right.perm))) := by
        rw [fieldEightOrbit_hypercubicAct_eq_unsigned]
        rfl
  rw [hfunctions, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

/-- Canonical product signature over the 24 coordinate permutations. -/
def canonicalUnsignedProductSignature
    (target : FieldEightOrbitCarrier) : Nat :=
  (((unsignedProductSignatureMultiset target).map
      (fun signature : Nat => (signature : WithTop Nat))).fold min ⊤).untopD 0

theorem canonicalUnsignedProductSignature_action (right : Hypercubic4)
    (target : FieldEightOrbitCarrier) :
    canonicalUnsignedProductSignature (target.hypercubicAct right) =
      canonicalUnsignedProductSignature target := by
  unfold canonicalUnsignedProductSignature
  rw [unsignedProductSignatureMultiset_action]

/-- Unequal canonical product signatures separate literal hypercubic orbits;
no completeness converse is asserted. -/
theorem not_hypercubic_related_of_canonicalProductSignature_ne
    (left right : FieldEightOrbitCarrier)
    (hdifferent : canonicalUnsignedProductSignature left ≠
      canonicalUnsignedProductSignature right) :
    ∀ h : Hypercubic4, left.hypercubicAct h ≠ right := by
  intro h hequal
  apply hdifferent
  rw [← hequal, canonicalUnsignedProductSignature_action]

theorem labeledTraceSignature_respects_fieldRelabelOrbit
    (left right : FieldEightLabeledSector)
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin 8))
      FieldEightLabeledSector left right) :
    labeledTraceSignature left = labeledTraceSignature right := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrename⟩
  change right.relabel rename = left at hrename
  rw [← hrename, labeledTraceSignature_relabel]

/-- The separating signature on the genuine field-relabel orbit carrier. -/
def fieldEightOrbitSignature : FieldEightOrbitCarrier → List Nat :=
  Quotient.lift labeledTraceSignature
    labeledTraceSignature_respects_fieldRelabelOrbit

@[simp] theorem fieldEightOrbitSignature_mk
    (sector : FieldEightLabeledSector) :
    fieldEightOrbitSignature (Quotient.mk _ sector) =
      labeledTraceSignature sector :=
  rfl

/-- All signature images of one carrier under the literal hypercubic group. -/
def hypercubicSignatureSet (target : FieldEightOrbitCarrier) :
    Finset (List Nat) :=
  Finset.univ.image fun h : Hypercubic4 =>
    fieldEightOrbitSignature (target.hypercubicAct h)

theorem hypercubicSignatureSet_nonempty (target : FieldEightOrbitCarrier) :
    (hypercubicSignatureSet target).Nonempty := by
  refine ⟨fieldEightOrbitSignature target, ?_⟩
  rw [hypercubicSignatureSet, Finset.mem_image]
  exact ⟨1, Finset.mem_univ _, by
    rw [FieldRelabelOrbitCarrier.hypercubicAct_one]⟩

/-- The 384 signature images with multiplicity.  This is the executable
carrier for the minimum, avoiding quadratic duplicate elimination. -/
def hypercubicSignatureMultiset (target : FieldEightOrbitCarrier) :
    Multiset (List Nat) :=
  Finset.univ.val.map fun h : Hypercubic4 =>
    fieldEightOrbitSignature (target.hypercubicAct h)

theorem hypercubicSignatureMultiset_action (right : Hypercubic4)
    (target : FieldEightOrbitCarrier) :
    hypercubicSignatureMultiset (target.hypercubicAct right) =
      hypercubicSignatureMultiset target := by
  unfold hypercubicSignatureMultiset
  have hfunctions :
      (fun left : Hypercubic4 =>
          fieldEightOrbitSignature
            ((target.hypercubicAct right).hypercubicAct left)) =
        (fun combined : Hypercubic4 =>
          fieldEightOrbitSignature (target.hypercubicAct combined)) ∘
            Equiv.mulRight right := by
    funext left
    exact congrArg fieldEightOrbitSignature
      (FieldRelabelOrbitCarrier.hypercubicAct_mul left right target).symm
  rw [hfunctions, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

/-- Canonical minimum of the independently defined signature over `H(4)`. -/
def canonicalHypercubicSignature (target : FieldEightOrbitCarrier) : List Nat :=
  (((hypercubicSignatureMultiset target).map
      (fun signature : List Nat =>
        (signature : WithTop (List Nat)))).fold min ⊤).untopD []

theorem hypercubicSignatureSet_action (right : Hypercubic4)
    (target : FieldEightOrbitCarrier) :
    hypercubicSignatureSet (target.hypercubicAct right) =
      hypercubicSignatureSet target := by
  apply Finset.ext
  intro signature
  simp only [hypercubicSignatureSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨left, rfl⟩
    refine ⟨left * right, ?_⟩
    rw [FieldRelabelOrbitCarrier.hypercubicAct_mul]
  · rintro ⟨combined, hcombined⟩
    refine ⟨combined * right⁻¹, ?_⟩
    rw [← FieldRelabelOrbitCarrier.hypercubicAct_mul]
    have hgroup : (combined * right⁻¹) * right = combined := by
      group
    rw [hgroup]
    exact hcombined

theorem canonicalHypercubicSignature_action (right : Hypercubic4)
    (target : FieldEightOrbitCarrier) :
    canonicalHypercubicSignature (target.hypercubicAct right) =
      canonicalHypercubicSignature target := by
  unfold canonicalHypercubicSignature
  rw [hypercubicSignatureMultiset_action]

/-- Different canonical signatures certify different literal hypercubic
orbits.  The converse is deliberately not asserted. -/
theorem not_hypercubic_related_of_canonicalSignature_ne
    (left right : FieldEightOrbitCarrier)
    (hdifferent : canonicalHypercubicSignature left ≠
      canonicalHypercubicSignature right) :
    ∀ h : Hypercubic4, left.hypercubicAct h ≠ right := by
  intro h hequal
  apply hdifferent
  rw [← hequal, canonicalHypercubicSignature_action]

end HypercubicDimension16TraceOrbitSignature
end YangMills
end QuantumTheory
end Mettapedia
