import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEquivariance
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticBasis
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Local derivative-word carrier at dimension sixteen

This module constructs the finite carrier which the dimension-sixteen
cycle-index expression is intended to count.  A labeled field carries one
oriented two-form component and one finite ordered word of derivative axes.
A sector consists of a trace permutation together with one such letter for
each field label, subject only to the exact total derivative degree.

Uniform field relabeling acts by conjugation on the trace permutation and by
transport on the decorated letters.  The literal hypercubic group acts on
every visible spacetime index.  The two actions are proved to commute, and
the complete tensor sign is proved invariant under field relabeling and to
satisfy the hypercubic cocycle law.  These equivariance statements precede
all orbit counting.

No Bianchi, EOM, IBP, covariant-commutator, trace, or Cayley--Hamilton
relation is imposed here.  Nor does this module yet identify global ordered
derivative words modulo adjacent different-owner shuffles with the local
words constructed below.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16LocalWordCarrier

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16RelationEquivariance
open SU2LatticeFDCensusNoGo

/-! ## The concrete finite carrier -/

/-- One field-strength letter after antisymmetric axis-pair normalization.
Its derivative axes retain their order within the field. -/
structure LocalFieldLetter (derivativeBudget : ℕ) where
  plane : OrientedPlane
  derivativeCount : Fin (derivativeBudget + 1)
  derivativeAxis : Fin derivativeCount.1 → Axis
deriving DecidableEq, Fintype

@[ext] theorem LocalFieldLetter.ext
    {derivativeBudget : ℕ}
    (left right : LocalFieldLetter derivativeBudget)
    (hplane : left.plane = right.plane)
    (hcount : left.derivativeCount = right.derivativeCount)
    (haxis : HEq left.derivativeAxis right.derivativeAxis) :
    left = right := by
  cases left
  cases right
  simp_all

/-- A family of local derivative words whose lengths add to the prescribed
total derivative degree. -/
abbrev LocalWordDecoration (fieldCount derivativeCount : ℕ) :=
  { letters : Fin fieldCount → LocalFieldLetter derivativeCount //
    ∑ field, (letters field).derivativeCount.1 = derivativeCount }

/-- Trace layout and decorated field letters before quotienting field labels. -/
structure LabeledLocalWordSector (fieldCount derivativeCount : ℕ) where
  trace : Equiv.Perm (Fin fieldCount)
  decoration : LocalWordDecoration fieldCount derivativeCount
deriving DecidableEq, Fintype

@[ext] theorem LabeledLocalWordSector.ext
    {fieldCount derivativeCount : ℕ}
    (left right : LabeledLocalWordSector fieldCount derivativeCount)
    (htrace : left.trace = right.trace)
    (hdecoration : left.decoration = right.decoration) : left = right := by
  cases left
  cases right
  simp_all

/-- The exact dimension-sixteen disjoint union, with field counts one through
eight and derivative degree `16 - 2 f`. -/
abbrev ExactDimension16LabeledLocalWordCarrier :=
  (fieldCount : Fin 8) ×'
    LabeledLocalWordSector (fieldCount.1 + 1)
      (16 - 2 * (fieldCount.1 + 1))

/-! ## Literal hypercubic action -/

def LocalFieldLetter.hypercubicAct (h : Hypercubic4)
    {derivativeBudget : ℕ} (letter : LocalFieldLetter derivativeBudget) :
    LocalFieldLetter derivativeBudget where
  plane := planeAction h letter.plane
  derivativeCount := letter.derivativeCount
  derivativeAxis := fun position => h.perm (letter.derivativeAxis position)

def LocalWordDecoration.hypercubicAct (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (decoration : LocalWordDecoration fieldCount derivativeCount) :
    LocalWordDecoration fieldCount derivativeCount :=
  ⟨fun field => (decoration.1 field).hypercubicAct h, by
    simpa [LocalFieldLetter.hypercubicAct] using decoration.2⟩

def LabeledLocalWordSector.hypercubicAct (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    LabeledLocalWordSector fieldCount derivativeCount where
  trace := sector.trace
  decoration := sector.decoration.hypercubicAct h

@[simp] theorem LocalFieldLetter.hypercubicAct_one
    {derivativeBudget : ℕ} (letter : LocalFieldLetter derivativeBudget) :
    letter.hypercubicAct 1 = letter := by
  apply LocalFieldLetter.ext
  · exact planeAction_one letter.plane
  · rfl
  · rfl

theorem LocalFieldLetter.hypercubicAct_mul (left right : Hypercubic4)
    {derivativeBudget : ℕ} (letter : LocalFieldLetter derivativeBudget) :
    letter.hypercubicAct (left * right) =
      (letter.hypercubicAct right).hypercubicAct left := by
  apply LocalFieldLetter.ext
  · exact planeAction_compose left right letter.plane
  · rfl
  · rfl

@[simp] theorem LabeledLocalWordSector.hypercubicAct_one
    {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    sector.hypercubicAct 1 = sector := by
  apply LabeledLocalWordSector.ext
  · rfl
  · apply Subtype.ext
    funext field
    exact LocalFieldLetter.hypercubicAct_one (sector.decoration.1 field)

theorem LabeledLocalWordSector.hypercubicAct_mul
    (left right : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    sector.hypercubicAct (left * right) =
      (sector.hypercubicAct right).hypercubicAct left := by
  apply LabeledLocalWordSector.ext
  · rfl
  · apply Subtype.ext
    funext field
    exact LocalFieldLetter.hypercubicAct_mul left right
      (sector.decoration.1 field)

instance labeledLocalWordSectorHypercubicMulAction
    (fieldCount derivativeCount : ℕ) :
    MulAction Hypercubic4
      (LabeledLocalWordSector fieldCount derivativeCount) where
  smul h sector := sector.hypercubicAct h
  one_smul := LabeledLocalWordSector.hypercubicAct_one
  mul_smul := by
    intro left right sector
    exact LabeledLocalWordSector.hypercubicAct_mul left right sector

/-! ## Uniform field relabeling -/

def LocalWordDecoration.relabel
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (decoration : LocalWordDecoration fieldCount derivativeCount) :
    LocalWordDecoration fieldCount derivativeCount :=
  ⟨fun field => decoration.1 (rename.symm field), by
    change (∑ field,
      (decoration.1 (rename.symm field)).derivativeCount.1) = derivativeCount
    exact (Equiv.sum_comp rename.symm
      (fun field => (decoration.1 field).derivativeCount.1)).trans
        decoration.2⟩

def LabeledLocalWordSector.relabel
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    LabeledLocalWordSector fieldCount derivativeCount where
  trace := rename.symm.trans (sector.trace.trans rename)
  decoration := sector.decoration.relabel rename

@[simp] theorem LabeledLocalWordSector.relabel_one
    {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    sector.relabel 1 = sector := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    rfl
  · apply Subtype.ext
    funext field
    rfl

theorem LabeledLocalWordSector.relabel_mul
    {fieldCount derivativeCount : ℕ}
    (left right : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    sector.relabel (left * right) =
      (sector.relabel right).relabel left := by
  apply LabeledLocalWordSector.ext
  · apply Equiv.ext
    intro field
    rfl
  · apply Subtype.ext
    funext field
    rfl

instance labeledLocalWordSectorFieldRelabelMulAction
    (fieldCount derivativeCount : ℕ) :
    MulAction (Equiv.Perm (Fin fieldCount))
      (LabeledLocalWordSector fieldCount derivativeCount) where
  smul rename sector := sector.relabel rename
  one_smul := LabeledLocalWordSector.relabel_one
  mul_smul := by
    intro left right sector
    exact LabeledLocalWordSector.relabel_mul left right sector

/-! ## Equivariance before orbit counting -/

theorem hypercubicAct_relabel
    {fieldCount derivativeCount : ℕ}
    (h : Hypercubic4) (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    (sector.relabel rename).hypercubicAct h =
      (sector.hypercubicAct h).relabel rename := by
  apply LabeledLocalWordSector.ext
  · rfl
  · apply Subtype.ext
    funext field
    rfl

/-- Rational tensor sign of one local field letter. -/
def LocalFieldLetter.tensorSign (h : Hypercubic4)
    {derivativeBudget : ℕ} (letter : LocalFieldLetter derivativeBudget) : ℚ :=
  (planeTensorSign h letter.plane : ℚ) *
    ∏ position, Hypercubic4.axisSign h (letter.derivativeAxis position)

/-- Complete tensor sign on the labeled local-word sector. -/
def LabeledLocalWordSector.tensorSign (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) : ℚ :=
  ∏ field, (sector.decoration.1 field).tensorSign h

@[simp] theorem LocalFieldLetter.tensorSign_one
    {derivativeBudget : ℕ} (letter : LocalFieldLetter derivativeBudget) :
    letter.tensorSign 1 = 1 := by
  simp [LocalFieldLetter.tensorSign, hypercubic_one_def,
    planeTensorSign, planeReorderSign, OrientedPlane.ordered]

@[simp] theorem LabeledLocalWordSector.tensorSign_one
    {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    sector.tensorSign 1 = 1 := by
  simp only [LabeledLocalWordSector.tensorSign,
    LocalFieldLetter.tensorSign_one, Finset.prod_const_one]

theorem LocalFieldLetter.tensorSign_mul (left right : Hypercubic4)
    {derivativeBudget : ℕ} (letter : LocalFieldLetter derivativeBudget) :
    letter.tensorSign (left * right) =
      letter.tensorSign right * (letter.hypercubicAct right).tensorSign left := by
  simp only [LocalFieldLetter.tensorSign, hypercubic_mul_def,
    planeTensorSign_compose, Int.cast_mul,
    Hypercubic4.axisSign_compose, Finset.prod_mul_distrib,
    LocalFieldLetter.hypercubicAct]
  ring_nf
  rfl

theorem LabeledLocalWordSector.tensorSign_mul
    (left right : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    sector.tensorSign (left * right) =
      sector.tensorSign right *
        (sector.hypercubicAct right).tensorSign left := by
  simp only [LabeledLocalWordSector.tensorSign,
    LocalFieldLetter.tensorSign_mul, Finset.prod_mul_distrib]
  rfl

theorem LabeledLocalWordSector.tensorSign_relabel
    {fieldCount derivativeCount : ℕ}
    (h : Hypercubic4) (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    (sector.relabel rename).tensorSign h = sector.tensorSign h := by
  unfold LabeledLocalWordSector.tensorSign
  exact Equiv.prod_comp rename.symm
    (fun field => (sector.decoration.1 field).tensorSign h)

/-! ## The honest field-label orbit carrier -/

abbrev FieldRelabelOrbitCarrier (fieldCount derivativeCount : ℕ) :=
  Quotient (MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
    (LabeledLocalWordSector fieldCount derivativeCount))

noncomputable instance fieldRelabelOrbitCarrierFintype
    (fieldCount derivativeCount : ℕ) :
    Fintype (FieldRelabelOrbitCarrier fieldCount derivativeCount) :=
  Fintype.ofFinite _

/-! ## Descent of the hypercubic action and tensor sign -/

theorem hypercubicAct_respects_fieldRelabelOrbit
    {fieldCount derivativeCount : ℕ} (h : Hypercubic4)
    (left right : LabeledLocalWordSector fieldCount derivativeCount)
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
      (LabeledLocalWordSector fieldCount derivativeCount) left right) :
    MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
      (LabeledLocalWordSector fieldCount derivativeCount)
      (left.hypercubicAct h) (right.hypercubicAct h) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame ⊢
  rcases hsame with ⟨rename, hrename⟩
  change right.relabel rename = left at hrename
  refine ⟨rename, ?_⟩
  change (right.hypercubicAct h).relabel rename = left.hypercubicAct h
  calc
    (right.hypercubicAct h).relabel rename =
        (right.relabel rename).hypercubicAct h :=
      (hypercubicAct_relabel h rename right).symm
    _ = left.hypercubicAct h := congrArg
      (LabeledLocalWordSector.hypercubicAct h) hrename

def FieldRelabelOrbitCarrier.hypercubicAct (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    FieldRelabelOrbitCarrier fieldCount derivativeCount :=
  Quotient.map (fun sector => sector.hypercubicAct h)
    (hypercubicAct_respects_fieldRelabelOrbit h) orbit

@[simp] theorem FieldRelabelOrbitCarrier.hypercubicAct_mk
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    FieldRelabelOrbitCarrier.hypercubicAct h
        (Quotient.mk _ sector) =
      Quotient.mk _ (sector.hypercubicAct h) :=
  rfl

@[simp] theorem FieldRelabelOrbitCarrier.hypercubicAct_one
    {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    orbit.hypercubicAct 1 = orbit := by
  refine Quotient.inductionOn orbit ?_
  intro sector
  exact congrArg (Quotient.mk _)
    (LabeledLocalWordSector.hypercubicAct_one sector)

theorem FieldRelabelOrbitCarrier.hypercubicAct_mul
    (left right : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    orbit.hypercubicAct (left * right) =
      (orbit.hypercubicAct right).hypercubicAct left := by
  refine Quotient.inductionOn orbit ?_
  intro sector
  simp only [FieldRelabelOrbitCarrier.hypercubicAct_mk]
  rw [LabeledLocalWordSector.hypercubicAct_mul]

instance fieldRelabelOrbitCarrierHypercubicMulAction
    (fieldCount derivativeCount : ℕ) :
    MulAction Hypercubic4
      (FieldRelabelOrbitCarrier fieldCount derivativeCount) where
  smul h orbit := orbit.hypercubicAct h
  one_smul := FieldRelabelOrbitCarrier.hypercubicAct_one
  mul_smul := by
    intro left right orbit
    exact FieldRelabelOrbitCarrier.hypercubicAct_mul left right orbit

theorem tensorSign_respects_fieldRelabelOrbit
    {fieldCount derivativeCount : ℕ} (h : Hypercubic4)
    (left right : LabeledLocalWordSector fieldCount derivativeCount)
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
      (LabeledLocalWordSector fieldCount derivativeCount) left right) :
    left.tensorSign h = right.tensorSign h := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrename⟩
  change right.relabel rename = left at hrename
  rw [← hrename, LabeledLocalWordSector.tensorSign_relabel]

/-- The signed tensor cocycle is well defined on field-label orbits. -/
def FieldRelabelOrbitCarrier.tensorSign (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ} :
    FieldRelabelOrbitCarrier fieldCount derivativeCount → ℚ :=
  Quotient.lift (fun sector => sector.tensorSign h)
    (tensorSign_respects_fieldRelabelOrbit h)

@[simp] theorem FieldRelabelOrbitCarrier.tensorSign_mk
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    FieldRelabelOrbitCarrier.tensorSign h (Quotient.mk _ sector) =
      sector.tensorSign h :=
  rfl

@[simp] theorem FieldRelabelOrbitCarrier.tensorSign_one
    {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    orbit.tensorSign 1 = 1 := by
  refine Quotient.inductionOn orbit ?_
  intro sector
  exact LabeledLocalWordSector.tensorSign_one sector

theorem FieldRelabelOrbitCarrier.tensorSign_mul
    (left right : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    orbit.tensorSign (left * right) =
      orbit.tensorSign right * (right • orbit).tensorSign left := by
  refine Quotient.inductionOn orbit ?_
  intro sector
  exact LabeledLocalWordSector.tensorSign_mul left right sector

end HypercubicDimension16LocalWordCarrier
end YangMills
end QuantumTheory
end Mettapedia
