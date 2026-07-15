import Mettapedia.QuantumTheory.YangMills.Dimension16WilsonExtractionCertificate
import Mettapedia.QuantumTheory.YangMills.SU2AssociatedGradedExtraction
import Mettapedia.QuantumTheory.YangMills.SU2CanonicalTruncationObstruction
import Mettapedia.QuantumTheory.YangMills.SU2IndependentTraceBasis

/-!
# No block-functional realization of the v14 `F,D` IBP quotient

V14 F.3 defines the extraction norm on ordinary analytic functions of a
gauge-fixed finite block with boundary data.  F.4.3 and O.9.2 both reduce the
continuum `F,D` operator catalog by integration by parts: an integrated total
derivative represents zero.  These two requirements are incompatible without
an additional boundary-cochain target.

The obstruction below is evaluated on the actual `SU(2)`, `b = 2` Wilson
block.  On profiles varying in one block direction, the centered second finite
difference of the Wilson density is the restriction of the scalar
dimension-six total derivative `∂² Tr(F²)`.  It is gauge invariant and is
nonzero on an explicit special-unitary link field.  The two-element source
slice quotients that total derivative to zero, exactly as integration by
parts requires.  Consequently no map from that quotient to ordinary
block-local functions can realize both zero and the actual finite difference.

The theorem applies to both manuscript relation branches: eliminating the
equations of motion on shell or retaining them off shell does not change the
integration-by-parts relation.  It also rules out an RG-compatible socket,
because such a socket first requires the impossible block realization.

There is a second obstruction before quotient realization.  Both surviving
MOVE-4 extractors grade by radial field-amplitude degree.  Canonical `F,D`
dimension also counts spacetime derivatives.  The one-direction restriction
of the scalar descendant `(∂²)³[(Tr F²)³]` is an explicit sixth finite
difference of a dimension-twelve cubic action jet and has canonical dimension
eighteen, but radial degrees six (associated grade) and three (centered trace).
Both survivor extractors therefore fix this operator instead of removing it.
They cannot be Ben's canonical-dimension-sixteen projection even after one
chooses an `F,D` quotient basis.

This is an as-written transfer no-go, not a claim that continuum `F,D`
quotients do not exist.  A repaired construction must retain boundary
descendants, map into functions modulo boundary coboundaries, or postpone
integration by parts until after global recombination.  None of those repairs
is the ordinary block-functional projection specified in v14.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14FDQuotientTransferNoGo

open SU2WilsonBlockPilot
open SU2CanonicalTruncationObstruction
open SU2AssociatedGradedExtraction
open SU2IndependentTraceBasis

/-! ## An actual three-plaquette total-derivative witness -/

/-- Three adjacent plaquette origins in the zeroth block direction. -/
def ibpProfileOrigin (i : Fin 3) : BlockVertex :=
  ![i, 0, 0, 1]

/-- Three adjacent `(1,2)` plaquettes.  The second finite difference in the
zeroth direction uses all three and requires no external extension rule. -/
def ibpProfilePlaquette (i : Fin 3) : BlockPlaquette where
  origin := ibpProfileOrigin i
  first := 1
  second := 2
  ordered := by decide
  canStepFirst := by simp [ibpProfileOrigin]
  canStepSecond := by simp [ibpProfileOrigin]

/-- An actual link field whose only nonidentity link is the first edge of the
last profile plaquette. -/
def ibpWitnessField : BlockLinkField := fun e =>
  if e = (ibpProfilePlaquette 2).firstLink then quarterTurn else 1

theorem ibpWitnessHolonomy_zero :
    plaquetteHolonomy ibpWitnessField (ibpProfilePlaquette 0) = 1 := by
  have hff : (ibpProfilePlaquette 0).firstLink ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  have hsf : (ibpProfilePlaquette 0).secondAfterFirst ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  have hfs : (ibpProfilePlaquette 0).firstAfterSecond ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  have hss : (ibpProfilePlaquette 0).secondLink ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  simp [plaquetteHolonomy, ibpWitnessField, hff, hsf, hfs, hss]

theorem ibpWitnessHolonomy_one :
    plaquetteHolonomy ibpWitnessField (ibpProfilePlaquette 1) = 1 := by
  have hff : (ibpProfilePlaquette 1).firstLink ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  have hsf : (ibpProfilePlaquette 1).secondAfterFirst ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  have hfs : (ibpProfilePlaquette 1).firstAfterSecond ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  have hss : (ibpProfilePlaquette 1).secondLink ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  simp [plaquetteHolonomy, ibpWitnessField, hff, hsf, hfs, hss]

theorem ibpWitnessHolonomy_two :
    plaquetteHolonomy ibpWitnessField (ibpProfilePlaquette 2) = quarterTurn := by
  have hsf : (ibpProfilePlaquette 2).secondAfterFirst ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  have hfs : (ibpProfilePlaquette 2).firstAfterSecond ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  have hss : (ibpProfilePlaquette 2).secondLink ≠
      (ibpProfilePlaquette 2).firstLink := by decide
  simp [plaquetteHolonomy, ibpWitnessField, hsf, hfs, hss]

theorem ibpWitnessPotential_zero :
    plaquettePotential ibpWitnessField (ibpProfilePlaquette 0) = 0 := by
  rw [plaquettePotential, ibpWitnessHolonomy_zero]
  norm_num [specialUnitaryWilsonPotential, Matrix.trace, Fin.sum_univ_two]

theorem ibpWitnessPotential_one :
    plaquettePotential ibpWitnessField (ibpProfilePlaquette 1) = 0 := by
  rw [plaquettePotential, ibpWitnessHolonomy_one]
  norm_num [specialUnitaryWilsonPotential, Matrix.trace, Fin.sum_univ_two]

theorem ibpWitnessPotential_two :
    plaquettePotential ibpWitnessField (ibpProfilePlaquette 2) = 1 := by
  rw [plaquettePotential, ibpWitnessHolonomy_two]
  simp [specialUnitaryWilsonPotential, quarterTurn_trace_real]

/-- Wilson-density profile on the three adjacent plaquettes. -/
def actionProfile (U : BlockLinkField) (i : Fin 3) : ℝ :=
  plaquettePotential U (ibpProfilePlaquette i)

/-- Centered second finite difference of the dimension-four Wilson density.
On profiles varying only in the zeroth direction, this is the finite-block
restriction of `∂² Tr(F²)`, a scalar dimension-six integrated total
derivative in the `F,D` catalog. -/
def actionLaplacianDensity (U : BlockLinkField) : ℝ :=
  actionProfile U 2 - 2 * actionProfile U 1 + actionProfile U 0

theorem actionLaplacianDensity_gaugeInvariant
    (g : BlockGaugeTransform) (U : BlockLinkField) :
    actionLaplacianDensity (gaugeAct g U) = actionLaplacianDensity U := by
  simp [actionLaplacianDensity, actionProfile,
    plaquettePotential_gaugeAct]

/-- The integration-by-parts witness is nonzero on the actual block. -/
theorem actionLaplacianDensity_witness :
    actionLaplacianDensity ibpWitnessField = 1 := by
  norm_num [actionLaplacianDensity, actionProfile,
    ibpWitnessPotential_zero, ibpWitnessPotential_one,
    ibpWitnessPotential_two]

/-- The action density has canonical dimension four and two derivatives add
two, so this common-IBP obstruction lies inside the requested cutoff. -/
def actionLaplacianCanonicalDimension : ℕ := 4 + 2

theorem actionLaplacianCanonicalDimension_eq :
    actionLaplacianCanonicalDimension = 6 := by rfl

theorem actionLaplacianCanonicalDimension_le_sixteen :
    actionLaplacianCanonicalDimension ≤ 16 := by decide

/-! ## The same obstruction in the pure associated grade -/

/-- The three scalar plaquette-log directions needed to expose the IBP
boundary term.  This is a finite slice of the plaquette-log chart used in
F.3--F.4, not a Wilson-loop completion with higher Taylor terms. -/
abbrev ThreePlaquetteActionJet := Fin 3 → ℂ

/-- Exact homogeneous quadratic action jet on one plaquette-log direction. -/
def homogeneousActionJet
    (A : ThreePlaquetteActionJet) (i : Fin 3) : ℂ :=
  (A i) ^ 2

/-- Pure degree-two associated-graded one-direction restriction of the scalar
descendant `∂² Tr(F²)` on the three actual plaquette positions. -/
def homogeneousActionLaplacian
    (A : ThreePlaquetteActionJet) : ℂ :=
  homogeneousActionJet A 2 - 2 * homogeneousActionJet A 1 +
    homogeneousActionJet A 0

/-- The representative is genuinely homogeneous of log-coordinate degree
two; no exact Wilson-loop tail is used in this second witness. -/
theorem homogeneousActionLaplacian_smul
    (z : ℂ) (A : ThreePlaquetteActionJet) :
    homogeneousActionLaplacian (z • A) =
      z ^ 2 * homogeneousActionLaplacian A := by
  simp [homogeneousActionLaplacian, homogeneousActionJet, smul_eq_mul]
  ring

def homogeneousActionJetWitness : ThreePlaquetteActionJet
  | 0 => 0
  | 1 => 0
  | 2 => 1

theorem homogeneousActionLaplacian_witness :
    homogeneousActionLaplacian homogeneousActionJetWitness = 1 := by
  norm_num [homogeneousActionLaplacian, homogeneousActionJet,
    homogeneousActionJetWitness]

/-- The MOVE-4 radial extractor fixes this pure degree-two descendant exactly.
Thus the associated-graded survivor does not erase the boundary term that the
source IBP quotient declares zero. -/
theorem radialExtraction16_fixes_homogeneousActionLaplacian
    (A : ThreePlaquetteActionJet) :
    radialExtraction16
        (fun z : ℂ => homogeneousActionLaplacian (z • A)) =
      homogeneousActionLaplacian A := by
  rw [show (fun z : ℂ => homogeneousActionLaplacian (z • A)) =
      fun z : ℂ =>
        (Polynomial.C (homogeneousActionLaplacian A) *
          Polynomial.X ^ 2).eval z by
    funext z
    rw [homogeneousActionLaplacian_smul]
    simp
    ring]
  rw [radialExtraction16_polynomial_eval]
  simp

/-! ## Canonical dimension is not radial field degree -/

/-- Forward translation on a two-cell complex jet, with the fixed boundary
fluctuation extended by zero. -/
def complexZeroBoundaryShift (f : Fin 2 → ℂ) : Fin 2 → ℂ
  | 0 => f 1
  | 1 => 0

def complexFiniteDifference (f : Fin 2 → ℂ) : Fin 2 → ℂ :=
  complexZeroBoundaryShift f - f

def complexIteratedDifference : ℕ → (Fin 2 → ℂ) → (Fin 2 → ℂ)
  | 0, f => f
  | n + 1, f => complexFiniteDifference (complexIteratedDifference n f)

/-- Pure associated-graded one-direction restriction of the scalar descendant
`(∂²)³[(Tr F²)³]`.  It has radial log-field degree six, but canonical
dimension `12 + 6 = 18`. -/
def associatedHighDerivativeJet (A : Fin 2 → ℂ) : ℂ :=
  complexIteratedDifference 6 (fun i => (A i) ^ 6) 0

/-- Independent centered-trace version of the same scalar descendant.  Its
trace-coordinate degree is three, but its six derivatives again give
canonical dimension eighteen. -/
def independentHighDerivativeJet (a : Fin 2 → ℂ) : ℂ :=
  complexIteratedDifference 6 (fun i => (a i) ^ 3) 0

def highDerivativeCanonicalDimension : ℕ := 12 + 6

theorem highDerivativeCanonicalDimension_eq :
    highDerivativeCanonicalDimension = 18 := by rfl

theorem highDerivativeCanonicalDimension_gt_sixteen :
    16 < highDerivativeCanonicalDimension := by decide

theorem associatedHighDerivativeJet_smul
    (z : ℂ) (A : Fin 2 → ℂ) :
    associatedHighDerivativeJet (z • A) =
      z ^ 6 * associatedHighDerivativeJet A := by
  simp [associatedHighDerivativeJet, complexIteratedDifference,
    complexFiniteDifference, complexZeroBoundaryShift, smul_eq_mul]
  ring

theorem independentHighDerivativeJet_smul
    (z : ℂ) (a : Fin 2 → ℂ) :
    independentHighDerivativeJet (z • a) =
      z ^ 3 * independentHighDerivativeJet a := by
  simp [independentHighDerivativeJet, complexIteratedDifference,
    complexFiniteDifference, complexZeroBoundaryShift, smul_eq_mul]
  ring

def highDerivativeJetWitness : Fin 2 → ℂ
  | 0 => 0
  | 1 => 1

theorem associatedHighDerivativeJet_witness :
    associatedHighDerivativeJet highDerivativeJetWitness = -6 := by
  norm_num [associatedHighDerivativeJet, complexIteratedDifference,
    complexFiniteDifference, complexZeroBoundaryShift,
    highDerivativeJetWitness]

theorem independentHighDerivativeJet_witness :
    independentHighDerivativeJet highDerivativeJetWitness = -6 := by
  norm_num [independentHighDerivativeJet, complexIteratedDifference,
    complexFiniteDifference, complexZeroBoundaryShift,
    highDerivativeJetWitness]

/-- Radial degree-six extraction retains the canonical-dimension-eighteen
associated-graded operator exactly. -/
theorem radialExtraction16_fixes_associatedHighDerivativeJet
    (A : Fin 2 → ℂ) :
    radialExtraction16
        (fun z : ℂ => associatedHighDerivativeJet (z • A)) =
      associatedHighDerivativeJet A := by
  rw [show (fun z : ℂ => associatedHighDerivativeJet (z • A)) =
      fun z : ℂ =>
        (Polynomial.C (associatedHighDerivativeJet A) *
          Polynomial.X ^ 6).eval z by
    funext z
    rw [associatedHighDerivativeJet_smul]
    simp
    ring]
  rw [radialExtraction16_polynomial_eval]
  simp

/-- The independent trace extractor retains the same canonical-dimension-
eighteen operator because its trace-coordinate radial degree is only three. -/
theorem independentRadialExtraction_fixes_highDerivativeJet
    (a : Fin 2 → ℂ) :
    (∑ d ∈ Finset.range 5,
        radialJetCoefficient d
          (fun z : ℂ => independentHighDerivativeJet (z • a))) =
      independentHighDerivativeJet a := by
  rw [show (fun z : ℂ => independentHighDerivativeJet (z • a)) =
      fun z : ℂ =>
        (Polynomial.C (independentHighDerivativeJet a) *
          Polynomial.X ^ 3).eval z by
    funext z
    rw [independentHighDerivativeJet_smul]
    simp
    ring]
  simp_rw [radialJetCoefficient_polynomial_eval]
  simp

/-- The requirement that the associated-graded radial extractor annihilate
this pure operator because its canonical dimension is above sixteen. -/
def AssociatedRadialImplementsCanonicalCutoff : Prop :=
  ∀ A : Fin 2 → ℂ,
    radialExtraction16
      (fun z : ℂ => associatedHighDerivativeJet (z • A)) = 0

/-- The analogous cutoff requirement for the independent trace extractor. -/
def IndependentRadialImplementsCanonicalCutoff : Prop :=
  ∀ a : Fin 2 → ℂ,
    (∑ d ∈ Finset.range 5,
      radialJetCoefficient d
        (fun z : ℂ => independentHighDerivativeJet (z • a))) = 0

/-- **Associated-survivor obstruction.**  Field-amplitude degree sixteen is
not canonical `F,D` dimension sixteen. -/
theorem not_associatedRadialImplementsCanonicalCutoff :
    ¬ AssociatedRadialImplementsCanonicalCutoff := by
  intro h
  have hw := h highDerivativeJetWitness
  rw [radialExtraction16_fixes_associatedHighDerivativeJet,
    associatedHighDerivativeJet_witness] at hw
  norm_num at hw

/-- **Independent-survivor obstruction.**  Trace-coordinate degree four is
also blind to the six contracted derivative indices. -/
theorem not_independentRadialImplementsCanonicalCutoff :
    ¬ IndependentRadialImplementsCanonicalCutoff := by
  intro h
  have hw := h highDerivativeJetWitness
  rw [independentRadialExtraction_fixes_highDerivativeJet,
    independentHighDerivativeJet_witness] at hw
  norm_num at hw

/-! ## The exact integration-by-parts quotient slice -/

/-- The smallest source slice needed for the transfer test. -/
inductive V14FDIBPDensity where
  | zero
  | actionLaplacian
deriving DecidableEq, Fintype, Repr

/-- Evaluation before imposing integration by parts. -/
def V14FDIBPDensity.evaluate :
    V14FDIBPDensity → BlockLinkField → ℝ
  | .zero, _ => 0
  | .actionLaplacian, U => actionLaplacianDensity U

/-- On this two-element slice, the v14 integration-by-parts relation identifies
the total derivative with zero. -/
def V14FDIBPEquivalent (_ _ : V14FDIBPDensity) : Prop := True

instance v14FDIBPSetoid : Setoid V14FDIBPDensity where
  r := V14FDIBPEquivalent
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

abbrev V14FDIBPQuotient := Quotient v14FDIBPSetoid

def v14FDIBPClass (density : V14FDIBPDensity) : V14FDIBPQuotient :=
  Quotient.mk v14FDIBPSetoid density

theorem actionLaplacian_eq_zero_in_ibpQuotient :
    v14FDIBPClass .actionLaplacian = v14FDIBPClass .zero := by
  exact Quotient.sound trivial

/-! ## Both relation branches fail the same block-realization gate -/

/-- The exact socket needed before either survivor can descend to the v14
`F,D` quotient.  `realize_zero` is ordinary linear semantics; the final field
requires the quotient class to retain its actual block-local representative.
The branch parameter records the EOM policy, while IBP is common to both. -/
structure V14FaithfulFDTransferSocket
    (_policy : V14ActionSectorRelationPolicy) where
  realize : V14FDIBPQuotient → BlockLinkField → ℝ
  realize_zero : realize (v14FDIBPClass .zero) = 0
  realize_actionLaplacian :
    realize (v14FDIBPClass .actionLaplacian) = actionLaplacianDensity

/-- **Common-branch transfer no-go.**  Neither the on-shell nor the off-shell
`F,D` quotient can be realized as the ordinary block-local function space used
by v14 while also imposing its integration-by-parts relation. -/
theorem no_faithfulFDTransferSocket
    (policy : V14ActionSectorRelationPolicy) :
    ¬ Nonempty (V14FaithfulFDTransferSocket policy) := by
  rintro ⟨socket⟩
  have hfunctions : actionLaplacianDensity = 0 := by
    calc
      actionLaplacianDensity =
          socket.realize (v14FDIBPClass .actionLaplacian) :=
        socket.realize_actionLaplacian.symm
      _ = socket.realize (v14FDIBPClass .zero) :=
        congrArg socket.realize actionLaplacian_eq_zero_in_ibpQuotient
      _ = 0 := socket.realize_zero
  have hw := congrFun hfunctions ibpWitnessField
  rw [actionLaplacianDensity_witness] at hw
  norm_num at hw

/-- Associated-graded version of the same faithful-realization gate.  It uses
the pure homogeneous quadratic jet rather than the exact Wilson density, so
the obstruction cannot be attributed to higher Taylor contamination in a
Wilson-loop representative. -/
structure V14FaithfulAssociatedGradedFDTransferSocket
    (_policy : V14ActionSectorRelationPolicy) where
  realize : V14FDIBPQuotient → ThreePlaquetteActionJet → ℂ
  realize_zero : realize (v14FDIBPClass .zero) = 0
  realize_actionLaplacian :
    realize (v14FDIBPClass .actionLaplacian) =
      homogeneousActionLaplacian

theorem no_faithfulAssociatedGradedFDTransferSocket
    (policy : V14ActionSectorRelationPolicy) :
    ¬ Nonempty (V14FaithfulAssociatedGradedFDTransferSocket policy) := by
  rintro ⟨socket⟩
  have hfunctions : homogeneousActionLaplacian = 0 := by
    calc
      homogeneousActionLaplacian =
          socket.realize (v14FDIBPClass .actionLaplacian) :=
        socket.realize_actionLaplacian.symm
      _ = socket.realize (v14FDIBPClass .zero) :=
        congrArg socket.realize actionLaplacian_eq_zero_in_ibpQuotient
      _ = 0 := socket.realize_zero
  have hw := congrFun hfunctions homogeneousActionJetWitness
  rw [homogeneousActionLaplacian_witness] at hw
  norm_num at hw

/-- Adding source/block RG maps and an intertwining law cannot repair the
missing realization: every RG-compatible socket contains a faithful transfer
socket as a prerequisite. -/
structure V14RGCompatibleFDTransferSocket
    (policy : V14ActionSectorRelationPolicy)
    extends V14FaithfulFDTransferSocket policy where
  sourceRG : V14FDIBPQuotient → V14FDIBPQuotient
  blockRG : (BlockLinkField → ℝ) → (BlockLinkField → ℝ)
  intertwines : ∀ q,
    realize (sourceRG q) = blockRG (realize q)

theorem no_rgCompatibleFDTransferSocket
    (policy : V14ActionSectorRelationPolicy) :
    ¬ Nonempty (V14RGCompatibleFDTransferSocket policy) := by
  rintro ⟨socket⟩
  exact no_faithfulFDTransferSocket policy ⟨socket.toV14FaithfulFDTransferSocket⟩

/-! ## Checked two-branch decision -/

inductive V14FDTransferDecisionRow where
  | actualWilsonBlockWitness
  | homogeneousAssociatedGradedWitness
  | associatedCanonicalCutoff
  | independentCanonicalCutoff
  | commonIBPQuotient
  | onShellAssociatedGradedRealization
  | offShellAssociatedGradedRealization
  | onShellBlockRealization
  | offShellBlockRealization
  | onShellRGIntertwining
  | offShellRGIntertwining
deriving DecidableEq, Fintype, Repr

inductive V14FDTransferDecisionStatus where
  | constructed
  | refutedByDerivativeBlindness
  | refutedByBoundaryDescendant
deriving DecidableEq, Repr

def v14FDTransferDecisionStatus :
    V14FDTransferDecisionRow → V14FDTransferDecisionStatus
  | .actualWilsonBlockWitness => .constructed
  | .homogeneousAssociatedGradedWitness => .constructed
  | .associatedCanonicalCutoff => .refutedByDerivativeBlindness
  | .independentCanonicalCutoff => .refutedByDerivativeBlindness
  | .commonIBPQuotient => .constructed
  | .onShellAssociatedGradedRealization => .refutedByBoundaryDescendant
  | .offShellAssociatedGradedRealization => .refutedByBoundaryDescendant
  | .onShellBlockRealization => .refutedByBoundaryDescendant
  | .offShellBlockRealization => .refutedByBoundaryDescendant
  | .onShellRGIntertwining => .refutedByBoundaryDescendant
  | .offShellRGIntertwining => .refutedByBoundaryDescendant

def v14FDTransferDecisionMatrix :
    List (V14FDTransferDecisionRow × V14FDTransferDecisionStatus) :=
  [ (.actualWilsonBlockWitness, .constructed)
  , (.homogeneousAssociatedGradedWitness, .constructed)
  , (.associatedCanonicalCutoff, .refutedByDerivativeBlindness)
  , (.independentCanonicalCutoff, .refutedByDerivativeBlindness)
  , (.commonIBPQuotient, .constructed)
  , (.onShellAssociatedGradedRealization, .refutedByBoundaryDescendant)
  , (.offShellAssociatedGradedRealization, .refutedByBoundaryDescendant)
  , (.onShellBlockRealization, .refutedByBoundaryDescendant)
  , (.offShellBlockRealization, .refutedByBoundaryDescendant)
  , (.onShellRGIntertwining, .refutedByBoundaryDescendant)
  , (.offShellRGIntertwining, .refutedByBoundaryDescendant)
  ]

theorem v14FDTransferDecisionMatrix_agrees
    (row : V14FDTransferDecisionRow) :
    (row, v14FDTransferDecisionStatus row) ∈ v14FDTransferDecisionMatrix := by
  cases row <;> decide

/-- **YM MOVE 5 decision.**  Both survivor extractors retain a canonical-
dimension-eighteen scalar derivative operator.  Independently, the common
dimension-six IBP relation has nonzero exact-Wilson and pure-jet block
realizations.  Hence neither EOM policy admits the ordinary block-functional
transfer socket required before an RG intertwining map can be formed. -/
theorem v14_fullFD_quotientTransfer_noGo :
    actionLaplacianCanonicalDimension ≤ 16 ∧
    actionLaplacianDensity ibpWitnessField ≠ 0 ∧
    homogeneousActionLaplacian homogeneousActionJetWitness ≠ 0 ∧
    16 < highDerivativeCanonicalDimension ∧
    (¬ AssociatedRadialImplementsCanonicalCutoff) ∧
    (¬ IndependentRadialImplementsCanonicalCutoff) ∧
    (¬ Nonempty
      (V14FaithfulAssociatedGradedFDTransferSocket .onShell)) ∧
    (¬ Nonempty
      (V14FaithfulAssociatedGradedFDTransferSocket .offShell)) ∧
    (¬ Nonempty (V14FaithfulFDTransferSocket .onShell)) ∧
    (¬ Nonempty (V14FaithfulFDTransferSocket .offShell)) ∧
    (¬ Nonempty (V14RGCompatibleFDTransferSocket .onShell)) ∧
    (¬ Nonempty (V14RGCompatibleFDTransferSocket .offShell)) := by
  exact
    ⟨actionLaplacianCanonicalDimension_le_sixteen,
      by rw [actionLaplacianDensity_witness]; norm_num,
      by rw [homogeneousActionLaplacian_witness]; norm_num,
      highDerivativeCanonicalDimension_gt_sixteen,
      not_associatedRadialImplementsCanonicalCutoff,
      not_independentRadialImplementsCanonicalCutoff,
      no_faithfulAssociatedGradedFDTransferSocket .onShell,
      no_faithfulAssociatedGradedFDTransferSocket .offShell,
      no_faithfulFDTransferSocket .onShell,
      no_faithfulFDTransferSocket .offShell,
      no_rgCompatibleFDTransferSocket .onShell,
      no_rgCompatibleFDTransferSocket .offShell⟩

end V14FDQuotientTransferNoGo
end YangMills
end QuantumTheory
end Mettapedia
