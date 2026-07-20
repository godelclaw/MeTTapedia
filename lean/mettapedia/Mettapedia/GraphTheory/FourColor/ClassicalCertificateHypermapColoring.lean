import Mettapedia.GraphTheory.FourColor.ClassicalCertificateColorTrace
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfiguration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateHypermapColoring

open ClassicalCertificateColorTrace
open ClassicalCertificateHypermap

namespace FiniteHypermap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A proper coloring of hypermap faces, presented on darts: colors are
constant around face cycles and differ across every edge. -/
def IsFaceColoring (hypermap : FiniteHypermap D) (color : D → Color) : Prop :=
  (∀ dart, color (hypermap.edge dart) ≠ color dart) ∧
    ∀ dart, color (hypermap.face dart) = color dart

def FaceColorable (hypermap : FiniteHypermap D) : Prop :=
  ∃ color, IsFaceColoring hypermap color

/-- The dart support of a list of contract-edge representatives. -/
def InContract (hypermap : FiniteHypermap D) (contract : Finset D)
    (dart : D) : Prop :=
  dart ∈ contract ∨ hypermap.edge dart ∈ contract

instance (hypermap : FiniteHypermap D) (contract : Finset D) (dart : D) :
    Decidable (InContract hypermap contract dart) := by
  unfold InContract
  infer_instance

/-- A contract coloring is allowed to identify the two face colors precisely
on selected contract edges, and is proper on every other edge. -/
def IsContractColoring (hypermap : FiniteHypermap D)
    (contract : Finset D) (color : D → Color) : Prop :=
  (∀ dart,
      (color (hypermap.edge dart) = color dart) ↔
        InContract hypermap contract dart) ∧
    ∀ dart, color (hypermap.face dart) = color dart

theorem isFaceColoring_of_isContractColoring_empty
    (hypermap : FiniteHypermap D) (color : D → Color)
    (hcolor : IsContractColoring hypermap ∅ color) :
    IsFaceColoring hypermap color := by
  constructor
  · intro dart heq
    have hin := (hcolor.1 dart).1 heq
    simp [InContract] at hin
  · exact hcolor.2

theorem isContractColoring_empty_of_isFaceColoring
    (hypermap : FiniteHypermap D) (color : D → Color)
    (hcolor : IsFaceColoring hypermap color) :
    IsContractColoring hypermap ∅ color := by
  constructor
  · intro dart
    constructor
    · intro heq
      exact (hcolor.1 dart heq).elim
    · intro hin
      simp [InContract] at hin
  · exact hcolor.2

theorem isContractColoring_empty_iff
    (hypermap : FiniteHypermap D) (color : D → Color) :
    IsContractColoring hypermap ∅ color ↔
      IsFaceColoring hypermap color :=
  ⟨isFaceColoring_of_isContractColoring_empty hypermap color,
    isContractColoring_empty_of_isFaceColoring hypermap color⟩

/-- The color word read around an ordered boundary ring. -/
def ringColorWord (ring : List D) (color : D → Color) : List Color :=
  ring.map color

/-- Boundary traces induced by genuine face colorings. -/
def RingTrace (hypermap : FiniteHypermap D) (ring : List D)
    (boundaryTrace : List Color) : Prop :=
  ∃ color, IsFaceColoring hypermap color ∧
    boundaryTrace = trace (ringColorWord ring color)

/-- Boundary traces induced after contracting the selected edges. -/
def ContractRingTrace (hypermap : FiniteHypermap D)
    (contract : Finset D) (ring : List D)
    (boundaryTrace : List Color) : Prop :=
  ∃ color, IsContractColoring hypermap contract color ∧
    boundaryTrace = trace (ringColorWord ring color)

theorem ringTrace_iff_contractRingTrace_empty
    (hypermap : FiniteHypermap D) (ring : List D)
    (boundaryTrace : List Color) :
    RingTrace hypermap ring boundaryTrace ↔
      ContractRingTrace hypermap ∅ ring boundaryTrace := by
  constructor
  · rintro ⟨color, hcolor, rfl⟩
    exact ⟨color,
      isContractColoring_empty_of_isFaceColoring hypermap color hcolor, rfl⟩
  · rintro ⟨color, hcolor, rfl⟩
    exact ⟨color,
      isFaceColoring_of_isContractColoring_empty hypermap color hcolor, rfl⟩

/-- The next boundary dart lies in the face reached by crossing the current
edge. -/
def BoundaryStep (hypermap : FiniteHypermap D) (current next : D) : Prop :=
  next = hypermap.face (hypermap.edge current)

theorem color_ne_of_boundaryStep
    (hypermap : FiniteHypermap D) {color : D → Color}
    (hcolor : IsFaceColoring hypermap color)
    {current next : D} (hstep : BoundaryStep hypermap current next) :
    color current ≠ color next := by
  intro heq
  apply hcolor.1 current
  rw [← hcolor.2 (hypermap.edge current), ← hstep]
  exact heq.symm

end FiniteHypermap

namespace HypermapCode

open ClassicalCertificateConfiguration

/-- A four-color assignment emitted alongside a materialized hypermap.  Values
outside `0,1,2,3` decode to zero and are rejected by proper-color checks. -/
structure ColoringCode where
  colors : Array Nat
  deriving Repr

def decodeColor (value : Nat) : Color :=
  match value with
  | 0 => 0
  | 1 => red
  | 2 => blue
  | 3 => purple
  | _ => 0

def ColoringCode.decode (code : ColoringCode) (dartCount : Nat) :
    Fin dartCount → Color := fun dart =>
  decodeColor (ClassicalCertificateConfiguration.HypermapCode.lookup
    code.colors dart.val)

/-- Face-coloring equations stated directly on raw executable tables. -/
def RawIsFaceColoring
    (raw : ClassicalCertificateConfiguration.RawHypermap)
    (color : Fin raw.dartCount → Color) : Prop :=
  (∀ dart, color (raw.edge.toFin dart) ≠ color dart) ∧
    ∀ dart, color (raw.face.toFin dart) = color dart

instance (raw : ClassicalCertificateConfiguration.RawHypermap)
    (color : Fin raw.dartCount → Color) :
    Decidable (RawIsFaceColoring raw color) := by
  unfold RawIsFaceColoring
  infer_instance

/-- Complete semantic proposition reflected by the coloring checker. -/
def ColoringAccepted
    (hypermapCode : ClassicalCertificateConfiguration.HypermapCode)
    (coloringCode : ColoringCode) : Prop :=
  hypermapCode.Accepted ∧
    coloringCode.colors.size = hypermapCode.dartCount ∧
    RawIsFaceColoring hypermapCode.decode
      (coloringCode.decode hypermapCode.dartCount)

instance
    (hypermapCode : ClassicalCertificateConfiguration.HypermapCode)
    (coloringCode : ColoringCode) :
    Decidable (ColoringAccepted hypermapCode coloringCode) := by
  unfold ColoringAccepted
  infer_instance

/-- Reflected checker for one proposed coloring of a materialized hypermap. -/
def coloringChecker
    (hypermapCode : ClassicalCertificateConfiguration.HypermapCode)
    (coloringCode : ColoringCode) : Bool :=
  decide (ColoringAccepted hypermapCode coloringCode)

theorem coloringAccepted_of_checker_true
    (hypermapCode : ClassicalCertificateConfiguration.HypermapCode)
    (coloringCode : ColoringCode)
    (haccepted : coloringChecker hypermapCode coloringCode = true) :
    ColoringAccepted hypermapCode coloringCode := by
  exact Bool.of_decide_true
    (by simpa [coloringChecker] using haccepted)

/-- A checked array coloring becomes a genuine coloring of the checked
standard finite hypermap. -/
theorem exists_isFaceColoring_of_coloringChecker_true
    (hypermapCode : ClassicalCertificateConfiguration.HypermapCode)
    (coloringCode : ColoringCode)
    (haccepted : coloringChecker hypermapCode coloringCode = true) :
    ∃ hvalid : hypermapCode.decode.WellFormed,
      FiniteHypermap.IsFaceColoring
        (hypermapCode.decode.toFiniteHypermap hvalid)
        (coloringCode.decode hypermapCode.dartCount) := by
  have hsemantic :=
    coloringAccepted_of_checker_true hypermapCode coloringCode haccepted
  refine ⟨hsemantic.1.2.2.2, ?_⟩
  exact hsemantic.2.2

end HypermapCode

end ClassicalCertificateHypermapColoring

end Mettapedia.GraphTheory.FourColor
