import Mathlib.Data.Finset.Basic

/-!
# A flat CSR checker for bounded eventual self-loops

This file is independent of any particular corridor.  It gives semantics to a
finite directed graph stored as flat byte arrays and checks a small witness
showing that every state reaches a self-loop in at most two steps.

The row offsets are unsigned little-endian sixteen-bit integers; transition
targets are unsigned bytes.  Keeping the payload flat avoids elaborating a
large nested term while leaving the decoder and its semantic statement small.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FiniteTransitionWeakSelfLoop

/-- A directed graph in compressed-sparse-row form. -/
structure ByteCSR where
  stateCount : Nat
  rowOffsetLE16 : ByteArray
  targetIndexU8 : ByteArray

/-- Read one unsigned little-endian sixteen-bit entry.  Malformed payloads are
rejected separately by `ByteCSR.WellFormed`. -/
def readU16LE (payload : ByteArray) (entry : Nat) : Nat :=
  (payload.get! (2 * entry)).toNat +
    256 * (payload.get! (2 * entry + 1)).toNat

/-- Executable membership in one CSR row. -/
def ByteCSR.edgeBool (csr : ByteCSR) (source target : Nat) : Bool :=
  if source < csr.stateCount then
    let first := readU16LE csr.rowOffsetLE16 source
    let after := readU16LE csr.rowOffsetLE16 (source + 1)
    (List.range (after - first)).any fun delta =>
      (csr.targetIndexU8.get! (first + delta)).toNat == target
  else
    false

/-- The mathematical edge relation decoded from the flat CSR payload. -/
def ByteCSR.Edge (csr : ByteCSR) (source target : Nat) : Prop :=
  source < csr.stateCount ∧ target < csr.stateCount ∧
    csr.edgeBool source target = true

instance (csr : ByteCSR) (source target : Nat) :
    Decidable (csr.Edge source target) := by
  unfold ByteCSR.Edge
  infer_instance

/-- Structural validity of the flat encoding, independent of graph-theoretic
claims made about it. -/
def ByteCSR.WellFormed (csr : ByteCSR) : Prop :=
  csr.rowOffsetLE16.size = 2 * (csr.stateCount + 1) ∧
  readU16LE csr.rowOffsetLE16 0 = 0 ∧
  readU16LE csr.rowOffsetLE16 csr.stateCount = csr.targetIndexU8.size ∧
  (∀ source : Fin csr.stateCount,
    readU16LE csr.rowOffsetLE16 source.val ≤
      readU16LE csr.rowOffsetLE16 (source.val + 1)) ∧
  (∀ entry : Fin csr.targetIndexU8.size,
    (csr.targetIndexU8.get! entry.val).toNat < csr.stateCount)

instance (csr : ByteCSR) : Decidable csr.WellFormed := by
  unfold ByteCSR.WellFormed
  infer_instance

/-- Boolean reflection gate for the structural encoding. -/
def ByteCSR.wellFormedCheck (csr : ByteCSR) : Bool :=
  decide csr.WellFormed

theorem ByteCSR.wellFormed_of_check_eq_true (csr : ByteCSR)
    (hcheck : csr.wellFormedCheck = true) : csr.WellFormed := by
  exact of_decide_eq_true hcheck

/-- Semantic weak-L2 conclusion with the source playbook's bounded fallback,
specialized to a bound of two transitions. -/
def ReachesSelfLoopWithinTwo (csr : ByteCSR) (source : Nat) : Prop :=
  csr.Edge source source ∨
    ∃ middle, csr.Edge source middle ∧
      (csr.Edge middle middle ∨
        ∃ last, csr.Edge middle last ∧ csr.Edge last last)

/-- A flat path witness.  `distanceU8` records 0, 1, or 2; `nextIndexU8`
records the selected successor. -/
structure TwoStepWitness where
  nextIndexU8 : ByteArray
  distanceU8 : ByteArray

def TwoStepWitness.nextIndex (witness : TwoStepWitness) (state : Nat) : Nat :=
  (witness.nextIndexU8.get! state).toNat

def TwoStepWitness.distance (witness : TwoStepWitness) (state : Nat) : Nat :=
  (witness.distanceU8.get! state).toNat

/-- One state's witness is checked directly against decoded CSR edges. -/
def TwoStepWitness.ValidAt (witness : TwoStepWitness) (csr : ByteCSR)
    (source : Nat) : Prop :=
  source < csr.stateCount ∧
    ((witness.distance source = 0 ∧ csr.Edge source source) ∨
      (witness.distance source = 1 ∧
        csr.Edge source (witness.nextIndex source) ∧
        csr.Edge (witness.nextIndex source) (witness.nextIndex source)) ∨
      (witness.distance source = 2 ∧
        csr.Edge source (witness.nextIndex source) ∧
        csr.Edge (witness.nextIndex source)
          (witness.nextIndex (witness.nextIndex source)) ∧
        csr.Edge (witness.nextIndex (witness.nextIndex source))
          (witness.nextIndex (witness.nextIndex source))))

instance (witness : TwoStepWitness) (csr : ByteCSR) (source : Nat) :
    Decidable (witness.ValidAt csr source) := by
  unfold TwoStepWitness.ValidAt
  infer_instance

/-- The witness has one entry per state and validates every entry. -/
def TwoStepWitness.Valid (witness : TwoStepWitness) (csr : ByteCSR) : Prop :=
  witness.nextIndexU8.size = csr.stateCount ∧
  witness.distanceU8.size = csr.stateCount ∧
  ∀ source : Fin csr.stateCount, witness.ValidAt csr source.val

instance (witness : TwoStepWitness) (csr : ByteCSR) :
    Decidable (witness.Valid csr) := by
  unfold TwoStepWitness.Valid
  infer_instance

/-- Boolean reflection gate for a bounded weak-L2 witness. -/
def TwoStepWitness.validCheck (witness : TwoStepWitness) (csr : ByteCSR) : Bool :=
  decide (witness.Valid csr)

theorem TwoStepWitness.valid_of_check_eq_true (witness : TwoStepWitness)
    (csr : ByteCSR) (hcheck : witness.validCheck csr = true) :
    witness.Valid csr := by
  exact of_decide_eq_true hcheck

theorem TwoStepWitness.ValidAt.reachesSelfLoopWithinTwo
    {witness : TwoStepWitness} {csr : ByteCSR} {source : Nat}
    (hvalid : witness.ValidAt csr source) :
    ReachesSelfLoopWithinTwo csr source := by
  rcases hvalid with ⟨_hsource, hzero | hone | htwo⟩
  · exact Or.inl hzero.2
  · exact Or.inr ⟨witness.nextIndex source, hone.2.1, Or.inl hone.2.2⟩
  · exact Or.inr ⟨witness.nextIndex source, htwo.2.1,
      Or.inr ⟨witness.nextIndex (witness.nextIndex source),
        htwo.2.2.1, htwo.2.2.2⟩⟩

/-- A checked flat witness yields the semantic weak-L2 statement for every
state, rather than merely a successful Boolean computation. -/
theorem TwoStepWitness.all_reach_selfLoop_within_two
    (witness : TwoStepWitness) (csr : ByteCSR)
    (hvalid : witness.Valid csr) (source : Fin csr.stateCount) :
    ReachesSelfLoopWithinTwo csr source.val :=
  (hvalid.2.2 source).reachesSelfLoopWithinTwo

end GoertzelV24FiniteTransitionWeakSelfLoop

end Mettapedia.GraphTheory.FourColor
