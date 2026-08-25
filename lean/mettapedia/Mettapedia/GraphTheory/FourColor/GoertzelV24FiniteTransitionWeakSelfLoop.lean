import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# A flat CSR checker for bounded eventual self-loops

This file is independent of any particular corridor.  It gives semantics to a
finite directed graph stored as flat byte arrays and checks a small witness
showing that every state reaches a self-loop in at most two steps.

The row offsets and transition targets are unsigned little-endian sixteen-bit
integers.  Target bytes may be split into flat pages; `targetIndex` is the
small decoder supplied by a concrete certificate.  This avoids both a nested
term graph and linear kernel reduction through one monolithic byte literal.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FiniteTransitionWeakSelfLoop

/-- A directed graph in compressed-sparse-row form. -/
structure ByteCSR where
  stateCount : Nat
  rowOffsetLE16 : ByteArray
  targetEntryCount : Nat
  targetIndex : Nat → Nat

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
      csr.targetIndex (first + delta) == target
  else
    false

/-- A particular payload entry witnesses a mathematical edge.  Keeping the
entry explicit lets finite certificates check selected paths in constant time,
without searching the whole CSR row during elaboration. -/
def ByteCSR.EdgeAt (csr : ByteCSR) (source target entry : Nat) : Prop :=
  source < csr.stateCount ∧ target < csr.stateCount ∧
    entry < csr.targetEntryCount ∧
    readU16LE csr.rowOffsetLE16 source ≤ entry ∧
    entry < readU16LE csr.rowOffsetLE16 (source + 1) ∧
    csr.targetIndex entry = target

/-- The mathematical edge relation decoded from the flat CSR payload. -/
def ByteCSR.Edge (csr : ByteCSR) (source target : Nat) : Prop :=
  ∃ entry : Fin csr.targetEntryCount,
    csr.EdgeAt source target entry.val

instance (csr : ByteCSR) (source target entry : Nat) :
    Decidable (csr.EdgeAt source target entry) := by
  unfold ByteCSR.EdgeAt
  infer_instance

instance (csr : ByteCSR) (source target : Nat) :
    Decidable (csr.Edge source target) := by
  unfold ByteCSR.Edge
  infer_instance

theorem ByteCSR.EdgeAt.toEdge {csr : ByteCSR} {source target entry : Nat}
    (hedge : csr.EdgeAt source target entry) : csr.Edge source target := by
  exact ⟨⟨entry, hedge.2.2.1⟩, hedge⟩

/-- Structural validity of the flat encoding, independent of graph-theoretic
claims made about it. -/
def ByteCSR.WellFormed (csr : ByteCSR) : Prop :=
  csr.rowOffsetLE16.size = 2 * (csr.stateCount + 1) ∧
  readU16LE csr.rowOffsetLE16 0 = 0 ∧
  readU16LE csr.rowOffsetLE16 csr.stateCount = csr.targetEntryCount ∧
  (∀ source : Fin csr.stateCount,
    readU16LE csr.rowOffsetLE16 source.val ≤
      readU16LE csr.rowOffsetLE16 (source.val + 1)) ∧
  (∀ entry : Fin csr.targetEntryCount,
    csr.targetIndex entry.val < csr.stateCount)

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

/-- A flat path witness.  `distanceU8` records 0, 1, or 2;
`nextIndexLE16` records the selected successor.  The three entry arrays point
directly to the CSR entries for the first step, optional second step, and final
self-loop. -/
structure TwoStepWitness where
  nextIndexLE16 : ByteArray
  firstEntryLE16 : ByteArray
  secondEntryLE16 : ByteArray
  loopEntryLE16 : ByteArray
  distanceU8 : ByteArray

def TwoStepWitness.nextIndex (witness : TwoStepWitness) (state : Nat) : Nat :=
  readU16LE witness.nextIndexLE16 state

def TwoStepWitness.distance (witness : TwoStepWitness) (state : Nat) : Nat :=
  (witness.distanceU8.get! state).toNat

def TwoStepWitness.firstEntry (witness : TwoStepWitness) (state : Nat) : Nat :=
  readU16LE witness.firstEntryLE16 state

def TwoStepWitness.secondEntry (witness : TwoStepWitness) (state : Nat) : Nat :=
  readU16LE witness.secondEntryLE16 state

def TwoStepWitness.loopEntry (witness : TwoStepWitness) (state : Nat) : Nat :=
  readU16LE witness.loopEntryLE16 state

/-- One state's witness is checked directly against decoded CSR edges. -/
def TwoStepWitness.ValidAt (witness : TwoStepWitness) (csr : ByteCSR)
    (source : Nat) : Prop :=
  source < csr.stateCount ∧
    ((witness.distance source = 0 ∧
        csr.EdgeAt source source (witness.loopEntry source)) ∨
      (witness.distance source = 1 ∧
        csr.EdgeAt source (witness.nextIndex source)
          (witness.firstEntry source) ∧
        csr.EdgeAt (witness.nextIndex source) (witness.nextIndex source)
          (witness.loopEntry source)) ∨
      (witness.distance source = 2 ∧
        csr.EdgeAt source (witness.nextIndex source)
          (witness.firstEntry source) ∧
        csr.EdgeAt (witness.nextIndex source)
          (witness.nextIndex (witness.nextIndex source))
          (witness.secondEntry source) ∧
        csr.EdgeAt (witness.nextIndex (witness.nextIndex source))
          (witness.nextIndex (witness.nextIndex source))
          (witness.loopEntry source)))

instance (witness : TwoStepWitness) (csr : ByteCSR) (source : Nat) :
    Decidable (witness.ValidAt csr source) := by
  unfold TwoStepWitness.ValidAt
  infer_instance

/-- The witness has one entry per state and validates every entry. -/
def TwoStepWitness.Valid (witness : TwoStepWitness) (csr : ByteCSR) : Prop :=
  witness.nextIndexLE16.size = 2 * csr.stateCount ∧
  witness.firstEntryLE16.size = 2 * csr.stateCount ∧
  witness.secondEntryLE16.size = 2 * csr.stateCount ∧
  witness.loopEntryLE16.size = 2 * csr.stateCount ∧
  witness.distanceU8.size = csr.stateCount ∧
  ∀ source : Fin csr.stateCount, witness.ValidAt csr source.val

instance (witness : TwoStepWitness) (csr : ByteCSR) :
    Decidable (witness.Valid csr) := by
  unfold TwoStepWitness.Valid
  infer_instance

/-- A bounded page of local path checks.  Certificate payloads use this to
keep each elaboration unit small and cacheable. -/
def TwoStepWitness.ValidPage (witness : TwoStepWitness) (csr : ByteCSR)
    (start count : Nat) : Prop :=
  ∀ offset : Fin count, witness.ValidAt csr (start + offset.val)

instance (witness : TwoStepWitness) (csr : ByteCSR) (start count : Nat) :
    Decidable (witness.ValidPage csr start count) := by
  unfold TwoStepWitness.ValidPage
  infer_instance

/-- Adjacent checked pages concatenate without rechecking either payload. -/
theorem TwoStepWitness.ValidPage.append
    {witness : TwoStepWitness} {csr : ByteCSR}
    {start leftCount rightCount : Nat}
    (left : witness.ValidPage csr start leftCount)
    (right : witness.ValidPage csr (start + leftCount) rightCount) :
    witness.ValidPage csr start (leftCount + rightCount) := by
  intro offset
  by_cases hleft : offset.val < leftCount
  · exact left ⟨offset.val, hleft⟩
  · have hright : offset.val - leftCount < rightCount := by omega
    have hindex :
        start + offset.val =
          (start + leftCount) + (offset.val - leftCount) := by omega
    rw [hindex]
    exact right ⟨offset.val - leftCount, hright⟩

/-- A page beginning at zero and covering the state carrier supplies the local
part of a complete witness. -/
theorem TwoStepWitness.valid_of_page_zero
    (witness : TwoStepWitness) (csr : ByteCSR)
    (hnext : witness.nextIndexLE16.size = 2 * csr.stateCount)
    (hfirst : witness.firstEntryLE16.size = 2 * csr.stateCount)
    (hsecond : witness.secondEntryLE16.size = 2 * csr.stateCount)
    (hloop : witness.loopEntryLE16.size = 2 * csr.stateCount)
    (hdistance : witness.distanceU8.size = csr.stateCount)
    (hpage : witness.ValidPage csr 0 csr.stateCount) :
    witness.Valid csr := by
  refine ⟨hnext, hfirst, hsecond, hloop, hdistance, ?_⟩
  intro source
  simpa [TwoStepWitness.ValidPage] using hpage source

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
  · exact Or.inl hzero.2.toEdge
  · exact Or.inr ⟨witness.nextIndex source, hone.2.1.toEdge,
      Or.inl hone.2.2.toEdge⟩
  · exact Or.inr ⟨witness.nextIndex source, htwo.2.1.toEdge,
      Or.inr ⟨witness.nextIndex (witness.nextIndex source),
        htwo.2.2.1.toEdge, htwo.2.2.2.toEdge⟩⟩

/-- A checked flat witness yields the semantic weak-L2 statement for every
state, rather than merely a successful Boolean computation. -/
theorem TwoStepWitness.all_reach_selfLoop_within_two
    (witness : TwoStepWitness) (csr : ByteCSR)
    (hvalid : witness.Valid csr) (source : Fin csr.stateCount) :
    ReachesSelfLoopWithinTwo csr source.val :=
  (hvalid.2.2.2.2.2 source).reachesSelfLoopWithinTwo

end GoertzelV24FiniteTransitionWeakSelfLoop

end Mettapedia.GraphTheory.FourColor
