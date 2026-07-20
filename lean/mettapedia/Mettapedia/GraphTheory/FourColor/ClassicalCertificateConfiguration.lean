import Mathlib.Data.Fintype.Card
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateHypermap

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfiguration

open ClassicalCertificateHypermap

/-- An executable permutation table on `n` darts.  Values are kept as natural
numbers so that certificate producers need not manufacture dependent terms. -/
abbrev RawTable (n : Nat) := Fin n → Nat

namespace RawTable

variable {n : Nat}

/-- Total interpretation of a raw table.  An out-of-range entry fixes its
input; accepted certificates never use this fallback branch. -/
def toFin (table : RawTable n) (dart : Fin n) : Fin n :=
  if h : table dart < n then ⟨table dart, h⟩ else dart

/-- The two conditions checked for each permutation table. -/
def IsPermutation (table : RawTable n) : Prop :=
  (∀ dart, table dart < n) ∧ Function.Injective table

instance (table : RawTable n) : Decidable table.IsPermutation := by
  unfold IsPermutation Function.Injective
  infer_instance

theorem toFin_val (table : RawTable n) (h : table.IsPermutation)
    (dart : Fin n) :
    (table.toFin dart).val = table dart := by
  simp [toFin, h.1 dart]

theorem toFin_injective (table : RawTable n) (h : table.IsPermutation) :
    Function.Injective table.toFin := by
  intro left right heq
  apply h.2
  simpa [toFin, h.1 left, h.1 right] using congrArg Fin.val heq

theorem toFin_bijective (table : RawTable n) (h : table.IsPermutation) :
    Function.Bijective table.toFin :=
  ⟨table.toFin_injective h,
    Finite.surjective_of_injective (table.toFin_injective h)⟩

/-- An accepted raw table determines a genuine finite permutation. -/
noncomputable def toPerm (table : RawTable n) (h : table.IsPermutation) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective table.toFin (table.toFin_bijective h)

@[simp] theorem toPerm_apply (table : RawTable n)
    (h : table.IsPermutation) (dart : Fin n) :
    table.toPerm h dart = table.toFin dart :=
  rfl

end RawTable

/-- Raw finite-hypermap data accepted from a certificate producer. -/
structure RawHypermap where
  dartCount : Nat
  edge : RawTable dartCount
  node : RawTable dartCount
  face : RawTable dartCount

namespace RawHypermap

/-- Semantic validity of an executable raw hypermap. -/
def WellFormed (raw : RawHypermap) : Prop :=
  raw.edge.IsPermutation ∧
    raw.node.IsPermutation ∧
    raw.face.IsPermutation ∧
    ∀ dart,
      raw.node.toFin (raw.face.toFin (raw.edge.toFin dart)) = dart

instance (raw : RawHypermap) : Decidable raw.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Reflected validity checker for a raw finite hypermap. -/
def wellFormedChecker (raw : RawHypermap) : Bool :=
  decide raw.WellFormed

theorem wellFormed_of_checker_true (raw : RawHypermap)
    (haccepted : raw.wellFormedChecker = true) :
    raw.WellFormed := by
  exact Bool.of_decide_true (by simpa [wellFormedChecker] using haccepted)

theorem checker_true_of_wellFormed (raw : RawHypermap)
    (hvalid : raw.WellFormed) :
    raw.wellFormedChecker = true := by
  simp [wellFormedChecker, hvalid]

/-- Every accepted raw certificate inhabits the standard finite-hypermap
structure used by the rotation-system bridge. -/
noncomputable def toFiniteHypermap (raw : RawHypermap)
    (hvalid : raw.WellFormed) :
    FiniteHypermap (Fin raw.dartCount) where
  edge := raw.edge.toPerm hvalid.1
  node := raw.node.toPerm hvalid.2.1
  face := raw.face.toPerm hvalid.2.2.1
  triangle := hvalid.2.2.2

/-- Checker-facing form of `toFiniteHypermap`: the only input proof is the
Boolean certificate equation. -/
noncomputable def finiteHypermapOfChecker (raw : RawHypermap)
    (haccepted : raw.wellFormedChecker = true) :
    FiniteHypermap (Fin raw.dartCount) :=
  raw.toFiniteHypermap (raw.wellFormed_of_checker_true haccepted)

end RawHypermap

/-- Materialized certificate data.  Arrays are the trust boundary: an
external producer may emit them by any method, but only the reflected checker
can turn them into a finite hypermap. -/
structure HypermapCode where
  dartCount : Nat
  edge : Array Nat
  node : Array Nat
  face : Array Nat
  deriving Repr

namespace HypermapCode

/-- Total lookup used while checking external arrays. -/
def lookup (table : Array Nat) (index : Nat) : Nat :=
  table[index]?.getD 0

/-- Decode arrays to the proof-oriented raw representation. -/
def decode (code : HypermapCode) : RawHypermap where
  dartCount := code.dartCount
  edge := fun dart => lookup code.edge dart.val
  node := fun dart => lookup code.node dart.val
  face := fun dart => lookup code.face dart.val

/-- Exact certificate semantics: every array has the declared dart count and
the decoded tables form a finite hypermap. -/
def Accepted (code : HypermapCode) : Prop :=
  code.edge.size = code.dartCount ∧
    code.node.size = code.dartCount ∧
    code.face.size = code.dartCount ∧
    code.decode.WellFormed

instance (code : HypermapCode) : Decidable code.Accepted := by
  unfold Accepted
  infer_instance

def checker (code : HypermapCode) : Bool :=
  decide code.Accepted

theorem accepted_of_checker_true (code : HypermapCode)
    (haccepted : code.checker = true) :
    code.Accepted := by
  exact Bool.of_decide_true (by simpa [checker] using haccepted)

theorem decoded_wellFormed_of_checker_true (code : HypermapCode)
    (haccepted : code.checker = true) :
    code.decode.WellFormed :=
  (code.accepted_of_checker_true haccepted).2.2.2

/-- Accepted materialized data produces the same standard finite-hypermap
object as an accepted function-valued table. -/
noncomputable def finiteHypermapOfChecker (code : HypermapCode)
    (haccepted : code.checker = true) :
    FiniteHypermap (Fin code.dartCount) :=
  code.decode.toFiniteHypermap
    (code.decoded_wellFormed_of_checker_true haccepted)

/-- Materialize a raw map for export by a certificate-generation tool. -/
def materialize (raw : RawHypermap) : HypermapCode where
  dartCount := raw.dartCount
  edge := Array.ofFn raw.edge
  node := Array.ofFn raw.node
  face := Array.ofFn raw.face

end HypermapCode

/-- The two-dart seed from which classical configuration programs grow. -/
def seed : RawHypermap where
  dartCount := 2
  edge := fun dart => if dart.val = 0 then 1 else 0
  node := fun dart => if dart.val = 0 then 1 else 0
  face := fun dart => dart.val

theorem seed_checker : seed.wellFormedChecker = true := by
  decide

/-- A raw hypermap together with the current dart on its outer ring. -/
structure RawPointedHypermap where
  dartCount : Nat
  edge : RawTable dartCount
  node : RawTable dartCount
  face : RawTable dartCount
  pointer : Fin dartCount

namespace RawPointedHypermap

/-- Forget the distinguished outer-ring dart. -/
def pointee (state : RawPointedHypermap) : RawHypermap where
  dartCount := state.dartCount
  edge := state.edge
  node := state.node
  face := state.face

private def oldDart {n : Nat} (dart : Fin (n + 2))
    (hold : 2 ≤ dart.val) : Fin n :=
  ⟨dart.val - 2, by omega⟩

/-- Add the two fresh darts `X`, `Xe`, placing every old dart after them. -/
private def extendedEdge (state : RawPointedHypermap) :
    RawTable (state.dartCount + 2) := fun dart =>
  if hzero : dart.val = 0 then 1
  else if hone : dart.val = 1 then 0
  else
    let old := oldDart dart (by omega)
    (state.edge.toFin old).val + 2

/-- The classical `U` extension: add a face without adding a junction. -/
def extendU (state : RawPointedHypermap) : RawPointedHypermap where
  dartCount := state.dartCount + 2
  edge := extendedEdge state
  node := fun dart =>
    if hzero : dart.val = 0 then 1
    else if hone : dart.val = 1 then
      (state.node.toFin (state.node.toFin state.pointer)).val + 2
    else
      let old := oldDart dart (by omega)
      if old = state.node.toFin state.pointer then 0
      else (state.node.toFin old).val + 2
  face := fun dart =>
    if hzero : dart.val = 0 then 0
    else if hone : dart.val = 1 then
      (state.node.toFin state.pointer).val + 2
    else
      let old := oldDart dart (by omega)
      if state.face.toFin old = state.node.toFin state.pointer then 1
      else (state.face.toFin old).val + 2
  pointer := ⟨0, by omega⟩

/-- Whether the pointed outer ring has more than two darts. -/
def hasLongRing (state : RawPointedHypermap) : Bool :=
  decide
    (state.face.toFin (state.edge.toFin state.pointer) ≠
      state.node.toFin state.pointer)

/-- The classical `N` extension immediately to the left of the ring head. -/
def extendN (state : RawPointedHypermap) : RawPointedHypermap where
  dartCount := state.dartCount + 2
  edge := extendedEdge state
  node := fun dart =>
    if hzero : dart.val = 0 then
      if state.hasLongRing then
        (state.node.toFin state.pointer).val + 2
      else 0
    else if hone : dart.val = 1 then
      (state.face.toFin (state.edge.toFin state.pointer)).val + 2
    else
      let old := oldDart dart (by omega)
      if old = state.pointer then 1
      else if state.node.toFin (state.node.toFin old) = state.pointer then 0
      else (state.node.toFin old).val + 2
  face := fun dart =>
    if hzero : dart.val = 0 then state.pointer.val + 2
    else if hone : dart.val = 1 then
      if state.hasLongRing then
        (state.face.toFin
          (state.edge.toFin
            (state.face.toFin
              (state.edge.toFin state.pointer)))).val + 2
      else 0
    else
      let old := oldDart dart (by omega)
      if old = state.edge.toFin
          (state.face.toFin (state.edge.toFin state.pointer)) then 1
      else if old = state.edge.toFin (state.node.toFin state.pointer) then 0
      else (state.face.toFin old).val + 2
  pointer := ⟨0, by omega⟩

/-- Add one outer junction and start a new face. -/
def extendY (state : RawPointedHypermap) : RawPointedHypermap :=
  state.extendU.extendN

/-- Add two adjacent outer junctions, closing an inner face. -/
def extendH (state : RawPointedHypermap) : RawPointedHypermap :=
  state.extendY.extendN

private def returnTimeAux {n : Nat} (next : Fin n → Fin n)
    (start : Fin n) : Nat → Fin n → Nat
  | 0, _ => 0
  | fuel + 1, current =>
      let following := next current
      if following = start then 1
      else
        let later := returnTimeAux next start fuel following
        if later = 0 then 0 else later + 1

/-- Bounded first-return time of the node table at the pointer. -/
def nodeOrder (state : RawPointedHypermap) : Nat :=
  returnTimeAux state.node.toFin state.pointer state.dartCount state.pointer

private def iterateNode (state : RawPointedHypermap) :
    Nat → Fin state.dartCount → Fin state.dartCount
  | 0, dart => dart
  | count + 1, dart => iterateNode state count (state.node.toFin dart)

/-- Reverse ring rotation.  As in the classical program language, an amount
at least the ring order leaves the pointer unchanged. -/
def rotate (amount : Nat) (state : RawPointedHypermap) :
    RawPointedHypermap where
  dartCount := state.dartCount
  edge := state.edge
  node := state.node
  face := state.face
  pointer := state.iterateNode (state.nodeOrder - amount) state.pointer

end RawPointedHypermap

/-- The three construction steps used by every member of the classical
reducible-configuration catalogue. -/
inductive ConfigurationStep where
  | rotate (amount : Nat)
  | yellow
  | hexagon
  deriving DecidableEq, Repr

abbrev ConfigurationProgram := List ConfigurationStep

/-- The pointed two-dart seed. -/
def pointedSeed : RawPointedHypermap where
  dartCount := seed.dartCount
  edge := seed.edge
  node := seed.node
  face := seed.face
  pointer := ⟨1, by decide⟩

def applyConfigurationStep (step : ConfigurationStep)
    (state : RawPointedHypermap) : RawPointedHypermap :=
  match step with
  | .rotate amount => state.rotate amount
  | .yellow => state.extendY
  | .hexagon => state.extendH

/-- Configuration programs are interpreted from right to left. -/
def compileConfigurationProgram :
    ConfigurationProgram → RawPointedHypermap
  | [] => pointedSeed
  | step :: rest =>
      applyConfigurationStep step (compileConfigurationProgram rest)

/-- A catalogue entry: symmetry metadata, contract references, and its map
construction program. -/
structure Configuration where
  symmetric : Bool
  contractReferences : List Nat
  program : ConfigurationProgram
  deriving DecidableEq, Repr

def Configuration.compile (configuration : Configuration) :
    RawPointedHypermap :=
  compileConfigurationProgram configuration.program

/-- The sample pentagonal map from the classical construction source. -/
def pentagonalSampleProgram : ConfigurationProgram :=
  [.hexagon, .rotate 4, .yellow, .yellow]

theorem pentagonalSample_checker :
    (compileConfigurationProgram pentagonalSampleProgram).pointee.wellFormedChecker =
      true := by
  decide

/-- The first entry of the classical reducible-configuration catalogue. -/
def firstCatalogueSample : Configuration where
  symmetric := true
  contractReferences := [15]
  program :=
    [.hexagon, .rotate 3, .hexagon, .rotate 5, .hexagon, .rotate 5,
      .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .rotate 2,
      .yellow, .rotate 1, .yellow]

def firstCatalogueSampleCode : HypermapCode where
  dartCount := 42
  edge :=
    #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16,
      19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32,
      35, 34, 37, 36, 39, 38, 41, 40]
  node :=
    #[5, 27, 1, 18, 3, 12, 11, 17, 7, 28, 9, 22, 6, 21, 13, 39, 15, 8,
      4, 35, 19, 14, 0, 31, 23, 32, 25, 2, 10, 41, 29, 24, 26, 36, 33,
      20, 34, 40, 37, 16, 38, 30]
  face :=
    #[2, 22, 4, 27, 0, 18, 8, 12, 10, 17, 6, 28, 14, 5, 16, 21, 7, 39,
      20, 3, 13, 35, 24, 11, 26, 31, 1, 32, 30, 9, 23, 41, 34, 25, 19,
      36, 38, 33, 15, 40, 29, 37]

theorem firstCatalogueSampleCode_checker :
    firstCatalogueSampleCode.checker = true := by
  decide

end ClassicalCertificateConfiguration

end Mettapedia.GraphTheory.FourColor
