import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTanglePersistentKempe

/-!
# Executable core for the persistent hexagon adversary

The physical mate of one bichromatic web persists under switches of that
same web.  This file tests the strongest boundary-only version of that fact.
It exhibits a nonempty, colour-blind sixty-word language which
avoids the literal hexagon support but carries a deterministic noncrossing
mate for every state and colour pair.  Every component-union switch stays in
the language and preserves the selected mate for that pair.

Thus even stateful same-family persistence does not recover the shared-edge
incidence between the three bichromatic webs.  The remaining source datum is
the genuinely joint idemposition action on one common trivalent web.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonPersistentKempeAdversary

open GoertzelV24RawNooseCountPumping
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24HexCycleBoundarySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Equality pattern `001001`. -/
private def pattern001001 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 1 ∧ word 0 = word 3 ∧ word 0 = word 4 ∧
    word 2 = word 5 ∧ word 0 ≠ word 2)

/-- Equality pattern `001010`. -/
private def pattern001010 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 1 ∧ word 0 = word 3 ∧ word 0 = word 5 ∧
    word 2 = word 4 ∧ word 0 ≠ word 2)

/-- Equality pattern `010001`. -/
private def pattern010001 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 2 ∧ word 0 = word 3 ∧ word 0 = word 4 ∧
    word 1 = word 5 ∧ word 0 ≠ word 1)

/-- Equality pattern `010010`. -/
private def pattern010010 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 2 ∧ word 0 = word 3 ∧ word 0 = word 5 ∧
    word 1 = word 4 ∧ word 0 ≠ word 1)

/-- Three two-element colour classes with equality pattern `010212`. -/
private def pattern010212 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 2 ∧ word 1 = word 4 ∧ word 3 = word 5 ∧
    word 0 ≠ word 1 ∧ word 0 ≠ word 3 ∧ word 1 ≠ word 3)

/-- Three two-element colour classes with equality pattern `010221`. -/
private def pattern010221 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 2 ∧ word 1 = word 5 ∧ word 3 = word 4 ∧
    word 0 ≠ word 1 ∧ word 0 ≠ word 3 ∧ word 1 ≠ word 3)

/-- Three two-element colour classes with equality pattern `011202`. -/
private def pattern011202 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 4 ∧ word 1 = word 2 ∧ word 3 = word 5 ∧
    word 0 ≠ word 1 ∧ word 0 ≠ word 3 ∧ word 1 ≠ word 3)

/-- Three two-element colour classes with equality pattern `011220`. -/
private def pattern011220 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 5 ∧ word 1 = word 2 ∧ word 3 = word 4 ∧
    word 0 ≠ word 1 ∧ word 0 ≠ word 3 ∧ word 1 ≠ word 3)

/-- Three two-element colour classes with equality pattern `012102`. -/
private def pattern012102 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 4 ∧ word 1 = word 3 ∧ word 2 = word 5 ∧
    word 0 ≠ word 1 ∧ word 0 ≠ word 2 ∧ word 1 ≠ word 2)

/-- Three two-element colour classes with equality pattern `012120`. -/
private def pattern012120 (word : HexagonTaitWord) : Bool :=
  decide (word 0 = word 5 ∧ word 1 = word 3 ∧ word 2 = word 4 ∧
    word 0 ≠ word 1 ∧ word 0 ≠ word 2 ∧ word 1 ≠ word 2)

/-- The adversary language is the union of ten equality-pattern classes.
Because its definition uses only equality and inequality, it is insensitive to
the names assigned to the three Tait colours. -/
def persistentAdversaryBool (word : HexagonTaitWord) : Bool :=
  pattern001001 word || pattern001010 word ||
  pattern010001 word || pattern010010 word ||
  pattern010212 word || pattern010221 word ||
  pattern011202 word || pattern011220 word ||
  pattern012102 word || pattern012120 word

def persistentAdversary : Set HexagonTaitWord :=
  {word | persistentAdversaryBool word = true}

theorem persistentAdversaryBool_eq_true_iff (word : HexagonTaitWord) :
    persistentAdversaryBool word = true ↔ word ∈ persistentAdversary :=
  Iff.rfl

private instance persistentAdversaryDecidablePred :
    DecidablePred (fun word : HexagonTaitWord => word ∈ persistentAdversary) :=
  fun word => by
    unfold persistentAdversary
    infer_instance

/-- The finite carrier corresponding exactly to `persistentAdversary`. -/
def persistentAdversaryFinset : Finset HexagonTaitWord :=
  Finset.univ.filter fun word => persistentAdversaryBool word

theorem mem_persistentAdversaryFinset_iff (word : HexagonTaitWord) :
    word ∈ persistentAdversaryFinset ↔ word ∈ persistentAdversary := by
  simp [persistentAdversaryFinset, persistentAdversary]

/-- The ten colour-blind equality patterns contain exactly sixty boundary
words over the three Tait colours. -/
theorem card_persistentAdversaryFinset :
    persistentAdversaryFinset.card = 60 := by
  decide

/-- Flat untrusted pattern hints: three blocks of 3^6 bytes.  The
kernel checker below validates every supported row and ignores defaults. -/
@[reducible] private def persistentPatternPayloadRedBlue : ByteArray :=
  ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
@[reducible] private def persistentPatternPayloadRedPurple : ByteArray :=
  ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
@[reducible] private def persistentPatternPayloadBluePurple : ByteArray :=
  ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def persistentColorDigit (color : TaitColor) : Nat :=
  if color.1 = red then 0 else if color.1 = blue then 1 else 2

private def persistentWordIndex (word : HexagonTaitWord) : Nat :=
  persistentColorDigit (word 0) * 243 +
    persistentColorDigit (word 1) * 81 +
    persistentColorDigit (word 2) * 27 +
    persistentColorDigit (word 3) * 9 +
    persistentColorDigit (word 4) * 3 +
    persistentColorDigit (word 5)

/-- The pattern suggested by the flat payload.  Correctness is not trusted:
the three certificate modules check the mathematical witness independently. -/
def persistentPattern (word : HexagonTaitWord)
    (pair : TaitColorPair) : Fin 5 :=
  let payload := match pair with
    | .redBlue => persistentPatternPayloadRedBlue
    | .redPurple => persistentPatternPayloadRedPurple
    | .bluePurple => persistentPatternPayloadBluePurple
  Fin.ofNat 5
    ((payload.get! (persistentWordIndex word)).toNat)


/-- Mathematical certificate carried by the deterministic boundary machine:
ordinary closure plus persistence of the same mate at every successor. -/
def PersistentCandidateKempeWitness
    (word : HexagonTaitWord) (pair : TaitColorPair) : Prop :=
  let pattern := persistentPattern word pair
  let mate := candidateMate word pair pattern
  CandidateKempeWitness persistentAdversary word pair pattern ∧
    ∀ selected : Finset (Fin 6),
      IsComponentUnion mate selected →
        candidateMate (swapBoundaryWord word pair selected) pair
            (persistentPattern (swapBoundaryWord word pair selected) pair) =
          mate

private def twoBooleans : List Bool := [false, true]

private theorem mem_twoBooleans (value : Bool) : value ∈ twoBooleans := by
  cases value <;> simp [twoBooleans]

private def selectedPorts (b0 b1 b2 b3 b4 b5 : Bool) :
    Finset (Fin 6) :=
  Finset.univ.filter fun port => ![b0, b1, b2, b3, b4, b5] port

private theorem selectedPorts_of_finset (selected : Finset (Fin 6)) :
    selectedPorts
      (decide (0 ∈ selected)) (decide (1 ∈ selected))
      (decide (2 ∈ selected)) (decide (3 ∈ selected))
      (decide (4 ∈ selected)) (decide (5 ∈ selected)) = selected := by
  ext port
  fin_cases port <;> simp [selectedPorts]

private def allSelectedPortSets (test : Finset (Fin 6) → Bool) : Bool :=
  twoBooleans.all fun b0 =>
    twoBooleans.all fun b1 =>
      twoBooleans.all fun b2 =>
        twoBooleans.all fun b3 =>
          twoBooleans.all fun b4 =>
            twoBooleans.all fun b5 =>
              test (selectedPorts b0 b1 b2 b3 b4 b5)

private theorem allSelectedPortSets_eq_true_iff
    (test : Finset (Fin 6) → Bool) :
    allSelectedPortSets test = true ↔ ∀ selected, test selected = true := by
  simp only [allSelectedPortSets, List.all_eq_true]
  constructor
  · intro h selected
    have hselected := h
      (decide (0 ∈ selected)) (mem_twoBooleans _)
      (decide (1 ∈ selected)) (mem_twoBooleans _)
      (decide (2 ∈ selected)) (mem_twoBooleans _)
      (decide (3 ∈ selected)) (mem_twoBooleans _)
      (decide (4 ∈ selected)) (mem_twoBooleans _)
      (decide (5 ∈ selected)) (mem_twoBooleans _)
    rw [selectedPorts_of_finset] at hselected
    exact hselected
  · intro h b0 _ b1 _ b2 _ b3 _ b4 _ b5 _
    exact h (selectedPorts b0 b1 b2 b3 b4 b5)

def persistentCandidateKempeWitnessBool
    (word : HexagonTaitWord) (pair : TaitColorPair) : Bool :=
  let pattern := persistentPattern word pair
  let mate := candidateMate word pair pattern
  candidateKempeWitnessBool persistentAdversaryBool word pair pattern &&
    allSelectedPortSets fun selected =>
      (!decide (IsComponentUnion mate selected)) ||
        decide (∀ port,
          candidateMate (swapBoundaryWord word pair selected) pair
              (persistentPattern (swapBoundaryWord word pair selected) pair)
              port =
            mate port)

theorem persistentCandidateKempeWitnessBool_eq_true_iff
    (word : HexagonTaitWord) (pair : TaitColorPair) :
    persistentCandidateKempeWitnessBool word pair = true ↔
      PersistentCandidateKempeWitness word pair := by
  rw [persistentCandidateKempeWitnessBool, Bool.and_eq_true,
    candidateKempeWitnessBool_eq_true_iff persistentAdversary
      persistentAdversaryBool persistentAdversaryBool_eq_true_iff,
    allSelectedPortSets_eq_true_iff]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, PersistentCandidateKempeWitness]
  constructor
  · rintro ⟨hordinary, hpersistent⟩
    refine ⟨hordinary, ?_⟩
    intro selected hunion
    funext port
    exact (hpersistent selected).resolve_left (fun hnot => hnot hunion) port
  · rintro ⟨hordinary, hpersistent⟩
    refine ⟨hordinary, ?_⟩
    intro selected
    by_cases hunion : IsComponentUnion
        (candidateMate word pair (persistentPattern word pair)) selected
    · exact Or.inr (fun port => congrFun (hpersistent selected hunion) port)
    · exact Or.inl hunion

def explicitWord (a b c d e f : TaitColor) : HexagonTaitWord :=
  ![a, b, c, d, e, f]

theorem explicitWord_of_word (word : HexagonTaitWord) :
    explicitWord (word 0) (word 1) (word 2) (word 3) (word 4) (word 5) =
      word := by
  funext port
  fin_cases port <;> rfl

private def threeTaitColors : List TaitColor :=
  [⟨red, red_ne_zero⟩, ⟨blue, blue_ne_zero⟩,
    ⟨purple, purple_ne_zero⟩]

private theorem mem_threeTaitColors (color : TaitColor) :
    color ∈ threeTaitColors := by
  rcases color with ⟨color, hcolor⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero color hcolor with
    rfl | rfl | rfl <;> simp [threeTaitColors]

def persistentRow (a b c d e f : TaitColor)
    (pair : TaitColorPair) : Bool :=
  let word := explicitWord a b c d e f
  if persistentAdversaryBool word = true then
    persistentCandidateKempeWitnessBool word pair &&
      !hexBoundaryRealizableBool word
  else true

def allPersistentRows (pair : TaitColorPair) : Bool :=
  threeTaitColors.all fun a =>
    threeTaitColors.all fun b =>
      threeTaitColors.all fun c =>
        threeTaitColors.all fun d =>
          threeTaitColors.all fun e =>
            threeTaitColors.all fun f => persistentRow a b c d e f pair

theorem persistentRow_eq_true
    (pair : TaitColorPair) (a b c d e f : TaitColor) :
    allPersistentRows pair = true → persistentRow a b c d e f pair = true := by
  simp only [allPersistentRows, List.all_eq_true]
  intro h
  exact h a (mem_threeTaitColors a)
    b (mem_threeTaitColors b) c (mem_threeTaitColors c)
    d (mem_threeTaitColors d) e (mem_threeTaitColors e)
    f (mem_threeTaitColors f)

end GoertzelV24HexagonPersistentKempeAdversary

end Mettapedia.GraphTheory.FourColor
