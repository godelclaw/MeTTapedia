import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatialControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagNames

/-!
# Completed space answers through the front door

The occurrence and complete-packet questions about a space's answer list are bag formulas. Their answers are arbitrary
patterns, so the front door reads them at the bag of the answers' names (`AnswerBag.Names`):

- **an answer occurrence is the front door's native type** at the bag of names (`occurrence_iff_frontDoor`), and so is
  a complete packet (`packet_iff_frontDoor`);
- **the generated front door's decided answers are the space's**: a decided answer about an occurrence or a packet is
  the space judgment (`occurrence_of_answer`, `packet_of_answer`);
- on the space with two observations of `b` the generated front door decides, with the kernel evaluating it, that `b`
  occurs twice and not three times, that `a` does not occur, and that the complete packet is `b, b` and not `b`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial

open Mettapedia.Languages.MeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag (Reference)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag.Names

/-- **An answer occurrence is the front door's native type** at the bag of the answers' names. -/
theorem occurrence_iff_frontDoor (space : PeTTa.PeTTaSpace) (pattern template result : Pattern) (occurrence : Nat) :
    MeTTaSpace.QueryMember space pattern template result occurrence ↔
      (Reference RelationEnv.empty numerals).sat Env.closed
        (closedFormula (occurrenceFormula result occurrence) (answers space pattern template))
        (BagModel.encode (namedBag (occurrenceFormula result occurrence) (answers space pattern template))) :=
  (occurrence_meaning space pattern template result occurrence).symm.trans (holds_iff_frontDoor _ _)

/-- **A complete packet is the front door's native type** at the bag of the answers' names. -/
theorem packet_iff_frontDoor (space : PeTTa.PeTTaSpace) (pattern template : Pattern) (expected : List Pattern) :
    MeTTaSpace.checkPacket space pattern template expected = true ↔
      (Reference RelationEnv.empty numerals).sat Env.closed
        (closedFormula (packetFormula expected) (answers space pattern template))
        (BagModel.encode (namedBag (packetFormula expected) (answers space pattern template))) :=
  (packet_meaning space pattern template expected).symm.trans (holds_iff_frontDoor _ _)

/-- **A decided front-door answer about an occurrence is the space's.** -/
theorem occurrence_of_answer {space : PeTTa.PeTTaSpace} {pattern template result : Pattern} {occurrence rounds : Nat}
    {decided : Bool}
    (answered : answer (occurrenceFormula result occurrence) (answers space pattern template) rounds = some decided) :
    MeTTaSpace.QueryMember space pattern template result occurrence ↔ decided = true :=
  (occurrence_meaning space pattern template result occurrence).symm.trans (answer_sound answered)

/-- **A decided front-door answer about a packet is the space's.** -/
theorem packet_of_answer {space : PeTTa.PeTTaSpace} {pattern template : Pattern} {expected : List Pattern}
    {rounds : Nat} {decided : Bool}
    (answered : answer (packetFormula expected) (answers space pattern template) rounds = some decided) :
    MeTTaSpace.checkPacket space pattern template expected = true ↔ decided = true :=
  (packet_meaning space pattern template expected).symm.trans (answer_sound answered)

namespace Controls

open PeTTa.MeTTaZeroExtension.NativeControls (a b)

theorem answers_eq : answers sourceSpace pattern template = [b, b] := source_answer_bag

theorem second_copy_answer : answer (occurrenceFormula b 1) [b, b] 4 = some true := by decide +kernel

/-- **`b` occurs twice**, decided by the generated front door. -/
theorem second_copy_frontDoor : MeTTaSpace.QueryMember sourceSpace pattern template b 1 :=
  (occurrence_of_answer (by rw [answers_eq]; exact second_copy_answer)).mpr rfl

theorem third_copy_answer : answer (occurrenceFormula b 2) [b, b] 4 = some false := by decide +kernel

/-- **`b` does not occur three times.** -/
theorem third_copy_absent_frontDoor : ¬ MeTTaSpace.QueryMember sourceSpace pattern template b 2 :=
  fun member => Bool.false_ne_true ((occurrence_of_answer (by rw [answers_eq]; exact third_copy_answer)).mp member)

theorem other_value_answer : answer (occurrenceFormula a 0) [b, b] 4 = some false := by decide +kernel

/-- **`a` does not occur.** -/
theorem other_value_absent_frontDoor : ¬ MeTTaSpace.QueryMember sourceSpace pattern template a 0 :=
  fun member => Bool.false_ne_true ((occurrence_of_answer (by rw [answers_eq]; exact other_value_answer)).mp member)

theorem packet_answer : answer (packetFormula [b, b]) [b, b] 4 = some true := by decide +kernel

/-- **The complete packet is `b, b`.** -/
theorem packet_frontDoor : MeTTaSpace.checkPacket sourceSpace pattern template [b, b] = true :=
  (packet_of_answer (by rw [answers_eq]; exact packet_answer)).mpr rfl

theorem missing_copy_answer : answer (packetFormula [b]) [b, b] 4 = some false := by decide +kernel

/-- **The packet `b` misses a copy.** -/
theorem missing_copy_frontDoor : MeTTaSpace.checkPacket sourceSpace pattern template [b] = false := by
  cases checked : MeTTaSpace.checkPacket sourceSpace pattern template [b] with
  | false => rfl
  | true => exact absurd ((packet_of_answer (by rw [answers_eq]; exact missing_copy_answer)).mp checked) Bool.false_ne_true

end Controls

end Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial
