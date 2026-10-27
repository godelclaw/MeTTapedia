import Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagControls

/-!
# Vector append's length through the front door

The append consumer observes only the length of the completed vector, through the answer-bag driver's cardinality
formula. A length observation does not read the payloads, so it is the same at the bag of as many atoms `a` of the
answer-bag reading's payload language (`AnswerBag.Controls.payloadCalc`). There the driver's formula is the generated
front door's closed formula (`AnswerBagReading.meaning_iff`):

- **the length is the front door's native type** at the bag of `a`s of that length (`sat_size_iff`);
- **the consumer's runtime check is a corollary** (`check_iff_frontDoor`), and so is the length of an appended vector
  (`append_length_iff_frontDoor`);
- the generated front door decides the length of small bags, and the runtime agrees (`three_of_three`,
  `not_two_of_three`), with the kernel evaluating the answers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag.Controls (payloadCalc payload payloads frontAnswer agrees a)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement (AgreesOn)
open Mettapedia.GSLT.LanguageDef IndexedInductive IndexedInductiveNatVec

/-- `n` atoms `a`. -/
def atoms (n : Nat) : List Pattern := List.replicate n a

theorem atoms_payloads (n : Nat) : Payloads payloadCalc (atoms n) :=
  payloads fun _ member => .inl (List.eq_of_mem_replicate member)

/-- The front door's closed formula of the length formula. -/
def sizeFormula (count : Nat) : Formula 0 :=
  (ofCore (LeafTable.positiveIndex (leaves (BagModel.sizeExactly count)))
    (LeafTable.negativeIndex (leaves (BagModel.sizeExactly count))) kindOf true
    (BagModel.sizeExactly count)).subst (LeafTable.closing (leaves (BagModel.sizeExactly count)) testFormula)

/-- **The length is the front door's native type** at the bag of `a`s of that length. -/
theorem sat_size_iff (count n : Nat) :
    (Reference RelationEnv.empty payloadCalc).sat Env.closed (sizeFormula count) (BagModel.encode (atoms n)) ↔
      n = count := by
  refine (meaning_iff (relEnv := RelationEnv.empty) payload (BagModel.sizeExactly count) (atoms_payloads n)).symm.trans ?_
  rw [Instances.SpatialBag.meaning_at_bag, BagModel.sizeExactly_iff]
  simp [atoms]

/-- **The consumer's runtime check is a corollary** of the front door's native type. -/
theorem check_iff_frontDoor (count : Nat) (items : List Pattern) (budget : Nat)
    (enough : Runtime.decisionBound Instances.SpatialBag.driver Instances.SpatialBag.engine
      (BagModel.sizeExactly count) (decoded items) ≤ budget) :
    (check count items budget).readout = .judgment (.decided true) ↔
      (Reference RelationEnv.empty payloadCalc).sat Env.closed (sizeFormula count)
        (BagModel.encode (atoms items.length)) := by
  rw [check_iff count items budget enough, sat_size_iff]

/-- **The length of an appended vector** is the front door's native type. -/
theorem append_length_iff_frontDoor {A : Type} (payloadOf : A → Pattern) {n m : Natural.Carrier}
    (left : Vectors.Vector A n) (right : Vectors.Vector A m) (count : Nat) :
    BagModel.holds (BagModel.sizeExactly count) (sourceBag payloadOf (Vectors.append left right)) ↔
      (Reference RelationEnv.empty payloadCalc).sat Env.closed (sizeFormula count)
        (BagModel.encode (atoms (Natural.toNat n + Natural.toNat m))) := by
  rw [append_source_length_iff, sat_size_iff]

theorem three_answer : frontAnswer (BagModel.sizeExactly 3) (atoms 3) = some true := by decide +kernel

/-- **Three atoms have length three**, decided by the generated front door; the runtime agrees. -/
theorem three_of_three : AgreesOn Instances.SpatialBag.installed (BagModel.sizeExactly 3) (BagModel.encode (atoms 3)) true :=
  agrees _ (atoms_payloads 3) three_answer

theorem two_answer : frontAnswer (BagModel.sizeExactly 2) (atoms 3) = some false := by decide +kernel

/-- **Three atoms do not have length two.** -/
theorem not_two_of_three :
    AgreesOn Instances.SpatialBag.installed (BagModel.sizeExactly 2) (BagModel.encode (atoms 3)) false :=
  agrees _ (atoms_payloads 3) two_answer

end Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend
