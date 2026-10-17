import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec

/-!
# MM2 support capabilities and encoding boundaries

This module characterizes the support-valued core already formalized by
`Space`, `resultSupport`, and the work-queue semantics.  It carefully separates
three claims that are easy to conflate:

1. Native MM2 storage and its count/sum reductions are duplicate-insensitive.
2. Explicit counts can nevertheless be represented as ordinary MM2 atoms.
3. Such a representation cannot preserve both occurrence multiplicity and the
   native idempotent union operation through a faithful choice homomorphism.

The third statement is an encoding-algebra obstruction, not a computability
separation.  It says that a counted encoding must change the update/merge
protocol somewhere; it does not say that MM2 cannot carry counts as data.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Which reduction presentations factor through support? -/

/-- An aggregator is support-invariant when only the distinct staged atoms
matter, not their order or occurrence multiplicity. -/
def AggregatorSupportInvariant (aggregator : FoldAggregator) : Prop :=
  ∀ left right : List Atom,
    resultSupport left = resultSupport right →
      applyAggregator aggregator left = applyAggregator aggregator right

/-- Native support count depends only on the staged support. -/
theorem count_support_invariant : AggregatorSupportInvariant .count := by
  intro left right supportEq
  simp [applyAggregator, supportEq]

/-- Native support sum depends only on the staged support. -/
theorem sum_support_invariant : AggregatorSupportInvariant .sum := by
  intro left right supportEq
  simp [applyAggregator, supportIntSum, supportEq]

/-- The authored `selectFirst` protocol does not factor through support:
swapping two distinct rows preserves support but changes the selected row. -/
theorem selectFirst_not_support_invariant :
    ¬ AggregatorSupportInvariant .selectFirst := by
  intro invariant
  have sameSupport :
      resultSupport [.symbol "left", .symbol "right"] =
        resultSupport [.symbol "right", .symbol "left"] := by
    decide
  have sameResult := invariant _ _ sameSupport
  simp [applyAggregator] at sameResult

/-- Repeated occurrences are invisible to native support count. -/
theorem support_count_duplicate_canary (answer : Atom) :
    applyAggregator .count [answer, answer] =
      some (.grounded (.int 1)) := by
  simp [applyAggregator, resultSupport]

/-- The support count can therefore differ from occurrence count. -/
theorem support_count_not_occurrence_count (answer : Atom) :
    applyAggregator .count [answer, answer] ≠
      some (.grounded (.int ([answer, answer].length))) := by
  simp [applyAggregator, resultSupport]

/-! ## Explicit counts remain representable as atoms -/

/-- A structural MM2 atom carrying an explicit natural-number count. -/
def countedAtom (payload : Atom) (count : ℕ) : Atom :=
  .expression [.symbol "counted", payload, .grounded (.int count)]

/-- The count field of `countedAtom` is injective for a fixed payload. -/
theorem countedAtom_count_injective (payload : Atom) :
    Function.Injective (countedAtom payload) := by
  intro left right equality
  have countEquality : (left : Int) = (right : Int) := by
    simpa [countedAtom] using equality
  exact Int.ofNat_inj.mp countEquality

/-- A support-valued MM2 space can distinguish all explicit counts.

This is the positive counterexample to the overstrong claim that set-valued
storage cannot represent multiplicity.  It can; the count becomes authored
data rather than native occurrence structure. -/
theorem explicit_count_spaces_injective (payload : Atom) :
    Function.Injective
      (fun count : ℕ => ({countedAtom payload count} : Space)) := by
  intro left right equality
  apply countedAtom_count_injective payload
  exact Finset.singleton_inj.mp equality

/-! ## The native union algebra cannot carry faithful bag choice -/

/-- An encoding carries occurrence-bag choice directly into support union. -/
def PreservesBagChoice {α β : Type} [DecidableEq β]
    (encode : Multiset α → Finset β) : Prop :=
  ∀ left right,
    encode (left + right) = encode left ∪ encode right

/-- No faithful encoding can preserve occurrence-bag addition as native
idempotent support union.

Taking one occurrence twice forces its image to equal the image of one
occurrence because union is idempotent.  Faithfulness would then identify
multisets of cardinalities two and one.  An explicit-count encoding therefore
needs a non-union update or merge operation (for example read/replace/add),
which is precisely the algebraic encoding tax. -/
theorem no_faithful_bag_choice_encoding_into_support_union
    {β : Type} [DecidableEq β] :
    ¬ ∃ encode : Multiset Unit → Finset β,
        Function.Injective encode ∧ PreservesBagChoice encode := by
  rintro ⟨encode, faithful, preserves⟩
  let one : Multiset Unit := {()}
  have sameImage : encode (one + one) = encode one := by
    calc
      encode (one + one) = encode one ∪ encode one := preserves one one
      _ = encode one := by ext; simp
  have impossible : one + one = one := faithful sameImage
  have cardEquality := congrArg Multiset.card impossible
  simp [one] at cardEquality

/-- **Every encoding that turns bag addition into union factors through the
support**: what it stores for a bag is what it stores for no element, together
with what it stores for each distinct element. -/
theorem preservesBagChoice_eq_biUnion {α β : Type} [DecidableEq α] [DecidableEq β]
    {encode : Multiset α → Finset β} (preserves : PreservesBagChoice encode) (bag : Multiset α) :
    encode bag = encode 0 ∪ bag.toFinset.biUnion fun element => encode {element} := by
  induction bag using Multiset.induction_on with
  | empty => simp
  | @cons element bag inductionHypothesis =>
      rw [show element ::ₘ bag = {element} + bag from rfl, preserves, inductionHypothesis,
        Multiset.toFinset_add]
      ext key
      simp only [Finset.mem_union, Finset.mem_biUnion, Multiset.toFinset_singleton,
        Finset.mem_singleton]
      constructor
      · rintro (inElement | inZero | ⟨other, otherMember, inOther⟩)
        · exact Or.inr ⟨element, Or.inl rfl, inElement⟩
        · exact Or.inl inZero
        · exact Or.inr ⟨other, Or.inr otherMember, inOther⟩
      · rintro (inZero | ⟨other, rfl | otherMember, inOther⟩)
        · exact Or.inr (Or.inl inZero)
        · exact Or.inl inOther
        · exact Or.inr (Or.inr ⟨other, otherMember, inOther⟩)

/-- Two bags with the same support are stored alike by such an encoding:
multiplicity is lost. -/
theorem preservesBagChoice_eq_of_toFinset_eq {α β : Type} [DecidableEq α] [DecidableEq β]
    {encode : Multiset α → Finset β} (preserves : PreservesBagChoice encode)
    {first second : Multiset α} (sameSupport : first.toFinset = second.toFinset) :
    encode first = encode second := by
  rw [preservesBagChoice_eq_biUnion preserves first, preservesBagChoice_eq_biUnion preserves second,
    sameSupport]

/-! ## A faithful store of occurrences needs occurrence identity in its keys -/

/-- **Keys must identify occurrences.**  Store each occurrence under a key, so
that a set of occurrences is stored as the set of their keys.  If the bag of
payloads can be read back from what is stored, distinct occurrences have
distinct keys. -/
theorem occurrence_keys_injective {Occurrence Payload Key : Type} [DecidableEq Occurrence]
    [DecidableEq Key] (payload : Occurrence → Payload) (key : Occurrence → Key)
    (read : Finset Key → Multiset Payload)
    (faithful : ∀ occurrences : Finset Occurrence,
      read (occurrences.image key) = occurrences.val.map payload) :
    Function.Injective key := by
  intro first second sameKey
  by_contra distinct
  have both := faithful {first, second}
  have one := faithful {first}
  rw [Finset.image_insert, Finset.image_singleton, sameKey,
    Finset.insert_eq_of_mem (Finset.mem_singleton_self (key second))] at both
  rw [Finset.image_singleton, sameKey] at one
  have cards := congrArg Multiset.card (one.symm.trans both)
  rw [Multiset.card_map, Multiset.card_map, Finset.card_val, Finset.card_val, Finset.card_singleton,
    Finset.card_pair distinct] at cards
  exact absurd cards (by decide)

/-- Consequently a key computed from the payload alone stores no repeated
payload faithfully: two distinct occurrences must carry distinct payloads. -/
theorem payload_keys_forbid_repeats {Occurrence Payload Key : Type} [DecidableEq Occurrence]
    [DecidableEq Key] (payload : Occurrence → Payload) (keyOf : Payload → Key)
    (read : Finset Key → Multiset Payload)
    (faithful : ∀ occurrences : Finset Occurrence,
      read (occurrences.image (keyOf ∘ payload)) = occurrences.val.map payload)
    {first second : Occurrence} (distinct : first ≠ second) : payload first ≠ payload second :=
  fun samePayload =>
    distinct (occurrence_keys_injective payload (keyOf ∘ payload) read faithful
      (by simp [samePayload]))

/-- The positive side, for the record: keys that carry an owned occurrence
trace do read back the bag (`MM2OccurrenceSupport.erase_support_bag`), and
counted atoms distinguish every count (`explicit_count_spaces_injective`), at
the price of a non-union update. -/
example : Function.Injective (fun count : ℕ => ({countedAtom (.symbol "a") count} : Space)) :=
  explicit_count_spaces_injective (.symbol "a")

/-! ## Existing positive operational witnesses

The work-queue theory already supplies the complementary strengths:

* `readCopy_mem_exec` and `readCopy_eq_of_mem`: a consumed exec remains visible
  to its snapshot query;
* `canary8_ground_self_respawn`: authored exec atoms can generate later work;
* `fireExecFact_card_lt_of_removeOnly`: a useful terminating fragment;
* `workQueueRunN_steps_le_fuel`: honest exact-fuel execution;
* `upstream_zero_differs_from_exact_fuel`: the pinned upstream post-check
  behavior is observably distinct when the first step changes state.
-/

end Mettapedia.Languages.ProcessCalculi.MORK
