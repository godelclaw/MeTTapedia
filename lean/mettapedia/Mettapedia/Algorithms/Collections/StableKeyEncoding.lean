import Mathlib.Data.List.Nodup

/-!
First-occurrence key encoding. The dictionary grows only at its right edge;
codes retain every input occurrence. Runtime hashing is admissible only when
its equality agrees with the equality used here. In particular, this model
does not justify hashing a non-equivalence numeric matching relation.
-/

namespace Mettapedia.Algorithms.Collections.StableKeyEncoding

variable {Key : Type*} [DecidableEq Key]

def extend (keys : List Key) (key : Key) : List Key :=
  if key ∈ keys then keys else keys ++ [key]

theorem extend_prefix (keys : List Key) (key : Key) : keys <+: extend keys key := by
  unfold extend
  split <;> simp

theorem mem_extend_self (keys : List Key) (key : Key) : key ∈ extend keys key := by
  by_cases present : key ∈ keys <;> simp [extend, present]

theorem extend_idxOf (keys : List Key) (key : Key) :
    (extend keys key).idxOf key = keys.idxOf key := by
  by_cases present : key ∈ keys
  · simp [extend, present]
  · simp [extend, present, List.idxOf_append_of_notMem]

theorem extend_nodup (keys : List Key) (key : Key) (unique : keys.Nodup) :
    (extend keys key).Nodup := by
  by_cases present : key ∈ keys <;> simp [extend, present, unique, List.nodup_append]
  intro other member same
  exact present (same ▸ member)

theorem mem_extend (keys : List Key) (key target : Key) :
    target ∈ extend keys key ↔ target ∈ keys ∨ target = key := by
  by_cases present : key ∈ keys
  · simp only [extend, if_pos present]
    constructor
    · exact Or.inl
    · rintro (member | rfl)
      · exact member
      · exact present
  · simp [extend, present]

/-- Streaming interning: the prefix dictionary is available before the next
item, and an absent key gets its next zero-based position. -/
def encode (keys : List Key) : List Key → List Key × List Nat
  | [] => (keys, [])
  | key :: rest =>
      let next := encode (extend keys key) rest
      (next.1, keys.idxOf key :: next.2)

theorem encode_prefix (keys input : List Key) : keys <+: (encode keys input).1 := by
  induction input generalizing keys with
  | nil => simp [encode]
  | cons key rest ih =>
      exact (extend_prefix keys key).trans (ih (extend keys key))

theorem encode_nodup (keys input : List Key) (unique : keys.Nodup) :
    (encode keys input).1.Nodup := by
  induction input generalizing keys with
  | nil => exact unique
  | cons key rest ih => exact ih _ (extend_nodup keys key unique)

theorem encode_membership (keys input : List Key) (key : Key) :
    key ∈ (encode keys input).1 ↔ key ∈ keys ∨ key ∈ input := by
  induction input generalizing keys with
  | nil => simp [encode]
  | cons item rest ih => simp [encode, ih, mem_extend, or_assoc]

/-- Later keys cannot renumber any already interned key. -/
theorem earlier_code_unchanged (keys input : List Key) (key : Key) (present : key ∈ keys) :
    (encode keys input).1.idxOf key = keys.idxOf key :=
  ((encode_prefix keys input).idxOf_eq_of_mem present).symm

/-- Decoding the inverse column gives the exact input, including repetitions
and occurrence order. Missing coordinates cannot appear in a valid encoding. -/
theorem decode_encode (keys input : List Key) :
    (encode keys input).2.map (fun code => (encode keys input).1[code]?) =
      input.map some := by
  induction input generalizing keys with
  | nil => simp [encode]
  | cons key rest ih =>
      have present := mem_extend_self keys key
      have code := earlier_code_unchanged (extend keys key) rest key present
      rw [extend_idxOf] at code
      have final_present := (encode_prefix (extend keys key) rest).subset present
      have observation := List.getElem?_idxOf final_present
      rw [code] at observation
      simpa [encode, observation] using congrArg (some key :: ·) (ih (extend keys key))

theorem code_in_bounds (keys input : List Key) (code : Nat)
    (member : code ∈ (encode keys input).2) : code < (encode keys input).1.length := by
  have observed : (encode keys input).1[code]? ∈
      (encode keys input).2.map (fun index => (encode keys input).1[index]?) :=
    List.mem_map.mpr ⟨code, member, rfl⟩
  rw [decode_encode] at observed
  obtain ⟨key, _, value⟩ := List.mem_map.mp observed
  by_contra outside
  have missing := List.getElem?_eq_none (Nat.le_of_not_gt outside)
  rw [missing] at value
  cases value

theorem first_position_existing (history : List Key) (item key : Key) (present : key ∈ history) :
    (history ++ [item]).idxOf key = history.idxOf key :=
  List.idxOf_append_of_mem present

theorem first_position_new (history : List Key) (key : Key) (absent : key ∉ history) :
    (history ++ [key]).idxOf key = history.length := by
  simp [List.idxOf_append_of_notMem absent]

example : encode ([] : List Nat) [8, 3, 8, 4, 3] = ([8, 3, 4], [0, 1, 0, 2, 1]) := by
  decide +kernel

example : (encode ([] : List Nat) [8, 3, 8]).1 ≠ (encode [] [3, 8, 8]).1 := by
  decide +kernel

#print axioms decode_encode
#print axioms earlier_code_unchanged
#print axioms encode_nodup
#print axioms encode_membership
#print axioms code_in_bounds

end Mettapedia.Algorithms.Collections.StableKeyEncoding
