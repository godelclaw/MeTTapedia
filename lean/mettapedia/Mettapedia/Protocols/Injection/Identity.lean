import Mathlib.Data.List.Basic

/-!
# Names, keys and the addresses shown for them

An address book maps local names (petnames) to keys, and may keep, beside each
key, a stored copy of its public encoding (an npub, a fingerprint). A client that
shows the stored copy shows whatever the entry says; one that shows the encoding
of the authenticated key shows that key, whatever the entry says.

The theorems:
- `shownStored_misleads`: a stored copy can name another member's address: the
  entry for one key shows the encoding of a different key.
- `shownDerived_ignores_book`: the derived address depends on the key alone.
- `checked_iff`: a book whose stored copies all match their keys shows, for each
  of its keys, exactly the derived address; checking at load and deriving at
  display agree on checked books.
- `flagged_nil_iff`: listing the entries whose copy disagrees (what `contacts`
  does) finds none exactly when the book is checked.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Injection.Identity

variable {K E : Type} [DecidableEq K] [DecidableEq E]

/-- An address-book entry: a local name, a key, and a stored copy of the key's
encoding. -/
structure Entry (K E : Type) where
  name : String
  key : K
  stored : E

/-- The address shown from the stored copy of the first entry with that key. -/
def shownStored (book : List (Entry K E)) (k : K) : Option E :=
  (book.find? (fun e => e.key = k)).map (·.stored)

/-- The address shown from the key itself. -/
def shownDerived (encode : K → E) (k : K) : E := encode k

/-- Every stored copy matches its key. -/
def Checked (encode : K → E) (book : List (Entry K E)) : Prop :=
  ∀ e ∈ book, e.stored = encode e.key

/-- The entries whose stored copy disagrees with their key. -/
def flagged (encode : K → E) (book : List (Entry K E)) : List (Entry K E) :=
  book.filter (fun e => e.stored ≠ encode e.key)

omit [DecidableEq E] in
/-- A stored copy can name another member's address. -/
theorem shownStored_misleads (encode : K → E) (hinj : Function.Injective encode) {k k' : K}
    (hne : k ≠ k') (name : String) :
    shownStored [⟨name, k, encode k'⟩] k = some (encode k') ∧ encode k' ≠ encode k := by
  refine ⟨by simp [shownStored], fun h => hne (hinj h).symm⟩

omit [DecidableEq K] [DecidableEq E] in
/-- The derived address depends on the key alone: no entry changes it. -/
theorem shownDerived_ignores_book (encode : K → E) (k : K) : shownDerived encode k = encode k :=
  rfl

omit [DecidableEq E] in
/-- On a checked book, the stored copy shown for a key it holds is the derived
address. -/
theorem checked_shows_derived {encode : K → E} {book : List (Entry K E)}
    (h : Checked encode book) {k : K} (hk : ∃ e ∈ book, e.key = k) :
    shownStored book k = some (shownDerived encode k) := by
  obtain ⟨e, he, hek⟩ := hk
  obtain ⟨f, hf⟩ : ∃ f, book.find? (fun e => e.key = k) = some f := by
    cases hfind : book.find? (fun e => e.key = k) with
    | none =>
      have := List.find?_eq_none.mp hfind e he
      simp [hek] at this
    | some f => exact ⟨f, rfl⟩
  have hfmem : f ∈ book := List.mem_of_find?_eq_some hf
  have hfk : f.key = k := by simpa using List.find?_some hf
  simp [shownStored, hf, shownDerived, h f hfmem, hfk]

omit [DecidableEq E] in
/-- **Checking is deriving.** A book shows the derived address for every key it
holds exactly when it is checked. -/
theorem checked_iff (encode : K → E) (book : List (Entry K E))
    (hfirst : ∀ e ∈ book, book.find? (fun x => x.key = e.key) = some e) :
    Checked encode book ↔
      ∀ e ∈ book, shownStored book e.key = some (shownDerived encode e.key) := by
  constructor
  · intro h e he
    exact checked_shows_derived h ⟨e, he, rfl⟩
  · intro h e he
    have := h e he
    simp [shownStored, hfirst e he, shownDerived] at this
    exact this

omit [DecidableEq K] in
/-- `contacts` flags nothing exactly when the book is checked. -/
theorem flagged_nil_iff (encode : K → E) (book : List (Entry K E)) :
    flagged encode book = [] ↔ Checked encode book := by
  simp [flagged, Checked, List.filter_eq_nil_iff]

end Mettapedia.Protocols.Injection.Identity
