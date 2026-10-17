import Mettapedia.GSLT.Parsing.TrieAutomatonProduct
import Mathlib.Data.List.MinMax

/-!
# Occurrence-preserving literal tables and shared prefix tries

Literal words carry their original source ordinal. Insertion retains every
terminal occurrence, including repeated equal words. A prefix traversal
collects only terminals on the input path; selecting the smallest source
ordinal is independent of the trie edge order and of word length.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TrieLiteralSelection

open PlainBnfGraphNameTrie (Trie lookup put childFor valueAt edgesOf)

variable {Scalar Payload : Type} [DecidableEq Scalar]

abbrev Table (Scalar Payload : Type) := List (List Scalar × Payload)

/-- This is a bucketed trie, not a set: the same word can retain several
distinct source-alternative occurrences in their original order. -/
def build : Table Scalar Payload → Trie (List Payload) Scalar
  | [] => .empty
  | (word, payload) :: rest =>
      let trie := build rest
      put word (payload :: (lookup word trie).getD []) trie

def bucket (table : Table Scalar Payload) (word : List Scalar) : List Payload :=
  table.filterMap (fun entry => if entry.1 = word then some entry.2 else none)

theorem lookup_build (table : Table Scalar Payload) (word : List Scalar) :
    (lookup word (build table)).getD [] = bucket table word := by
  induction table with
  | nil => simp [build, PlainBnfGraphNameTrie.lookup_empty, bucket]
  | cons entry rest ih =>
      rcases entry with ⟨key, payload⟩
      by_cases same : word = key
      · subst word
        simpa [build, PlainBnfGraphNameTrie.lookup_put, bucket] using congrArg (payload :: ·) ih
      · simp [build, PlainBnfGraphNameTrie.lookup_put, same, bucket, Ne.symm same, ih]

def prefixes : List Scalar → List (List Scalar)
  | [] => [[]]
  | scalar :: rest => [] :: (prefixes rest).map (scalar :: ·)

omit [DecidableEq Scalar] in
theorem mem_prefixes (input word : List Scalar) : word ∈ prefixes input ↔ word <+: input := by
  induction input generalizing word with
  | nil => simp [prefixes]
  | cons scalar rest ih =>
      cases word with
      | nil => simp [prefixes]
      | cons head tail => simp [prefixes, ih, List.prefix_cons_iff, eq_comm, and_comm]

/-- Traverse one input path, emitting every visited terminal bucket. No
alternative word is independently scanned and no terminal is deduplicated. -/
def prefixQuery : Trie (List Payload) Scalar → List Scalar → List (Nat × Payload)
  | trie, [] => ((valueAt trie).getD []).map (fun value => (0, value))
  | trie, scalar :: rest =>
      ((valueAt trie).getD []).map (fun value => (0, value)) ++
        (prefixQuery (childFor scalar (edgesOf trie)) rest).map
          (fun value => (value.1 + 1, value.2))

theorem prefixQuery_eq_buckets (trie : Trie (List Payload) Scalar) (input : List Scalar) :
    prefixQuery trie input =
      (prefixes input).flatMap (fun word =>
        ((lookup word trie).getD []).map (fun value => (word.length, value))) := by
  induction input generalizing trie with
  | nil => simp [prefixQuery, prefixes, lookup]
  | cons scalar rest ih =>
      simp only [prefixQuery, ih, prefixes, List.flatMap_cons, List.flatMap_map,
        List.map_flatMap, List.map_map, lookup, List.length_cons, List.length_nil]
      rfl

/-- Exact occurrence list at the traversed prefixes. Source order within a
terminal bucket is retained even when several alternatives spell one word. -/
theorem prefixQuery_build (table : Table Scalar Payload) (input : List Scalar) :
    prefixQuery (build table) input =
      (prefixes input).flatMap (fun word =>
        (bucket table word).map (fun value => (word.length, value))) := by
  rw [prefixQuery_eq_buckets]
  simp only [lookup_build]

theorem prefixQuery_build_mem (table : Table Scalar Payload) (input : List Scalar)
    (length : Nat) (payload : Payload) :
    (length, payload) ∈ prefixQuery (build table) input ↔
      ∃ word, (word, payload) ∈ table ∧ word <+: input ∧ word.length = length := by
  rw [prefixQuery_build]
  simp only [List.mem_flatMap, List.mem_map, bucket, List.mem_filterMap]
  constructor
  · rintro ⟨word, prefixed, value, ⟨entry, member, found⟩, same⟩
    split at found
    · rename_i equal
      cases Option.some.inj found
      obtain ⟨lengthSame, payloadSame⟩ := Prod.mk.inj same
      cases entry with
      | mk key value =>
          simp only at equal
          subst key
          exact ⟨word, payloadSame ▸ member, (mem_prefixes input word).mp prefixed, lengthSame⟩
    · cases found
  · rintro ⟨word, member, prefixed, rfl⟩
    exact ⟨word, (mem_prefixes input word).mpr prefixed, payload,
      ⟨(word, payload), member, by simp⟩, rfl⟩

/-- Full matching restricts eligible terminal endpoints before selecting a
source ordinal. A short preferred prefix does not suppress a later full word. -/
def candidates (full : Bool) (table : Table Scalar Nat) (input : List Scalar) : List Nat :=
  ((prefixQuery (build table) input).filter
    (fun found => !full || found.1 == input.length)).map Prod.snd

theorem candidates_mem (full : Bool) (table : Table Scalar Nat) (input : List Scalar) (ordinal : Nat) :
    ordinal ∈ candidates full table input ↔
      ∃ word, (word, ordinal) ∈ table ∧ word <+: input ∧ (full = true → word = input) := by
  simp only [candidates, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨length, foundOrdinal⟩, ⟨present, allowed⟩, rfl⟩
    obtain ⟨word, member, isPrefix, sameLength⟩ := (prefixQuery_build_mem table input _ _).mp present
    refine ⟨word, member, isPrefix, ?_⟩
    intro all
    have lengths : word.length = input.length := by simpa [all, sameLength] using allowed
    obtain ⟨suffix, same⟩ := isPrefix
    have empty : suffix = [] := by
      have equalLengths := congrArg List.length same
      simp only [List.length_append] at equalLengths
      have zero : suffix.length = 0 := by omega
      exact List.length_eq_zero_iff.mp zero
    simpa [empty] using same
  · rintro ⟨word, member, isPrefix, fullWord⟩
    refine ⟨(word.length, ordinal), ⟨?_, ?_⟩, rfl⟩
    · exact (prefixQuery_build_mem table input _ _).mpr ⟨word, member, isPrefix, rfl⟩
    · cases full with
      | false => simp
      | true => simp [fullWord rfl]

/-- Minimum source priority, not maximum word length or traversal order. -/
def winner (full : Bool) (table : Table Scalar Nat) (input : List Scalar) : Option Nat :=
  (candidates full table input).min?

theorem winner_some_iff (full : Bool) (table : Table Scalar Nat) (input : List Scalar) (ordinal : Nat) :
    winner full table input = some ordinal ↔
      (∃ word, (word, ordinal) ∈ table ∧ word <+: input ∧ (full = true → word = input)) ∧
      ∀ other word, (word, other) ∈ table → word <+: input →
        (full = true → word = input) → ordinal ≤ other := by
  rw [winner, List.min?_eq_some_iff, candidates_mem]
  constructor
  · rintro ⟨witness, least⟩
    exact ⟨witness, fun other word member prefixed fullWord =>
      least other ((candidates_mem full table input other).mpr ⟨word, member, prefixed, fullWord⟩)⟩
  · rintro ⟨witness, least⟩
    refine ⟨witness, ?_⟩
    intro other member
    obtain ⟨word, present, prefixed, fullWord⟩ := (candidates_mem full table input other).mp member
    exact least other word present prefixed fullWord

theorem winner_none_iff (full : Bool) (table : Table Scalar Nat) (input : List Scalar) :
    winner full table input = none ↔
      ∀ word ordinal, (word, ordinal) ∈ table → word <+: input →
        (full = true → word = input) → False := by
  rw [winner, List.min?_eq_none_iff, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro empty word ordinal member prefixed fullWord
    exact empty ordinal ((candidates_mem full table input ordinal).mpr ⟨word, member, prefixed, fullWord⟩)
  · intro absent ordinal member
    obtain ⟨word, present, prefixed, fullWord⟩ := (candidates_mem full table input ordinal).mp member
    exact absent word ordinal present prefixed fullWord

/-- Ordered starts are a separate observer from alternative priority. -/
def scan (table : Table Scalar Nat) (input : List Scalar) : List Nat → Option (Nat × Nat)
  | [] => none
  | start :: rest =>
      match winner false table (input.drop start) with
      | some ordinal => some (start, ordinal)
      | none => scan table input rest

theorem scan_some_iff (table : Table Scalar Nat) (input : List Scalar)
    (starts : List Nat) (start ordinal : Nat) :
    scan table input starts = some (start, ordinal) ↔
      ∃ before after, starts = before ++ start :: after ∧
        (∀ earlier ∈ before, winner false table (input.drop earlier) = none) ∧
        winner false table (input.drop start) = some ordinal := by
  induction starts with
  | nil => simp [scan]
  | cons position rest ih =>
      cases found : winner false table (input.drop position) with
      | none =>
          rw [scan, found, ih]
          constructor
          · rintro ⟨before, after, same, absent, selected⟩
            refine ⟨position :: before, after, by simp [same], ?_, selected⟩
            intro earlier member
            rcases List.mem_cons.mp member with rfl | member
            · exact found
            · exact absent earlier member
          · rintro ⟨before, after, same, absent, selected⟩
            cases before with
            | nil =>
                have equal : position = start := by simpa using congrArg List.head? same
                simp [equal, selected] at found
            | cons earlier before =>
                exact ⟨before, after, by simpa using congrArg List.tail same,
                  fun p member => absent p (by simp [member]), selected⟩
      | some rank =>
          simp only [scan, found, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩
            exact ⟨[], rest, rfl, by simp, found⟩
          · rintro ⟨before, after, same, absent, selected⟩
            cases before with
            | nil =>
                have equal : position = start := by simpa using congrArg List.head? same
                subst position
                exact ⟨rfl, Option.some.inj (found.symm.trans selected)⟩
            | cons earlier before =>
                have equal : position = earlier := by simpa using congrArg List.head? same
                have impossible := absent earlier (by simp)
                simp [← equal, found] at impossible

/-- At ascending starts the selected start is minimal; at that start the
selected ordinal is minimal. This is the global leftmost-first observation. -/
theorem scan_range_minimum (table : Table Scalar Nat) (input : List Scalar)
    (limit start ordinal : Nat) :
    scan table input (List.range limit) = some (start, ordinal) ↔
      start < limit ∧ winner false table (input.drop start) = some ordinal ∧
        ∀ earlier, earlier < start → winner false table (input.drop earlier) = none := by
  rw [scan_some_iff]
  constructor
  · rintro ⟨before, after, same, absent, selected⟩
    have present : start ∈ List.range limit := by rw [same]; simp
    have ordered := List.pairwise_lt_range (n := limit)
    rw [same, List.pairwise_append] at ordered
    refine ⟨List.mem_range.mp present, selected, ?_⟩
    intro earlier less
    have member : earlier ∈ before ++ start :: after := by
      rw [← same]; exact List.mem_range.mpr (Nat.lt_trans less (List.mem_range.mp present))
    rcases List.mem_append.mp member with earlierMember | laterMember
    · exact absent earlier earlierMember
    · rcases List.mem_cons.mp laterMember with rfl | laterMember
      · omega
      · have bigger := (List.pairwise_cons.mp ordered.2.1).1 _ laterMember
        omega
  · rintro ⟨bounded, selected, absent⟩
    have present : start ∈ List.range limit := List.mem_range.mpr bounded
    obtain ⟨before, after, same⟩ := List.mem_iff_append.mp present
    refine ⟨before, after, same, ?_, selected⟩
    intro earlier member
    have ordered := List.pairwise_lt_range (n := limit)
    rw [same, List.pairwise_append] at ordered
    exact absent earlier (ordered.2.2 earlier member start (by simp))

namespace Controls

private def alternatives : Table Nat Nat := [([97], 0), ([97, 98], 1), ([97], 2)]

theorem shorter_preferred_alternative_wins :
    (candidates false alternatives [97, 98]).min? = some 0 := by decide

theorem full_match_filters_before_minimum :
    (candidates true alternatives [97, 98]).min? = some 1 := by decide

theorem duplicate_words_keep_separate_ordinals :
    prefixQuery (build alternatives) [97, 98] = [(1, 0), (1, 2), (2, 1)] := by decide

theorem empty_and_unicode_words_are_retained :
    prefixQuery (build ([([], 2), ([955], 1)] : Table Nat Nat)) [955, 98] = [(0, 2), (1, 1)] := by
  decide

theorem absent_literal_does_not_invent_ordinal :
    (candidates false alternatives [98]).min? = none := by decide

end Controls

end Mettapedia.GSLT.Parsing.TrieLiteralSelection
