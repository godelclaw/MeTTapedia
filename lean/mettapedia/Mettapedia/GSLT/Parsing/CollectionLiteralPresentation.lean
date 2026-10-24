import Mettapedia.GSLT.Parsing.ExactPresentation
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Multiset

/-!
# Collection literals as exact presentations

A collection literal is one concrete syntax of an abstract collection value,
indexed by its kind `CollType`: a list, a bag or a set of elements. Elements
are single tokens here; a token printer for elements is assumed to read back.

* **Canonical printing.** Bags and sets print their elements in a fixed
  linear order, so the printed form is a function of the value and the
  presentation's normal form is the sorted literal (`expanded`,
  `normalize_permuted_bag`). Printing in the order of some representative is
  not a function of the bag (`Controls.representative_order_not_function`).
* **Delimiters.** A streaming reader finds the end of a literal at its
  closing token, so no element may print as the closing token of its kind
  (`readStream_view`; `Controls.element_spelled_as_closing`). A reader that
  does not know the kind in advance chooses it by the opening token, and reads
  every literal back exactly when distinct kinds have distinct openings
  (`readAny_view`; `Controls.shared_opening_confuses_kinds`).
* **Strict and lenient cores.** A lenient set reader merges repeated
  elements; a strict one refuses them. Both are exact presentations with the
  same printer, and the strict reader accepts a subset of what the lenient one
  accepts, with the same value (`strict_le_lenient`).
* **Counts.** Bags also print with counts: an element occurring `n > 1` times
  is preceded by a count token (`counted`, `readCounted_countedTokens`). This
  needs count tokens and element tokens to be disjoint: with bare numerals for
  both, two different bags print alike (`Controls.counts_need_marker`).
  Conversion between the expanded and the counted notation preserves the bag
  and returns to each notation's normal form, by `ExactPresentation`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CollectionLiteralPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax (CollType)
open Mettapedia.GSLT.Parsing.ExactPresentation

universe u v

/-- The abstract value of a collection literal of each kind. -/
abbrev CollValue (α : Type u) : CollType → Type u
  | .vec => List α
  | .hashBag => Multiset α
  | .hashSet => Finset α

variable {α : Type u} {Tok : Type v}

/-- How element atoms are spelled as tokens. -/
structure ElementSyntax (α : Type u) (Tok : Type v) where
  print : α → Tok
  read : Tok → Option α
  read_print : ∀ value, read (print value) = some value

/-- Opening and closing tokens of each kind. -/
structure Delimiters (Tok : Type v) where
  opening : CollType → Tok
  closing : CollType → Tok

/-- Building a value of a kind from the enumerated elements. The lenient core
merges repeated set elements; the strict core refuses them. -/
def build [DecidableEq α] (strict : Bool) : (kind : CollType) → List α → Option (CollValue α kind)
  | .vec, values => some values
  | .hashBag, values => some (values : Multiset α)
  | .hashSet, values =>
      if strict && !decide values.Nodup then none else some values.toFinset

section Canonical

variable [LinearOrder α]

/-- The canonical enumeration: lists as they are, bags and sets sorted. -/
def canonical : (kind : CollType) → CollValue α kind → List α
  | .vec, values => values
  | .hashBag, values => Multiset.sort values
  | .hashSet, values => Finset.sort values

theorem build_canonical (strict : Bool) (kind : CollType)
    (value : CollValue α kind) : build strict kind (canonical kind value) = some value := by
  cases kind with
  | vec => rfl
  | hashBag =>
      show some ((Multiset.sort (value : Multiset α) : List α) : Multiset α) = some value
      rw [Multiset.sort_eq]
  | hashSet =>
      show (if strict && !decide (Finset.sort (value : Finset α)).Nodup then none
        else some (Finset.sort (value : Finset α)).toFinset) = some value
      rw [if_neg (by simp [Finset.sort_nodup]), Finset.sort_toFinset]

end Canonical

section Reading

variable [DecidableEq Tok] (elements : ElementSyntax α Tok)

/-- Read element tokens up to a closing token; return the rest of the input. -/
def readElements (close : Tok) : List Tok → Option (List α × List Tok)
  | [] => none
  | token :: rest =>
      if token = close then some ([], rest)
      else
        match elements.read token, readElements close rest with
        | some value, some (more, remaining) => some (value :: more, remaining)
        | _, _ => none

theorem readElements_print (close : Tok) (values : List α)
    (separated : ∀ value ∈ values, elements.print value ≠ close) (rest : List Tok) :
    readElements elements close (values.map elements.print ++ close :: rest) =
      some (values, rest) := by
  induction values with
  | nil => simp [readElements]
  | cons head tail ih =>
      have headSeparated := separated head (by simp)
      have tailSeparated : ∀ value ∈ tail, elements.print value ≠ close :=
        fun value member => separated value (by simp [member])
      simp only [List.map_cons, List.cons_append, readElements, if_neg headSeparated,
        elements.read_print, ih tailSeparated]

variable (delimiters : Delimiters Tok)

/-- Read one literal of a known kind from the front of the input. -/
def readStream [DecidableEq α] (strict : Bool) (kind : CollType) : List Tok → Option (CollValue α kind × List Tok)
  | [] => none
  | token :: rest =>
      if token = delimiters.opening kind then
        match readElements elements (delimiters.closing kind) rest with
        | some (values, remaining) => (build strict kind values).map (·, remaining)
        | none => none
      else none

/-- No element prints as the closing token of a kind. -/
def Separated : Prop :=
  ∀ (kind : CollType) (value : α), elements.print value ≠ delimiters.closing kind

/-- Read a literal of any kind, choosing the kind by its opening token. -/
def readAny [DecidableEq α] (strict : Bool) (surface : List Tok) :
    Option ((kind : CollType) × CollValue α kind × List Tok) :=
  match surface with
  | [] => none
  | token :: _ =>
      if token = delimiters.opening .vec then
        (readStream elements delimiters strict .vec surface).map fun read => ⟨.vec, read⟩
      else if token = delimiters.opening .hashBag then
        (readStream elements delimiters strict .hashBag surface).map fun read => ⟨.hashBag, read⟩
      else if token = delimiters.opening .hashSet then
        (readStream elements delimiters strict .hashSet surface).map fun read => ⟨.hashSet, read⟩
      else none

/-- Distinct kinds have distinct opening tokens. -/
def OpeningsDistinct : Prop := Function.Injective delimiters.opening

/-- Whatever the strict reader accepts, the lenient reader accepts with the
same value. -/
theorem strict_le_lenient [DecidableEq α] (kind : CollType) (surface : List Tok)
    (value : CollValue α kind) (remaining : List Tok)
    (accepted : readStream elements delimiters true kind surface = some (value, remaining)) :
    readStream elements delimiters false kind surface = some (value, remaining) := by
  cases surface with
  | nil => simp [readStream] at accepted
  | cons token rest =>
      simp only [readStream] at accepted ⊢
      split_ifs at accepted ⊢ with opened
      cases reading : readElements elements (delimiters.closing kind) rest with
      | none => simp [reading] at accepted
      | some result =>
          obtain ⟨values, after⟩ := result
          simp only [reading] at accepted ⊢
          cases kind with
          | vec => simpa [build] using accepted
          | hashBag => simpa [build] using accepted
          | hashSet =>
              by_cases nodup : values.Nodup
              · simpa [build, nodup] using accepted
              · simp [build, nodup] at accepted

variable [LinearOrder α]

/-- The printed literal of a value of a known kind. -/
def view (kind : CollType) (value : CollValue α kind) : List Tok :=
  delimiters.opening kind ::
    ((canonical kind value).map elements.print ++ [delimiters.closing kind])

theorem readStream_view (separated : Separated elements delimiters) (strict : Bool)
    (kind : CollType) (value : CollValue α kind) (rest : List Tok) :
    readStream elements delimiters strict kind (view elements delimiters kind value ++ rest) =
      some (value, rest) := by
  simp only [view, List.cons_append, List.append_assoc, readStream]
  rw [readElements_print elements _ _ (fun value _ => separated kind value)]
  simp [build_canonical]

/-- The expanded notation, as an exact presentation of each kind. -/
def expanded (separated : Separated elements delimiters) (strict : Bool) :
    Presentation (CollValue α) (fun _ : CollType => List Tok) where
  key := ⟨if strict then "collection-literal-strict" else "collection-literal", 1⟩
  expand := fun {kind} surface =>
    match readStream elements delimiters strict kind surface with
    | some (value, []) => some value
    | _ => none
  view := fun {kind} value => view elements delimiters kind value
  expand_view := by
    intro kind value
    have := readStream_view elements delimiters separated strict kind value []
    rw [List.append_nil] at this
    simp only [this]

theorem readAny_view (separated : Separated elements delimiters)
    (distinct : OpeningsDistinct delimiters) (strict : Bool) (kind : CollType)
    (value : CollValue α kind) (rest : List Tok) :
    readAny elements delimiters strict (view elements delimiters kind value ++ rest) =
      some ⟨kind, value, rest⟩ := by
  have reads := readStream_view elements delimiters separated strict
  have other : ∀ first second : CollType, first ≠ second →
      delimiters.opening first ≠ delimiters.opening second :=
    fun _ _ different same => different (distinct same)
  have readsKind := reads kind value rest
  cases kind <;>
    simp only [view, List.cons_append, List.append_assoc, List.nil_append]
      at readsKind ⊢ <;>
    simp [readAny, readsKind, other]

end Reading

/-! ## Counted bags -/

section Counted

variable [DecidableEq Tok]

/-- How a count is spelled as one token. -/
structure CountSyntax (Tok : Type v) where
  print : ℕ → Tok
  read : Tok → Option ℕ
  read_print : ∀ count, read (print count) = some count

variable (elements : ElementSyntax α Tok) (counts : CountSyntax Tok)

/-- The tokens of one element with its count; a count of one is omitted. -/
def entryTokens (count : ℕ) (value : α) : List Tok :=
  if count = 1 then [elements.print value] else [counts.print count, elements.print value]

/-- Read a counted body: a count token applies to the next element. -/
def readCounted : List Tok → Option (Multiset α)
  | [] => some 0
  | [token] => (elements.read token).map fun value => {value}
  | token :: next :: rest =>
      match counts.read token with
      | some count =>
          match elements.read next, readCounted rest with
          | some value, some bag => some (Multiset.replicate count value + bag)
          | _, _ => none
      | none =>
          match elements.read token, readCounted (next :: rest) with
          | some value, some bag => some (value ::ₘ bag)
          | _, _ => none

/-- Element tokens are never count tokens. -/
def CountsMarked : Prop := ∀ value : α, counts.read (elements.print value) = none

omit [DecidableEq Tok] in
theorem readCounted_entry (marked : CountsMarked elements counts) (count : ℕ) (value : α)
    (rest : List Tok) (bag : Multiset α)
    (restReads : readCounted elements counts rest = some bag) :
    readCounted elements counts (entryTokens elements counts count value ++ rest) =
      some (Multiset.replicate count value + bag) := by
  by_cases single : count = 1
  · subst single
    rw [entryTokens, if_pos rfl, Multiset.replicate_one, Multiset.singleton_add]
    cases rest with
    | nil =>
        simp only [readCounted, Option.some.injEq] at restReads
        subst restReads
        simp [readCounted, elements.read_print]
    | cons next more =>
        simp [readCounted, marked value, elements.read_print, restReads]
  · rw [entryTokens, if_neg single]
    simp [readCounted, counts.read_print, elements.read_print, restReads]

omit [DecidableEq Tok] in
theorem readCounted_entries (marked : CountsMarked elements counts)
    (entries : List (ℕ × α)) :
    readCounted elements counts (entries.flatMap fun entry =>
        entryTokens elements counts entry.1 entry.2) =
      some (entries.map fun entry => Multiset.replicate entry.1 entry.2).sum := by
  induction entries with
  | nil => simp [readCounted]
  | cons head tail ih =>
      rw [List.flatMap_cons, readCounted_entry elements counts marked _ _ _ _ ih]
      simp

variable [LinearOrder α]

/-- The counted body: distinct elements in order, each with its count. -/
def countedTokens (bag : Multiset α) : List Tok :=
  (bag.toFinset.sort).flatMap fun value => entryTokens elements counts (bag.count value) value

omit [DecidableEq Tok] in
theorem readCounted_countedTokens (marked : CountsMarked elements counts) (bag : Multiset α) :
    readCounted elements counts (countedTokens elements counts bag) = some bag := by
  have entries := readCounted_entries elements counts marked
    ((bag.toFinset.sort).map fun value => (bag.count value, value))
  rw [List.flatMap_map, List.map_map] at entries
  rw [countedTokens, entries]
  congr 1
  rw [Function.comp_def, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  simp only [← Multiset.nsmul_singleton]
  exact Multiset.toFinset_sum_count_nsmul_eq bag

/-- The counted notation for bags, with the expanded notation for lists and
sets. The bag reader reads a whole literal: its body ends at the last token. -/
def counted (delimiters : Delimiters Tok) (separated : Separated elements delimiters)
    (marked : CountsMarked elements counts) :
    Presentation (CollValue α) (fun _ : CollType => List Tok) where
  key := ⟨"collection-literal-counted", 1⟩
  expand := fun {kind} surface =>
    match kind with
    | .hashBag =>
        match surface with
        | opening :: body =>
            if opening = delimiters.opening .hashBag ∧
                body.getLast? = some (delimiters.closing .hashBag) then
              readCounted elements counts body.dropLast
            else none
        | [] => none
    | other =>
        match readStream elements delimiters false other surface with
        | some (value, []) => some value
        | _ => none
  view := fun {kind} value =>
    match kind with
    | .hashBag => delimiters.opening .hashBag ::
        (countedTokens elements counts value ++ [delimiters.closing .hashBag])
    | other => view elements delimiters other value
  expand_view := by
    intro kind value
    cases kind with
    | hashBag =>
        simp only [List.getLast?_concat, and_self, if_true, List.dropLast_concat]
        exact readCounted_countedTokens elements counts marked value
    | vec =>
        have := readStream_view elements delimiters separated false .vec value []
        rw [List.append_nil] at this
        simp only [this]
    | hashSet =>
        have := readStream_view elements delimiters separated false .hashSet value []
        rw [List.append_nil] at this
        simp only [this]

end Counted

/-! ## Controls -/

namespace Controls

/-- Tokens for the controls: delimiters, count markers and numerals. -/
inductive Token where
  | openList | closeList | openBag | closeBag | openSet | closeSet
  | times (count : ℕ)
  | numeral (value : ℕ)
  deriving DecidableEq, Repr

def numerals : ElementSyntax ℕ Token where
  print := .numeral
  read := fun | .numeral value => some value | _ => none
  read_print := fun _ => rfl

def marks : CountSyntax Token where
  print := .times
  read := fun | .times count => some count | _ => none
  read_print := fun _ => rfl

def delimiters : Delimiters Token where
  opening := fun | .vec => .openList | .hashBag => .openBag | .hashSet => .openSet
  closing := fun | .vec => .closeList | .hashBag => .closeBag | .hashSet => .closeSet

theorem separated : Separated numerals delimiters := by
  intro kind value
  cases kind <;> simp [numerals, delimiters]

theorem distinct : OpeningsDistinct delimiters := by
  intro first second same
  cases first <;> cases second <;> simp_all [delimiters]

theorem marked : CountsMarked numerals marks := fun _ => rfl

/-- Two spellings of one bag denote it and so share a normal form. -/
theorem permuted_bag_same_normal_form :
    normalize (expanded numerals delimiters separated false) (sort := .hashBag)
        [.openBag, .numeral 2, .numeral 1, .numeral 2, .closeBag] =
      normalize (expanded numerals delimiters separated false) (sort := .hashBag)
        [.openBag, .numeral 1, .numeral 2, .numeral 2, .closeBag] := by
  apply normalize_of_same_tree
  decide

/-- A list literal keeps its order: the two spellings are different lists. -/
theorem permuted_list_differs :
    (expanded numerals delimiters separated false).expand (sort := .vec)
        [.openList, .numeral 2, .numeral 1, .closeList] ≠
      (expanded numerals delimiters separated false).expand (sort := .vec)
        [.openList, .numeral 1, .numeral 2, .closeList] := by
  decide

/-- The lenient set reader merges a repetition; the strict one refuses it. -/
theorem lenient_merges_strict_refuses :
    (expanded numerals delimiters separated false).expand (sort := .hashSet)
        [.openSet, .numeral 1, .numeral 1, .closeSet] = some ({1} : Finset ℕ) ∧
      (expanded numerals delimiters separated true).expand (sort := .hashSet)
        [.openSet, .numeral 1, .numeral 1, .closeSet] = none := by
  decide

/-- The same bag, spelled with a repeated element and with a count. -/
theorem counted_and_expanded_agree :
    readCounted numerals marks [.numeral 1, .times 2, .numeral 2] =
        some ({1, 2, 2} : Multiset ℕ) ∧
      (expanded numerals delimiters separated false).expand (sort := .hashBag)
        [.openBag, .numeral 2, .numeral 1, .numeral 2, .closeBag] = some ({1, 2, 2} : Multiset ℕ) := by
  decide

/-- The counted printer of a concrete bag. -/
theorem countedTokens_example :
    countedTokens numerals marks ({2, 1, 2} : Multiset ℕ) =
      [.numeral 1, .times 2, .numeral 2] := by
  have sorted : (({2, 1, 2} : Multiset ℕ).toFinset).sort = [1, 2] := by
    rw [show (({2, 1, 2} : Multiset ℕ).toFinset) = insert 1 {2} by decide,
      Finset.sort_insert (s := {2}) (r := fun a b : ℕ => a ≤ b) (by simp) (by simp)]
    simp [Finset.sort_singleton]
  simp only [countedTokens, sorted]
  decide

/-- Printing a bag in the order of a representative list is not a function of
the bag: two representatives of one bag print differently. -/
theorem representative_order_not_function :
    (([1, 2] : List ℕ) : Multiset ℕ) = (([2, 1] : List ℕ) : Multiset ℕ) ∧
      ([1, 2].map numerals.print) ≠ ([2, 1].map numerals.print) := by
  refine ⟨Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ []), by decide⟩

/-- An element spelled like the closing token ends the literal early. -/
theorem element_spelled_as_closing :
    readStream (⟨id, some, fun _ => rfl⟩ : ElementSyntax Token Token) delimiters false .vec
        [Token.openList, Token.closeList, Token.closeList] = some ([], [Token.closeList]) := by
  decide

/-- With one opening token shared by bags and sets, the untyped reader reads
a printed set as a bag, and a set and a bag print alike: no reader recovers
both kinds. -/
theorem shared_opening_confuses_kinds :
    let shared : Delimiters Token :=
      ⟨fun | .vec => .openList | _ => .openBag, fun | .vec => .closeList | _ => .closeBag⟩
    (readAny numerals shared false
        [Token.openBag, Token.numeral 1, Token.closeBag]).map (fun read => read.1) =
        some .hashBag ∧
      view numerals shared .hashSet ({1} : Finset ℕ) =
        view numerals shared .hashBag ({1} : Multiset ℕ) := by
  refine ⟨by decide, ?_⟩
  simp [view, canonical]

/-- Bare numerals for both counts and elements: the bags `{2, 3}` and
`{3, 3}` print alike, so no reader recovers both. -/
theorem counts_need_marker :
    let bare : CountSyntax Token :=
      ⟨Token.numeral, fun | .numeral count => some count | _ => none, fun _ => rfl⟩
    countedTokens numerals bare ({2, 3} : Multiset ℕ) =
        countedTokens numerals bare ({3, 3} : Multiset ℕ) ∧
      ({2, 3} : Multiset ℕ) ≠ {3, 3} := by
  intro bare
  have twoThree : (({2, 3} : Multiset ℕ).toFinset).sort = [2, 3] := by
    rw [show (({2, 3} : Multiset ℕ).toFinset) = insert 2 {3} by decide,
      Finset.sort_insert (s := {3}) (r := fun a b : ℕ => a ≤ b) (by simp) (by simp)]
    simp [Finset.sort_singleton]
  have threeThree : (({3, 3} : Multiset ℕ).toFinset).sort = [3] := by
    rw [show (({3, 3} : Multiset ℕ).toFinset) = {3} by decide]
    simp [Finset.sort_singleton]
  refine ⟨?_, by decide⟩
  simp only [countedTokens, twoThree, threeThree]
  decide

end Controls

end Mettapedia.GSLT.Parsing.CollectionLiteralPresentation
