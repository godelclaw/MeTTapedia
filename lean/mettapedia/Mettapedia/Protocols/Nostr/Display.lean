import Mathlib.Data.List.Basic

/-!
# Names shown escaped: distinct names never look alike

A registry name is written by whoever made the entry, so it can hold control
characters and invisible format characters. Removing them for display merges
names: `lead` and `lead` followed by a bell both show as `lead`
(`Names.printable_merges_names`). Here a name is shown as it is, unless it holds
an invisible character or begins with `$'`. Such a name is shown as a bash
ANSI-C string `$'…'`, in which the invisible characters, the backslash and the
single quote are escaped (bash manual, "ANSI-C Quoting"). Hex digits are lower
case, two after `\x` and four after `\u`.

The invisible characters are C0, DEL and C1, together with the format and
separator characters that a terminal does not show:
- U+00AD, U+061C, U+180E;
- U+200B–U+200F, U+2028–U+202E, U+2060–U+2064 and U+2066–U+206F, which include
  the bidirectional controls;
- U+FEFF and U+FFF9–U+FFFB.

The theorems:
- `shown_injective`: distinct names are shown distinctly.
- `shown_visible`: a shown name holds no invisible character.
- `shown_reads_back`: bash reads the quoted form back as the name.
- `shown_plain`: every other name is shown exactly as it is, so the rule alters
  only the names it has to.
- Necessity: changing one part of the rule refutes one of these.
  - Without the check for a leading `$'`, a name can be shown as another's quoted
    form (`unchecked_start_merges`).
  - Without escaping the backslash, two names share a quoted form
    (`unescaped_backslash_merges`).
  - Without escaping the quote, bash ends the string early
    (`unescaped_quote_unreadable`).
  - Shown raw, an invisible character stays in the display (`raw_invisible`).

The model is bash's reading of exactly the escapes written here, in a UTF-8
locale, where `\uHHHH` is a code point and `\xHH`, used only below 0x80, is that
character. Not modelled: look-alike letters (Unicode's confusables, UTS #39),
and history expansion of `!` in an interactive shell.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.Display

/-- The code points a shown name never holds. -/
def invisible (n : Nat) : Bool :=
  n < 0x20 || n == 0x7f || (0x80 ≤ n && n ≤ 0x9f) || n == 0xad || n == 0x61c || n == 0x180e ||
    (0x200b ≤ n && n ≤ 0x200f) || (0x2028 ≤ n && n ≤ 0x202e) || (0x2060 ≤ n && n ≤ 0x2064) ||
    (0x2066 ≤ n && n ≤ 0x206f) || n == 0xfeff || (0xfff9 ≤ n && n ≤ 0xfffb)

theorem lt_of_invisible {n : Nat} (h : invisible n = true) : n < 0x10000 := by
  simp only [invisible, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.and_eq_true] at h
  omega

/-- A lower-case hex digit. -/
def hexDigit (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- A hex digit's value, as bash reads it here. -/
def hexVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87) else none

theorem hexVal_hexDigit_all : ∀ d, d < 16 → hexVal (hexDigit d) = some d := by decide

theorem hexVal_hexDigit {d : Nat} (h : d < 16) : hexVal (hexDigit d) = some d :=
  hexVal_hexDigit_all d h

theorem hexDigit_visible_all : ∀ d, d < 16 → invisible (hexDigit d).toNat = false := by decide

/-- The characters written with a letter after the backslash. -/
def named : List (Nat × Char) :=
  [(7, 'a'), (8, 'b'), (9, 't'), (10, 'n'), (11, 'v'), (12, 'f'), (13, 'r'), (27, 'e'),
    (92, '\\'), (39, '\'')]

/-- An invisible character in hex: two digits below 0x80, four above. -/
def escapeHex (c : Char) : List Char :=
  if c.toNat < 0x80 then ['\\', 'x', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else
    ['\\', 'u', hexDigit (c.toNat / 4096 % 16), hexDigit (c.toNat / 256 % 16),
      hexDigit (c.toNat / 16 % 16), hexDigit (c.toNat % 16)]

/-- One character as written inside `$'…'`. -/
def escapeChar (c : Char) : List Char :=
  match named.lookup c.toNat with
  | some l => ['\\', l]
  | none => if invisible c.toNat then escapeHex c else [c]

/-- bash's reading of the inside of `$'…'`, for the escapes `escapeChar` writes.
An unescaped quote ends the string, so it cannot occur inside. -/
def unescape : List Char → Option (List Char)
  | [] => some []
  | '\\' :: 'a' :: rest => (unescape rest).map (Char.ofNat 7 :: ·)
  | '\\' :: 'b' :: rest => (unescape rest).map (Char.ofNat 8 :: ·)
  | '\\' :: 't' :: rest => (unescape rest).map (Char.ofNat 9 :: ·)
  | '\\' :: 'n' :: rest => (unescape rest).map (Char.ofNat 10 :: ·)
  | '\\' :: 'v' :: rest => (unescape rest).map (Char.ofNat 11 :: ·)
  | '\\' :: 'f' :: rest => (unescape rest).map (Char.ofNat 12 :: ·)
  | '\\' :: 'r' :: rest => (unescape rest).map (Char.ofNat 13 :: ·)
  | '\\' :: 'e' :: rest => (unescape rest).map (Char.ofNat 27 :: ·)
  | '\\' :: '\\' :: rest => (unescape rest).map ('\\' :: ·)
  | '\\' :: '\'' :: rest => (unescape rest).map ('\'' :: ·)
  | '\\' :: 'x' :: h1 :: h2 :: rest =>
    match hexVal h1, hexVal h2 with
    | some a, some b => (unescape rest).map (Char.ofNat (16 * a + b) :: ·)
    | _, _ => none
  | '\\' :: 'u' :: h1 :: h2 :: h3 :: h4 :: rest =>
    match hexVal h1, hexVal h2, hexVal h3, hexVal h4 with
    | some a, some b, some c, some d =>
      (unescape rest).map (Char.ofNat (4096 * a + 256 * b + 16 * c + d) :: ·)
    | _, _, _, _ => none
  | '\\' :: _ => none
  | '\'' :: _ => none
  | c :: rest => (unescape rest).map (c :: ·)

/-- The start of a quoted form. -/
def quoteStart : List Char := ['$', '\'']

/-- A name is shown quoted when it holds an invisible character, or begins as a
quoted form does. -/
def needsQuote (name : List Char) : Bool :=
  name.any (fun c => invisible c.toNat) || name.take 2 == quoteStart

/-- How a registry name is shown. -/
def shown (name : List Char) : List Char :=
  if needsQuote name then quoteStart ++ name.flatMap escapeChar ++ ['\''] else name

/-! ## Reading back -/

theorem ofNat_eq {c : Char} {n : Nat} (h : c.toNat = n) : Char.ofNat n = c := by
  rw [← h, Char.ofNat_toNat]

theorem unescape_plain {c : Char} (h1 : c ≠ '\\') (h2 : c ≠ '\'') (rest : List Char) :
    unescape (c :: rest) = (unescape rest).map (c :: ·) := by
  rw [unescape.eq_def]
  split <;> simp_all

theorem mem_of_lookup {n : Nat} {l : Char} :
    ∀ {t : List (Nat × Char)}, t.lookup n = some l → (n, l) ∈ t
  | [], h => by simp [List.lookup] at h
  | (k, v) :: t, h => by
    simp only [List.lookup] at h
    split at h
    · next hk =>
      cases h
      simp only [beq_iff_eq] at hk
      simp [hk]
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem ne_of_lookup_none {c : Char} (h : named.lookup c.toNat = none) : c ≠ '\\' ∧ c ≠ '\'' := by
  constructor <;> rintro rfl <;> simp [named, List.lookup] at h

/-- Each named character reads back. -/
theorem unescape_named {n : Nat} {l : Char} (h : (n, l) ∈ named) (rest : List Char) :
    unescape ('\\' :: l :: rest) = (unescape rest).map (Char.ofNat n :: ·) := by
  simp only [named, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [unescape]

theorem unescape_escapeHex {c : Char} (hc : invisible c.toNat = true) (rest : List Char) :
    unescape (escapeHex c ++ rest) = (unescape rest).map (c :: ·) := by
  unfold escapeHex
  by_cases hx : c.toNat < 0x80
  · rw [if_pos hx]
    have h1 : c.toNat / 16 < 16 := by omega
    have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
    simp only [List.cons_append, List.nil_append, unescape, hexVal_hexDigit h1, hexVal_hexDigit h2]
    rw [show 16 * (c.toNat / 16) + c.toNat % 16 = c.toNat by omega, Char.ofNat_toNat]
  · rw [if_neg hx]
    have hlt := lt_of_invisible hc
    have h1 : c.toNat / 4096 % 16 < 16 := Nat.mod_lt _ (by omega)
    have h2 : c.toNat / 256 % 16 < 16 := Nat.mod_lt _ (by omega)
    have h3 : c.toNat / 16 % 16 < 16 := Nat.mod_lt _ (by omega)
    have h4 : c.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
    simp only [List.cons_append, List.nil_append, unescape, hexVal_hexDigit h1, hexVal_hexDigit h2,
      hexVal_hexDigit h3, hexVal_hexDigit h4]
    rw [show 4096 * (c.toNat / 4096 % 16) + 256 * (c.toNat / 256 % 16) + 16 * (c.toNat / 16 % 16) +
        c.toNat % 16 = c.toNat by omega, Char.ofNat_toNat]

theorem unescape_escapeChar (c : Char) (rest : List Char) :
    unescape (escapeChar c ++ rest) = (unescape rest).map (c :: ·) := by
  unfold escapeChar
  cases hl : named.lookup c.toNat with
  | some l =>
    simp only [List.cons_append, List.nil_append]
    rw [unescape_named (mem_of_lookup hl), Char.ofNat_toNat]
  | none =>
    simp only
    by_cases hi : invisible c.toNat = true
    · rw [if_pos hi, unescape_escapeHex hi]
    · rw [if_neg hi]
      exact unescape_plain (ne_of_lookup_none hl).1 (ne_of_lookup_none hl).2 rest

theorem unescape_flatMap (name : List Char) : unescape (name.flatMap escapeChar) = some name := by
  induction name with
  | nil => rfl
  | cons c name ih => rw [List.flatMap_cons, unescape_escapeChar, ih]; rfl

/-- **bash reads the quoted form back.** A quoted name is `$'`, an inside that
bash reads as the name, and `'`. -/
theorem shown_reads_back {name : List Char} (h : needsQuote name = true) :
    ∃ inside, shown name = quoteStart ++ inside ++ ['\''] ∧ unescape inside = some name :=
  ⟨name.flatMap escapeChar, by simp [shown, h], unescape_flatMap name⟩

/-- **The rule alters only the names it has to.** -/
theorem shown_plain {name : List Char} (h : needsQuote name = false) : shown name = name := by
  simp [shown, h]

/-! ## Distinct and visible -/

theorem flatMap_escapeChar_injective : Function.Injective (List.flatMap escapeChar) := by
  intro a b h
  have := congrArg unescape h
  rwa [unescape_flatMap, unescape_flatMap, Option.some_inj] at this

/-- **Distinct names are shown distinctly.** -/
theorem shown_injective : Function.Injective shown := by
  intro a b h
  unfold shown at h
  cases ha : needsQuote a <;> cases hb : needsQuote b <;> simp only [ha, hb, if_true, if_false,
    Bool.false_eq_true] at h
  · exact h
  · -- `a` plain, `b` quoted: then `a` begins with `$'`, so it needs quoting
    have : a.take 2 = quoteStart := by rw [h]; rfl
    simp [needsQuote, this] at ha
  · have : b.take 2 = quoteStart := by rw [← h]; rfl
    simp [needsQuote, this] at hb
  · have h' : a.flatMap escapeChar = b.flatMap escapeChar := by
      simpa [quoteStart] using h
    exact flatMap_escapeChar_injective h'

theorem named_visible : ∀ p ∈ named, invisible p.2.toNat = false := by decide

theorem escapeChar_visible (c : Char) : ∀ d ∈ escapeChar c, invisible d.toNat = false := by
  unfold escapeChar
  cases hl : named.lookup c.toNat with
  | some l =>
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · decide
    · exact named_visible (c.toNat, _) (mem_of_lookup hl)
  | none =>
    simp only
    by_cases hi : invisible c.toNat = true
    · rw [if_pos hi]
      intro d hd
      unfold escapeHex at hd
      split at hd
      · have h1 : c.toNat / 16 < 16 := by omega
        have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl
        · decide
        · decide
        · exact hexDigit_visible_all _ h1
        · exact hexDigit_visible_all _ h2
      · have h1 : c.toNat / 4096 % 16 < 16 := Nat.mod_lt _ (by omega)
        have h2 : c.toNat / 256 % 16 < 16 := Nat.mod_lt _ (by omega)
        have h3 : c.toNat / 16 % 16 < 16 := Nat.mod_lt _ (by omega)
        have h4 : c.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
        · decide
        · decide
        · exact hexDigit_visible_all _ h1
        · exact hexDigit_visible_all _ h2
        · exact hexDigit_visible_all _ h3
        · exact hexDigit_visible_all _ h4
    · rw [if_neg hi]
      intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      simpa using hi

/-- **No invisible character is shown.** -/
theorem shown_visible (name : List Char) : ∀ d ∈ shown name, invisible d.toNat = false := by
  intro d hd
  unfold shown at hd
  split at hd
  · simp only [quoteStart, List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
      List.mem_flatMap, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | ⟨c, -, hc⟩ | rfl
    · decide
    · decide
    · exact escapeChar_visible c d hc
    · decide
  · next h =>
    have h' : (name.any fun c => invisible c.toNat) = false := by
      cases hh : name.any (fun c => invisible c.toNat) <;> simp_all [needsQuote]
    rw [List.any_eq_false] at h'
    simpa using h' d hd

/-! ## The rule at work -/

/-- `lead` and a bell is shown `$'lead\a'`, `lead` as it is, and the two differ,
which cleaning merged (`Names.printable_merges_names`). -/
example : shown ['l', 'e', 'a', 'd', Char.ofNat 7] = "$'lead\\a'".toList ∧
    shown "lead".toList = "lead".toList := by
  decide

/-- A name with a backslash or a quote, and no invisible character, is shown as
it is. -/
example : shown "C:\\x it's".toList = "C:\\x it's".toList := by decide

/-! ## Necessity -/

/-- The quoted form of `lead` and a bell, written as a name of its own. -/
def lookalike : List Char := "$'lead\\a'".toList

/-- The rule quotes it, so the two stay apart. -/
example : shown lookalike ≠ shown ['l', 'e', 'a', 'd', Char.ofNat 7] := by decide

/-- Without the check for a leading `$'`, that name is shown as the other's
quoted form. -/
theorem unchecked_start_merges :
    (if lookalike.any (fun c => invisible c.toNat) then quoteStart ++ lookalike.flatMap escapeChar ++ ['\'']
      else lookalike) = shown ['l', 'e', 'a', 'd', Char.ofNat 7] := by
  decide

/-- Inside the quotes, a backslash written as it is. -/
def escapeNoBackslash (c : Char) : List Char := if c = '\\' then ['\\'] else escapeChar c

/-- Without escaping the backslash, a bell and a written `\a` share a quoted
form. -/
theorem unescaped_backslash_merges :
    ['l', 'e', 'a', 'd', Char.ofNat 7].flatMap escapeNoBackslash =
      ['l', 'e', 'a', 'd', '\\', 'a'].flatMap escapeNoBackslash := by
  decide

/-- Inside the quotes, a quote written as it is. -/
def escapeNoQuote (c : Char) : List Char := if c = '\'' then ['\''] else escapeChar c

/-- Without escaping the quote, bash ends the string at it. -/
theorem unescaped_quote_unreadable :
    unescape (['i', 't', '\'', 's', Char.ofNat 7].flatMap escapeNoQuote) = none := by
  decide

/-- Shown raw, the bell stays in the display. -/
theorem raw_invisible : ∃ d ∈ ['l', 'e', 'a', 'd', Char.ofNat 7], invisible d.toNat = true :=
  ⟨Char.ofNat 7, by decide, by decide⟩

end Mettapedia.Protocols.Nostr.Display
