import Mathlib.Data.List.Basic

/-!
# Literals in patterns

A shell pattern (`find -name`, `fnmatch`) reads `*` as any run of characters and
`?` as any one character. A program that builds a pattern from a value it does
not control, such as `"*.$id.*"` to find the file of one message, must make sure
the value is read as itself. Otherwise `id = *` matches every file.

`glob` is the matcher, with `*` and `?`. A *literal* is text with no `*`, `?`,
`[` or `.`.

The theorems:
- `glob_star_id`: the pattern built from the id `*` matches the file of any
  message.
- `glob_literal_id`: for a literal id, the pattern matches exactly the names in
  which `.id.` occurs: the id is read as itself, and every such name is found.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Injection.Patterns

/-- Text, as characters. -/
abbrev Text := List Char

/-- `*` before a rest: some suffix of the text (all of it, or empty) matches the rest. -/
def anySuffix (rest : Text → Bool) : Text → Bool
  | [] => rest []
  | x :: s => rest (x :: s) || anySuffix rest s

/-- Shell-pattern matching with `*` (any run) and `?` (any one character). -/
def glob : Text → Text → Bool
  | [], s => s.isEmpty
  | '*' :: p, s => anySuffix (glob p) s
  | '?' :: p, s =>
    match s with
    | [] => false
    | _ :: s' => glob p s'
  | c :: p, s =>
    match s with
    | [] => false
    | d :: s' => c == d && glob p s'

/-- No pattern character, and no dot: it can only stand for itself, and the dots
around it are the separators. -/
def Literal (t : Text) : Prop := ∀ c ∈ t, c ≠ '*' ∧ c ≠ '?' ∧ c ≠ '[' ∧ c ≠ '.'

/-- The pattern that finds the file of message `id`: `*.id.*`. -/
def idPattern (id : Text) : Text := '*' :: '.' :: id ++ ['.', '*']

/-! ## The bug -/

/-- An id of `*`: its pattern matches the file of a different message, `ab`. -/
theorem glob_star_id : glob (idPattern ['*']) ['1', '.', 'a', 'b', '.', 'm', 'e'] = true := by
  decide

/-! ## The fix -/

theorem anySuffix_iff (rest : Text → Bool) (s : Text) :
    anySuffix rest s = true ↔ ∃ a b, s = a ++ b ∧ rest b = true := by
  induction s with
  | nil => simp [anySuffix]
  | cons x s ih =>
    simp only [anySuffix, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨a, b, rfl, hb⟩)
      · exact ⟨[], x :: s, rfl, h⟩
      · exact ⟨x :: a, b, rfl, hb⟩
    · rintro ⟨a, b, hs, hb⟩
      cases a with
      | nil => simp at hs; subst hs; exact Or.inl hb
      | cons y a =>
        simp only [List.cons_append, List.cons.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact Or.inr ⟨a, b, rfl, hb⟩

/-- `*` matches when what follows it matches some suffix. -/
theorem glob_star_iff (p s : Text) :
    glob ('*' :: p) s = true ↔ ∃ a b, s = a ++ b ∧ glob p b = true := by
  rw [glob, anySuffix_iff]

theorem glob_char {c : Char} (hs : c ≠ '*') (hq : c ≠ '?') (p : Text) (d : Char) (s : Text) :
    glob (c :: p) (d :: s) = (c == d && glob p s) := by
  rw [glob.eq_def]
  split <;> simp_all

theorem glob_char_nil {c : Char} (hs : c ≠ '*') (hq : c ≠ '?') (p : Text) :
    glob (c :: p) [] = false := by
  rw [glob.eq_def]
  split <;> simp_all

/-- A literal stands for itself. -/
theorem glob_literal_append {t : Text} (ht : ∀ c ∈ t, c ≠ '*' ∧ c ≠ '?') (p s : Text) :
    glob (t ++ p) s = true ↔ ∃ s', s = t ++ s' ∧ glob p s' = true := by
  induction t generalizing s with
  | nil => simp
  | cons c t ih =>
    have hc := ht c (by simp)
    have ht' : ∀ x ∈ t, x ≠ '*' ∧ x ≠ '?' := fun x hx => ht x (by simp [hx])
    rw [List.cons_append]
    cases s with
    | nil => simp [glob_char_nil hc.1 hc.2]
    | cons d s =>
      rw [glob_char hc.1 hc.2]
      simp only [Bool.and_eq_true, beq_iff_eq, ih ht']
      constructor
      · rintro ⟨rfl, s', rfl, h⟩; exact ⟨s', rfl, h⟩
      · rintro ⟨s', h, hp⟩
        simp only [List.cons_append, List.cons.injEq] at h
        exact ⟨h.1.symm, s', h.2, hp⟩

theorem glob_star_end (s : Text) : glob ['*'] s = true :=
  (glob_star_iff [] s).mpr ⟨s, [], by simp, rfl⟩

/-- **A literal id is read as itself.** Its pattern matches exactly the names in
which `.id.` occurs. -/
theorem glob_literal_id {id : Text} (hid : Literal id) (name : Text) :
    glob (idPattern id) name = true ↔ ∃ a b, name = a ++ '.' :: id ++ '.' :: b := by
  have hseg : ∀ c ∈ '.' :: id ++ ['.'], c ≠ '*' ∧ c ≠ '?' := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_cons.mp hc with rfl | hc
      · decide
      · exact ⟨(hid c hc).1, (hid c hc).2.1⟩
    · rw [List.mem_singleton] at hc
      subst hc
      decide
  have hpat : idPattern id = '*' :: (('.' :: id ++ ['.']) ++ ['*']) := by
    simp [idPattern]
  rw [hpat, glob_star_iff]
  constructor
  · rintro ⟨a, b, rfl, hb⟩
    obtain ⟨b', rfl, -⟩ := (glob_literal_append hseg ['*'] b).mp hb
    exact ⟨a, b', by simp⟩
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, '.' :: id ++ '.' :: b, by simp, ?_⟩
    exact (glob_literal_append hseg ['*'] _).mpr ⟨b, by simp, glob_star_end b⟩

end Mettapedia.Protocols.Injection.Patterns
