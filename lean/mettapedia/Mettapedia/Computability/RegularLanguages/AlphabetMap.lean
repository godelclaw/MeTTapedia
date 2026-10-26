import Mettapedia.Computability.RegularLanguages.Regex
import Mathlib.Data.String.Basic

/-!
# Literal alphabet relabeling and Unicode scalar inputs

Relabeling changes literal atoms and keeps the wildcard atom. Matching is
preserved on mapped words for injective relabelings. A wildcard in the target
still accepts all target letters, so this does not assert language-image
equality for a relabeling that is not surjective.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages

universe u v
variable {α : Type u} {β : Type v}

/-- Relabel literal letters, leaving the wildcard as a wildcard. -/
def Atom.mapAlphabet (f : α → β) : Atom α → Atom β
  | .literal a => .literal (f a)
  | .any => .any

/-- Relabel through Mathlib's existing regular-expression alphabet map. -/
def mapAlphabet (f : α → β) (p : Regex α) : Regex β :=
  p.map (Atom.mapAlphabet f)

@[simp] theorem mapAlphabet_zero (f : α → β) : mapAlphabet f (0 : Regex α) = 0 := rfl
@[simp] theorem mapAlphabet_one (f : α → β) : mapAlphabet f (1 : Regex α) = 1 := rfl
@[simp] theorem mapAlphabet_literal (f : α → β) (a : α) :
    mapAlphabet f (literal a) = literal (f a) := rfl
@[simp] theorem mapAlphabet_any (f : α → β) :
    mapAlphabet f (any : Regex α) = (any : Regex β) := rfl
@[simp] theorem mapAlphabet_add (f : α → β) (p q : Regex α) :
    mapAlphabet f (p + q) = mapAlphabet f p + mapAlphabet f q := rfl
@[simp] theorem mapAlphabet_mul (f : α → β) (p q : Regex α) :
    mapAlphabet f (p * q) = mapAlphabet f p * mapAlphabet f q := rfl
@[simp] theorem mapAlphabet_star (f : α → β) (p : Regex α) :
    mapAlphabet f p.star = (mapAlphabet f p).star := rfl

/-- Nullability is independent of literal alphabet labels. -/
@[simp] theorem mapAlphabet_nullable (f : α → β) (p : Regex α) :
    (mapAlphabet f p).matchEpsilon = p.matchEpsilon := by
  induction p <;> simp_all [mapAlphabet, RegularExpression.map, RegularExpression.matchEpsilon]

/-- Relabeling is functorial on syntax, without injectivity premises. -/
@[simp] theorem mapAlphabet_id (p : Regex α) : mapAlphabet id p = p := by
  have atoms : Atom.mapAlphabet (id : α → α) = id := by funext a; cases a <;> rfl
  simp [mapAlphabet, atoms, RegularExpression.map_id]

theorem mapAlphabet_comp {γ : Type*} (g : β → γ) (f : α → β) (p : Regex α) :
    mapAlphabet g (mapAlphabet f p) = mapAlphabet (g ∘ f) p := by
  have atoms : Atom.mapAlphabet g ∘ Atom.mapAlphabet f = Atom.mapAlphabet (g ∘ f) := by
    funext a; cases a <;> rfl
  simp only [mapAlphabet, RegularExpression.map_map, atoms]

section Executable
variable [DecidableEq α] [DecidableEq β]

theorem atom_accepts_mapAlphabet (f : α → β) (injective : Function.Injective f)
    (atom : Atom α) (a : α) :
    (atom.mapAlphabet f).accepts (f a) = atom.accepts a := by
  cases atom with
  | literal expected => simp [Atom.mapAlphabet, Atom.accepts, injective.eq_iff]
  | any => rfl

/-- A mapped-letter derivative is the relabeling of the source derivative. -/
theorem derivative_mapAlphabet (f : α → β) (injective : Function.Injective f)
    (a : α) (p : Regex α) :
    derivative (f a) (mapAlphabet f p) = mapAlphabet f (derivative a p) := by
  have nullable (q : Regex α) : (q.map (Atom.mapAlphabet f)).matchEpsilon = q.matchEpsilon :=
    mapAlphabet_nullable f q
  induction p <;> simp_all [mapAlphabet, RegularExpression.map, derivative,
    atom_accepts_mapAlphabet f injective, apply_ite]

/-- Matching is unchanged on mapped words under an injective relabeling. -/
theorem fullMatch_mapAlphabet (f : α → β) (injective : Function.Injective f)
    (p : Regex α) (word : List α) :
    fullMatch (mapAlphabet f p) (word.map f) = fullMatch p word := by
  induction word generalizing p <;> simp_all only [List.map_nil, List.map_cons, fullMatch,
    mapAlphabet_nullable, derivative_mapAlphabet f injective]

/-- This is a pullback comparison on mapped words, not an unrestricted image claim. -/
theorem mapped_word_mem_language (f : α → β) (injective : Function.Injective f)
    (p : Regex α) (word : List α) :
    word.map f ∈ language (mapAlphabet f p) ↔ word ∈ language p := by
  rw [← fullMatch_correct, ← fullMatch_correct, fullMatch_mapAlphabet f injective]

end Executable

/-- A Unicode scalar is encoded as a singleton string, not as a byte sequence. -/
theorem stringSingleton_injective : Function.Injective String.singleton :=
  fun _ _ same => String.singleton_inj.mp same

/-- The scalar-string alphabet spelling of a character expression. -/
def scalarRegex (p : Regex Char) : Regex String := mapAlphabet String.singleton p

/-- One input alphabet element per Unicode scalar. -/
def scalarInput (input : String) : List String := input.toList.map String.singleton

theorem fullMatch_scalarRegex (p : Regex Char) (input : String) :
    fullMatch (scalarRegex p) (scalarInput input) = fullMatch p input.toList :=
  fullMatch_mapAlphabet String.singleton stringSingleton_injective p input.toList

theorem scalarInput_length (input : String) : (scalarInput input).length = input.toList.length := by
  simp [scalarInput]

theorem scalarInput_letter {input : String} {letter : String} (member : letter ∈ scalarInput input) :
    ∃ character : Char, letter = String.singleton character := by
  obtain ⟨character, _, same⟩ := List.mem_map.mp member
  exact ⟨character, same.symm⟩

/-- An unrestricted string alphabet contains letters that are not singleton scalar strings. -/
theorem multiScalar_not_singleton : "ab" ∉ Set.range String.singleton := by
  rintro ⟨character, same⟩
  have lengths := congrArg (fun s : String => s.toList.length) same
  simp at lengths

namespace AlphabetTransportControls

/-- Collapsing different letters can create a match. -/
theorem noninjective_map_changes_recognition :
    fullMatch (mapAlphabet (fun _ : Bool => ()) (literal true)) [()] = true ∧
      fullMatch (literal true) [false] = false := by decide

end AlphabetTransportControls

namespace AlphabetMapControls

/-- A non-ASCII literal is preserved exactly by the scalar spelling. -/
theorem unicode_literal : fullMatch (scalarRegex (literal 'é')) (scalarInput "é") = true := by
  rw [fullMatch_scalarRegex]
  decide

theorem unicode_literal_mismatch : fullMatch (scalarRegex (literal 'é')) (scalarInput "e") = false := by
  rw [fullMatch_scalarRegex]
  decide

/-- Dot consumes one Unicode scalar, including a scalar with a four-byte UTF-8 encoding. -/
theorem scalar_wildcard : fullMatch (scalarRegex (any : Regex Char)) (scalarInput "🦀") = true := by
  rw [fullMatch_scalarRegex]
  decide

/-- One wildcard does not consume the two UTF-8 bytes encoding a non-ASCII scalar. -/
theorem byte_wildcard_differs :
    fullMatch (any : Regex UInt8) (String.utf8EncodeChar 'é') = false := by
  decide

theorem scalar_not_byte_interpretation :
    fullMatch (scalarRegex (any : Regex Char)) (scalarInput "é") ≠
      fullMatch (any : Regex UInt8) (String.utf8EncodeChar 'é') := by
  rw [fullMatch_scalarRegex, byte_wildcard_differs]
  decide

theorem utf8_nonAscii_length : (String.utf8EncodeChar 'é').length = 2 := by
  decide

/-- A wildcard over unrestricted String letters also accepts a multi-scalar letter. -/
theorem unrestricted_string_wildcard :
    fullMatch (mapAlphabet String.singleton (any : Regex Char)) ["ab"] = true := by
  decide

/-- The wildcard language cannot be identified with its non-surjective scalar image. -/
theorem scalar_wildcard_language_ne_image :
    language (scalarRegex (any : Regex Char)) ≠
      Language.map String.singleton (language (any : Regex Char)) := by
  intro same
  have accepted := (fullMatch_correct _ _).mp unrestricted_string_wildcard
  obtain ⟨word, ⟨character, rfl⟩, mapped⟩ :
      ["ab"] ∈ Language.map String.singleton (language (any : Regex Char)) := same ▸ accepted
  exact multiScalar_not_singleton ⟨character, List.singleton_inj.mp mapped⟩

end AlphabetMapControls

end Mettapedia.Computability.RegularLanguages
