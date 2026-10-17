import Mettapedia.Computability.FramedWordMapping
import Mettapedia.Computability.WordHomomorphismMachine

/-!
# Controls for executed framed mapping

A nonidentity subroutine erases false symbols and expands true symbols.
The caller retains empty fields, repeated words, order and delimiters.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedWordMapping.Controls
open Turing

def image (symbol : Bool) : List Bool := if symbol then [false, true, false] else []
def source : FinTM2 := WordHomomorphismMachine.machine image
local instance : Fintype (source.Γ source.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (source.Γ source.k₀) := inferInstanceAs (Inhabited Bool)
local instance : Inhabited (source.Γ source.k₁) := inferInstanceAs (Inhabited Bool)

def mapped : FinTM2 := machine source

def encoded (words : List (List Bool)) : List (Option Bool) :=
  WordTemplateMachine.Indexed.frame words

def expected (words : List (List Bool)) : List (Option Bool) :=
  WordTemplateMachine.Indexed.frame (words.map (List.flatMap image))

def budget (words : List (List Bool)) : Nat :=
  totalClock source id (List.flatMap image)
    (fun word => 2 * word.length + 2 * (word.flatMap image).length + 2) words

noncomputable def runs (words : List (List Bool)) :
    TM2OutputsInTime mapped (encoded words) (some (expected words)) (budget words) := by
  simpa only [mapped, encoded, expected, budget, List.map_id_fun, id_eq] using
    outputs source id (List.flatMap image) _ (WordHomomorphismMachine.outputs image) words

theorem erased_word_retains_boundary : expected [[false]] = [none] := rfl

theorem no_words_is_different : expected [[false]] ≠ expected [] := by decide

theorem mixed_words : expected [[false], [true], [], [true]] =
    [none, some false, some true, some false, none, none, some false, some true, some false, none] := rfl

theorem order_matters : expected [[false], [true]] ≠ expected [[true], [false]] := by decide

theorem duplicated_words (word : List Bool) :
    expected [word, word] = expected [word] ++ expected [word] := by
  simp [expected, WordTemplateMachine.Indexed.frame]

theorem finiteAlphabet (key : mapped.K) : Finite (mapped.Γ key) := by
  apply FramedWordMapping.finiteAlphabet source
  intro key
  change Finite (WordHomomorphismMachine.Alphabet (A := Bool) (B := Bool) key)
  cases key <;> infer_instance

end Mettapedia.Computability.FramedWordMapping.Controls
