import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Nat.Pairing

/-!
# A number for every pattern and every rule instance

The judgments of a calculus of the shared checker are patterns, and a rule
instance is a rule name with a list of patterns.  Both are finite trees over
strings and numbers, so each has a number, different for different trees
(`patternCode_injective`, `ruleInstanceCode_injective`).

The numbers are given by a definition, not chosen: a string is the code of the
list of the numbers of its characters, a pattern is the pair of the number of
its constructor and the numbers of its parts.  No instance is declared and
nothing is assumed of the strings beyond what they are.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker (RuleInstance)

/-- **The number of a string**: the code of the list of the numbers of its
characters. -/
def stringCode (text : String) : Nat :=
  Encodable.encode (text.toList.map Char.toNat)

/-- Different strings have different numbers. -/
theorem stringCode_injective : Function.Injective stringCode := by
  intro first second same
  have characters : first.toList.map Char.toNat = second.toList.map Char.toNat :=
    Encodable.encode_injective same
  exact String.toList_injective
    (List.map_injective_iff.mpr (fun _ _ equal => Char.toNat_inj.mp equal) characters)

/-- The number of a list of strings. -/
def stringsCode (texts : List String) : Nat :=
  Encodable.encode (texts.map stringCode)

theorem stringsCode_injective : Function.Injective stringsCode := fun _ _ same =>
  List.map_injective_iff.mpr stringCode_injective (Encodable.encode_injective same)

/-- The number of a string that may be absent. -/
def optionalStringCode (text : Option String) : Nat :=
  Encodable.encode (text.map stringCode)

theorem optionalStringCode_injective : Function.Injective optionalStringCode := fun _ _ same =>
  Option.map_injective stringCode_injective (Encodable.encode_injective same)

/-- The number of a kind of collection. -/
def collectionCode : CollType → Nat
  | .vec => 0
  | .hashBag => 1
  | .hashSet => 2

theorem collectionCode_injective : Function.Injective collectionCode := by
  intro first second same
  cases first <;> cases second <;> first | rfl | cases same

mutual

/-- **The number of a pattern**: the number of its constructor paired with
the numbers of its parts. -/
def patternCode : Pattern → Nat
  | .bvar index => Nat.pair 0 index
  | .fvar name => Nat.pair 1 (stringCode name)
  | .apply label arguments => Nat.pair 2 (Nat.pair (stringCode label) (patternsCode arguments))
  | .lambda name body => Nat.pair 3 (Nat.pair (optionalStringCode name) (patternCode body))
  | .multiLambda arity names body =>
      Nat.pair 4 (Nat.pair arity (Nat.pair (stringsCode names) (patternCode body)))
  | .subst body replacement => Nat.pair 5 (Nat.pair (patternCode body) (patternCode replacement))
  | .collection kind elements rest =>
      Nat.pair 6 (Nat.pair (collectionCode kind)
        (Nat.pair (patternsCode elements) (optionalStringCode rest)))

/-- The number of a list of patterns: zero for the empty list, otherwise one
more than the pair of the numbers of its head and its tail. -/
def patternsCode : List Pattern → Nat
  | [] => 0
  | head :: tail => Nat.pair (patternCode head) (patternsCode tail) + 1

end

/-- Lists of patterns whose members have numbers of their own have numbers of
their own. -/
theorem patternsCode_injective_of {first : List Pattern}
    (each : ∀ pattern ∈ first, ∀ other,
      patternCode pattern = patternCode other → pattern = other) :
    ∀ second, patternsCode first = patternsCode second → first = second := by
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons head tail => simp [patternsCode] at same
  | cons head tail ih =>
      intro second same
      cases second with
      | nil => simp [patternsCode] at same
      | cons otherHead otherTail =>
          simp only [patternsCode, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at same
          rw [each head List.mem_cons_self otherHead same.1,
            ih (fun pattern member => each pattern (List.mem_cons_of_mem _ member)) otherTail
              same.2]

/-- **Different patterns have different numbers.** -/
theorem patternCode_injective : Function.Injective patternCode := by
  intro first
  induction first using Pattern.inductionOn with
  | hbvar index =>
      intro second same
      cases second with
      | bvar other =>
          simp only [patternCode, Nat.pair_eq_pair, true_and] at same
          rw [same]
      | _ => simp [patternCode, Nat.pair_eq_pair] at same
  | hfvar name =>
      intro second same
      cases second with
      | fvar other =>
          simp only [patternCode, Nat.pair_eq_pair, true_and] at same
          rw [stringCode_injective same]
      | _ => simp [patternCode, Nat.pair_eq_pair] at same
  | happly label arguments ih =>
      intro second same
      cases second with
      | apply otherLabel otherArguments =>
          simp only [patternCode, Nat.pair_eq_pair, true_and] at same
          rw [stringCode_injective same.1, patternsCode_injective_of ih otherArguments same.2]
      | _ => simp [patternCode, Nat.pair_eq_pair] at same
  | hlambda name body ih =>
      intro second same
      cases second with
      | lambda otherName otherBody =>
          simp only [patternCode, Nat.pair_eq_pair, true_and] at same
          rw [optionalStringCode_injective same.1, ih same.2]
      | _ => simp [patternCode, Nat.pair_eq_pair] at same
  | hmultiLambda arity names body ih =>
      intro second same
      cases second with
      | multiLambda otherArity otherNames otherBody =>
          simp only [patternCode, Nat.pair_eq_pair, true_and] at same
          rw [same.1, stringsCode_injective same.2.1, ih same.2.2]
      | _ => simp [patternCode, Nat.pair_eq_pair] at same
  | hsubst body replacement ihBody ihReplacement =>
      intro second same
      cases second with
      | subst otherBody otherReplacement =>
          simp only [patternCode, Nat.pair_eq_pair, true_and] at same
          rw [ihBody same.1, ihReplacement same.2]
      | _ => simp [patternCode, Nat.pair_eq_pair] at same
  | hcollection kind elements rest ih =>
      intro second same
      cases second with
      | collection otherKind otherElements otherRest =>
          simp only [patternCode, Nat.pair_eq_pair, true_and] at same
          rw [collectionCode_injective same.1, patternsCode_injective_of ih otherElements same.2.1,
            optionalStringCode_injective same.2.2]
      | _ => simp [patternCode, Nat.pair_eq_pair] at same

/-- **Different lists of patterns have different numbers.** -/
theorem patternsCode_injective : Function.Injective patternsCode := fun _ second same =>
  patternsCode_injective_of (fun _ _ _ equal => patternCode_injective equal) second same

/-- **The number of a rule instance**: the number of the name of its rule
paired with the number of its arguments. -/
def ruleInstanceCode (ruleInstance : RuleInstance) : Nat :=
  Nat.pair (stringCode ruleInstance.ruleId.value) (patternsCode ruleInstance.arguments)

/-- **Different rule instances have different numbers.** -/
theorem ruleInstanceCode_injective : Function.Injective ruleInstanceCode := by
  rintro ⟨⟨firstName⟩, firstArguments⟩ ⟨⟨secondName⟩, secondArguments⟩ same
  simp only [ruleInstanceCode, Nat.pair_eq_pair] at same
  rw [stringCode_injective same.1, patternsCode_injective same.2]

/-- **Positive**: a variable and a constant have different numbers. -/
theorem patternCode_fvar_ne_apply (name label : String) :
    patternCode (.fvar name) ≠ patternCode (.apply label []) :=
  fun same => by cases patternCode_injective same

/-- **Negative**: the length of a string is no number of it; two strings of
one length share it. -/
theorem length_not_injective : ¬ Function.Injective String.length :=
  fun injective => absurd (injective (a₁ := "a") (a₂ := "b") rfl) (by decide)

#print axioms stringCode_injective
#print axioms patternCode_injective
#print axioms patternsCode_injective
#print axioms ruleInstanceCode_injective

end Mettapedia.Logic.HostingStyles.Guests
