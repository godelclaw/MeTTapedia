import Mettapedia.Languages.MM0.Kernel.Term
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mathlib.Data.List.Indexes
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Forall2

/-!
# Named first-order patterns and MM0 application spines

Constructor names are resolved against an explicit ordered inventory. The
source uses the existing `Pattern`; the target uses MM0's `Preterm`. Ordinary
context variables are indices on both sides. An n-ary constructor application
becomes a binary application spine. Unsupported forms and unknown names are
refused. Typing, rule instantiation, and declaration admission are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Kernel

/-- Lookup retains the declaration's position in the authored inventory. -/
def index? (names : List String) (name : String) : Option Nat :=
  if name ∈ names then some (names.idxOf name) else none

theorem index?_some (names : List String) (name : String) (member : name ∈ names) :
    index? names name = some (names.idxOf name) := by
  simp [index?, member]

theorem index?_none (names : List String) (name : String) (absent : name ∉ names) :
    index? names name = none := by
  simp [index?, absent]

theorem getElem?_index? {names : List String} {name : String} {index : Nat}
    (found : index? names name = some index) : names[index]? = some name := by
  unfold index? at found
  split at found
  next member =>
    have same := Option.some.inj found
    subst index
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr member), List.getElem_idxOf]
  next absent => cases found

theorem index?_getElem? {names : List String} {name : String} {index : Nat}
    (distinct : names.Nodup) (lookup : names[index]? = some name) :
    index? names name = some index := by
  have member := List.mem_of_getElem? lookup
  have found := index?_some names name member
  obtain ⟨leftBound, leftValue⟩ := List.getElem?_eq_some_iff.mp (getElem?_index? found)
  obtain ⟨rightBound, rightValue⟩ := List.getElem?_eq_some_iff.mp lookup
  have same : names.idxOf name = index := distinct.getElem_inj_iff.mp
    (leftValue.trans rightValue.symm)
  simpa [same] using found

/-- Resolve a local numeric reference by its retained name in the joined inventory. -/
def references? (localNames joinedNames : List String) (index : Nat) : Option Nat :=
  localNames[index]?.bind (index? joinedNames)

theorem references?_of_name {localNames joinedNames : List String} {name : String}
    {localIndex joinedIndex : Nat}
    (original : index? localNames name = some localIndex)
    (joined : index? joinedNames name = some joinedIndex) :
    references? localNames joinedNames localIndex = some joinedIndex := by
  simp [references?, getElem?_index? original, joined]

mutual
  def encode (names : List String) : Pattern → Option Preterm
    | .bvar index => some (.var index)
    | .apply name arguments => do
        let index ← index? names name
        let arguments' ← encodeList names arguments
        pure (Preterm.applyArgs (.term index) arguments')
    | _ => none
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def encodeList (names : List String) : List Pattern → Option (List Preterm)
    | [] => some []
    | pattern :: patterns => do
        let first ← encode names pattern
        let rest ← encodeList names patterns
        pure (first :: rest)
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- The independent structural graph of the translation. -/
inductive Encodes (names : List String) : Pattern → Preterm → Prop where
  | boundVariable (index : Nat) : Encodes names (.bvar index) (.var index)
  | constructor {name : String} {index : Nat} {arguments : List Pattern}
      {encoded : List Preterm} :
      index? names name = some index →
      List.Forall₂ (Encodes names) arguments encoded →
      Encodes names (.apply name arguments) (Preterm.applyArgs (.term index) encoded)

mutual
  theorem Encodes.eval {names : List String} {pattern : Pattern} {expression : Preterm}
      (encoded : Encodes names pattern expression) : encode names pattern = some expression := by
    cases encoded with
    | boundVariable index => simp [encode]
    | constructor found arguments =>
        simp [encode, found, encodesList_eval arguments]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodesList_eval {names : List String} {patterns : List Pattern}
      {expressions : List Preterm} (encoded : List.Forall₂ (Encodes names) patterns expressions) :
      encodeList names patterns = some expressions := by
    cases encoded with
    | nil => simp [encodeList]
    | cons head tail => simp [encodeList, head.eval, encodesList_eval tail]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  theorem encode_sound {names : List String} {pattern : Pattern} {expression : Preterm}
      (encoded : encode names pattern = some expression) : Encodes names pattern expression := by
    cases pattern with
    | bvar index =>
        simp only [encode, Option.some.injEq] at encoded
        subst expression
        exact .boundVariable index
    | apply name arguments =>
        cases found : index? names name with
        | none => simp [encode, found] at encoded
        | some index =>
            cases result : encodeList names arguments with
            | none => simp [encode, found, result] at encoded
            | some expressions =>
                have same : Preterm.applyArgs (.term index) expressions = expression := by
                  simpa [encode, found, result] using encoded
                subst expression
                exact .constructor found (encodeList_sound result)
    | _ => simp [encode] at encoded
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodeList_sound {names : List String} {patterns : List Pattern}
      {expressions : List Preterm} (encoded : encodeList names patterns = some expressions) :
      List.Forall₂ (Encodes names) patterns expressions := by
    cases patterns with
    | nil =>
        simp only [encodeList, Option.some.injEq] at encoded
        subst expressions
        exact .nil
    | cons pattern patterns =>
        cases first : encode names pattern with
        | none => simp [encodeList, first] at encoded
        | some expression =>
            cases rest : encodeList names patterns with
            | none => simp [encodeList, first, rest] at encoded
            | some remaining =>
                have same : expression :: remaining = expressions := by
                  simpa [encodeList, first, rest] using encoded
                subst expressions
                exact .cons (encode_sound first) (encodeList_sound rest)
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem encode_eq_some_iff (names : List String) (pattern : Pattern) (expression : Preterm) :
    encode names pattern = some expression ↔ Encodes names pattern expression :=
  ⟨encode_sound, Encodes.eval⟩

mutual
  /-- Recompilation of one named term in a joined module is actual index relocation. -/
  theorem Encodes.relocate {localNames joinedNames : List String} {pattern : Pattern}
      {localExpression joinedExpression : Preterm}
      (original : Encodes localNames pattern localExpression)
      (joined : Encodes joinedNames pattern joinedExpression) :
      localExpression.relocateTerms? (references? localNames joinedNames) =
        some joinedExpression := by
    cases original with
    | boundVariable index => cases joined; rfl
    | constructor localFound localChildren =>
        cases joined with
        | constructor joinedFound joinedChildren =>
            apply Preterm.relocateTerms?_applyArgs
            · simp [Preterm.relocateTerms?, references?_of_name localFound joinedFound]
            · exact encodesList_relocate localChildren joinedChildren
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodesList_relocate {localNames joinedNames : List String}
      {patterns : List Pattern} {localExpressions joinedExpressions : List Preterm}
      (original : List.Forall₂ (Encodes localNames) patterns localExpressions)
      (joined : List.Forall₂ (Encodes joinedNames) patterns joinedExpressions) :
      List.Forall₂ (fun source target =>
        source.relocateTerms? (references? localNames joinedNames) = some target)
        localExpressions joinedExpressions := by
    cases original with
    | nil => cases joined; exact .nil
    | cons localHead localTail =>
        cases joined with
        | cons joinedHead joinedTail =>
            exact .cons (localHead.relocate joinedHead)
              (encodesList_relocate localTail joinedTail)
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- The relocated list keeps premise order and every occurrence. -/
theorem encodesList_relocate_eval {localNames joinedNames : List String}
    {patterns : List Pattern} {original image : List Preterm}
    (before : List.Forall₂ (Encodes localNames) patterns original)
    (after : List.Forall₂ (Encodes joinedNames) patterns image) :
    original.mapM (Preterm.relocateTerms? (references? localNames joinedNames)) = some image := by
  have relocated := encodesList_relocate before after
  clear before after
  induction relocated with
  | nil => rfl
  | cons first rest ih => simp [first, ih]

/-- Reading binary application appends one argument to its named constructor. -/
def decode (names : List String) : Preterm → Option Pattern
  | .var index => some (.bvar index)
  | .term index => do
      let name ← names[index]?
      pure (.apply name [])
  | .app function argument => do
      let function' ← decode names function
      let argument' ← decode names argument
      match function' with
      | .apply name arguments => pure (.apply name (arguments ++ [argument']))
      | _ => none

theorem decode_applyArgs (names : List String) (function : Preterm) (arguments : List Preterm)
    (name : String) (preceding : List Pattern)
    (decoded : decode names function = some (.apply name preceding))
    (results : List Pattern)
    (decodedArguments : List.Forall₂ (fun expression pattern =>
      decode names expression = some pattern) arguments results) :
    decode names (Preterm.applyArgs function arguments) = some (.apply name (preceding ++ results)) := by
  induction decodedArguments generalizing function preceding with
  | nil => simpa using decoded
  | @cons expression pattern expressions patterns head tail ih =>
      have applied : decode names (.app function expression) =
          some (.apply name (preceding ++ [pattern])) := by
        simp [decode, decoded, head]
      simpa only [Preterm.applyArgs, List.append_assoc, List.singleton_append] using
        ih (.app function expression) (preceding ++ [pattern]) applied

mutual
  theorem Encodes.decode {names : List String} {pattern : Pattern} {expression : Preterm}
      (encoded : Encodes names pattern expression) : decode names expression = some pattern := by
    cases encoded with
    | boundVariable => rfl
    | @constructor name index arguments expressions found encodedArguments =>
        have decoded : decode names (.term index) = some (.apply name []) := by
          simp [decode, getElem?_index? found]
        simpa using decode_applyArgs names (.term index) expressions name [] decoded arguments
          (encodesList_decode encodedArguments)
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodesList_decode {names : List String} {patterns : List Pattern}
      {expressions : List Preterm} (encoded : List.Forall₂ (Encodes names) patterns expressions) :
      List.Forall₂ (fun expression pattern => decode names expression = some pattern)
        expressions patterns := by
    cases encoded with
    | nil => exact .nil
    | cons head tail => exact .cons head.decode (encodesList_decode tail)
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem encoded_injective {names : List String} {first second : Pattern} {expression : Preterm}
    (left : Encodes names first expression) (right : Encodes names second expression) : first = second :=
  Option.some.inj (left.decode.symm.trans right.decode)

/-- Decoding a well-indexed spine introduces no term that cannot be re-encoded.
Distinct names make a declaration's numeric position recoverable. -/
theorem decode_sound {names : List String} (distinct : names.Nodup)
    {expression : Preterm} {pattern : Pattern} (decoded : decode names expression = some pattern) :
    Encodes names pattern expression := by
  induction expression generalizing pattern with
  | var index =>
      simp only [decode, Option.some.injEq] at decoded
      subst pattern
      exact .boundVariable index
  | term index =>
      cases found : names[index]? with
      | none => simp [decode, found] at decoded
      | some name =>
          simp [decode, found] at decoded
          subst pattern
          exact .constructor (index?_getElem? distinct found) .nil
  | app function argument ihFunction ihArgument =>
      cases functionResult : decode names function with
      | none => simp [decode, functionResult] at decoded
      | some functionPattern =>
          cases argumentResult : decode names argument with
          | none => simp [decode, functionResult, argumentResult] at decoded
          | some argumentPattern =>
              cases functionPattern with
              | apply name arguments =>
                  simp [decode, functionResult, argumentResult] at decoded
                  subst pattern
                  have encodedFunction := ihFunction functionResult
                  have encodedArgument := ihArgument argumentResult
                  cases encodedFunction with
                  | constructor found encodedArguments =>
                      simpa only [Preterm.applyArgs_append, Preterm.applyArgs] using
                        (Encodes.constructor found
                          (List.rel_append encodedArguments (.cons encodedArgument .nil)))
              | _ => simp [decode, functionResult, argumentResult] at decoded

theorem decode_eq_some_iff {names : List String} (distinct : names.Nodup)
    (expression : Preterm) (pattern : Pattern) :
    decode names expression = some pattern ↔ Encodes names pattern expression :=
  ⟨decode_sound distinct, Encodes.decode⟩

mutual
  /-- The shared context-substitution action agrees with MM0 substitution.
  The image premise constrains actual successful lookups, so a finite
  substitution need not provide images outside its declared context. -/
  theorem Encodes.substitute {names : List String} {pattern : Pattern}
      {expression result : Preterm}
      (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
      {substitution : Kernel.Substitution} (encoded : Encodes names pattern expression)
      (substituted : Preterm.Substitutes substitution expression result)
      (images : ∀ index image, substitution index = some image →
        Encodes names (assignment index) image) :
      Encodes names (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment pattern)
        result := by
    cases encoded with
    | boundVariable index =>
        cases substituted with
        | var lookup => exact images index _ lookup
    | constructor found encodedArguments =>
        obtain ⟨head, arguments, same, headSubstituted, argumentsSubstituted⟩ :=
          (Preterm.substitutes_applyArgs_iff _ _ _ _).mp substituted
        cases headSubstituted
        subst result
        exact .constructor found
          (encodesList_substitute assignment encodedArguments argumentsSubstituted images)
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodesList_substitute {names : List String} {patterns : List Pattern}
      {expressions results : List Preterm}
      (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
      {substitution : Kernel.Substitution}
      (encoded : List.Forall₂ (Encodes names) patterns expressions)
      (substituted : List.Forall₂ (Preterm.Substitutes substitution) expressions results)
      (images : ∀ index image, substitution index = some image →
        Encodes names (assignment index) image) :
      List.Forall₂ (Encodes names)
        (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList assignment patterns) results := by
    cases encoded with
    | nil => cases substituted; exact .nil
    | cons first rest =>
        cases substituted with
        | cons firstSubstituted restSubstituted =>
            exact .cons (first.substitute assignment firstSubstituted images)
              (encodesList_substitute assignment rest restSubstituted images)
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem unknown_constructor_refused (names : List String) (name : String)
    (absent : name ∉ names) (arguments : List Pattern) : encode names (.apply name arguments) = none := by
  simp [encode, index?_none names name absent]

example : encode ["imp", "truth"] (.apply "imp" [.apply "truth" [], .bvar 0]) =
    some (.app (.app (.term 0) (.term 1)) (.var 0)) := by
  simp [encode, encodeList, index?, Preterm.applyArgs]

example : encode ["imp", "truth"] (.lambda none (.bvar 0)) = none := by simp [encode]

example : decode ["imp", "truth"] (.app (.var 0) (.term 1)) = none := rfl

end Mettapedia.Languages.MM0.Translation.FirstOrderSyntax
