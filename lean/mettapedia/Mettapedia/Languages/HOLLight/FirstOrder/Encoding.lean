import Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
import Mettapedia.Languages.OpenTheory.Sequent
import Mathlib.Data.Finset.Sort

/-!
# HOL Light's syntax as labeled trees

Every piece of HOL Light's syntax becomes a labeled tree: a constructor becomes a label, its
fields become children. A character is its Unicode plane in unary followed by the sixteen bits
of its position in the plane, so labels stay small and every valid tree of this shape is a
character. The encodings are injective, so the structural
order of trees orders the syntax, and a finite set of hypotheses has one sorted listing.

* **Encodings.** `encodeChar`, `encodeString`, `encodeName`, the mutual `encodeTy`,
  `encodeTypeOp`, `encodeConst`, their provenances and `encodeSourceTerm`, and `encodeTerm`
  for de Bruijn terms, whose indices are unary (`encodeUnary`); each is injective
  (`encodeTy_injective`, `encodeTerm_injective`, ...).
* **Hypothesis sets.** Canonical terms compare by their encodings (`CanonicalLe`), a total
  order; `sortedHypotheses` lists a hypothesis set in that order, and the listing determines
  the set (`sortedHypotheses_injective`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.Languages.OpenTheory

/-! ## Labels -/

abbrev stringLabel : Nat := 3
abbrev nameLabel : Nat := 4
abbrev listLabel : Nat := 5
abbrev tyVarLabel : Nat := 6
abbrev tyOpLabel : Nat := 7
abbrev typeOpLabel : Nat := 8
abbrev typeOpUndefinedLabel : Nat := 9
abbrev typeOpDefinedLabel : Nat := 10
abbrev constLabel : Nat := 11
abbrev constUndefinedLabel : Nat := 12
abbrev constDefinedLabel : Nat := 13
abbrev constAbstractionLabel : Nat := 14
abbrev constRepresentationLabel : Nat := 15
abbrev sourceConstLabel : Nat := 16
abbrev sourceVarLabel : Nat := 17
abbrev sourceAppLabel : Nat := 18
abbrev sourceAbsLabel : Nat := 19
abbrev termConstLabel : Nat := 20
abbrev termFreeLabel : Nat := 21
abbrev termBoundLabel : Nat := 22
abbrev termAppLabel : Nat := 23
abbrev termAbsLabel : Nat := 24
abbrev unaryZeroLabel : Nat := 25
abbrev unarySuccLabel : Nat := 26
abbrev termMapletLabel : Nat := 27
abbrev pairLabel : Nat := 28
abbrev typeMapletLabel : Nat := 29
abbrev charLabel : Nat := 30

/-! ## Characters, strings and names -/

/-- A binary digit is a leaf labeled with the digit. -/
def encodeDigit (digit : Nat) : LabeledTree := .node digit []

/-- De Bruijn indices and character planes in unary. -/
def encodeUnary : Nat → LabeledTree
  | 0 => .node unaryZeroLabel []
  | count + 1 => .node unarySuccLabel [encodeUnary count]

theorem encodeUnary_injective : Function.Injective encodeUnary := by
  intro first
  induction first with
  | zero => intro second same; cases second <;> simp_all [encodeUnary, unaryZeroLabel, unarySuccLabel]
  | succ count ih =>
      intro second same
      cases second with
      | zero => simp [encodeUnary, unaryZeroLabel, unarySuccLabel] at same
      | succ other =>
          simp only [encodeUnary, LabeledTree.node.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [ih same]

/-- The bits of a number at positions `count - 1` down to `0`. -/
def bitsDown (number : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 => (number / 2 ^ count % 2) :: bitsDown number count

/-- The value of bits listed from the most significant. -/
def valueDown : List Nat → Nat
  | [] => 0
  | bit :: rest => bit * 2 ^ rest.length + valueDown rest

theorem bitsDown_length (number : Nat) : ∀ count, (bitsDown number count).length = count
  | 0 => rfl
  | count + 1 => by simp [bitsDown, bitsDown_length number count]

theorem valueDown_bitsDown (number : Nat) : ∀ count, valueDown (bitsDown number count) = number % 2 ^ count
  | 0 => by simp [bitsDown, valueDown, Nat.mod_one]
  | count + 1 => by
      rw [bitsDown, valueDown, bitsDown_length, valueDown_bitsDown number count, Nat.mod_pow_succ,
        Nat.mul_comm, Nat.add_comm]

/-- A character: its plane in unary, then the sixteen bits of its position in the plane. -/
def encodeChar (character : Char) : LabeledTree :=
  .node charLabel (encodeUnary (character.toNat / 65536) ::
    (bitsDown character.toNat 16).map encodeDigit)

theorem encodeChar_injective : Function.Injective encodeChar := by
  intro first second same
  simp only [encodeChar, LabeledTree.node.injEq, List.cons.injEq, true_and] at same
  have planes := encodeUnary_injective same.1
  have bits : bitsDown first.toNat 16 = bitsDown second.toNat 16 :=
    List.map_injective_iff.mpr (fun _ _ equal => by simpa [encodeDigit] using equal) same.2
  have offsets : first.toNat % 2 ^ 16 = second.toNat % 2 ^ 16 := by
    rw [← valueDown_bitsDown, ← valueDown_bitsDown, bits]
  apply Char.toNat_inj.mp
  rw [← Nat.div_add_mod first.toNat 65536, ← Nat.div_add_mod second.toNat 65536, planes]
  simpa using congrArg (65536 * (second.toNat / 65536) + ·) offsets

/-- A string as the list of its characters. -/
def encodeString (text : String) : LabeledTree :=
  .node stringLabel (text.toList.map encodeChar)

theorem encodeString_injective : Function.Injective encodeString := by
  intro first second same
  simp only [encodeString, LabeledTree.node.injEq, true_and] at same
  exact String.toList_injective (List.map_injective_iff.mpr encodeChar_injective same)

/-- A name: its namespace components, then its own component. -/
def encodeName (name : Name) : LabeledTree :=
  .node nameLabel [.node listLabel (name.namespaceComponents.map encodeString),
    encodeString name.component]

theorem encodeName_injective : Function.Injective encodeName := by
  intro first second same
  simp only [encodeName, LabeledTree.node.injEq, List.cons.injEq, true_and, and_true] at same
  obtain ⟨namespaces, component⟩ := same
  cases first
  cases second
  simp only [Name.mk.injEq]
  exact ⟨List.map_injective_iff.mpr encodeString_injective namespaces,
    encodeString_injective component⟩

/-! ## Types, constants and source terms -/

mutual
  def encodeTy : Ty → LabeledTree
    | .var name => .node tyVarLabel [encodeName name]
    | .op operator arguments => .node tyOpLabel [encodeTypeOp operator, .node listLabel (encodeTys arguments)]

  def encodeTys : List Ty → List LabeledTree
    | [] => []
    | type :: types => encodeTy type :: encodeTys types

  def encodeTypeOp : TypeOp → LabeledTree
    | .mk name provenance => .node typeOpLabel [encodeName name, encodeTypeOpProvenance provenance]

  def encodeTypeOpProvenance : TypeOpProvenance → LabeledTree
    | .undefined => .node typeOpUndefinedLabel []
    | .defined predicate parameters =>
        .node typeOpDefinedLabel [encodeSourceTerm predicate, .node listLabel (parameters.map encodeName)]

  def encodeConst : Const → LabeledTree
    | .mk name provenance => .node constLabel [encodeName name, encodeConstProvenance provenance]

  def encodeConstProvenance : ConstProvenance → LabeledTree
    | .undefined => .node constUndefinedLabel []
    | .defined definition => .node constDefinedLabel [encodeSourceTerm definition]
    | .abstraction operator => .node constAbstractionLabel [encodeTypeOp operator]
    | .representation operator => .node constRepresentationLabel [encodeTypeOp operator]

  def encodeSourceTerm : SourceTerm → LabeledTree
    | .const constant type => .node sourceConstLabel [encodeConst constant, encodeTy type]
    | .var name type => .node sourceVarLabel [encodeName name, encodeTy type]
    | .app function argument => .node sourceAppLabel [encodeSourceTerm function, encodeSourceTerm argument]
    | .abs name type body => .node sourceAbsLabel [encodeName name, encodeTy type, encodeSourceTerm body]
end

mutual
  theorem encodeTy_injective : ∀ (first second : Ty), encodeTy first = encodeTy second → first = second
    | .var firstName, .var secondName, same => by
        simp only [encodeTy, LabeledTree.node.injEq, List.cons.injEq, and_true, true_and] at same
        rw [encodeName_injective same]
    | .op firstOp firstArgs, .op secondOp secondArgs, same => by
        simp only [encodeTy, LabeledTree.node.injEq, List.cons.injEq, and_true, true_and] at same
        rw [encodeTypeOp_injective firstOp secondOp same.1, encodeTys_injective firstArgs secondArgs same.2]
    | .var _, .op _ _, same => by simp [encodeTy, tyVarLabel, tyOpLabel] at same
    | .op _ _, .var _, same => by simp [encodeTy, tyVarLabel, tyOpLabel] at same
  termination_by first => sizeOf first

  theorem encodeTys_injective : ∀ (first second : List Ty), encodeTys first = encodeTys second → first = second
    | [], [], _ => rfl
    | [], _ :: _, same => by simp [encodeTys] at same
    | _ :: _, [], same => by simp [encodeTys] at same
    | firstHead :: firstTail, secondHead :: secondTail, same => by
        simp only [encodeTys, List.cons.injEq] at same
        rw [encodeTy_injective firstHead secondHead same.1, encodeTys_injective firstTail secondTail same.2]
  termination_by first => sizeOf first

  theorem encodeTypeOp_injective : ∀ (first second : TypeOp),
      encodeTypeOp first = encodeTypeOp second → first = second
    | .mk firstName firstProvenance, .mk secondName secondProvenance, same => by
        simp only [encodeTypeOp, LabeledTree.node.injEq, List.cons.injEq, and_true, true_and] at same
        rw [encodeName_injective same.1,
          encodeTypeOpProvenance_injective firstProvenance secondProvenance same.2]
  termination_by first => sizeOf first

  theorem encodeTypeOpProvenance_injective : ∀ (first second : TypeOpProvenance),
      encodeTypeOpProvenance first = encodeTypeOpProvenance second → first = second
    | .undefined, .undefined, _ => rfl
    | .defined firstPredicate firstVariables, .defined secondPredicate secondVariables, same => by
        simp only [encodeTypeOpProvenance, LabeledTree.node.injEq, List.cons.injEq, and_true,
          true_and] at same
        rw [encodeSourceTerm_injective firstPredicate secondPredicate same.1,
          List.map_injective_iff.mpr encodeName_injective same.2]
    | .undefined, .defined _ _, same => by simp [encodeTypeOpProvenance, typeOpUndefinedLabel, typeOpDefinedLabel] at same
    | .defined _ _, .undefined, same => by simp [encodeTypeOpProvenance, typeOpUndefinedLabel, typeOpDefinedLabel] at same
  termination_by first => sizeOf first

  theorem encodeConst_injective : ∀ (first second : Const),
      encodeConst first = encodeConst second → first = second
    | .mk firstName firstProvenance, .mk secondName secondProvenance, same => by
        simp only [encodeConst, LabeledTree.node.injEq, List.cons.injEq, and_true, true_and] at same
        rw [encodeName_injective same.1,
          encodeConstProvenance_injective firstProvenance secondProvenance same.2]
  termination_by first => sizeOf first

  theorem encodeConstProvenance_injective : ∀ (first second : ConstProvenance),
      encodeConstProvenance first = encodeConstProvenance second → first = second
    | .undefined, .undefined, _ => rfl
    | .defined first, .defined second, same => by
        simp only [encodeConstProvenance, LabeledTree.node.injEq, List.cons.injEq, and_true,
          true_and] at same
        rw [encodeSourceTerm_injective first second same]
    | .abstraction first, .abstraction second, same => by
        simp only [encodeConstProvenance, LabeledTree.node.injEq, List.cons.injEq, and_true,
          true_and] at same
        rw [encodeTypeOp_injective first second same]
    | .representation first, .representation second, same => by
        simp only [encodeConstProvenance, LabeledTree.node.injEq, List.cons.injEq, and_true,
          true_and] at same
        rw [encodeTypeOp_injective first second same]
    | .undefined, .defined _, same | .undefined, .abstraction _, same
    | .undefined, .representation _, same | .defined _, .undefined, same
    | .defined _, .abstraction _, same | .defined _, .representation _, same
    | .abstraction _, .undefined, same | .abstraction _, .defined _, same
    | .abstraction _, .representation _, same | .representation _, .undefined, same
    | .representation _, .defined _, same | .representation _, .abstraction _, same => by
        simp [encodeConstProvenance, constUndefinedLabel, constDefinedLabel, constAbstractionLabel,
          constRepresentationLabel] at same
  termination_by first => sizeOf first

  theorem encodeSourceTerm_injective : ∀ (first second : SourceTerm),
      encodeSourceTerm first = encodeSourceTerm second → first = second
    | .const firstConst firstType, .const secondConst secondType, same => by
        simp only [encodeSourceTerm, LabeledTree.node.injEq, List.cons.injEq, and_true, true_and] at same
        rw [encodeConst_injective firstConst secondConst same.1, encodeTy_injective firstType secondType same.2]
    | .var firstName firstType, .var secondName secondType, same => by
        simp only [encodeSourceTerm, LabeledTree.node.injEq, List.cons.injEq, and_true, true_and] at same
        rw [encodeName_injective same.1, encodeTy_injective firstType secondType same.2]
    | .app firstFunction firstArgument, .app secondFunction secondArgument, same => by
        simp only [encodeSourceTerm, LabeledTree.node.injEq, List.cons.injEq, and_true, true_and] at same
        rw [encodeSourceTerm_injective firstFunction secondFunction same.1,
          encodeSourceTerm_injective firstArgument secondArgument same.2]
    | .abs firstName firstType firstBody, .abs secondName secondType secondBody, same => by
        simp only [encodeSourceTerm, LabeledTree.node.injEq, List.cons.injEq, and_true, true_and] at same
        rw [encodeName_injective same.1, encodeTy_injective firstType secondType same.2.1,
          encodeSourceTerm_injective firstBody secondBody same.2.2]
    | .const _ _, .var _ _, same | .const _ _, .app _ _, same | .const _ _, .abs _ _ _, same
    | .var _ _, .const _ _, same | .var _ _, .app _ _, same | .var _ _, .abs _ _ _, same
    | .app _ _, .const _ _, same | .app _ _, .var _ _, same | .app _ _, .abs _ _ _, same
    | .abs _ _ _, .const _ _, same | .abs _ _ _, .var _ _, same | .abs _ _ _, .app _ _, same => by
        simp [encodeSourceTerm, sourceConstLabel, sourceVarLabel, sourceAppLabel, sourceAbsLabel] at same
  termination_by first => sizeOf first
end

/-! ## De Bruijn terms -/

def encodeTerm : DBTerm → LabeledTree
  | .const constant type => .node termConstLabel [encodeConst constant, encodeTy type]
  | .free sourceVar => .node termFreeLabel [encodeName sourceVar.name, encodeTy sourceVar.ty]
  | .bound index => .node termBoundLabel [encodeUnary index]
  | .app function argument => .node termAppLabel [encodeTerm function, encodeTerm argument]
  | .abs type body => .node termAbsLabel [encodeTy type, encodeTerm body]

theorem encodeTerm_injective : Function.Injective encodeTerm := by
  intro first
  induction first with
  | const constant type =>
      intro second same
      cases second <;> simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel,
        termAbsLabel] at same
      rw [encodeConst_injective _ _ same.1, encodeTy_injective _ _ same.2]
  | free sourceVar =>
      intro second same
      cases second <;> simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel,
        termAbsLabel] at same
      rename_i other
      have names := encodeName_injective same.1
      have types := encodeTy_injective _ _ same.2
      cases sourceVar
      cases other
      simp only at names types
      rw [names, types]
  | bound index =>
      intro second same
      cases second <;> simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel,
        termAbsLabel] at same
      rw [encodeUnary_injective same]
  | app function argument functionIh argumentIh =>
      intro second same
      cases second <;> simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel,
        termAbsLabel] at same
      rw [functionIh same.1, argumentIh same.2]
  | abs type body bodyIh =>
      intro second same
      cases second <;> simp [encodeTerm, termConstLabel, termFreeLabel, termBoundLabel, termAppLabel,
        termAbsLabel] at same
      rw [encodeTy_injective _ _ same.1, bodyIh same.2]

/-! ## Canonical terms and hypothesis sets -/

/-- A canonical term is determined by its de Bruijn term. -/
def encodeCanonical (term : CanonicalTerm) : LabeledTree := encodeTerm term.term

theorem encodeCanonical_injective : Function.Injective encodeCanonical := fun _ _ same =>
  CanonicalTerm.ext_term (encodeTerm_injective same)

/-- Canonical terms ordered by their encodings. -/
def CanonicalLe (first second : CanonicalTerm) : Prop := encodeCanonical first ≤ encodeCanonical second

instance : DecidableRel CanonicalLe := fun first second =>
  inferInstanceAs (Decidable (encodeCanonical first ≤ encodeCanonical second))

instance : IsTrans CanonicalTerm CanonicalLe := ⟨fun _ _ _ => le_trans⟩
instance : Std.Total CanonicalLe := ⟨fun _ _ => le_total _ _⟩
instance : Std.Antisymm CanonicalLe :=
  ⟨fun _ _ first second => encodeCanonical_injective (le_antisymm first second)⟩

/-- A hypothesis set, listed in the order of its encodings. -/
def sortedHypotheses (hypotheses : Finset CanonicalTerm) : List CanonicalTerm :=
  hypotheses.sort CanonicalLe

theorem sortedHypotheses_injective : Function.Injective sortedHypotheses := by
  intro first second same
  rw [← Finset.sort_toFinset first CanonicalLe, ← Finset.sort_toFinset second CanonicalLe]
  exact congrArg List.toFinset same

end Mettapedia.Languages.HOLLight.FirstOrder
