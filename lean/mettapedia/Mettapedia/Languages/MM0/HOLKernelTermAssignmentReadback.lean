import Mettapedia.Languages.MM0.HOLKernelReadbackRenaming

/-!
# Simultaneous-substitution readback of native HOL term assignments

Every one of the thirteen intrinsic term constructors preserves pointwise
readings of native compound assignments. A source binder extends the reader
frame and lifts the interpreted substitution. Its fresh variable must not
shadow an existing variable or constant; internal binders of the assigned
terms need no separate name bound.

Literal insertion of encoded substitution images and encoding the intrinsic
substitution therefore have the same exact source reading. Their raw native
preterms can still differ. These are syntax interpretation laws; admission
of the recursively generated equality receipts is a separate theorem.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelTermReadback
open Mettapedia.Logic.HOL Kernel HOLKernelSyntax HOLKernelTermAssignments
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u}

/-- Pointwise readings of native variable images extend through every term constructor as intrinsic simultaneous substitution. -/
theorem readTermWith_encodeWithAssignment
    (extras : {context : Ctx Unit} → Preterm → Option (Decoded Const context))
    (extrasNatural : ∀ {first second : Ctx Unit} (rho : Rename Unit first second) (native : Preterm),
      extras (context := second) native = (extras (context := first) native).map (Decoded.rename rho))
    (references : HOLKernelSyntax.Symbol → Nat) (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    (binders : Nat → Nat) (injective : Function.Injective binders) (above : ∀ level, parameters ≤ binders level)
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type) :
    ∀ {delta : Ctx Unit} (substitution : Subst Const gamma delta) (assignment : Assignment gamma)
      (names : Names delta) (depth : Nat),
      (∀ {type} (index : Var gamma type),
        readTermWith extras references constants parameters names (assignment index) = some ⟨type, substitution index⟩) →
      (∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none) →
      (∀ offset < source.binderDepth, names.lookup? (binders (depth + offset)) = none) →
      (∀ offset < source.binderDepth, constants (binders (depth + offset)) = none) →
      readTermWith extras references constants parameters names
        (encodeWithAssignment references (fun _ : Unit => .var 0) (fun {_} symbol => .var (indices symbol))
          binders assignment depth source) = some ⟨type, subst substitution source⟩ := by
  induction source with
  | var index =>
      intro delta substitution assignment names depth images constantsAbsent fresh dictionaryFresh
      exact images index
  | const symbol =>
      intro delta substitution assignment names depth images constantsAbsent fresh dictionaryFresh
      simp [encodeWithAssignment, readTermWith, readVariable, constantsAbsent, lookup, subst]
  | top | bot =>
      intros
      simp [encodeWithAssignment, applySymbol, readTermWith, readHead_reference references faithful, subst]
  | app first second ihFirst ihSecond | and first second ihFirst ihSecond
  | or first second ihFirst ihSecond | imp first second ihFirst ihSecond =>
      intro delta substitution assignment names depth images constantsAbsent fresh dictionaryFresh
      have left := ihFirst substitution assignment names depth images constantsAbsent
        (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)))
        (fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)))
      have right := ihSecond substitution assignment names depth images constantsAbsent
        (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)))
        (fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)))
      simp [encodeWithAssignment, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, left, right, application, logicalBinary, expect_same, subst]
  | not body ih =>
      intro delta substitution assignment names depth images constantsAbsent fresh dictionaryFresh
      simp [encodeWithAssignment, applySymbol, Preterm.applyArgs, readTermWith, readHead_reference references faithful,
        ih substitution assignment names depth images constantsAbsent fresh dictionaryFresh, expect_same, subst]
  | eq first second ihFirst ihSecond =>
      intro delta substitution assignment names depth images constantsAbsent fresh dictionaryFresh
      have left := ihFirst substitution assignment names depth images constantsAbsent
        (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)))
        (fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)))
      have right := ihSecond substitution assignment names depth images constantsAbsent
        (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)))
        (fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)))
      simp only [encodeWithAssignment, applySymbol, Preterm.applyArgs, subst]
      unfold readTermWith
      simp [readHead_reference references faithful, readType_encode references faithful, left, right, expect_same]
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro delta substitution assignment names depth images constantsAbsent fresh dictionaryFresh
      let next : Names (domain :: delta) := BinderNames.cons (binders depth) names
      have headFresh : names.lookup? (binders depth) = none := by
        simpa only [Nat.add_zero] using fresh 0 (Nat.zero_lt_succ _)
      have headDictionary : constants (binders depth) = none := by
        simpa only [Nat.add_zero] using dictionaryFresh 0 (Nat.zero_lt_succ _)
      have nextImages : ∀ {type} (index : Var (domain :: gamma) type),
          readTermWith extras references constants parameters next
            (Assignment.extend (.var (binders depth)) assignment index) =
              some ⟨type, Subst.lift substitution index⟩ := by
        intro type index
        cases index with
        | vz => simp [Assignment.extend, Subst.lift, readTermWith, readVariable, next]
        | vs index =>
            exact readTermWith_weaken_of_read extras extrasNatural references constants parameters names
              (assignment index) domain (binders depth) headFresh headDictionary (substitution index) (images index)
      have nextConstants : ∀ {type} (symbol : Const type), next.lookup? (indices symbol) = none := by
        intro type symbol
        have apart : binders depth ≠ indices symbol := by have lo := above depth; have hi := bounded symbol; omega
        simp [next, BinderNames.lookup?_cons_of_ne apart, constantsAbsent]
      have nextFresh : ∀ offset < body.binderDepth, next.lookup? (binders (depth + 1 + offset)) = none := by
        intro offset less
        have apart : binders depth ≠ binders (depth + 1 + offset) := by
          intro same
          have impossible := injective same
          omega
        have absent := fresh (offset + 1) (Nat.add_lt_add_right less 1)
        simp only [next, BinderNames.lookup?_cons_of_ne apart]
        simp only [Nat.add_assoc, Nat.add_comm 1 offset, absent, Option.map_none]
      have nextDictionary : ∀ offset < body.binderDepth, constants (binders (depth + 1 + offset)) = none := by
        intro offset less
        have absent := dictionaryFresh (offset + 1) (Nat.add_lt_add_right less 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent
      have bodyRead := ih (Subst.lift substitution) (Assignment.extend (.var (binders depth)) assignment)
        next (depth + 1) nextImages nextConstants nextFresh nextDictionary
      have lower : ¬ binders depth < parameters := Nat.not_lt.mpr (above depth)
      simp [encodeWithAssignment, applySymbol, Preterm.applyArgs, readTermWith, readHead_reference references faithful,
        readType_encode references faithful, lower, next, bodyRead, expect_same, subst]

#print axioms readTermWith_encodeWithAssignment

/-- The actual literal-insertion and source-substitution encodings have the same reading, under the producer's joint finite binder budget. -/
theorem readTermWith_substitution_encodings
    (extras : {context : Ctx Unit} → Preterm → Option (Decoded Const context))
    (extrasNatural : ∀ {first second : Ctx Unit} (rho : Rename Unit first second) (native : Preterm),
      extras (context := second) native = (extras (context := first) native).map (Decoded.rename rho))
    (references : HOLKernelSyntax.Symbol → Nat) (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    (binders : Nat → Nat) (injective : Function.Injective binders) (above : ∀ level, parameters ≤ binders level)
    {gamma delta target : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type)
    (substitution : Subst Const gamma delta) (meaning : Subst Const delta target)
    (assignment : Assignment delta) (names : Names target) (depth : Nat)
    (images : ∀ {type} (index : Var delta type),
      readTermWith extras references constants parameters names (assignment index) = some ⟨type, meaning index⟩)
    (constantsAbsent : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none)
    (fresh : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
      names.lookup? (binders (depth + offset)) = none)
    (dictionaryFresh : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
      constants (binders (depth + offset)) = none) :
    readTermWith extras references constants parameters names
      (encodeWithAssignment references (fun _ : Unit => .var 0) (fun {_} symbol => .var (indices symbol)) binders
        (encodeSubstitution references (fun _ : Unit => .var 0) (fun {_} symbol => .var (indices symbol))
          binders assignment depth substitution) depth source) =
        some ⟨type, subst meaning (subst substitution source)⟩ ∧
    readTermWith extras references constants parameters names
      (encodeWithAssignment references (fun _ : Unit => .var 0) (fun {_} symbol => .var (indices symbol))
        binders assignment depth (subst substitution source)) =
        some ⟨type, subst meaning (subst substitution source)⟩ := by
  have imageReads : ∀ {type} (index : Var gamma type),
      readTermWith extras references constants parameters names
        (encodeSubstitution references (fun _ : Unit => .var 0) (fun {_} symbol => .var (indices symbol))
          binders assignment depth substitution index) = some ⟨type, subst meaning (substitution index)⟩ := by
    intro type index
    apply readTermWith_encodeWithAssignment extras extrasNatural references faithful constants indices parameters
      lookup bounded binders injective above (substitution index) meaning assignment names depth images constantsAbsent
    · intro offset less
      exact fresh offset (Nat.lt_of_lt_of_le less (Nat.le_trans
        (Subst.binderDepth_le_maxBinderDepth substitution index) (Nat.le_add_left _ _)))
    · intro offset less
      exact dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_trans
        (Subst.binderDepth_le_maxBinderDepth substitution index) (Nat.le_add_left _ _)))
  constructor
  · have result := readTermWith_encodeWithAssignment extras extrasNatural references faithful constants indices parameters
      lookup bounded binders injective above source (fun index => subst meaning (substitution index))
      (encodeSubstitution references (fun _ : Unit => .var 0) (fun {_} symbol => .var (indices symbol))
        binders assignment depth substitution) names depth imageReads constantsAbsent
      (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_add_right _ _)))
      (fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_add_right _ _)))
    have composition : subst meaning (subst substitution source) =
        subst (fun index => subst meaning (substitution index)) source := by
      rw [Mettapedia.Logic.HOL.subst_comp]
      exact subst_ext (fun _ => rfl) source
    rw [composition]
    exact result
  · exact readTermWith_encodeWithAssignment extras extrasNatural references faithful constants indices parameters
      lookup bounded binders injective above (subst substitution source) meaning assignment names depth images constantsAbsent
      (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Term.binderDepth_subst_le source substitution)))
      (fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Term.binderDepth_subst_le source substitution)))

#print axioms readTermWith_substitution_encodings
end Mettapedia.Languages.MM0.HOLKernelTermReadback
