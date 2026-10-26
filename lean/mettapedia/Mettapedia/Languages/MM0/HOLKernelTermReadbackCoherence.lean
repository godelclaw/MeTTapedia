import Mettapedia.Logic.HOL.Syntax.BindingDepth
import Mettapedia.Languages.MM0.HOLKernelTermReadback
import Mettapedia.Languages.MM0.HOLKernelTermAssignments

/-!
# Contextual round trips for the native HOL syntax reader

Every intrinsic term constructor survives encoding and readback when the
constant dictionary is faithful on its parameter indices and binder names
avoid the source variable positions. Reading commutes with source renaming;
target names unused by the source may be shadowed. The hypotheses concern individual dictionary
entries and names; no model or source derivation is supplied.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelTermReadback
open Mettapedia.Logic.HOL Kernel HOLKernelSyntax
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u}

theorem readType_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) (type : Ty Unit) :
    readType references (encodeType references (fun _ : Unit => Preterm.var 0) type) = some type := by
  induction type with
  | prop => simp [encodeType, applySymbol, readType, readHead_reference references faithful]
  | base name => cases name; rfl
  | arr domain codomain ihDomain ihCodomain =>
      simp [encodeType, applySymbol, Preterm.applyArgs, readType,
        readHead_reference references faithful, ihDomain, ihCodomain]


def InScope {gamma : Ctx Unit} (parameters : Nat) (names : Names gamma) (depth : Nat) : Prop :=
  names.toList.Nodup ∧ ∀ name ∈ names.toList, parameters ≤ name ∧ name < parameters + depth

theorem InScope.fresh {gamma : Ctx Unit} {parameters depth : Nat} {names : Names gamma}
    (scope : InScope parameters names depth) : names.lookup? (parameters + depth) = none := by
  apply BinderNames.lookup?_none_of_not_mem
  intro member
  exact (Nat.lt_irrefl _) (scope.2 _ member).2

theorem InScope.extend {gamma : Ctx Unit} {parameters depth : Nat} {names : Names gamma}
    (scope : InScope parameters names depth) (type : Ty Unit) :
    InScope parameters (BinderNames.cons (type := type) (parameters + depth) names) (depth + 1) := by
  refine ⟨List.nodup_cons.mpr ⟨?_, scope.1⟩, ?_⟩
  · intro member
    exact (Nat.lt_irrefl _) (scope.2 _ member).2
  · intro name member
    simp only [BinderNames.toList, List.mem_cons] at member
    rcases member with rfl | member
    · omega
    · have bounds := scope.2 name member
      omega

theorem InScope.constant_absent {gamma : Ctx Unit} {parameters depth : Nat} {names : Names gamma}
    (scope : InScope parameters names depth) (index : Nat) (bounded : index < parameters) :
    names.lookup? index = none := by
  apply BinderNames.lookup?_none_of_not_mem
  intro member
  have lower := (scope.2 _ member).1
  omega

theorem positions_cons {gamma : Ctx Unit} {type : Ty Unit} (name : Nat) (names : Names gamma) :
    (Positions.extend (domain := type) name names.nameOf : Positions (type :: gamma)) =
      (fun {_} index => (BinderNames.cons (type := type) name names).nameOf index) := by
  funext type index
  cases index <;> rfl

/-- Exact readback under a source renaming into an arbitrary target frame.
Only the source positions must avoid the used binder window. A target name
unused by the source may be shadowed without changing the reading. -/
theorem readTermWith_encode_renamed
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma))
    (references : HOLKernelSyntax.Symbol → Nat) (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    (binders : Nat → Nat) (injective : Function.Injective binders) (above : ∀ level, parameters ≤ binders level)
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type) :
    ∀ {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta) (positions : Positions gamma) (depth : Nat),
      (∀ {type} (index : Var gamma type), names.lookup? (positions index) = some ⟨type, rho index⟩) →
      (∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none) →
      (∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (depth + offset) ≠ positions index) →
      readTermWith extras references constants parameters names
        (encodeTerm references (fun _ : Unit => .var 0) (fun {_} symbol => .var (indices symbol)) binders positions depth source) =
        some ⟨type, rename rho source⟩ := by
  induction source with
  | var index =>
      intro delta rho names positions depth variablesRead constantsAbsent fresh
      simp [encodeTerm, readTermWith, readVariable, variablesRead, rename]
  | const symbol =>
      intro delta rho names positions depth variablesRead constantsAbsent fresh
      simp [encodeTerm, readTermWith, readVariable, constantsAbsent, lookup, rename]
  | top | bot =>
      intros
      simp [encodeTerm, applySymbol, readTermWith, readHead_reference references faithful, rename]
  | app first second ihFirst ihSecond | and first second ihFirst ihSecond
  | or first second ihFirst ihSecond | imp first second ihFirst ihSecond =>
      intro delta rho names positions depth variablesRead constantsAbsent fresh
      have left := ihFirst rho names positions depth variablesRead constantsAbsent
        (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)))
      have right := ihSecond rho names positions depth variablesRead constantsAbsent
        (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)))
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith,
        readHead_reference references faithful, left, right, application, logicalBinary, expect_same, rename]
  | not body ih =>
      intro delta rho names positions depth variablesRead constantsAbsent fresh
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith, readHead_reference references faithful,
        ih rho names positions depth variablesRead constantsAbsent fresh, expect_same, rename]
  | eq first second ihFirst ihSecond =>
      intro delta rho names positions depth variablesRead constantsAbsent fresh
      have left := ihFirst rho names positions depth variablesRead constantsAbsent
        (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)))
      have right := ihSecond rho names positions depth variablesRead constantsAbsent
        (fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)))
      simp only [encodeTerm, applySymbol, Preterm.applyArgs, rename]
      unfold readTermWith
      simp [readHead_reference references faithful, readType_encode references faithful, left, right, expect_same]
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro delta rho names positions depth variablesRead constantsAbsent fresh
      let nextNames : Names (domain :: delta) := BinderNames.cons (binders depth) names
      let nextPositions : Positions (domain :: gamma) := Positions.extend (binders depth) positions
      have nextRead : ∀ {type} (index : Var (domain :: gamma) type),
          nextNames.lookup? (nextPositions index) = some ⟨type, Rename.lift rho index⟩ := by
        intro type index
        cases index with
        | vz => simp [nextNames, nextPositions, Positions.extend, Rename.lift]
        | vs index =>
            have apart : binders depth ≠ positions index := by
              simpa only [Nat.add_zero] using fresh 0 (Nat.zero_lt_succ _) index
            simp [nextNames, nextPositions, Positions.extend, BinderNames.lookup?_cons_of_ne apart, variablesRead, Rename.lift]
      have nextConstants : ∀ {type} (symbol : Const type), nextNames.lookup? (indices symbol) = none := by
        intro type symbol
        have apart : binders depth ≠ indices symbol := by have lo := above depth; have hi := bounded symbol; omega
        simp [nextNames, BinderNames.lookup?_cons_of_ne apart, constantsAbsent]
      have nextFresh : ∀ offset < body.binderDepth, ∀ {type} (index : Var (domain :: gamma) type),
          binders (depth + 1 + offset) ≠ nextPositions index := by
        intro offset less type index
        cases index with
        | vz =>
            intro same
            have impossible := injective same
            change depth + 1 + offset = depth at impossible
            omega
        | vs index =>
            have apart := fresh (offset + 1) (Nat.add_lt_add_right less 1) index
            simpa only [nextPositions, Positions.extend, Nat.add_assoc, Nat.add_comm 1 offset] using apart
      have bodyRead := ih (Rename.lift rho) nextNames nextPositions (depth + 1) nextRead nextConstants nextFresh
      have lower : ¬ binders depth < parameters := Nat.not_lt.mpr (above depth)
      simp [encodeTerm, applySymbol, Preterm.applyArgs, readTermWith, readHead_reference references faithful,
        readType_encode references faithful, lower, nextNames, nextPositions, bodyRead, expect_same, rename]

/-- Literal native substitution images retain their source meanings in any
reader frame with the specified variable lookup. Image binders may shadow
target-frame variables outside the source image of the renaming. -/
theorem readTermWith_encodeSubstitution
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma))
    (references : HOLKernelSyntax.Symbol → Nat) (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    (binders : Nat → Nat) (injective : Function.Injective binders)
    (above : ∀ level, parameters ≤ binders level)
    {gamma delta target : Ctx Unit} (substitution : Subst Const gamma delta)
    (rho : Rename Unit delta target) (names : Names target) (positions : Positions delta) (depth : Nat)
    (variablesRead : ∀ {type} (index : Var delta type), names.lookup? (positions index) = some ⟨type, rho index⟩)
    (constantsAbsent : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none)
    (fresh : ∀ offset < Subst.maxBinderDepth substitution, ∀ {type} (index : Var delta type),
      binders (depth + offset) ≠ positions index)
    {type : Ty Unit} (index : Var gamma type) :
    readTermWith extras references constants parameters names
      (HOLKernelTermAssignments.encodeSubstitution references (fun _ : Unit => .var 0)
        (fun {_} symbol => .var (indices symbol)) binders (fun index => .var (positions index)) depth
        substitution index) = some ⟨type, rename rho (substitution index)⟩ := by
  unfold HOLKernelTermAssignments.encodeSubstitution
  rw [HOLKernelTermAssignments.encode_positions]
  exact readTermWith_encode_renamed extras references faithful constants indices parameters lookup bounded
    binders injective above (substitution index) rho names positions depth variablesRead constantsAbsent
    (fun offset less => fresh offset
      (Nat.lt_of_lt_of_le less (Subst.binderDepth_le_maxBinderDepth substitution index)))

/-- Adding an outer binder weakens each literal substitution image. The new
name must avoid the source positions and constant prefix, but may coincide
with an image's internal binder: that occurrence shadows only the new name. -/
theorem readTermWith_encodeSubstitution_weaken
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma))
    (references : HOLKernelSyntax.Symbol → Nat) (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    (binders : Nat → Nat) (injective : Function.Injective binders)
    (above : ∀ level, parameters ≤ binders level)
    {gamma delta target : Ctx Unit} (substitution : Subst Const gamma delta)
    (rho : Rename Unit delta target) (names : Names target) (positions : Positions delta) (depth : Nat)
    (variablesRead : ∀ {type} (index : Var delta type), names.lookup? (positions index) = some ⟨type, rho index⟩)
    (constantsAbsent : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none)
    (fresh : ∀ offset < Subst.maxBinderDepth substitution, ∀ {type} (index : Var delta type),
      binders (depth + offset) ≠ positions index)
    (domain : Ty Unit) (name : Nat) (nameAbove : parameters ≤ name)
    (nameFresh : ∀ {type} (index : Var delta type), name ≠ positions index)
    {type : Ty Unit} (index : Var gamma type) :
    readTermWith extras references constants parameters (BinderNames.cons (type := domain) name names)
      (HOLKernelTermAssignments.encodeSubstitution references (fun _ : Unit => .var 0)
        (fun {_} symbol => .var (indices symbol)) binders (fun index => .var (positions index)) depth
        substitution index) = some ⟨type, weaken (rename rho (substitution index))⟩ := by
  have result := readTermWith_encodeSubstitution extras references faithful constants indices parameters
    lookup bounded binders injective above substitution (fun index => Var.vs (σ := domain) (rho index))
    (BinderNames.cons name names) positions depth
    (by
      intro type index
      simp only [BinderNames.lookup?_cons_of_ne (nameFresh index), variablesRead, Option.map_some])
    (by
      intro type symbol
      have apart : name ≠ indices symbol := by have upper := bounded symbol; omega
      simp only [BinderNames.lookup?_cons_of_ne apart, constantsAbsent, Option.map_none])
    fresh index
  simpa only [weaken, rename_comp, Rename.weaken] using result

/-- Any injective binder allocation avoiding the finite free-name context
on the source term's used window has exact readback. Free names may lie above
that window; constants retain the separate parameter prefix. -/
theorem readTermWith_encode_fresh
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma))
    (references : HOLKernelSyntax.Symbol → Nat) (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    (binders : Nat → Nat) (injective : Function.Injective binders)
    (above : ∀ level, parameters ≤ binders level)
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type) :
    ∀ (names : Names gamma) (depth : Nat), names.toList.Nodup →
      (∀ name ∈ names.toList, parameters ≤ name) →
      (∀ offset < source.binderDepth, binders (depth + offset) ∉ names.toList) →
      readTermWith extras references constants parameters names
        (encodeTerm references (fun _ : Unit => .var 0) (fun {_} symbol => .var (indices symbol))
          binders names.nameOf depth source) = some ⟨type, source⟩ := by
  intro names depth nodup namesAbove fresh
  have constantsAbsent : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none := by
    intro type symbol
    apply BinderNames.lookup?_none_of_not_mem
    intro member
    have lower := namesAbove _ member
    have upper := bounded symbol
    omega
  have result := readTermWith_encode_renamed extras references faithful constants indices parameters
    lookup bounded binders injective above source Rename.id names names.nameOf depth
    (fun index => BinderNames.lookup?_nameOf names nodup index) constantsAbsent
    (by
      intro offset less type index same
      apply fresh offset less
      rw [same]
      exact BinderNames.nameOf_mem names index)
  simpa only [rename_id] using result

/-- Read every constructor of an intrinsically typed source term. -/
theorem readTermWith_encode
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma))
    (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    {gamma : Ctx Unit} {type : Ty Unit}
    (source : Term Const gamma type) :
    ∀ (names : Names gamma) (depth : Nat), InScope parameters names depth →
      readTermWith extras references constants parameters names
        (encodeTerm references (fun _ : Unit => Preterm.var 0) (fun {_} symbol => Preterm.var (indices symbol))
          (fun value => parameters + value) names.nameOf depth source) = some ⟨type, source⟩ := by
  intro names depth scope
  apply readTermWith_encode_fresh extras references faithful constants indices parameters lookup bounded
    (fun level => parameters + level) (by intro first second same; exact Nat.add_left_cancel same) (by intro level; omega)
    source names depth scope.1 (fun name member => (scope.2 name member).1)
  intro offset _ member
  have upper := (scope.2 _ member).2
  omega


/-- The primitive-only reader is the empty auxiliary-dictionary instance. -/
theorem readTerm_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type)
    (names : Names gamma) (depth : Nat) (scope : InScope parameters names depth) :
    readTerm references constants parameters names
      (encodeTerm references (fun _ : Unit => Preterm.var 0) (fun {_} symbol => Preterm.var (indices symbol))
        (fun value => parameters + value) names.nameOf depth source) = some ⟨type, source⟩ :=
  readTermWith_encode (fun {_} _ => none) references faithful constants indices parameters
    lookup bounded source names depth scope

#print axioms readTermWith_encode_renamed
#print axioms readTermWith_encodeSubstitution
#print axioms readTermWith_encodeSubstitution_weaken
#print axioms readTermWith_encode_fresh
#print axioms readType_encode
#print axioms readTerm_encode
end Mettapedia.Languages.MM0.HOLKernelTermReadback
