import Mettapedia.GSLT.Dedukti.LeanMinusLevelNormalization

/-!
# Theorems 2 and 3 for levels in one variable, in the theory with explicit substitution

By `conv_code_iff_normalSet`, two level codes are convertible in
`leanTheoryExplicit` exactly when the sets `normalSet` computed by the rules
are equal.  For the levels whose only variable is `α` (numbered `0`), these
sets are **shapes**: at most one constant `C ∅ c` (`c ≥ 1`), one constant
guarded by `α`, `C {α} d`, and one `V {α} α k`, in this order, with Géran's
incomparability: `c < d` and `k + 1 < d` when `C {α} d` is present
(`Shape.Valid`).  Each corrected rule inserts a sublevel into a shape as the
shape of the pointwise maximum (`addSub_toSet`), so every level in one
variable has a shape whose value is the value of the level
(`normalSet_shape`), and a valid shape is determined by its values
(`Shape.eq_of_value`).  Hence:

* **Theorem 3, one variable** (`theorem3_one_variable`): equivalent levels in
  one variable have convertible codes, also read in any frame
  (`theorem3_one_variable_in`).
* **Theorem 2, one variable** (`theorem2_one_variable`): two levels in one
  variable have convertible codes exactly when they are equivalent.
* **Inside a declaration** the frame variable `x` is inert: `sub x |l₁|` and
  `sub x |l₂|` are convertible exactly when `|l₁|` and `|l₂|` are
  (`conv_subVar_iff`), so Theorem 2 holds there too
  (`theorem2_one_variable_in`).

The paper's own rules fail both directions already here (`LeanMinusLevels`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF

/-! ## Shapes -/

/-- A set of sublevels of one variable: `free` is `C ∅ free` (absent when
`0`), `guarded` is `C {α} guarded` (absent when `0`), `offset` is
`V {α} α offset`. -/
structure Shape where
  free : Nat
  guarded : Nat
  offset : Option Nat
  deriving DecidableEq, Repr

namespace Shape

/-- The sorted set of sublevels of a shape. -/
def toSet (shape : Shape) : List Sublevel :=
  (if shape.free = 0 then [] else [.cst [] shape.free]) ++
    (if shape.guarded = 0 then [] else [.cst [0] shape.guarded]) ++
    (match shape.offset with
      | none => []
      | some offset => [.var [0] 0 offset])

/-- Géran's incomparability: the guarded constant, when present, is above the
free constant and above `α + offset` at `α = 1`. -/
def Valid (shape : Shape) : Prop :=
  shape.guarded = 0 ∨
    (shape.free < shape.guarded ∧ ∀ offset, shape.offset = some offset → offset + 1 < shape.guarded)

/-- The value of the offset part at `α = value`. -/
def offsetValue (shape : Shape) (value : Nat) : Nat :=
  match shape.offset with
  | none => 0
  | some offset => value + offset

/-- The value of a shape when `α` has the value `value`. -/
def value (shape : Shape) (value : Nat) : Nat :=
  max shape.free (if value = 0 then 0 else max shape.guarded (shape.offsetValue value))

/-- The pointwise maximum of two shapes, made valid. -/
def join (first second : Shape) : Shape :=
  let free := max first.free second.free
  let offset : Option Nat :=
    match first.offset, second.offset with
    | none, other => other
    | other, none => other
    | some offset, some offset' => some (max offset offset')
  let guarded := max first.guarded second.guarded
  { free := free
    offset := offset
    guarded :=
      match offset with
      | none => if free < guarded then guarded else 0
      | some offset => if free < guarded ∧ offset + 1 < guarded then guarded else 0 }

end Shape

/-! ## Values -/

/-- The value of a sublevel when every level variable has the value `value`. -/
def sublevelValue (value : Nat) : Sublevel → Nat
  | .cst guard constant => if guard = [] ∨ value ≠ 0 then constant else 0
  | .var guard _ offset => if guard = [] ∨ value ≠ 0 then value + offset else 0

/-- The value of a set of sublevels: the maximum, `0` for the empty set. -/
def setValue (value : Nat) (set : List Sublevel) : Nat :=
  set.foldr (fun sublevel accumulated => max (sublevelValue value sublevel) accumulated) 0

theorem setValue_nil (value : Nat) : setValue value [] = 0 := rfl

theorem setValue_cons (value : Nat) (head : Sublevel) (rest : List Sublevel) :
    setValue value (head :: rest) = max (sublevelValue value head) (setValue value rest) := rfl

theorem setValue_append (value : Nat) (first second : List Sublevel) :
    setValue value (first ++ second) = max (setValue value first) (setValue value second) := by
  induction first with
  | nil => simp [setValue_nil]
  | cons head rest ih => simp only [List.cons_append, setValue_cons, ih]; omega

namespace Shape

/-- **The value of the set of a shape is the value of the shape.** -/
theorem setValue_toSet (shape : Shape) (value : Nat) :
    setValue value shape.toSet = shape.value value := by
  obtain ⟨free, guarded, offset⟩ := shape
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    by_cases valueZero : value = 0 <;>
    simp [toSet, Shape.value, offsetValue, setValue, sublevelValue, freeZero, guardedZero, valueZero]

/-- **The value of `join` is the maximum of the values.** -/
theorem value_join (first second : Shape) (value : Nat) :
    (join first second).value value = max (first.value value) (second.value value) := by
  obtain ⟨free, guarded, offset⟩ := first
  obtain ⟨free', guarded', offset'⟩ := second
  rcases offset with _ | offset <;> rcases offset' with _ | offset' <;> by_cases valueZero : value = 0 <;>
    simp only [join, Shape.value, offsetValue, valueZero, if_true, if_false] <;> (try split_ifs) <;> omega

theorem join_valid (first second : Shape) : (join first second).Valid := by
  obtain ⟨free, guarded, offset⟩ := first
  obtain ⟨free', guarded', offset'⟩ := second
  unfold Valid join
  rcases offset with _ | offset <;> rcases offset' with _ | offset' <;> simp only <;> (try split_ifs) <;>
    simp_all

/-- **A valid shape is determined by its values.** -/
theorem eq_of_value {first second : Shape} (firstValid : first.Valid) (secondValid : second.Valid)
    (same : ∀ value, first.value value = second.value value) : first = second := by
  obtain ⟨free, guarded, offset⟩ := first
  obtain ⟨free', guarded', offset'⟩ := second
  unfold Valid at firstValid secondValid
  have atZero : free = free' := by simpa [Shape.value] using same 0
  subst atZero
  have atOne := same 1
  rcases offset with _ | offset <;> rcases offset' with _ | offset'
  · simp only [Shape.value, offsetValue, one_ne_zero, if_false] at atOne
    simp only [reduceCtorEq, false_implies, implies_true, and_true] at firstValid secondValid
    simp only [Shape.mk.injEq, true_and, and_true]
    omega
  · have atBig := same (free + guarded + guarded' + 2)
    have atBigger := same (free + guarded + guarded' + 3)
    simp only [Shape.value, offsetValue, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
      if_false] at atBig atBigger
    omega
  · have atBig := same (free + guarded + guarded' + 2)
    have atBigger := same (free + guarded + guarded' + 3)
    simp only [Shape.value, offsetValue, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
      if_false] at atBig atBigger
    omega
  · have atBig := same (free + guarded + guarded' + 2)
    simp only [Shape.value, offsetValue, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
      if_false] at atBig
    have sameOffset : offset = offset' := by omega
    subst sameOffset
    simp only [Shape.value, offsetValue, one_ne_zero, if_false] at atOne
    simp only [Option.some.injEq, forall_eq'] at firstValid secondValid
    simp only [Shape.mk.injEq, true_and, and_true]
    omega

end Shape

/-! ## The corrected `Add` inserts into a shape -/

namespace Shape

/-- **Inserting `C ∅ c`.** -/
theorem addSub_free {constant : Nat} (positive : 1 ≤ constant) {shape : Shape} (valid : shape.Valid) :
    addSub (.cst [] constant) shape.toSet = (join ⟨constant, 0, none⟩ shape).toSet := by
  obtain ⟨free, guarded, offset⟩ := shape
  unfold Valid at valid
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    simp only [toSet, join, freeZero, guardedZero, if_true, if_false, List.nil_append, List.append_nil,
      List.cons_append, addSub, leSub, inclNat, insertSorted, cmpSub, cmpList, Nat.max_def,
      decide_eq_true_eq, Bool.true_and, Bool.false_and, Bool.false_eq_true, reduceCtorEq] at valid ⊢ <;>
    (try split_ifs) <;> (try (exfalso; omega)) <;> simp_all

/-- **Inserting `C {α} d`.** -/
theorem addSub_guarded {constant : Nat} (positive : 1 ≤ constant) {shape : Shape} (valid : shape.Valid) :
    addSub (.cst [0] constant) shape.toSet = (join ⟨0, constant, none⟩ shape).toSet := by
  obtain ⟨free, guarded, offset⟩ := shape
  unfold Valid at valid
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    simp only [toSet, join, freeZero, guardedZero, if_true, if_false, List.nil_append, List.append_nil,
      List.cons_append, addSub, leSub, inclNat, insertSorted, cmpSub, cmpList, cmpNat, Nat.max_def,
      decide_eq_true_eq, Bool.true_and, Bool.false_and, Bool.false_eq_true, reduceCtorEq] at valid ⊢ <;>
    (try split_ifs) <;> (try (exfalso; omega)) <;> simp_all [insertSorted, cmpSub, cmpList] <;> omega

/-- **Inserting `V {α} α k`.** -/
theorem addSub_variable (offset' : Nat) {shape : Shape} (valid : shape.Valid) :
    addSub (.var [0] 0 offset') shape.toSet = (join ⟨0, 0, some offset'⟩ shape).toSet := by
  obtain ⟨free, guarded, offset⟩ := shape
  unfold Valid at valid
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    simp only [toSet, join, freeZero, guardedZero, if_true, if_false, List.nil_append, List.append_nil,
      List.cons_append, addSub, leSub, inclNat, insertSorted, cmpSub, cmpList, cmpNat, Nat.max_def,
      Bool.and_eq_true, decide_eq_true_eq, Bool.true_and, Bool.false_and, Bool.false_eq_true, true_and,
      reduceCtorEq] at valid ⊢ <;>
    (try split_ifs) <;> (try (exfalso; omega)) <;> simp_all [insertSorted, cmpSub, cmpList]

end Shape

/-! ## Sublevels of one variable -/

/-- The sublevels of one variable: `C ∅ c` and `C {α} c` with `c ≥ 1`, and
`V {α} α k`. -/
inductive OneVarSub : Sublevel → Prop where
  | free {constant : Nat} : 1 ≤ constant → OneVarSub (.cst [] constant)
  | guarded {constant : Nat} : 1 ≤ constant → OneVarSub (.cst [0] constant)
  | variable_ (offset : Nat) : OneVarSub (.var [0] 0 offset)

/-- The shape of one sublevel. -/
def shapeOf : Sublevel → Shape
  | .cst [] constant => ⟨constant, 0, none⟩
  | .cst _ constant => ⟨0, constant, none⟩
  | .var _ _ offset => ⟨0, 0, some offset⟩

theorem shapeOf_valid {sublevel : Sublevel} (oneVar : OneVarSub sublevel) : (shapeOf sublevel).Valid := by
  cases oneVar with
  | free _ => left; rfl
  | guarded positive => right; exact ⟨by simp [shapeOf]; omega, fun _ absent => by simp [shapeOf] at absent⟩
  | variable_ _ => left; rfl

theorem value_shapeOf {sublevel : Sublevel} (oneVar : OneVarSub sublevel) (value : Nat) :
    (shapeOf sublevel).value value = sublevelValue value sublevel := by
  cases oneVar <;> by_cases valueZero : value = 0 <;>
    simp [shapeOf, Shape.value, Shape.offsetValue, sublevelValue, valueZero]

/-- **The corrected `Add` inserts a sublevel of one variable into a shape.** -/
theorem addSub_toSet {sublevel : Sublevel} (oneVar : OneVarSub sublevel) {shape : Shape}
    (valid : shape.Valid) : addSub sublevel shape.toSet = (Shape.join (shapeOf sublevel) shape).toSet := by
  cases oneVar with
  | free positive => exact Shape.addSub_free positive valid
  | guarded positive => exact Shape.addSub_guarded positive valid
  | variable_ offset => exact Shape.addSub_variable offset valid

theorem toSet_oneVar {shape : Shape} : ∀ sublevel ∈ shape.toSet, OneVarSub sublevel := by
  obtain ⟨free, guarded, offset⟩ := shape
  intro sublevel member
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    simp [Shape.toSet, freeZero, guardedZero] at member <;>
    (try rcases member with rfl | rfl | rfl) <;>
    first
      | exact .free (by omega)
      | exact .guarded (by omega)
      | exact .variable_ _

/-- **Inserting a list of sublevels of one variable into a shape.** -/
theorem foldAdd_toSet :
    ∀ (list : List Sublevel), (∀ sublevel ∈ list, OneVarSub sublevel) →
      ∀ {shape : Shape}, shape.Valid →
        ∃ result : Shape, result.Valid ∧
          list.foldl (fun accumulated element => addSub element accumulated) shape.toSet = result.toSet ∧
          ∀ value, result.value value = max (setValue value list) (shape.value value)
  | [], _, shape, valid => ⟨shape, valid, rfl, fun value => by simp [setValue_nil]⟩
  | head :: rest, oneVar, shape, valid => by
      have headOneVar := oneVar head (List.mem_cons_self ..)
      obtain ⟨result, resultValid, folded, values⟩ := foldAdd_toSet rest
        (fun sublevel member => oneVar sublevel (List.mem_cons_of_mem _ member))
        (Shape.join_valid (shapeOf head) shape)
      refine ⟨result, resultValid, ?_, fun value => ?_⟩
      · simp only [List.foldl_cons]
        rw [addSub_toSet headOneVar valid]
        exact folded
      · rw [values, Shape.value_join, value_shapeOf headOneVar, setValue_cons]
        omega

/-! ## Increments and guards -/

/-- The shape of the increments of a shape. -/
def Shape.shift (shape : Shape) : Shape :=
  ⟨if shape.free = 0 then 0 else shape.free + 1, if shape.guarded = 0 then 0 else shape.guarded + 1,
    shape.offset.map (· + 1)⟩

theorem Shape.map_incr (shape : Shape) : shape.toSet.map incrSub = shape.shift.toSet := by
  obtain ⟨free, guarded, offset⟩ := shape
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    simp [Shape.toSet, Shape.shift, freeZero, guardedZero, incrSub]

theorem Shape.shift_valid {shape : Shape} (valid : shape.Valid) : shape.shift.Valid := by
  obtain ⟨free, guarded, offset⟩ := shape
  unfold Shape.Valid at valid ⊢
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    simp_all [Shape.shift]

theorem Shape.value_succ (shape : Shape) (value : Nat) :
    max 1 (shape.shift.value value) = shape.value value + 1 := by
  obtain ⟨free, guarded, offset⟩ := shape
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    by_cases valueZero : value = 0 <;>
    simp [Shape.value, Shape.shift, Shape.offsetValue, freeZero, guardedZero, valueZero] <;> omega

theorem unionSorted_guards (first second : List Nat) (firstGuard : first = [] ∨ first = [0])
    (secondGuard : second = [] ∨ second = [0]) :
    unionSorted cmpNat first second = (if first = [] ∧ second = [] then [] else [0]) := by
  rcases firstGuard with rfl | rfl <;> rcases secondGuard with rfl | rfl <;>
    simp [unionSorted, insertSorted, cmpNat]

theorem addguard_oneVar {first second : Sublevel} (firstOneVar : OneVarSub first)
    (secondOneVar : OneVarSub second) : OneVarSub (addguardSub first second) := by
  cases firstOneVar <;> cases secondOneVar <;>
    simp [addguardSub, guardOfSub, unionSorted, insertSorted, cmpNat] <;>
    first
      | exact .free (by omega)
      | exact .guarded (by omega)
      | exact .variable_ _

/-- The value of the guarded copies of a sublevel by the sublevels of a
nonempty shape. -/
theorem setValue_guarded {sublevel : Sublevel} (oneVar : OneVarSub sublevel) {shape : Shape}
    (nonempty : shape.toSet ≠ []) (value : Nat) :
    setValue value (shape.toSet.map (addguardSub sublevel)) =
      if value = 0 ∧ shape.free = 0 then 0 else sublevelValue value sublevel := by
  obtain ⟨free, guarded, offset⟩ := shape
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    by_cases valueZero : value = 0 <;> cases oneVar <;>
    simp_all [Shape.toSet, setValue, sublevelValue, addguardSub, guardOfSub, unionSorted, insertSorted,
      cmpNat]

theorem Shape.value_pos {shape : Shape} (nonempty : shape.toSet ≠ []) {value : Nat} (positive : value ≠ 0) :
    1 ≤ shape.value value := by
  obtain ⟨free, guarded, offset⟩ := shape
  rcases offset with _ | offset <;> by_cases freeZero : free = 0 <;> by_cases guardedZero : guarded = 0 <;>
    simp_all [Shape.toSet, Shape.value, Shape.offsetValue] <;> omega

theorem imaxSet_of_ne_nil (first : List Sublevel) {second : List Sublevel} (nonempty : second ≠ []) :
    imaxSet first second = guardedSet first second second := by
  cases second with
  | nil => exact absurd rfl nonempty
  | cons head rest => rfl

theorem guardedSet_eq_fold (first second accumulated : List Sublevel) :
    guardedSet first second accumulated =
      (first.flatMap fun element => second.map (addguardSub element)).foldl
        (fun accumulated' element => addSub element accumulated') accumulated := by
  induction first generalizing accumulated with
  | nil => rfl
  | cons head rest ih =>
      simp only [guardedSet, List.foldl_cons, List.flatMap_cons, List.foldl_append, List.foldl_map]
      exact ih _

theorem setValue_flatMap (value : Nat) (function : Sublevel → List Sublevel) :
    ∀ list : List Sublevel,
      setValue value (list.flatMap function) =
        list.foldr (fun element accumulated => max (setValue value (function element)) accumulated) 0
  | [] => rfl
  | head :: rest => by
      rw [List.flatMap_cons, setValue_append, setValue_flatMap value function rest]
      rfl

/-! ## The sets of levels in one variable -/

theorem LeanLevel.eval_oneVariable :
    ∀ (level : LeanLevel), level.OneVariable = true →
      ∀ valuation : Nat → Nat, level.eval valuation = level.eval (fun _ => valuation 0)
  | .zero, _, _ => rfl
  | .succ level, oneVar, valuation => by
      simp only [LeanLevel.OneVariable] at oneVar
      simp [LeanLevel.eval, LeanLevel.eval_oneVariable level oneVar valuation]
  | .max first second, oneVar, valuation => by
      simp only [LeanLevel.OneVariable, Bool.and_eq_true] at oneVar
      simp [LeanLevel.eval, LeanLevel.eval_oneVariable first oneVar.1 valuation,
        LeanLevel.eval_oneVariable second oneVar.2 valuation]
  | .imax first second, oneVar, valuation => by
      simp only [LeanLevel.OneVariable, Bool.and_eq_true] at oneVar
      simp [LeanLevel.eval, LeanLevel.eval_oneVariable first oneVar.1 valuation,
        LeanLevel.eval_oneVariable second oneVar.2 valuation]
  | .param index, oneVar, valuation => by
      simp only [LeanLevel.OneVariable, beq_iff_eq] at oneVar
      subst oneVar
      rfl

/-- **Every level in one variable has a valid shape, whose value is the value
of the level.** -/
theorem normalSet_shape :
    ∀ level : LeanLevel, level.OneVariable = true →
      ∃ shape : Shape, shape.Valid ∧ normalSet level = shape.toSet ∧
        ∀ value, shape.value value = level.eval (fun _ => value)
  | .zero, _ => ⟨⟨0, 0, none⟩, Or.inl rfl, rfl, fun value => by
      simp [Shape.value, Shape.offsetValue, LeanLevel.eval]⟩
  | .param index, oneVar => by
      simp only [LeanLevel.OneVariable, beq_iff_eq] at oneVar
      subst oneVar
      refine ⟨⟨0, 0, some 0⟩, Or.inl rfl, rfl, fun value => ?_⟩
      by_cases valueZero : value = 0 <;> simp [Shape.value, Shape.offsetValue, LeanLevel.eval, valueZero]
  | .succ level, oneVar => by
      simp only [LeanLevel.OneVariable] at oneVar
      obtain ⟨shape, valid, same, values⟩ := normalSet_shape level oneVar
      refine ⟨Shape.join ⟨1, 0, none⟩ shape.shift, Shape.join_valid _ _, ?_, fun value => ?_⟩
      · simp only [normalSet, succSet, same, Shape.map_incr]
        exact addSub_toSet (.free (le_refl 1)) (Shape.shift_valid valid)
      · rw [Shape.value_join, show (⟨1, 0, none⟩ : Shape).value value = 1 by
          by_cases valueZero : value = 0 <;> simp [Shape.value, Shape.offsetValue, valueZero],
          Shape.value_succ, values]
        rfl
  | .max first second, oneVar => by
      simp only [LeanLevel.OneVariable, Bool.and_eq_true] at oneVar
      obtain ⟨firstShape, firstValid, firstSame, firstValues⟩ := normalSet_shape first oneVar.1
      obtain ⟨secondShape, secondValid, secondSame, secondValues⟩ := normalSet_shape second oneVar.2
      obtain ⟨result, resultValid, folded, values⟩ :=
        foldAdd_toSet firstShape.toSet (fun sublevel member => toSet_oneVar sublevel member) secondValid
      refine ⟨result, resultValid, ?_, fun value => ?_⟩
      · simp only [normalSet, maxSet, firstSame, secondSame]
        exact folded
      · rw [values, Shape.setValue_toSet, firstValues, secondValues]
        rfl
  | .imax first second, oneVar => by
      simp only [LeanLevel.OneVariable, Bool.and_eq_true] at oneVar
      obtain ⟨firstShape, firstValid, firstSame, firstValues⟩ := normalSet_shape first oneVar.1
      obtain ⟨secondShape, secondValid, secondSame, secondValues⟩ := normalSet_shape second oneVar.2
      by_cases empty : secondShape.toSet = []
      · refine ⟨⟨0, 0, none⟩, Or.inl rfl, ?_, fun value => ?_⟩
        · show imaxSet (normalSet first) (normalSet second) = _
          rw [secondSame, empty]
          rfl
        · have zeroValue : LeanLevel.eval (fun _ => value) second = 0 := by
            rw [← secondValues, ← Shape.setValue_toSet, empty, setValue_nil]
          simp [Shape.value, Shape.offsetValue, LeanLevel.eval, zeroValue]
      · obtain ⟨result, resultValid, folded, values⟩ :=
          foldAdd_toSet (firstShape.toSet.flatMap fun element => secondShape.toSet.map (addguardSub element))
            (fun sublevel member => by
              obtain ⟨element, elementMember, inner⟩ := List.mem_flatMap.mp member
              obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp inner
              exact addguard_oneVar (toSet_oneVar element elementMember) (toSet_oneVar other otherMember))
            secondValid
        refine ⟨result, resultValid, ?_, fun value => ?_⟩
        · show imaxSet (normalSet first) (normalSet second) = _
          rw [firstSame, secondSame, imaxSet_of_ne_nil _ empty, guardedSet_eq_fold]
          exact folded
        · rw [values, setValue_flatMap]
          have guardedValues : ∀ list : List Sublevel, (∀ sublevel ∈ list, OneVarSub sublevel) →
              list.foldr (fun element accumulated =>
                max (setValue value (secondShape.toSet.map (addguardSub element))) accumulated) 0 =
                if value = 0 ∧ secondShape.free = 0 then 0 else setValue value list := by
            intro list oneVars
            induction list with
            | nil => simp [setValue_nil]
            | cons head rest ih =>
                rw [List.foldr_cons, setValue_guarded (oneVars head (List.mem_cons_self ..)) empty,
                  ih (fun sublevel member => oneVars sublevel (List.mem_cons_of_mem _ member)), setValue_cons]
                split_ifs <;> omega
          rw [guardedValues firstShape.toSet (fun sublevel member => toSet_oneVar sublevel member),
            Shape.setValue_toSet]
          show _ = (if LeanLevel.eval (fun _ => value) second = 0 then 0
            else max (LeanLevel.eval (fun _ => value) first) (LeanLevel.eval (fun _ => value) second))
          rw [← firstValues, ← secondValues]
          by_cases valueZero : value = 0
          · have atZero : secondShape.value 0 = secondShape.free := by simp [Shape.value]
            subst valueZero
            rw [atZero]
            split_ifs <;> omega
          · have positive := Shape.value_pos empty valueZero
            split_ifs <;> omega

/-! ## Theorems 2 and 3 for one variable -/

/-- **Theorem 3, for the levels in one variable**: equivalent levels have
convertible codes. -/
theorem theorem3_one_variable {first second : LeanLevel} (firstOne : first.OneVariable = true)
    (secondOne : second.OneVariable = true) (equivalent : LeanLevel.Equiv first second) :
    Conv leanTheoryExplicit (code first) (code second) := by
  obtain ⟨firstShape, firstValid, firstSame, firstValues⟩ := normalSet_shape first firstOne
  obtain ⟨secondShape, secondValid, secondSame, secondValues⟩ := normalSet_shape second secondOne
  have shapes : firstShape = secondShape :=
    Shape.eq_of_value firstValid secondValid fun value => by
      rw [firstValues, secondValues]
      exact equivalent _
  exact conv_code_iff_normalSet.mpr (by rw [firstSame, secondSame, shapes])

/-- **Theorem 3, for the levels in one variable, in a frame.** -/
theorem theorem3_one_variable_in (frame : Term) {first second : LeanLevel}
    (firstOne : first.OneVariable = true) (secondOne : second.OneVariable = true)
    (equivalent : LeanLevel.Equiv first second) :
    Conv leanTheoryExplicit (levelIn frame first) (levelIn frame second) :=
  Conv.app (.refl _) (theorem3_one_variable firstOne secondOne equivalent)

/-- **Theorem 2, for the levels in one variable**: two levels in one variable
have convertible codes exactly when they are equivalent. -/
theorem theorem2_one_variable {first second : LeanLevel} (firstOne : first.OneVariable = true)
    (secondOne : second.OneVariable = true) :
    Conv leanTheoryExplicit (code first) (code second) ↔ LeanLevel.Equiv first second := by
  refine ⟨fun convertible valuation => ?_, theorem3_one_variable firstOne secondOne⟩
  have same := conv_code_iff_normalSet.mp convertible
  obtain ⟨firstShape, _, firstSame, firstValues⟩ := normalSet_shape first firstOne
  obtain ⟨secondShape, _, secondSame, secondValues⟩ := normalSet_shape second secondOne
  rw [LeanLevel.eval_oneVariable first firstOne, LeanLevel.eval_oneVariable second secondOne,
    ← firstValues, ← secondValues, ← Shape.setValue_toSet, ← Shape.setValue_toSet, ← firstSame,
    ← secondSame, same]

/-! ## Inside a declaration the frame variable is inert

Inside a declaration with frame variable `x`, the level `l` is `sub x |l|`.
No rule applies to `sub x` itself (the only rule on `sub` asks for `inst`), so
every reduct of `sub x e` is `sub x e'` with `e ⟶* e'`, and two such levels
are convertible exactly when their codes are. -/

theorem subRule_lhs : subRule.lhs = ap "sub" [ap "inst" [.var 0], .var 1] := by
  decide

/-- Every rule other than the one on `sub` clashes with `sub x e`, and every
rule clashes with `sub x` and with `sub`. -/
theorem explicitRules_clash_sub : ∀ rule ∈ explicitRules,
    (rule = subRule ∨ clashes rule.lhs (ap "sub" [.var 0, .var 1]) = true) ∧
      clashes rule.lhs (ap "sub" [.var 0]) = true ∧ clashes rule.lhs (.con "sub") = true := by
  decide +kernel

/-- `sub x e`, with `x` a variable, has no root contraction. -/
theorem not_rootStep_subVar (index : Nat) (body target : Term) :
    ¬ RootStep leanTheoryExplicit (ap "sub" [.var index, body]) target := by
  intro root
  generalize same : ap "sub" [.var index, body] = source at root
  cases root with
  | beta domain inner argument => simp [ap, apT] at same
  | delta defined => simp [ap, apT] at same
  | @rule declared assignment member =>
      rcases (explicitRules_clash_sub declared member).1 with rfl | clash
      · rw [subRule_lhs] at same
        simp [ap, apT] at same
      · refine ne_inst_of_clashes clash assignment (assign [.var index, body]) ?_
        rw [← same]
        simp [ap, apT, assign]

/-- `sub x`, with `x` a variable, has no step. -/
theorem not_step_subVarHead (index : Nat) (target : Term) :
    ¬ Step leanTheoryExplicit (ap "sub" [.var index]) target := by
  intro step
  rcases Step.app_inv step with root | ⟨function', functionStep, _⟩ | ⟨argument', argumentStep, _⟩
  · generalize same : Term.app (.con "sub") (.var index) = source at root
    cases root with
    | beta domain inner argument => cases same
    | delta defined => cases same
    | @rule declared assignment member =>
        refine ne_inst_of_clashes (explicitRules_clash_sub declared member).2.1 assignment
          (assign [.var index]) ?_
        rw [← same]
        simp [ap, apT, assign]
  · have root := Step.con_inv functionStep
    generalize same : Term.con "sub" = source at root
    cases root with
    | beta domain inner argument => cases same
    | delta defined =>
        cases same
        have undefined : leanTheoryExplicit.body "sub" = none := by decide +kernel
        rw [undefined] at defined
        cases defined
    | @rule declared assignment member =>
        exact ne_inst_of_clashes (explicitRules_clash_sub declared member).2.2 assignment assignment
          (by rw [← same, inst_con])
  · exact var_normal leanTheoryExplicit_headed index _ argumentStep

/-- **Every reduct of `sub x e`, `x` a variable, is `sub x e'` with
`e ⟶* e'`.** -/
theorem reduces_subVar {index : Nat} {body target : Term}
    (reduces : Reduces leanTheoryExplicit (ap "sub" [.var index, body]) target) :
    ∃ body', target = ap "sub" [.var index, body'] ∧ Reduces leanTheoryExplicit body body' := by
  induction reduces with
  | refl => exact ⟨body, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨body', rfl, inner⟩ := ih
      rcases Step.app_inv step with root | ⟨function', functionStep, _⟩ |
          ⟨argument', argumentStep, rfl⟩
      · exact absurd root (not_rootStep_subVar index body' _)
      · exact absurd functionStep (not_step_subVarHead index function')
      · exact ⟨argument', rfl, inner.tail argumentStep⟩

/-- **Inside a declaration, two levels are convertible exactly when their codes
are.** -/
theorem conv_subVar_iff {index : Nat} {first second : Term} :
    Conv leanTheoryExplicit (ap "sub" [.var index, first]) (ap "sub" [.var index, second]) ↔
      Conv leanTheoryExplicit first second := by
  refine ⟨fun convertible => ?_, fun convertible => Conv.app (.refl _) convertible⟩
  obtain ⟨common, left, right⟩ :=
    (Dedukti.conv_iff_joinable leanTheoryExplicit_confluent).mp convertible
  obtain ⟨body, rfl, leftBody⟩ := reduces_subVar left
  obtain ⟨body', same, rightBody⟩ := reduces_subVar right
  have equal : body = body' := by simpa [ap, apT] using same
  subst equal
  exact Joinable.conv ⟨body, leftBody, rightBody⟩

/-- **Theorem 2 inside a declaration, for the levels in one variable**: read in
the frame variable of a declaration, two levels in one variable are
convertible exactly when they are equivalent. -/
theorem theorem2_one_variable_in {index : Nat} {first second : LeanLevel}
    (firstOne : first.OneVariable = true) (secondOne : second.OneVariable = true) :
    Conv leanTheoryExplicit (levelIn (.var index) first) (levelIn (.var index) second) ↔
      LeanLevel.Equiv first second :=
  conv_subVar_iff.trans (theorem2_one_variable firstOne secondOne)

#print axioms Shape.eq_of_value
#print axioms addSub_toSet
#print axioms normalSet_shape
#print axioms theorem3_one_variable
#print axioms theorem3_one_variable_in
#print axioms theorem2_one_variable
#print axioms reduces_subVar
#print axioms conv_subVar_iff
#print axioms theorem2_one_variable_in

end Mettapedia.GSLT.Dedukti.LeanMinus
