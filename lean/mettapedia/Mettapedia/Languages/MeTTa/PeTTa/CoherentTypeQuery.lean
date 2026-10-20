import Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryEnumeration

/-!
# Coherent type enumeration and checking for the v1.0.6 prototype (rules v2)

This is the finite, resolved, ground-declaration fragment of the prototype's
rules; the rule names (S-, C-, K-, Q-) are those of the prototype's design
note. Arrow declarations and annotations are ground occurrences from one
atomspace revision. Authored classifiers and open unification are outside
the model. So is answer multiplicity: the theorems are about answer support.
The executable lists do count as the prototype does on this fragment (a check
is Boolean, so duplicate evidence never repeats an answer, and each type of
the head, each declaration and each annotation contributes one answer); the
controls below show it, but no theorem states it. The term and snapshot
carriers are shared with the mainline model.

* Synthesis (S-rules). The head of an expression is typed like any other
  term, and every type of the head is one reading: an arrow applies (S-App),
  any other type builds a tuple (S-Tuple). A symbol's types are its arrow
  declarations, viewed as terms `(-> A1 ... An B)`, then its annotations, so
  compound heads such as `(make-adder 1)` and symbols with both kinds of
  type need no special case. An expression with no answer has no type.
* Checking (C-rules). One judgment serves S-App and the call guards: `Atom`
  and unknown (`%Undefined%` or `_`) parameters accept every argument, a
  metatype parameter accepts a value of that metatype (`GetMetatype` of the
  mainline model), and otherwise some synthesized type must be consistent.
* Consistency (K-rules): an unknown, at any depth, fits anything. The
  relation is not transitive.

The executable enumeration is proved against the independently stated rules.
Its depth parameter bounds recursion, and the height of the queried term is
always enough.

Outside this fragment: in the prototype, a variable subject's type is a
fresh type variable; here it is `%Undefined%`, which every check treats the
same way (both are consistent with every type), although the two print
differently. Holes and their readback as `%Undefined%` (R-Hole) concern type
variables, which a ground fragment does not have.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CoherentTypeQuery

open MainlineTypeQueryGSLT
open MainlineTypeQueryModes (intrinsic all₂ all₂_iff all₂_congr_on annotations annotations_iff
  height_positive height_le_listHeight)
open MainlineTypeQueryEnumeration (combinations mapped_combinations_iff)

/-! ## Unknown types and consistency (K-rules) -/

/-- The spelling `_` of `%Undefined%` (the mainline model's `holeType`; in the
prototype's rules a hole is instead a type variable standing for an unknown). -/
def wildcardType : Term := .atom "_"

/-- `unknown(T)`: `T` is `%Undefined%` or `_`. -/
def IsUnknown (type : Term) : Prop := type = undefinedType ∨ type = wildcardType

instance (type : Term) : Decidable (IsUnknown type) := by
  unfold IsUnknown
  infer_instance

mutual
  /-- `T ~ A` on ground types: K-Unknown, K-Expr and K-Const. -/
  def Consistent (a b : Term) : Prop :=
    IsUnknown a ∨ IsUnknown b ∨
      match a, b with
      | .list xs, .list ys => ConsistentList xs ys
      | _, _ => a = b

  def ConsistentList : List Term → List Term → Prop
    | [], [] => True
    | a :: xs, b :: ys => Consistent a b ∧ ConsistentList xs ys
    | _, _ => False
end

mutual
  def consistent (a b : Term) : Bool :=
    if IsUnknown a ∨ IsUnknown b then true else
      match a, b with
      | .list xs, .list ys => consistentList xs ys
      | _, _ => decide (a = b)

  def consistentList : List Term → List Term → Bool
    | [], [] => true
    | a :: xs, b :: ys => consistent a b && consistentList xs ys
    | _, _ => false
end

mutual
  theorem consistent_iff (a b : Term) : consistent a b = true ↔ Consistent a b := by
    cases a <;> cases b <;>
      simp [consistent, Consistent, IsUnknown, undefinedType, wildcardType,
        consistentList_iff, or_assoc]

  theorem consistentList_iff (xs ys : List Term) :
      consistentList xs ys = true ↔ ConsistentList xs ys := by
    cases xs <;> cases ys <;>
      simp [consistentList, ConsistentList, consistent_iff, consistentList_iff]
end

mutual
  /-- A type without an unknown at any depth. -/
  def Defined (type : Term) : Prop :=
    ¬ IsUnknown type ∧ match type with
      | .list xs => DefinedList xs
      | _ => True

  def DefinedList : List Term → Prop
    | [] => True
    | x :: xs => Defined x ∧ DefinedList xs
end

mutual
  /-- Without unknowns, consistency is equality. -/
  theorem consistent_defined_iff (a b : Term) (ha : Defined a) (hb : Defined b) :
      Consistent a b ↔ a = b := by
    cases a <;> cases b <;>
      simp_all [Defined, Consistent, IsUnknown, undefinedType, wildcardType,
        consistent_definedList_iff]

  theorem consistent_definedList_iff (xs ys : List Term)
      (hx : DefinedList xs) (hy : DefinedList ys) :
      ConsistentList xs ys ↔ xs = ys := by
    cases xs <;> cases ys <;>
      simp_all [DefinedList, ConsistentList, consistent_defined_iff,
        consistent_definedList_iff]
end

/-! ## Arrow types -/

/-- The arrow `(-> A1 ... An B)`, `n ≥ 0`. -/
def arrowTerm (domains : List Term) (result : Term) : Term :=
  .list (.atom "->" :: (domains ++ [result]))

def IsArrow (type : Term) : Prop := ∃ domains result, type = arrowTerm domains result

/-- A nonempty list as its front and its last element. -/
def splitLast : List Term → Option (List Term × Term)
  | [] => none
  | first :: rest =>
      match splitLast rest with
      | none => some ([], first)
      | some (front, last) => some (first :: front, last)

theorem splitLast_eq_none_iff (items : List Term) : splitLast items = none ↔ items = [] := by
  cases items with
  | nil => simp [splitLast]
  | cons first rest => cases found : splitLast rest <;> simp [splitLast, found]

theorem splitLast_eq_some_iff (items front : List Term) (last : Term) :
    splitLast items = some (front, last) ↔ items = front ++ [last] := by
  induction items generalizing front last with
  | nil => simp [splitLast]
  | cons first rest ih =>
      cases found : splitLast rest with
      | none =>
          obtain rfl := (splitLast_eq_none_iff rest).mp found
          cases front <;> simp [splitLast]
      | some parts =>
          obtain ⟨front', last'⟩ := parts
          obtain rfl := (ih front' last').mp found
          simp only [splitLast, found, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩
            rfl
          · intro same
            obtain ⟨fronts, lasts⟩ :=
              List.append_inj' (show (first :: front') ++ [last'] = front ++ [last] from same) rfl
            exact ⟨fronts, by simpa using lasts⟩

/-- The domains and the result of an arrow; `none` for every other type,
including `(->)` and a list whose first element is not `->`. -/
def arrowParts : Term → Option (List Term × Term)
  | .list (head :: rest) => if head = .atom "->" then splitLast rest else none
  | _ => none

theorem arrowParts_eq_some_iff (type : Term) (domains : List Term) (result : Term) :
    arrowParts type = some (domains, result) ↔ type = arrowTerm domains result := by
  cases type with
  | list elements =>
      cases elements with
      | nil => simp [arrowParts, arrowTerm]
      | cons head rest =>
          by_cases arrow : head = .atom "->"
          · subst arrow
            simp [arrowParts, arrowTerm, splitLast_eq_some_iff]
          · simp [arrowParts, arrowTerm, arrow]
  | _ => simp [arrowParts, arrowTerm]

theorem arrowParts_eq_none_iff (type : Term) : arrowParts type = none ↔ ¬ IsArrow type := by
  constructor
  · rintro missing ⟨domains, result, rfl⟩
    have found := (arrowParts_eq_some_iff (arrowTerm domains result) domains result).mpr rfl
    rw [missing] at found
    cases found
  · intro notArrow
    cases parts : arrowParts type with
    | none => rfl
    | some pair =>
        obtain ⟨domains, result⟩ := pair
        exact absurd ⟨domains, result, (arrowParts_eq_some_iff type domains result).mp parts⟩
          notArrow

theorem arrowTerm_inj {domains other : List Term} {result otherResult : Term}
    (same : arrowTerm domains result = arrowTerm other otherResult) :
    domains = other ∧ result = otherResult := by
  have mine := (arrowParts_eq_some_iff (arrowTerm domains result) domains result).mpr rfl
  have theirs := (arrowParts_eq_some_iff (arrowTerm domains result) other otherResult).mpr same
  rw [mine] at theirs
  simpa using theirs

/-! ## Types of a symbol -/

/-- The term view `(-> A1 ... An B)` of an arrow declaration. -/
def declaredType (declaration : ArrowDeclaration) : Term :=
  arrowTerm declaration.inputTypes declaration.outputType

/-- The declarations of a symbol as terms, then its annotations. -/
def symbolTypes (snapshot : Snapshot) (name : String) : List Term :=
  snapshot.declarations.filterMap (fun declaration =>
      if declaration.function = name then some (declaredType declaration) else none) ++
    annotations snapshot (.atom name)

def SymbolHasType (snapshot : Snapshot) (name : String) (type : Term) : Prop :=
  (∃ declaration ∈ snapshot.declarations,
      declaration.function = name ∧ declaredType declaration = type) ∨
    snapshot.HasAnnotation (.atom name) type

theorem symbolTypes_iff (snapshot : Snapshot) (name : String) (type : Term) :
    type ∈ symbolTypes snapshot name ↔ SymbolHasType snapshot name type := by
  simp [symbolTypes, SymbolHasType, annotations_iff]

theorem symbolTypes_isEmpty_iff (snapshot : Snapshot) (name : String) :
    (symbolTypes snapshot name).isEmpty = true ↔ ∀ type, ¬ SymbolHasType snapshot name type := by
  rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
  simp only [symbolTypes_iff]

/-! ## Checking (C-rules) -/

/-- `check(value, expected)`, with the value's types supplied by `fresh`:
C-Atom, C-Unknown, C-Meta and C-Synth. `GetMetatype` relates a value only to
`Symbol`, `Expression`, `Variable` or `Grounded`, so C-Meta needs no separate
test that `expected` is one of those names. -/
def checkWith (snapshot : Snapshot) (fresh : Term → List Term) (value expected : Term) : Bool :=
  decide (expected = atomType) || decide (IsUnknown expected) ||
    decide (GetMetatype snapshot value expected) ||
    (fresh value).any fun actual => consistent actual expected

def CheckUsing (snapshot : Snapshot) (typed : Term → Term → Prop) (value expected : Term) :
    Prop :=
  expected = atomType ∨ IsUnknown expected ∨ GetMetatype snapshot value expected ∨
    ∃ actual, typed value actual ∧ Consistent actual expected

theorem checkWith_iff (snapshot : Snapshot) {fresh : Term → List Term}
    {typed : Term → Term → Prop}
    (correct : ∀ value type, type ∈ fresh value ↔ typed value type) (value expected : Term) :
    checkWith snapshot fresh value expected = true ↔ CheckUsing snapshot typed value expected := by
  simp [checkWith, CheckUsing, List.any_eq_true, consistent_iff, correct, or_assoc]

theorem checkWith_congr (snapshot : Snapshot) {left right : Term → List Term} {value : Term}
    (same : left value = right value) (expected : Term) :
    checkWith snapshot left value expected = checkWith snapshot right value expected := by
  simp only [checkWith, same]

/-! ## Synthesis (S-rules) -/

/-- The reading of `(head args...)` for one type `headType` of its head: an
arrow applies or contributes nothing (S-App); any other type builds a tuple
(S-Tuple). -/
def reading (check : Term → Term → Bool) (fresh : Term → List Term)
    (headType : Term) (args : List Term) : List Term :=
  match arrowParts headType with
  | some (domains, result) => if all₂ check args domains then [result] else []
  | none => (combinations (args.map fresh)).map fun types => .list (headType :: types)

def ReadingUsing (check typed : Term → Term → Prop) (headType : Term) (args : List Term)
    (type : Term) : Prop :=
  (∃ domains, headType = arrowTerm domains type ∧ List.Forall₂ check args domains) ∨
    (¬ IsArrow headType ∧
      ∃ types, type = .list (headType :: types) ∧ List.Forall₂ typed args types)

theorem reading_iff {check : Term → Term → Bool} {checkRelation : Term → Term → Prop}
    {fresh : Term → List Term} {typed : Term → Term → Prop}
    (checkCorrect : ∀ value type, check value type = true ↔ checkRelation value type)
    (freshCorrect : ∀ value type, type ∈ fresh value ↔ typed value type)
    (headType : Term) (args : List Term) (type : Term) :
    type ∈ reading check fresh headType args ↔
      ReadingUsing checkRelation typed headType args type := by
  unfold reading ReadingUsing
  cases parts : arrowParts headType with
  | some pair =>
      obtain ⟨domains, result⟩ := pair
      have arrow := (arrowParts_eq_some_iff headType domains result).mp parts
      have isArrow : IsArrow headType := ⟨domains, result, arrow⟩
      simp only [isArrow, not_true_eq_false, false_and, or_false]
      constructor
      · intro member
        by_cases fits : all₂ check args domains = true
        · simp only [fits, ↓reduceIte, List.mem_singleton] at member
          subst member
          exact ⟨domains, arrow, (all₂_iff checkCorrect _ _).mp fits⟩
        · simp [fits] at member
      · rintro ⟨other, same, fits⟩
        rw [arrow] at same
        obtain ⟨rfl, rfl⟩ := arrowTerm_inj same
        simp [(all₂_iff checkCorrect _ _).mpr fits]
  | none =>
      have notArrow := (arrowParts_eq_none_iff headType).mp parts
      simp only [notArrow, not_false_eq_true, true_and, List.mem_map]
      constructor
      · rintro ⟨types, member, rfl⟩
        exact .inr ⟨types, rfl, (mapped_combinations_iff freshCorrect _ _).mp member⟩
      · rintro (⟨domains, same, _⟩ | ⟨types, rfl, fits⟩)
        · exact absurd ⟨domains, type, same⟩ notArrow
        · exact ⟨types, (mapped_combinations_iff freshCorrect _ _).mpr fits, rfl⟩

theorem reading_congr {leftCheck rightCheck : Term → Term → Bool}
    {leftFresh rightFresh : Term → List Term} {args : List Term}
    (checks : ∀ arg ∈ args, ∀ type, leftCheck arg type = rightCheck arg type)
    (fresh : ∀ arg ∈ args, leftFresh arg = rightFresh arg) (headType : Term) :
    reading leftCheck leftFresh headType args = reading rightCheck rightFresh headType args := by
  unfold reading
  cases arrowParts headType with
  | some pair => simp only [all₂_congr_on checks]
  | none => rw [List.map_congr_left fresh]

/-- One synthesis step, with the types of strict subterms supplied by `fresh`. -/
def candidates (snapshot : Snapshot) (fresh : Term → List Term) (value : Term) : List Term :=
  match intrinsic value with
  | some primitive => [primitive]
  | none =>
      match value with
      | .list [] => [.list []]
      | .list (head :: args) =>
          (fresh head).flatMap (fun headType =>
              reading (checkWith snapshot fresh) fresh headType args) ++
            annotations snapshot value
      | .atom name =>
          if (symbolTypes snapshot name).isEmpty then [undefinedType] else symbolTypes snapshot name
      | _ => [undefinedType]

/-- The S-rules, stated independently: S-Lit, S-Unit, S-Expr (S-App or
S-Tuple for each type of the head, then annotations), S-Sym. -/
def CandidateUsing (snapshot : Snapshot) (typed : Term → Term → Prop) (value type : Term) :
    Prop :=
  match intrinsic value with
  | some primitive => type = primitive
  | none =>
      match value with
      | .list [] => type = .list []
      | .list (head :: args) =>
          (∃ headType, typed head headType ∧
              ReadingUsing (CheckUsing snapshot typed) typed headType args type) ∨
            snapshot.HasAnnotation value type
      | .atom name =>
          SymbolHasType snapshot name type ∨
            ((∀ other, ¬ SymbolHasType snapshot name other) ∧ type = undefinedType)
      | _ => type = undefinedType

def TypedAtDepth (snapshot : Snapshot) : Nat → Term → Term → Prop
  | 0, _, _ => False
  | n + 1, value, type => CandidateUsing snapshot (TypedAtDepth snapshot n) value type

def enumerate (snapshot : Snapshot) : Nat → Term → List Term
  | 0, _ => []
  | n + 1, value => candidates snapshot (enumerate snapshot n) value

theorem candidates_iff (snapshot : Snapshot)
    {fresh : Term → List Term} {typed : Term → Term → Prop}
    (correct : ∀ value type, type ∈ fresh value ↔ typed value type)
    (value type : Term) :
    type ∈ candidates snapshot fresh value ↔ CandidateUsing snapshot typed value type := by
  cases primitive : intrinsic value with
  | some p => simp [candidates, CandidateUsing, primitive]
  | none =>
      cases value with
      | list elements =>
          cases elements with
          | nil => simp [candidates, CandidateUsing, primitive]
          | cons head args =>
              simp only [candidates, CandidateUsing, primitive, List.mem_append,
                List.mem_flatMap, annotations_iff, correct,
                reading_iff (checkWith_iff snapshot correct) correct]
      | atom name =>
          simp only [candidates, CandidateUsing, primitive]
          by_cases empty : (symbolTypes snapshot name).isEmpty = true
          · have none := (symbolTypes_isEmpty_iff snapshot name).mp empty
            simp [empty, none]
          · have some : ¬ ∀ other, ¬ SymbolHasType snapshot name other :=
              fun none => empty ((symbolTypes_isEmpty_iff snapshot name).mpr none)
            simp [empty, some, symbolTypes_iff]
      | _ => simp_all [candidates, CandidateUsing, intrinsic]

theorem enumerate_iff (snapshot : Snapshot) (depth : Nat) (value type : Term) :
    type ∈ enumerate snapshot depth value ↔ TypedAtDepth snapshot depth value type := by
  induction depth generalizing value type with
  | zero => simp [enumerate, TypedAtDepth]
  | succ n ih => exact candidates_iff snapshot ih value type

/-- The recursion bound is the height of the queried term. -/
theorem enumerate_stable (snapshot : Snapshot) (value : Term)
    (left right : Nat) (leftEnough : value.height ≤ left)
    (rightEnough : value.height ≤ right) :
    enumerate snapshot left value = enumerate snapshot right value := by
  cases left with
  | zero => have := height_positive value; omega
  | succ left =>
    cases right with
    | zero => have := height_positive value; omega
    | succ right =>
      simp only [enumerate]
      cases value with
      | list elements =>
        cases elements with
        | nil => rfl
        | cons head args =>
          have headBound : head.height ≤ Term.listHeight (head :: args) :=
            height_le_listHeight (by simp)
          have headSame : enumerate snapshot left head = enumerate snapshot right head :=
            enumerate_stable snapshot head left right
              (by simp only [Term.height] at leftEnough; omega)
              (by simp only [Term.height] at rightEnough; omega)
          have argsSame : ∀ arg ∈ args,
              enumerate snapshot left arg = enumerate snapshot right arg := by
            intro arg member
            have argBound : arg.height ≤ Term.listHeight (head :: args) :=
              height_le_listHeight (by simp [member])
            exact enumerate_stable snapshot arg left right
              (by simp only [Term.height] at leftEnough; omega)
              (by simp only [Term.height] at rightEnough; omega)
          have checksSame : ∀ arg ∈ args, ∀ type,
              checkWith snapshot (enumerate snapshot left) arg type =
                checkWith snapshot (enumerate snapshot right) arg type :=
            fun arg member type => checkWith_congr snapshot (argsSame arg member) type
          simp only [candidates, intrinsic, headSame, reading_congr checksSame argsSame]
      | _ => rfl
termination_by value.height
decreasing_by
  all_goals
    subst_vars
    simp only [Term.height]
    omega

/-! ## Public judgments -/

/-- A total decision procedure for the resolved fragment. -/
def types (snapshot : Snapshot) (value : Term) : List Term :=
  enumerate snapshot value.height value

def HasType (snapshot : Snapshot) (value type : Term) : Prop :=
  TypedAtDepth snapshot value.height value type

theorem types_iff (snapshot : Snapshot) (value type : Term) :
    type ∈ types snapshot value ↔ HasType snapshot value type :=
  enumerate_iff snapshot value.height value type

theorem adequate_depth (snapshot : Snapshot) (value type : Term)
    (depth : Nat) (enough : value.height ≤ depth) :
    TypedAtDepth snapshot depth value type ↔ HasType snapshot value type := by
  rw [← enumerate_iff, ← types_iff]
  unfold types
  rw [enumerate_stable snapshot value depth value.height enough (Nat.le_refl _)]

/-- Q-Bound: a requested output filters a fresh enumeration; it is never an
input to synthesis. -/
def query (snapshot : Snapshot) (value expected : Term) : List Term :=
  (types snapshot value).filter (· == expected)

theorem query_iff (snapshot : Snapshot) (value expected answer : Term) :
    answer ∈ query snapshot value expected ↔ HasType snapshot value answer ∧ answer = expected := by
  simp [query, types_iff]

/-- The checking judgment of S-App and of the call guards. -/
def check (snapshot : Snapshot) (value expected : Term) : Bool :=
  checkWith snapshot (types snapshot) value expected

def Check (snapshot : Snapshot) (value expected : Term) : Prop :=
  CheckUsing snapshot (HasType snapshot) value expected

theorem check_iff (snapshot : Snapshot) (value expected : Term) :
    check snapshot value expected = true ↔ Check snapshot value expected :=
  checkWith_iff snapshot (types_iff snapshot) value expected

/-- When every type of the head is an arrow, no argument list fits any of
them, and the expression has no annotation, the expression has no type: a
failed application never becomes a tuple or an unknown. The head may be any
term, including a compound one. -/
theorem known_arrow_failure (snapshot : Snapshot) (depth : Nat) (head : Term)
    (args : List Term)
    (allArrows : ∀ headType, TypedAtDepth snapshot depth head headType → IsArrow headType)
    (noFit : ∀ domains result, TypedAtDepth snapshot depth head (arrowTerm domains result) →
      ¬ List.Forall₂ (CheckUsing snapshot (TypedAtDepth snapshot depth)) args domains)
    (noAnnotation : ∀ type, ¬ snapshot.HasAnnotation (.list (head :: args)) type) :
    enumerate snapshot (depth + 1) (.list (head :: args)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro type member
  have typed := (enumerate_iff snapshot (depth + 1) _ type).mp member
  simp only [TypedAtDepth, CandidateUsing, intrinsic] at typed
  rcases typed with ⟨headType, headTyped, applied | ⟨notArrow, _⟩⟩ | annotated
  · obtain ⟨domains, rfl, fits⟩ := applied
    exact noFit domains type headTyped fits
  · exact notArrow (allArrows headType headTyped)
  · exact noAnnotation type annotated

/-- Agreement of get-type with the call guards: when the only type of the
head is `(-> A B)` and the application has no annotation, its types are
`[B]` if `check arg A` holds, and none otherwise. -/
theorem application_types (snapshot : Snapshot) (head arg domain result : Term)
    (onlyArrow : types snapshot head = [arrowTerm [domain] result])
    (noAnnotation : annotations snapshot (.list [head, arg]) = []) :
    types snapshot (.list [head, arg]) =
      if check snapshot arg domain then [result] else [] := by
  have headSame : enumerate snapshot (Term.listHeight [head, arg]) head =
      [arrowTerm [domain] result] := by
    rw [enumerate_stable snapshot head _ head.height (height_le_listHeight (by simp))
      (Nat.le_refl _)]
    exact onlyArrow
  have argSame : enumerate snapshot (Term.listHeight [head, arg]) arg = types snapshot arg :=
    enumerate_stable snapshot arg _ arg.height (height_le_listHeight (by simp)) (Nat.le_refl _)
  have parts : arrowParts (arrowTerm [domain] result) = some ([domain], result) :=
    (arrowParts_eq_some_iff _ _ _).mpr rfl
  have unfolded : types snapshot (.list [head, arg]) =
      candidates snapshot (enumerate snapshot (Term.listHeight [head, arg])) (.list [head, arg]) :=
    rfl
  have fits : all₂ (checkWith snapshot (enumerate snapshot (Term.listHeight [head, arg])))
      [arg] [domain] = check snapshot arg domain := by
    simp [all₂, check, checkWith_congr snapshot argSame]
  rw [unfolded]
  simp only [candidates, intrinsic, headSame, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, noAnnotation, reading, parts]
  rw [fits]

theorem application_agreement (snapshot : Snapshot) (head arg domain result type : Term)
    (onlyArrow : types snapshot head = [arrowTerm [domain] result])
    (noAnnotation : annotations snapshot (.list [head, arg]) = []) :
    type ∈ types snapshot (.list [head, arg]) ↔
      type = result ∧ check snapshot arg domain = true := by
  rw [application_types snapshot head arg domain result onlyArrow noAnnotation]
  by_cases fits : check snapshot arg domain = true <;> simp [fits]

namespace Controls

def R : Term := .atom "R"
def C : Term := .atom "C"
def Result : Term := .atom "Result"

def snapshot : Snapshot := {
  revision := 0
  declarations := [
    {occurrence := 0, function := "held", inputTypes := [atomType], outputType := R},
    {occurrence := 1, function := "quote-e", inputTypes := [expressionMetaType], outputType := R},
    {occurrence := 2, function := "sym-only", inputTypes := [symbolMetaType], outputType := R},
    {occurrence := 3, function := "f2", inputTypes := [wildcardType], outputType := C},
    {occurrence := 4, function := "make-adder", inputTypes := [numberType],
      outputType := arrowTerm [numberType] numberType},
    {occurrence := 5, function := "mixed", inputTypes := [.atom "B"], outputType := C},
    {occurrence := 6, function := "number-only", inputTypes := [numberType], outputType := Result},
    {occurrence := 7, function := "unknown-input", inputTypes := [undefinedType],
      outputType := Result},
    {occurrence := 8, function := "f", inputTypes := [numberType], outputType := boolType}]
  annotations := [
    {occurrence := 9, subject := .atom "mixed", type := .atom "A"},
    {occurrence := 10, subject := .atom "bb", type := .atom "B"},
    {occurrence := 11, subject := .atom "n", type := numberType},
    {occurrence := 12, subject := .atom "twice", type := numberType},
    {occurrence := 13, subject := .atom "twice", type := numberType}]
  registeredFunctions := [] }

def app (head : String) (args : List Term) : Term := .list (.atom head :: args)
def bad : Term := app "number-only" [.string "bad"]

/-! Known arrows: application, arity, no tuple after a failed argument. -/
example : types snapshot (app "f" [.number "3"]) = [boolType] := by decide
example : types snapshot (app "f" [.string "bad"]) = [] := by decide
example : types snapshot (app "f" [.number "3", .number "4"]) = [] := by decide
example : query snapshot (.number "3") undefinedType = [] := by decide
example : types snapshot (.atom "twice") = [numberType, numberType] := by decide
example : check snapshot (.atom "twice") numberType = true := by decide

/-! C-Atom accepts every argument, even one without a type. -/
example : types snapshot (app "held" [bad]) = [R] := by decide
example : types snapshot (app "held" [.number "1", .number "2"]) = [] := by decide

/-! C-Meta, and its fall-through to C-Synth. -/
example : types snapshot (app "quote-e" [.list [.atom "x", .atom "y"]]) = [R] := by decide
example : types snapshot (app "quote-e" [bad]) = [R] := by decide
example : types snapshot (app "quote-e" [.atom "n"]) = [] := by decide
example : types snapshot (app "quote-e" [.number "3"]) = [] := by decide
example : types snapshot (app "quote-e" [.atom "untyped"]) = [R] := by decide
example : types snapshot (app "sym-only" [.atom "foo"]) = [R] := by decide
example : types snapshot (app "sym-only" [.number "3"]) = [] := by decide
example : types snapshot (app "sym-only" [bad]) = [] := by decide

/-! C-Unknown in both spellings; only a top-level unknown parameter is unchecked. -/
example : types snapshot (app "f2" [.number "3"]) = [C] := by decide
example : types snapshot (app "f2" [.number "1", .number "2"]) = [] := by decide
example : types snapshot (app "unknown-input" [bad]) = [Result] := by decide

/-! Every type of the head is a reading: a compound head. -/
example : types snapshot (.list [app "make-adder" [.number "1"], .number "2"]) =
    [numberType] := by decide
example : types snapshot (.list [app "make-adder" [.number "1"], .string "s"]) = [] := by
  decide
example : types snapshot (.list [app "make-adder" [.string "s"], .number "2"]) = [] := by
  decide

/-! Every type of the head is a reading: a symbol with both kinds of type. -/
example : types snapshot (app "mixed" [.atom "bb"]) = [C, .list [.atom "A", .atom "B"]] := by
  decide
example : types snapshot (app "mixed" [.number "3"]) = [.list [.atom "A", numberType]] := by
  decide

/-! Counts: duplicate evidence for an argument gives one answer; a head
declared twice gives two readings. -/
example : types snapshot (app "number-only" [.atom "twice"]) = [Result] := by decide
example : types ⟨0, [⟨0, "fd", [numberType], C⟩, ⟨1, "fd", [numberType], C⟩], [], []⟩
    (app "fd" [.number "1"]) = [C, C] := by decide

/-! `(->)` is not an arrow, so it builds a tuple. -/
example : types ⟨0, [], [⟨0, .atom "arrow0", .list [.atom "->"]⟩], []⟩
    (app "arrow0" [.number "3"]) = [.list [.list [.atom "->"], numberType]] := by decide

/-! The agreement law on two parameter types and three values. -/
example : check snapshot (.atom "untyped") expressionMetaType = true := by decide
example : check snapshot (.atom "n") expressionMetaType = false := by decide
example : check snapshot bad wildcardType = true := by decide
example : check snapshot bad numberType = false := by decide

def vec (type : Term) : Term := .list [.atom "Vec", type]

/-- Pairwise consistency through a stored wildcard loses the common
constraint required by a shared static scheme variable. -/
theorem wildcard_mediator_accepts_conflict :
    consistent (vec numberType) (vec undefinedType) = true ∧
    consistent (vec undefinedType) (vec stringType) = true ∧
    consistent (vec numberType) (vec stringType) = false := by decide

theorem no_common_static_scheme_instance :
    ¬ ∃ type, Defined type ∧ Consistent (vec numberType) type ∧
      Consistent (vec stringType) type := by
  rintro ⟨type, defined, number, string⟩
  have dn : Defined (vec numberType) := by
    simp [Defined, DefinedList, vec, numberType, IsUnknown, undefinedType, wildcardType]
  have ds : Defined (vec stringType) := by
    simp [Defined, DefinedList, vec, stringType, IsUnknown, undefinedType, wildcardType]
  have same := ((consistent_defined_iff _ _ dn defined).mp number).trans
    ((consistent_defined_iff _ _ ds defined).mp string).symm
  simp [vec, numberType, stringType] at same

end Controls

#print axioms consistent_iff
#print axioms consistent_defined_iff
#print axioms arrowParts_eq_some_iff
#print axioms reading_iff
#print axioms candidates_iff
#print axioms enumerate_iff
#print axioms enumerate_stable
#print axioms types_iff
#print axioms adequate_depth
#print axioms query_iff
#print axioms check_iff
#print axioms known_arrow_failure
#print axioms application_types
#print axioms application_agreement
#print axioms Controls.wildcard_mediator_accepts_conflict
#print axioms Controls.no_common_static_scheme_instance
end Mettapedia.Languages.MeTTa.PeTTa.CoherentTypeQuery
