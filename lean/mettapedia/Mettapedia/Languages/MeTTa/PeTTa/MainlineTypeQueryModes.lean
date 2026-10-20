import Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT

/-!
# Mainline type queries with an already constrained output

The output argument of Prolog's `get-type/2` is part of the call. A primitive
clause whose output cannot unify is skipped before its cut is reached. The
soft-cut fallback tests that constrained candidate call, not an independent
enumeration of every possible type.

This module gives the resolved, ground-declaration membership judgment for
bound queries, its executable decision, and the separation from fresh-output
enumeration. It reuses the existing snapshot and term carriers. It does not
claim an interpretation of open Prolog variables, polymorphic declaration
matching, answer multiplicity, or authored extensions of `get-type/2`.

Depth is the finite recursive presentation's index. A zero-depth refusal is
not a source-language failure. Public source correspondence additionally
requires sufficient depth, ground admission and the declaration-resolution
boundary; this file does not silently identify the older `GetType` relation
with a constrained Prolog call.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryModes

open MainlineTypeQueryGSLT

def intrinsic : Term → Option Term
  | .number _ => some numberType
  | .string _ => some stringType
  | .atom "true" | .atom "false" => some boolType
  | _ => none

def all₂ (check : Term → Term → Bool) : List Term → List Term → Bool
  | [], [] => true
  | left :: lefts, right :: rights => check left right && all₂ check lefts rights
  | _, _ => false

theorem all₂_iff {relation : Term → Term → Prop} {check : Term → Term → Bool}
    (correct : ∀ value type, check value type = true ↔ relation value type)
    (values types : List Term) :
    all₂ check values types = true ↔ List.Forall₂ relation values types := by
  induction values generalizing types with
  | nil => cases types <;> simp [all₂, List.forall₂_nil_left_iff]
  | cons value values ih =>
      cases types with
      | nil => simp [all₂]
      | cons type types => simp [all₂, correct, ih, List.forall₂_cons]

/-- Every declaration is an occurrence; duplicate result types remain in this list. -/
def functionTypes (snapshot : Snapshot) (check : Term → Term → Bool) : Term → List Term
  | .list (.atom function :: arguments) =>
      snapshot.declarations.filterMap fun declaration =>
        if declaration.function = function ∧ all₂ check arguments declaration.inputTypes = true
        then some declaration.outputType else none
  | _ => []

/-- Independent rule for a resolved function declaration and its argument checks. -/
def FunctionTypeUsing (snapshot : Snapshot) (child : Term → Term → Prop)
    (value type : Term) : Prop :=
  match value with
  | .list (.atom function :: arguments) =>
      ∃ declaration ∈ snapshot.declarations,
        declaration.function = function ∧ declaration.outputType = type ∧
          List.Forall₂ child arguments declaration.inputTypes
  | _ => False

theorem functionTypes_iff (snapshot : Snapshot)
    {relation : Term → Term → Prop} {check : Term → Term → Bool}
    (correct : ∀ value type, check value type = true ↔ relation value type)
    (value type : Term) :
    type ∈ functionTypes snapshot check value ↔ FunctionTypeUsing snapshot relation value type := by
  cases value with
  | list elements =>
      cases elements with
      | nil => simp [functionTypes, FunctionTypeUsing]
      | cons head arguments =>
          cases head with
          | atom function =>
              simp only [functionTypes, FunctionTypeUsing, List.mem_filterMap]
              constructor
              · rintro ⟨declaration, member, found⟩
                split at found
                · next good =>
                    exact ⟨declaration, member, good.1, Option.some.inj found,
                      (all₂_iff correct _ _).mp good.2⟩
                · contradiction
              · rintro ⟨declaration, member, name, result, children⟩
                refine ⟨declaration, member, ?_⟩
                simp [name, result, (all₂_iff correct _ _).mpr children]
          | _ => simp [functionTypes, FunctionTypeUsing]
  | _ => simp [functionTypes, FunctionTypeUsing]

def annotations (snapshot : Snapshot) (value : Term) : List Term :=
  snapshot.annotations.filterMap fun annotation =>
    if annotation.subject = value then some annotation.type else none

theorem annotations_iff (snapshot : Snapshot) (value type : Term) :
    type ∈ annotations snapshot value ↔ snapshot.HasAnnotation value type := by
  simp only [annotations, List.mem_filterMap, Snapshot.HasAnnotation]
  constructor
  · rintro ⟨annotation, member, found⟩
    split at found
    · exact ⟨annotation, member, by assumption, Option.some.inj found⟩
    · contradiction
  · rintro ⟨annotation, member, subject, result⟩
    exact ⟨annotation, member, by simp [subject, result]⟩

/-- Candidate membership with a ground, already supplied output. Primitive
cuts cannot remove a different successful output of this bound goal. -/
def BoundCandidateUsing (snapshot : Snapshot) (child : Term → Term → Prop)
    (value expected : Term) : Prop :=
  intrinsic value = some expected ∨
    FunctionTypeUsing snapshot child value expected ∨
    (¬ (∃ result, FunctionTypeUsing snapshot child value result) ∧
      match value, expected with
      | .list values, .list types => List.Forall₂ child values types
      | _, _ => False) ∨
    snapshot.HasAnnotation value expected

/-- The source soft cut either returns a candidate, or supplies Undefined
when no candidate unifies with the already constrained output. -/
def BoundAtDepth (snapshot : Snapshot) : Nat → Term → Term → Prop
  | 0, _, _ => False
  | depth + 1, value, expected =>
      BoundCandidateUsing snapshot (BoundAtDepth snapshot depth) value expected ∨
        (¬ BoundCandidateUsing snapshot (BoundAtDepth snapshot depth) value expected ∧
          expected = undefinedType)

theorem bound_step_iff (snapshot : Snapshot) (depth : Nat) (value expected : Term) :
    BoundAtDepth snapshot (depth + 1) value expected ↔
      expected = undefinedType ∨
        BoundCandidateUsing snapshot (BoundAtDepth snapshot depth) value expected := by
  classical
  simp only [BoundAtDepth]
  tauto

/-- The executable decision uses source-specific candidate structure and the
bound soft-cut simplification. It does not enumerate every possible type. -/
def checkAtDepth (snapshot : Snapshot) : Nat → Term → Term → Bool
  | 0, _, _ => false
  | depth + 1, value, expected =>
      let functions := functionTypes snapshot (checkAtDepth snapshot depth) value
      decide (expected = undefinedType) || decide (intrinsic value = some expected) ||
        functions.contains expected ||
        (functions.isEmpty &&
          match value, expected with
          | .list values, .list types => all₂ (checkAtDepth snapshot depth) values types
          | _, _ => false) ||
        (annotations snapshot value).contains expected

theorem checkAtDepth_iff (snapshot : Snapshot) (depth : Nat) (value expected : Term) :
    checkAtDepth snapshot depth value expected = true ↔
      BoundAtDepth snapshot depth value expected := by
  induction depth generalizing value expected with
  | zero => simp [checkAtDepth, BoundAtDepth]
  | succ depth ih =>
      rw [bound_step_iff]
      have absent : (functionTypes snapshot (checkAtDepth snapshot depth) value).isEmpty = true ↔
          ¬ ∃ result, FunctionTypeUsing snapshot (BoundAtDepth snapshot depth) value result := by
        simp only [List.isEmpty_iff]
        rw [List.eq_nil_iff_forall_not_mem]
        simp only [functionTypes_iff snapshot ih]
        simp
      simp only [checkAtDepth, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.contains_iff_mem, functionTypes_iff snapshot ih, absent, annotations_iff]
      unfold BoundCandidateUsing
      cases value <;> cases expected <;>
        simp only [Bool.false_eq_true, and_false, or_false, all₂_iff ih] <;> tauto

/-- The fallback of a completed bound query is always compatible with an
explicit Undefined request, even when fresh enumeration has a concrete type. -/
theorem bound_undefined (snapshot : Snapshot) (depth : Nat) (value : Term) :
    BoundAtDepth snapshot (depth + 1) value undefinedType :=
  (bound_step_iff _ _ _ _).mpr (.inl rfl)

theorem nonundefined_iff_candidate (snapshot : Snapshot) (depth : Nat)
    (value expected : Term) (notUndefined : expected ≠ undefinedType) :
    BoundAtDepth snapshot (depth + 1) value expected ↔
      BoundCandidateUsing snapshot (BoundAtDepth snapshot depth) value expected := by
  simp [bound_step_iff, notUndefined]

theorem all₂_congr_on {left right : Term → Term → Bool} {values : List Term}
    (agree : ∀ value ∈ values, ∀ type, left value type = right value type)
    (types : List Term) : all₂ left values types = all₂ right values types := by
  induction values generalizing types with
  | nil => cases types <;> rfl
  | cons value values ih =>
      cases types with
      | nil => rfl
      | cons type types =>
          simp only [all₂, agree value (by simp) type,
            ih (fun child member => agree child (by simp [member])) types]

theorem functionTypes_congr_on (snapshot : Snapshot)
    {left right : Term → Term → Bool} {elements : List Term}
    (agree : ∀ value ∈ elements, ∀ type, left value type = right value type) :
    functionTypes snapshot left (.list elements) =
      functionTypes snapshot right (.list elements) := by
  cases elements with
  | nil => rfl
  | cons head arguments =>
      cases head with
      | atom function =>
          simp only [functionTypes]
          congr 1
          funext declaration
          rw [all₂_congr_on (fun child member => agree child (by simp [member]))]
      | _ => rfl

theorem checkAtDepth_list_congr (snapshot : Snapshot) (left right : Nat)
    (elements : List Term) (expected : Term)
    (agree : ∀ value ∈ elements, ∀ type,
      checkAtDepth snapshot left value type = checkAtDepth snapshot right value type) :
    checkAtDepth snapshot (left + 1) (.list elements) expected =
      checkAtDepth snapshot (right + 1) (.list elements) expected := by
  simp only [checkAtDepth, functionTypes_congr_on snapshot agree]
  cases expected <;> simp only [all₂_congr_on agree]

theorem height_positive (value : Term) : 0 < value.height := by
  cases value <;> simp [Term.height]

theorem height_le_listHeight {value : Term} {elements : List Term}
    (member : value ∈ elements) : value.height ≤ Term.listHeight elements := by
  induction elements with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- Negated function lookup prevents arbitrary fuel monotonicity. Once every
recursive argument has been inspected, both positive and negative answers
are stable. The sufficient bound depends only on the queried term. -/
theorem checkAtDepth_stable (snapshot : Snapshot) (value : Term)
    (left right : Nat) (leftEnough : value.height ≤ left)
    (rightEnough : value.height ≤ right) (expected : Term) :
    checkAtDepth snapshot left value expected = checkAtDepth snapshot right value expected := by
  cases left with
  | zero => have := height_positive value; omega
  | succ left =>
      cases right with
      | zero => have := height_positive value; omega
      | succ right =>
          cases value with
          | list elements =>
              apply checkAtDepth_list_congr
              intro child member type
              have childBound := height_le_listHeight member
              apply checkAtDepth_stable snapshot child left right
                (by simp only [Term.height] at leftEnough; omega)
                (by simp only [Term.height] at rightEnough; omega) type
          | _ =>
              simp only [checkAtDepth, functionTypes]
termination_by value.height
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (height_le_listHeight member)

/-- Finite, resolved bound-query membership, independent of an external budget. -/
def Bound (snapshot : Snapshot) (value expected : Term) : Prop :=
  BoundAtDepth snapshot value.height value expected

def check (snapshot : Snapshot) (value expected : Term) : Bool :=
  checkAtDepth snapshot value.height value expected

theorem check_iff (snapshot : Snapshot) (value expected : Term) :
    check snapshot value expected = true ↔ Bound snapshot value expected :=
  checkAtDepth_iff _ _ _ _

theorem boundAtDepth_iff (snapshot : Snapshot) (value expected : Term)
    (depth : Nat) (enough : value.height ≤ depth) :
    BoundAtDepth snapshot depth value expected ↔ Bound snapshot value expected := by
  rw [← checkAtDepth_iff, ← check_iff]
  unfold check
  rw [checkAtDepth_stable snapshot value depth value.height enough (Nat.le_refl _) expected]

/-- A completed refused bound query has no derivation at any sufficient depth. -/
theorem refusal_iff (snapshot : Snapshot) (value expected : Term) :
    check snapshot value expected = false ↔
      ¬ ∃ depth, value.height ≤ depth ∧ BoundAtDepth snapshot depth value expected := by
  have exactDepth : (∃ depth, value.height ≤ depth ∧
      BoundAtDepth snapshot depth value expected) ↔ Bound snapshot value expected := by
    constructor
    · rintro ⟨depth, enough, accepted⟩
      exact (boundAtDepth_iff _ _ _ _ enough).mp accepted
    · intro accepted
      exact ⟨value.height, Nat.le_refl _, accepted⟩
  rw [exactDepth, ← check_iff]
  cases check snapshot value expected <;> simp

namespace Controls

def empty : Snapshot := ⟨0, [], [], []⟩

theorem bound_number_undefined :
    BoundAtDepth empty 2 (.number "3") undefinedType := bound_undefined _ _ _

theorem old_enumeration_number_not_undefined :
    ¬ MainlineTypeQueryGSLT.GetType empty (.number "3") undefinedType := by
  decide

/-- No single membership relation can identify these two query observations. -/
theorem fresh_membership_not_bound_query :
    ¬ (∀ value type, MainlineTypeQueryGSLT.GetType empty value type ↔
      BoundAtDepth empty (value.height + 1) value type) := by
  intro same
  exact old_enumeration_number_not_undefined
    ((same (.number "3") undefinedType).mpr bound_number_undefined)

def sample : Snapshot :=
  ⟨0, [⟨0, "f", [.atom "A"], .atom "C"⟩],
    [⟨1, .atom "a", .atom "A"⟩, ⟨2, .atom "b", .atom "B"⟩,
     ⟨3, .atom "f", .list [.atom "->", .atom "A", .atom "C"]⟩], []⟩

example : checkAtDepth sample 4 (.list [.atom "f", .atom "a"]) (.atom "C") = true := by
  decide

example : checkAtDepth sample 4 (.list [.atom "f", .atom "b"]) (.atom "C") = false := by
  decide

example : checkAtDepth sample 4 (.list [.atom "f", .atom "b"])
    (.list [.list [.atom "->", .atom "A", .atom "C"], .atom "B"]) = true := by
  decide

/-- A bound primitive query can reach a later annotation when the primitive
clause's output does not match and therefore its cut has not executed. -/
example : checkAtDepth ⟨0, [], [⟨0, .number "3", .atom "Special"⟩], []⟩
    2 (.number "3") (.atom "Special") = true := by decide

end Controls

#print axioms checkAtDepth_iff
#print axioms bound_undefined
#print axioms Controls.fresh_membership_not_bound_query
#print axioms checkAtDepth_stable
#print axioms refusal_iff

end Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryModes
