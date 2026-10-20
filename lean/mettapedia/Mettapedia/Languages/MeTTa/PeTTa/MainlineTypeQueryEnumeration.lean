import Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryModes
import Mettapedia.Languages.MeTTa.PeTTa.TypedCheckElimination

/-!
# Fresh type-query support with bound recursive argument checks

Fresh output enumeration and bound output checking are different requests.
The former still checks a function's arguments against its already supplied
declaration types. Structural list fallback recursively enumerates its elements.
Primitive cuts apply before annotations only when their output head unifies.

The executable list below represents answer support, not Prolog answer
multiplicity: several proofs of a bound argument may produce repeated source
answers. The source boundary is the same finite, resolved, ground-declaration
fragment as `MainlineTypeQueryModes`. Open query variables and polymorphic
declaration resolution are not identified with this ground model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryEnumeration

open MainlineTypeQueryGSLT MainlineTypeQueryModes

def combinations : List (List Term) → List (List Term)
  | [] => [[]]
  | choices :: rest => choices.flatMap fun choice =>
      (combinations rest).map (choice :: ·)

theorem mem_combinations_iff (choices : List (List Term)) (values : List Term) :
    values ∈ combinations choices ↔ List.Forall₂ (fun options value => value ∈ options) choices values := by
  induction choices generalizing values with
  | nil => cases values <;> simp [combinations]
  | cons options choices ih =>
      cases values with
      | nil => simp [combinations]
      | cons value values =>
          simp [combinations, List.mem_flatMap, List.mem_map, ih, List.forall₂_cons]

def CandidateUsing (snapshot : Snapshot) (bound fresh : Term → Term → Prop)
    (value expected : Term) : Prop :=
  match intrinsic value with
  | some primitive => expected = primitive
  | none =>
      FunctionTypeUsing snapshot bound value expected ∨
        (¬ (∃ result, FunctionTypeUsing snapshot bound value result) ∧
          match value, expected with
          | .list values, .list types => List.Forall₂ fresh values types
          | _, _ => False) ∨
        snapshot.HasAnnotation value expected

def FreshAtDepth (snapshot : Snapshot) : Nat → Term → Term → Prop
  | 0, _, _ => False
  | depth + 1, value, expected =>
      CandidateUsing snapshot (BoundAtDepth snapshot depth) (FreshAtDepth snapshot depth)
        value expected ∨
        (¬ ∃ type, CandidateUsing snapshot (BoundAtDepth snapshot depth)
          (FreshAtDepth snapshot depth) value type) ∧ expected = undefinedType

def candidates (snapshot : Snapshot) (bound : Term → Term → Bool)
    (fresh : Term → List Term) (value : Term) : List Term :=
  match intrinsic value with
  | some primitive => [primitive]
  | none =>
      let functions := functionTypes snapshot bound value
      let tuples := if functions.isEmpty then
        match value with
        | .list values => (combinations (values.map fresh)).map Term.list
        | _ => []
      else []
      functions ++ tuples ++ annotations snapshot value

def supportAtDepth (snapshot : Snapshot) : Nat → Term → List Term
  | 0, _ => []
  | depth + 1, value =>
      let found := candidates snapshot (checkAtDepth snapshot depth) (supportAtDepth snapshot depth) value
      if found.isEmpty then [undefinedType] else found

theorem mapped_combinations_iff {fresh : Term → List Term} {relation : Term → Term → Prop}
    (correct : ∀ value type, type ∈ fresh value ↔ relation value type)
    (values types : List Term) :
    types ∈ combinations (values.map fresh) ↔ List.Forall₂ relation values types := by
  rw [mem_combinations_iff]
  induction values generalizing types with
  | nil => cases types <;> simp
  | cons value values ih =>
      cases types with
      | nil => simp
      | cons type types => simp [List.forall₂_cons, correct, ih]

theorem candidates_iff (snapshot : Snapshot)
    {bound : Term → Term → Bool} {boundRelation : Term → Term → Prop}
    {fresh : Term → List Term} {freshRelation : Term → Term → Prop}
    (boundCorrect : ∀ value type, bound value type = true ↔ boundRelation value type)
    (freshCorrect : ∀ value type, type ∈ fresh value ↔ freshRelation value type)
    (value type : Term) :
    type ∈ candidates snapshot bound fresh value ↔
      CandidateUsing snapshot boundRelation freshRelation value type := by
  cases primitive : intrinsic value with
  | some actual => simp [candidates, CandidateUsing, primitive]
  | none =>
      have absent : (functionTypes snapshot bound value).isEmpty = true ↔
          ¬ ∃ result, FunctionTypeUsing snapshot boundRelation value result := by
        simp only [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem,
          functionTypes_iff snapshot boundCorrect]
        simp
      simp only [candidates, CandidateUsing, primitive, List.mem_append,
        functionTypes_iff snapshot boundCorrect, annotations_iff]
      by_cases noFunctions : (functionTypes snapshot bound value).isEmpty = true
      · simp only [noFunctions, ↓reduceIte, (absent.mp noFunctions)]
        cases value <;> cases type <;>
          simp [mapped_combinations_iff freshCorrect, or_assoc]
      · have someFunction : ¬ ¬ ∃ result, FunctionTypeUsing snapshot boundRelation value result :=
          fun none => noFunctions (absent.mpr none)
        simp [noFunctions, someFunction]

theorem supportAtDepth_iff (snapshot : Snapshot) (depth : Nat) (value type : Term) :
    type ∈ supportAtDepth snapshot depth value ↔ FreshAtDepth snapshot depth value type := by
  induction depth generalizing value type with
  | zero => simp [supportAtDepth, FreshAtDepth]
  | succ depth ih =>
      let found := candidates snapshot (checkAtDepth snapshot depth) (supportAtDepth snapshot depth) value
      have candidateCorrect := candidates_iff snapshot (checkAtDepth_iff snapshot depth) ih value
      have absent : found.isEmpty = true ↔
          ¬ ∃ result, CandidateUsing snapshot (BoundAtDepth snapshot depth)
            (FreshAtDepth snapshot depth) value result := by
        simp only [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
        change (∀ result, result ∉ candidates snapshot (checkAtDepth snapshot depth)
          (supportAtDepth snapshot depth) value) ↔ _
        simp only [candidateCorrect]
        simp
      change (type ∈ if found.isEmpty then [undefinedType] else found) ↔
        CandidateUsing snapshot (BoundAtDepth snapshot depth) (FreshAtDepth snapshot depth)
          value type ∨
        (¬ ∃ result, CandidateUsing snapshot (BoundAtDepth snapshot depth)
          (FreshAtDepth snapshot depth) value result) ∧ type = undefinedType
      by_cases none : found.isEmpty = true
      · have noType := absent.mp none
        have noCurrent : ¬ CandidateUsing snapshot (BoundAtDepth snapshot depth)
            (FreshAtDepth snapshot depth) value type := fun present => noType ⟨type, present⟩
        rw [if_pos none]
        constructor
        · intro member
          exact .inr ⟨noType, List.mem_singleton.mp member⟩
        · rintro (bad | ⟨_, same⟩)
          · exact False.elim (noCurrent bad)
          · exact List.mem_singleton.mpr same
      · rw [if_neg none]
        constructor
        · intro member
          exact .inl ((candidateCorrect type).mp member)
        · rintro (member | absent')
          · exact (candidateCorrect type).mpr member
          · exact False.elim (none (absent.mpr absent'.1))

/-- The result list stabilizes once every structurally smaller argument has
been considered, including the negative test that permits tuple fallback. -/
theorem supportAtDepth_stable (snapshot : Snapshot) (value : Term)
    (left right : Nat) (leftEnough : value.height ≤ left)
    (rightEnough : value.height ≤ right) :
    supportAtDepth snapshot left value = supportAtDepth snapshot right value := by
  cases left with
  | zero => have := height_positive value; omega
  | succ left =>
      cases right with
      | zero => have := height_positive value; omega
      | succ right =>
          have same : candidates snapshot (checkAtDepth snapshot left)
              (supportAtDepth snapshot left) value =
              candidates snapshot (checkAtDepth snapshot right)
                (supportAtDepth snapshot right) value := by
            cases value with
            | list elements =>
                have boundSame : ∀ child ∈ elements, ∀ type,
                    checkAtDepth snapshot left child type = checkAtDepth snapshot right child type := by
                  intro child member type
                  have childBound := height_le_listHeight member
                  exact checkAtDepth_stable snapshot child left right
                    (by simp only [Term.height] at leftEnough; omega)
                    (by simp only [Term.height] at rightEnough; omega) type
                have freshSame : elements.map (supportAtDepth snapshot left) =
                    elements.map (supportAtDepth snapshot right) := by
                  apply List.map_congr_left
                  intro child member
                  have childBound := height_le_listHeight member
                  exact supportAtDepth_stable snapshot child left right
                    (by simp only [Term.height] at leftEnough; omega)
                    (by simp only [Term.height] at rightEnough; omega)
                simp only [candidates, intrinsic, functionTypes_congr_on snapshot boundSame,
                  freshSame]
            | _ => simp only [candidates, intrinsic, functionTypes] <;> rfl
          simp only [supportAtDepth, same]
termination_by value.height
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (height_le_listHeight member)

def Support (snapshot : Snapshot) (value type : Term) : Prop :=
  FreshAtDepth snapshot value.height value type

def enumerateSupport (snapshot : Snapshot) (value : Term) : List Term :=
  supportAtDepth snapshot value.height value

theorem enumerateSupport_iff (snapshot : Snapshot) (value type : Term) :
    type ∈ enumerateSupport snapshot value ↔ Support snapshot value type :=
  supportAtDepth_iff _ _ _ _

theorem freshAtDepth_iff (snapshot : Snapshot) (value type : Term)
    (depth : Nat) (enough : value.height ≤ depth) :
    FreshAtDepth snapshot depth value type ↔ Support snapshot value type := by
  rw [← supportAtDepth_iff, ← enumerateSupport_iff]
  unfold enumerateSupport
  rw [supportAtDepth_stable snapshot value depth value.height enough (Nat.le_refl _)]

namespace Controls

def sample : Snapshot := MainlineTypeQueryModes.Controls.sample

example : enumerateSupport sample (.list [.atom "f", .atom "a"]) = [.atom "C"] := by decide

example : enumerateSupport sample (.list [.atom "f", .atom "b"]) =
    [.list [.list [.atom "->", .atom "A", .atom "C"], .atom "B"]] := by decide

example : enumerateSupport ⟨0, [], [⟨0, .number "3", .atom "Special"⟩], []⟩
    (.number "3") = [numberType] := by decide

def wildcard : Snapshot :=
  ⟨0, [⟨0, "f", [undefinedType], .atom "C"⟩],
    [⟨1, .atom "f", .list [.atom "->", undefinedType, .atom "C"]⟩], []⟩

/-- Even a fresh outer query contains bound inner calls. Replacing those by
membership in a fresh enumeration changes an ordinary closed program. -/
theorem bound_arguments_affect_fresh_result :
    enumerateSupport wildcard (.list [.atom "f", .number "3"]) = [.atom "C"] := by decide

theorem old_closed_model_misses_result :
    ¬ MainlineTypeQueryGSLT.GetType wildcard (.list [.atom "f", .number "3"]) (.atom "C") := by
  decide

/-- A cache of fresh answer membership cannot also serve bound queries under
the same key. The mode belongs to the request, even in an empty source space. -/
theorem no_mode_blind_relation :
    ¬ ∃ relation : Term → Term → Prop,
      (∀ value type, relation value type ↔ Support MainlineTypeQueryModes.Controls.empty value type) ∧
      (∀ value type, relation value type ↔ Bound MainlineTypeQueryModes.Controls.empty value type) := by
  rintro ⟨relation, fresh, bound⟩
  have accepted : Bound MainlineTypeQueryModes.Controls.empty (.number "3") undefinedType := by
    exact (check_iff _ _ _).mp (by decide)
  have refused : ¬ Support MainlineTypeQueryModes.Controls.empty (.number "3") undefinedType := by
    rw [← enumerateSupport_iff]
    decide
  exact refused ((fresh _ _).mp ((bound _ _).mpr accepted))

namespace Multiplicity

open TypedCheckElimination

/-- Reuse the existing mode-sensitive count model for the monomorphic slice;
do not treat the support enumerator as an answer-count implementation. -/
def repeatedDeclarations : Decls
  | 0 => [.con 1, .con 1]
  | 1 => [.arrow [.con 1] (.con 2)]
  | _ => []

theorem repeated_argument_proofs_repeat_the_result :
    answers repeatedDeclarations (.app [.sym 1, .sym 0]) = [.con 2, .con 2] := rfl

def repeatedSnapshot : Snapshot :=
  ⟨0, [⟨0, "f", [.atom "A"], .atom "C"⟩],
    [⟨1, .atom "a", .atom "A"⟩, ⟨2, .atom "a", .atom "A"⟩], []⟩

theorem support_does_not_count_bound_proofs :
    enumerateSupport repeatedSnapshot (.list [.atom "f", .atom "a"]) = [.atom "C"] := by decide

end Multiplicity

end Controls

#print axioms supportAtDepth_iff
#print axioms enumerateSupport_iff
#print axioms supportAtDepth_stable
#print axioms Controls.bound_arguments_affect_fresh_result
#print axioms Controls.old_closed_model_misses_result
#print axioms Controls.no_mode_blind_relation
#print axioms Controls.Multiplicity.repeated_argument_proofs_repeat_the_result

end Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryEnumeration
