import Mettapedia.Algorithms.Compression.TemplateGrammar

/-!
# Ranked template generation with simultaneous source guides

The template language and canonical hole state are those of TemplateGrammar.
A capture stores an ordered vector of source subtrees. Equality of a repeated
capture checks all guides; it does not deduplicate their occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.GuidedTemplateGrammar

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open TemplateGrammar

abbrev Captures := SchemaHole → Option (List Prog)
abbrev Step := (SchemaPattern × State) × Captures
abbrev ForestStep := (List SchemaPattern × State) × Captures

def nodes (op : Nat) : List Prog → Option (List (List Prog))
  | [] => some []
  | .node actual children :: rest =>
      if op = actual then (nodes op rest).map (children :: ·) else none

def columns : List (List Prog) → Option (List Prog × List (List Prog))
  | [] => some ([], [])
  | [] :: _ => none
  | (first :: rest) :: rows => do
      let (heads, tails) ← columns rows
      pure (first :: heads, rest :: tails)

def emptyForests (rows : List (List Prog)) : Bool := rows.all List.isEmpty

theorem nodes_of_map (op : Nat) (rows : List (List Prog)) :
    nodes op (rows.map (.node op)) = some rows := by
  induction rows with
  | nil => rfl
  | cons first rest ih => simp [nodes, ih]

theorem nodes_sound {op : Nat} {values : List Prog} {rows : List (List Prog)}
    (found : nodes op values = some rows) : values = rows.map (.node op) := by
  induction values generalizing rows with
  | nil => simp [nodes] at found; subst rows; rfl
  | cons first rest ih =>
      cases first with
      | node actual children =>
          simp only [nodes] at found
          split at found
          · rename_i same
            cases tailResult : nodes op rest with
            | none => simp [tailResult] at found
            | some tails =>
                simp only [tailResult, Option.map_some, Option.some.injEq] at found
                subst rows
                subst actual
                simp [ih tailResult]
          · simp at found

theorem nodes_length {op : Nat} {values : List Prog} {rows : List (List Prog)}
    (found : nodes op values = some rows) : rows.length = values.length := by
  rw [nodes_sound found, List.length_map]

theorem columns_length {rows : List (List Prog)} {heads : List Prog} {tails : List (List Prog)}
    (found : columns rows = some (heads, tails)) :
    heads.length = rows.length ∧ tails.length = rows.length := by
  induction rows generalizing heads tails with
  | nil => simp [columns] at found; rcases found with ⟨rfl, rfl⟩; simp
  | cons first rest ih =>
      cases first with
      | nil => simp [columns] at found
      | cons head tail =>
          cases result : columns rest with
          | none => simp [columns, result] at found
          | some pair =>
              rcases pair with ⟨hs, ts⟩
              simp [columns, result] at found
              rcases found with ⟨rfl, rfl⟩
              simpa using ih result

mutual
def matchVector (captures : Captures) : SchemaPattern → List Prog → Option Captures
  | .hole role index, values => TemplateMatching.assign captures (role, index) values
  | .node op patterns, values => do
      let rows ← nodes op values
      matchForests captures patterns rows

def matchForests (captures : Captures) : List SchemaPattern → List (List Prog) → Option Captures
  | [], rows => if emptyForests rows then some captures else none
  | pattern :: patterns, rows => do
      let (heads, tails) ← columns rows
      let middle ← matchVector captures pattern heads
      matchForests middle patterns tails
end

def checked (candidates : List (SchemaPattern × State)) (captures : Captures)
    (values : List Prog) : List Step :=
  candidates.filterMap fun candidate =>
    (matchVector captures candidate.1 values).map (fun next => (candidate, next))

def forests (generate : Slot → State → Captures → List Prog → List Step) :
    List Slot → State → Captures → List (List Prog) → List ForestStep
  | [], state, captures, rows => if emptyForests rows then [(([], state), captures)] else []
  | slot :: slots, state, captures, rows =>
      match columns rows with
      | none => []
      | some (heads, tails) =>
          (generate slot state captures heads).flatMap fun ((pattern, middle), assigned) =>
            (forests generate slots middle assigned tails).map fun ((patterns, final), complete) =>
              ((pattern :: patterns, final), complete)

def terms (signature : List Operator) : Nat → Slot → State → Captures → List Prog → List Step
  | 0, slot, state, captures, values => checked (holes slot state) captures values
  | depth + 1, slot, state, captures, values =>
      checked (holes slot state) captures values ++
      (match values with
      | [] => []
      | .node op _ :: _ =>
          match signature[op]? with
          | none => []
          | some entry =>
              if entry.result = slot.sort then
                match nodes op values with
                | none => []
                | some rows =>
                    (forests (terms signature depth) entry.inputs state captures rows).map
                      fun ((patterns, final), assigned) => ((.node op patterns, final), assigned)
              else [])

theorem checked_mem (candidates : List (SchemaPattern × State)) (captures after : Captures)
    (values : List Prog) (pattern : SchemaPattern) (final : State) :
    ((pattern, final), after) ∈ checked candidates captures values ↔
      (pattern, final) ∈ candidates ∧ matchVector captures pattern values = some after := by
  simp only [checked, List.mem_filterMap]
  constructor
  · rintro ⟨⟨actual, state⟩, present, accepted⟩
    cases result : matchVector captures actual values with
    | none => simp [result] at accepted
    | some next =>
        simp [result] at accepted
        rcases accepted with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨present, result⟩
  · rintro ⟨present, matched⟩
    exact ⟨(pattern, final), present, by simp [matched]⟩

theorem forests_mem_iff
    (generate : Slot → State → List (SchemaPattern × State))
    (guided : Slot → State → Captures → List Prog → List Step)
    (exact_term : ∀ slot before captures values pattern final after, values ≠ [] →
      (((pattern, final), after) ∈ guided slot before captures values ↔
        (pattern, final) ∈ generate slot before ∧ matchVector captures pattern values = some after))
    (slots : List Slot) (before : State) (captures : Captures) (rows : List (List Prog))
    (patterns : List SchemaPattern) (final : State) (after : Captures) (nonempty : rows ≠ []) :
    ((patterns, final), after) ∈ forests guided slots before captures rows ↔
      (patterns, final) ∈ TemplateGrammar.forests generate slots before ∧
        matchForests captures patterns rows = some after := by
  induction slots generalizing before captures rows patterns final after with
  | nil =>
      by_cases empty : emptyForests rows
      · simp only [forests, empty, ↓reduceIte, List.mem_singleton,
          TemplateGrammar.forests, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨rfl, rfl⟩, rfl⟩
          simp [matchForests, empty]
        · rintro ⟨⟨rfl, rfl⟩, matched⟩
          have equal : captures = after := by simpa [matchForests, empty] using matched
          exact ⟨⟨rfl, rfl⟩, equal.symm⟩
      · have isfalse : emptyForests rows = false := Bool.eq_false_iff.mpr empty
        constructor
        · intro found
          simp [forests, isfalse] at found
        · rintro ⟨plain, matched⟩
          have equal : (patterns, final) = ([], before) := List.mem_singleton.mp plain
          cases equal
          simp [matchForests, isfalse] at matched
  | cons slot slots ih =>
      cases selected : columns rows with
      | none =>
          simp only [forests, selected, List.not_mem_nil, false_iff,
            TemplateGrammar.forests, List.mem_flatMap, List.mem_map]
          rintro ⟨⟨⟨pattern, middle⟩, head, ⟨⟨rest, finish⟩, tail, equal⟩⟩, matched⟩
          simp only [Prod.mk.injEq] at equal
          rcases equal with ⟨rfl, rfl⟩
          simp [matchForests, selected] at matched
      | some pair =>
          rcases pair with ⟨heads, tails⟩
          have lengths := columns_length selected
          have heads_nonempty : heads ≠ [] := by
            intro empty
            have zero : rows.length = 0 := by simpa [empty] using lengths.1.symm
            exact nonempty (List.length_eq_zero_iff.mp zero)
          have tails_nonempty : tails ≠ [] := by
            intro empty
            have zero : rows.length = 0 := by simpa [empty] using lengths.2.symm
            exact nonempty (List.length_eq_zero_iff.mp zero)
          constructor
          · intro found
            simp only [forests, selected, List.mem_flatMap, List.mem_map] at found
            obtain ⟨⟨⟨pattern, middle⟩, assigned⟩, head,
              ⟨⟨⟨rest, finish⟩, complete⟩, tail, equal⟩⟩ := found
            simp only [Prod.mk.injEq] at equal
            rcases equal with ⟨⟨rfl, rfl⟩, rfl⟩
            obtain ⟨plain_head, matched_head⟩ :=
              (exact_term slot before captures heads pattern middle assigned heads_nonempty).mp head
            obtain ⟨plain_tail, matched_tail⟩ :=
              (ih middle assigned tails rest finish complete tails_nonempty).mp tail
            refine ⟨List.mem_flatMap.mpr ⟨(pattern, middle), plain_head,
              List.mem_map.mpr ⟨(rest, finish), plain_tail, rfl⟩⟩, ?_⟩
            simp [matchForests, selected, matched_head, matched_tail]
          · rintro ⟨plain, matched⟩
            simp only [TemplateGrammar.forests, List.mem_flatMap, List.mem_map] at plain
            obtain ⟨⟨pattern, middle⟩, head, ⟨⟨rest, finish⟩, tail, equal⟩⟩ := plain
            simp only [Prod.mk.injEq] at equal
            rcases equal with ⟨rfl, rfl⟩
            cases head_result : matchVector captures pattern heads with
            | none => simp [matchForests, selected, head_result] at matched
            | some assigned =>
                have tail_result : matchForests assigned rest tails = some after := by
                  simpa [matchForests, selected, head_result] using matched
                have guided_head :=
                  (exact_term slot before captures heads pattern middle assigned heads_nonempty).mpr ⟨head, head_result⟩
                have guided_tail :=
                  (ih middle assigned tails rest finish after tails_nonempty).mpr ⟨tail, tail_result⟩
                simp only [forests, selected, List.mem_flatMap, List.mem_map]
                exact ⟨((pattern, middle), assigned), guided_head,
                  ((rest, finish), after), guided_tail, rfl⟩

theorem nodes_first {op actual : Nat} {children : List Prog} {rest : List Prog}
    {rows : List (List Prog)} (found : nodes op (.node actual children :: rest) = some rows) :
    op = actual := by
  by_contra different
  simp [nodes, different] at found

/-- Early guide checks preserve the complete bounded grammar's supported
region. This is a membership equality; evaluator answer order is separate. -/
theorem terms_mem_iff (signature : List Operator) (depth : Nat) (slot : Slot)
    (before : State) (captures : Captures) (values : List Prog)
    (pattern : SchemaPattern) (final : State) (after : Captures) (nonempty : values ≠ []) :
    ((pattern, final), after) ∈ terms signature depth slot before captures values ↔
      (pattern, final) ∈ TemplateGrammar.terms signature depth slot before ∧
        matchVector captures pattern values = some after := by
  induction depth generalizing slot before captures values pattern final after with
  | zero => exact checked_mem _ _ _ _ _ _
  | succ depth ih =>
      cases values with
      | nil => exact False.elim (nonempty rfl)
      | cons first rest =>
          cases first with
          | node actual arguments =>
              have forest_exact := forests_mem_iff (TemplateGrammar.terms signature depth)
                (terms signature depth) (fun s b c v p f a ne => ih s b c v p f a ne)
              constructor
              · intro found
                simp only [terms] at found
                rcases List.mem_append.mp found with hole | node
                · obtain ⟨plain, matched⟩ := (checked_mem _ _ _ _ _ _).mp hole
                  exact ⟨List.mem_append_left _ plain, matched⟩
                · cases entry_result : signature[actual]? with
                  | none => simp [entry_result] at node
                  | some entry =>
                      by_cases typed : entry.result = slot.sort
                      · cases rows_result : nodes actual (.node actual arguments :: rest) with
                        | none => simp [entry_result, typed, rows_result] at node
                        | some rows =>
                            simp only [entry_result, typed, ↓reduceIte, rows_result] at node
                            obtain ⟨⟨⟨children, finish⟩, complete⟩, generated, equal⟩ := List.mem_map.mp node
                            simp only [Prod.mk.injEq] at equal
                            rcases equal with ⟨⟨rfl, rfl⟩, rfl⟩
                            have rows_nonempty : rows ≠ [] := by
                              intro empty
                              have len := nodes_length rows_result
                              simp [empty] at len
                            obtain ⟨plain, matched⟩ :=
                              (forest_exact entry.inputs before captures rows children finish complete rows_nonempty).mp generated
                            refine ⟨?_, by simp [matchVector, rows_result, matched]⟩
                            apply List.mem_append_right
                            apply List.mem_flatMap.mpr
                            refine ⟨(entry, actual), List.mk_mem_zipIdx_iff_getElem?.mpr entry_result, ?_⟩
                            simp only [typed, ↓reduceIte]
                            exact List.mem_map.mpr ⟨(children, finish), plain, rfl⟩
                      · simp [entry_result, typed] at node
              · rintro ⟨plain, matched⟩
                simp only [TemplateGrammar.terms] at plain
                rcases List.mem_append.mp plain with hole | node
                · apply List.mem_append_left
                  exact (checked_mem _ _ _ _ _ _).mpr ⟨hole, matched⟩
                · obtain ⟨⟨entry, index⟩, present, generated⟩ := List.mem_flatMap.mp node
                  by_cases typed : entry.result = slot.sort
                  · simp only [typed, ↓reduceIte] at generated
                    obtain ⟨⟨children, finish⟩, forest_generated, equal⟩ := List.mem_map.mp generated
                    simp only [Prod.mk.injEq] at equal
                    rcases equal with ⟨rfl, rfl⟩
                    cases rows_result : nodes index (.node actual arguments :: rest) with
                    | none => simp [matchVector, rows_result] at matched
                    | some rows =>
                        have head_equal := nodes_first rows_result
                        subst actual
                        have entry_result := List.mk_mem_zipIdx_iff_getElem?.mp present
                        have rows_nonempty : rows ≠ [] := by
                          intro empty
                          have len := nodes_length rows_result
                          simp [empty] at len
                        have forest_matched : matchForests captures children rows = some after := by
                          simpa [matchVector, rows_result] using matched
                        have guided :=
                          (forest_exact entry.inputs before captures rows children finish after rows_nonempty).mpr
                            ⟨forest_generated, forest_matched⟩
                        simp only [terms, entry_result, typed, ↓reduceIte, rows_result]
                        exact List.mem_append_right _ (List.mem_map.mpr ⟨((children, finish), after), guided, rfl⟩)
                  · simp [typed] at generated

theorem supported_region_iff (signature : List Operator) (depth : Nat) (slot : Slot)
    (before : State) (captures : Captures) (values : List Prog) (result : Step)
    (nonempty : values ≠ []) :
    result ∈ terms signature depth slot before captures values ↔
      result ∈ checked (TemplateGrammar.terms signature depth slot before) captures values := by
  rcases result with ⟨⟨pattern, final⟩, after⟩
  rw [terms_mem_iff _ _ _ _ _ _ _ _ _ nonempty, checked_mem]

theorem score_range_iff (signature : List Operator) (depth : Nat) (slot : Slot)
    (before : State) (captures : Captures) (values : List Prog)
    (score : Step → Option Nat) (cost : Nat) (nonempty : values ≠ []) :
    cost ∈ (terms signature depth slot before captures values).filterMap score ↔
      cost ∈ (checked (TemplateGrammar.terms signature depth slot before) captures values).filterMap score := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨result, present, scored⟩
    exact ⟨result, (supported_region_iff _ _ _ _ _ _ result nonempty).mp present, scored⟩
  · rintro ⟨result, present, scored⟩
    exact ⟨result, (supported_region_iff _ _ _ _ _ _ result nonempty).mpr present, scored⟩

theorem lower_le_minimum (costs : List Nat) (initial lower : Nat) :
    lower ≤ costs.foldl min initial ↔ lower ≤ initial ∧ ∀ cost ∈ costs, lower ≤ cost := by
  induction costs generalizing initial with
  | nil => simp
  | cons first rest ih =>
      simp only [List.foldl_cons, ih, Nat.le_min, List.forall_mem_cons]
      tauto

/-- Filtering during generation preserves a completed region's best score.
The score may encode full serialization and reject invalid candidates with
none. This does not justify heuristic costs or an interrupted optimum claim. -/
theorem minimum_score_eq (signature : List Operator) (depth : Nat) (slot : Slot)
    (before : State) (captures : Captures) (values : List Prog) (score : Step → Option Nat)
    (initial : Nat) (nonempty : values ≠ []) :
    ((terms signature depth slot before captures values).filterMap score).foldl min initial =
      ((checked (TemplateGrammar.terms signature depth slot before) captures values).filterMap score).foldl min initial := by
  have bounds (lower : Nat) :
      lower ≤ ((terms signature depth slot before captures values).filterMap score).foldl min initial ↔
        lower ≤ ((checked (TemplateGrammar.terms signature depth slot before) captures values).filterMap score).foldl min initial := by
    rw [lower_le_minimum, lower_le_minimum]
    constructor
    · rintro ⟨bound, all⟩
      exact ⟨bound, fun cost present => all cost ((score_range_iff _ _ _ _ _ _ score cost nonempty).mpr present)⟩
    · rintro ⟨bound, all⟩
      exact ⟨bound, fun cost present => all cost ((score_range_iff _ _ _ _ _ _ score cost nonempty).mp present)⟩
  exact Nat.le_antisymm ((bounds _).mp (Nat.le_refl _)) ((bounds _).mpr (Nat.le_refl _))

namespace CallingConventions

variable {Key : Type*}

/-- The two child continuations choose ready or delayed for the next eligible
port. Only a completed branch is materialized into a source helper. -/
def choices : List Key → List Key → List (List Key)
  | [], chosen => [chosen]
  | first :: rest, chosen => choices rest (first :: chosen) ++ choices rest chosen

theorem choices_mem_iff (available chosen selected : List Key) :
    selected ∈ choices available chosen ↔
      ∃ subset : List Key, subset.Sublist available ∧ selected = subset.reverse ++ chosen := by
  induction available generalizing chosen selected with
  | nil => simp [choices]
  | cons first rest ih =>
      rw [choices, List.mem_append, ih, ih]
      constructor
      · rintro (⟨subset, below, equal⟩ | ⟨subset, below, equal⟩)
        · exact ⟨first :: subset, below.cons_cons first, by simpa using equal⟩
        · exact ⟨subset, below.cons first, equal⟩
      · rintro ⟨subset, below, equal⟩
        cases below with
        | cons _ below => exact Or.inr ⟨_, below, equal⟩
        | cons_cons _ below =>
            exact Or.inl ⟨_, below, by simpa using equal⟩

theorem effective_subset_covered [DecidableEq Key] (available wanted : List Key)
    (included : ∀ key ∈ wanted, key ∈ available) :
    ∃ selected ∈ choices available [], ∀ key, key ∈ selected ↔ key ∈ wanted := by
  let subset := available.filter (fun key => key ∈ wanted)
  refine ⟨subset.reverse, (choices_mem_iff _ _ _).mpr ⟨subset, List.filter_sublist, by simp⟩, ?_⟩
  intro key
  simp only [List.mem_reverse, subset, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun present => ⟨included key present, present⟩⟩

end CallingConventions

end Mettapedia.Algorithms.Compression.GuidedTemplateGrammar
