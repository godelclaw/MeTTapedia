import Mettapedia.Algorithms.Compression.ScopedTemplates
import Mathlib.Data.List.Dedup

/-!
# Corpus-guided scoped refinement

Finite leaf choices describe the admitted ordinary/contextual parameters.
Rigid constructors come from an actual source occurrence and open precisely
their declared binders. Matching is interleaved with generation, retaining one
partial capture accumulator across the whole argument forest. This is a
bounded declared region, not general higher-order anti-unification.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ScopedGuidance

open Mettapedia.OSLF.Binding

variable {S : Signature} {M : List (MetaArity S)} {ordinary : Ctx S}
variable [DecidableEq S.Srt] [opDec : ∀ sort, DecidableEq (S.Op sort)]

abbrev LeafChoices (S : Signature) (M : List (MetaArity S)) (ordinary : Ctx S) :=
  (bound : Ctx S) → (sort : S.Srt) → List (Term (withMetas S M) (bound ++ ordinary) sort)

abbrev Generator (S : Signature) (M : List (MetaArity S)) (ordinary : Ctx S) :=
  (bound : Ctx S) → {sort : S.Srt} → MAcc S M ordinary →
    Term S (bound ++ []) sort →
      List (Term (withMetas S M) (bound ++ ordinary) sort × MAcc S M ordinary)

def leaves (choices : LeafChoices S M ordinary) : Generator S M ordinary :=
  fun bound {sort} before source => (choices bound sort).filterMap fun pattern =>
    (smatchAtT bound before pattern source).map (pattern, ·)

def arguments (generate : Generator S M ordinary) (bound : Ctx S)
    (before : MAcc S M ordinary) : {arity : List (List S.Srt × S.Srt)} →
    Args S arity (bound ++ []) →
      List (Args (withMetas S M) arity (bound ++ ordinary) × MAcc S M ordinary)
  | _, .nil => [(.nil, before)]
  | _, .cons (bs := binders) head tail =>
      (generate (binders ++ bound) before
        (castTermCtx (List.append_assoc binders bound []).symm head)).flatMap fun (pattern, middle) =>
        (arguments generate bound middle tail).map fun (rest, after) =>
          (.cons (castTermCtx (T := withMetas S M) (List.append_assoc binders bound ordinary) pattern) rest, after)

def terms (choices : LeafChoices S M ordinary) : Nat → Generator S M ordinary
  | 0 => leaves choices
  | depth + 1 => fun bound {_sort} before source =>
      leaves choices bound before source ++
        match source with
        | .var _ => []
        | .op constructor children =>
            (arguments (terms choices depth) bound before children).map fun (patterns, after) =>
              (.op (.inl constructor) patterns, after)

theorem leaves_mem_iff (choices : LeafChoices S M ordinary) (bound : Ctx S)
    {sort : S.Srt} (before after : MAcc S M ordinary)
    (source : Term S (bound ++ []) sort)
    (pattern : Term (withMetas S M) (bound ++ ordinary) sort) :
    (pattern, after) ∈ leaves choices bound before source ↔
      pattern ∈ choices bound sort ∧ smatchAtT bound before pattern source = some after := by
  simp only [leaves, List.mem_filterMap]
  constructor
  · rintro ⟨candidate, present, found⟩
    cases matched : smatchAtT bound before candidate source with
    | none => simp [matched] at found
    | some captures =>
        simp only [matched, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
        rcases found with ⟨rfl, rfl⟩
        exact ⟨present, matched⟩
  · rintro ⟨present, found⟩
    exact ⟨pattern, present, by simp [found]⟩

private theorem cast_roundtrip {T : Signature} {first second : Ctx T}
    (same : first = second) {sort : T.Srt} (value : Term T first sort) :
    castTermCtx same.symm (castTermCtx same value) = value := by cases same; rfl

theorem arguments_matched (generate : Generator S M ordinary)
    (sound : ∀ (bound : Ctx S) {sort : S.Srt} (before after : MAcc S M ordinary)
      (source : Term S (bound ++ []) sort)
      (pattern : Term (withMetas S M) (bound ++ ordinary) sort),
      (pattern, after) ∈ generate bound before source →
        smatchAtT bound before pattern source = some after) :
    ∀ {arity : List (List S.Srt × S.Srt)} (bound : Ctx S) (before : MAcc S M ordinary)
      (source : Args S arity (bound ++ []))
      (patterns : Args (withMetas S M) arity (bound ++ ordinary)) (after : MAcc S M ordinary),
      (patterns, after) ∈ arguments generate bound before source →
        smatchAtA bound before patterns source = some after
  | _, bound, before, .nil, patterns, after, found => by
      simp only [arguments, List.mem_singleton, Prod.mk.injEq] at found
      rcases found with ⟨samePattern, sameAfter⟩
      subst patterns
      subst after
      exact smatchAtA_nil bound before
  | _, bound, before, .cons (bs := binders) head tail, patterns, after, found => by
      simp only [arguments, List.mem_flatMap, List.mem_map] at found
      obtain ⟨⟨pattern, middle⟩, first, ⟨rest, final⟩, later, equal⟩ := found
      cases equal
      have one := sound (binders ++ bound) before middle _ pattern first
      have remaining := arguments_matched generate sound bound middle tail rest final later
      rw [smatchAtA, cast_roundtrip, one]
      exact remaining

theorem terms_matched (choices : LeafChoices S M ordinary) (depth : Nat) :
    ∀ (bound : Ctx S) {sort : S.Srt} (before after : MAcc S M ordinary)
      (source : Term S (bound ++ []) sort)
      (pattern : Term (withMetas S M) (bound ++ ordinary) sort),
      (pattern, after) ∈ terms choices depth bound before source →
        smatchAtT bound before pattern source = some after := by
  induction depth with
  | zero =>
      intro bound sort before after source pattern found
      exact ((leaves_mem_iff choices bound before after source pattern).mp found).2
  | succ depth ih =>
      intro bound sort before after source pattern found
      rcases List.mem_append.mp found with leaf | rigid
      · exact ((leaves_mem_iff choices bound before after source pattern).mp leaf).2
      · cases source with
        | var position => simp at rigid
        | op constructor children =>
            obtain ⟨⟨patterns, final⟩, present, equal⟩ := List.mem_map.mp rigid
            cases equal
            have matched := arguments_matched (terms choices depth) ih bound before children patterns after present
            rw [smatchAtT.eq_3, dif_pos rfl]
            exact matched

/-- Candidate syntax without interleaved capture checks. Matching a complete
forest afterward provides an independent specification of early pruning. -/
abbrev Shapes (S : Signature) (M : List (MetaArity S)) (ordinary : Ctx S) :=
  (bound : Ctx S) → {sort : S.Srt} → Term S (bound ++ []) sort →
    List (Term (withMetas S M) (bound ++ ordinary) sort)

def shapeArguments (generate : Shapes S M ordinary) (bound : Ctx S) :
    {arity : List (List S.Srt × S.Srt)} → Args S arity (bound ++ []) →
      List (Args (withMetas S M) arity (bound ++ ordinary))
  | _, .nil => [.nil]
  | _, .cons (bs := binders) head tail =>
      (generate (binders ++ bound)
        (castTermCtx (List.append_assoc binders bound []).symm head)).flatMap fun pattern =>
        (shapeArguments generate bound tail).map fun rest =>
          .cons (castTermCtx (T := withMetas S M)
            (List.append_assoc binders bound ordinary) pattern) rest

def shapes (choices : LeafChoices S M ordinary) : Nat → Shapes S M ordinary
  | 0 => fun bound {sort} _ => choices bound sort
  | depth + 1 => fun bound {sort} source =>
      choices bound sort ++ match source with
        | .var _ => []
        | .op constructor children =>
            (shapeArguments (shapes choices depth) bound children).map
              (fun patterns => .op (.inl constructor) patterns)

omit [DecidableEq S.Srt] opDec in
theorem arguments_shape (generate : Generator S M ordinary) (raw : Shapes S M ordinary)
    (included : ∀ (bound : Ctx S) {sort : S.Srt} (before after : MAcc S M ordinary)
      (source : Term S (bound ++ []) sort)
      (pattern : Term (withMetas S M) (bound ++ ordinary) sort),
      (pattern, after) ∈ generate bound before source → pattern ∈ raw bound source) :
    ∀ {arity : List (List S.Srt × S.Srt)} (bound : Ctx S) (before : MAcc S M ordinary)
      (source : Args S arity (bound ++ []))
      (patterns : Args (withMetas S M) arity (bound ++ ordinary)) (after : MAcc S M ordinary),
      (patterns, after) ∈ arguments generate bound before source →
        patterns ∈ shapeArguments raw bound source
  | _, bound, before, .nil, patterns, after, found => by
      simp only [arguments, List.mem_singleton, Prod.mk.injEq] at found
      cases found.1
      exact List.mem_singleton_self _
  | _, bound, before, .cons head tail, patterns, after, found => by
      simp only [arguments, List.mem_flatMap, List.mem_map] at found
      obtain ⟨⟨pattern, middle⟩, first, ⟨rest, final⟩, later, equal⟩ := found
      cases equal
      exact List.mem_flatMap.mpr ⟨pattern, included _ before middle _ pattern first,
        List.mem_map.mpr ⟨rest, arguments_shape generate raw included bound middle tail rest final later, rfl⟩⟩

theorem arguments_complete (generate : Generator S M ordinary) (raw : Shapes S M ordinary)
    (complete : ∀ (bound : Ctx S) {sort : S.Srt} (before after : MAcc S M ordinary)
      (source : Term S (bound ++ []) sort)
      (pattern : Term (withMetas S M) (bound ++ ordinary) sort),
      pattern ∈ raw bound source → smatchAtT bound before pattern source = some after →
        (pattern, after) ∈ generate bound before source) :
    ∀ {arity : List (List S.Srt × S.Srt)} (bound : Ctx S) (before : MAcc S M ordinary)
      (source : Args S arity (bound ++ []))
      (patterns : Args (withMetas S M) arity (bound ++ ordinary)) (after : MAcc S M ordinary),
      patterns ∈ shapeArguments raw bound source →
      smatchAtA bound before patterns source = some after →
        (patterns, after) ∈ arguments generate bound before source
  | _, bound, before, .nil, patterns, after, present, matched => by
      simp only [shapeArguments, List.mem_singleton] at present
      cases present
      have equal : before = after := Option.some.inj (by simpa only [smatchAtA_nil] using matched)
      cases equal
      exact List.mem_singleton_self _
  | _, bound, before, .cons head tail, patterns, after, present, matched => by
      simp only [shapeArguments, List.mem_flatMap, List.mem_map] at present
      obtain ⟨pattern, first, rest, later, equal⟩ := present
      cases equal
      rw [smatchAtA, cast_roundtrip] at matched
      cases headMatch : smatchAtT _ before pattern
        (castTermCtx (List.append_assoc _ bound []).symm head) with
      | none => simp [headMatch] at matched
      | some middle =>
          simp only [headMatch] at matched
          exact List.mem_flatMap.mpr ⟨(pattern, middle), complete _ before middle _ pattern first headMatch,
            List.mem_map.mpr ⟨(rest, after), arguments_complete generate raw complete bound middle
              tail rest after later matched, rfl⟩⟩

theorem terms_mem_iff (choices : LeafChoices S M ordinary) (depth : Nat) :
    ∀ (bound : Ctx S) {sort : S.Srt} (before after : MAcc S M ordinary)
      (source : Term S (bound ++ []) sort)
      (pattern : Term (withMetas S M) (bound ++ ordinary) sort),
      (pattern, after) ∈ terms choices depth bound before source ↔
        pattern ∈ shapes choices depth bound source ∧
          smatchAtT bound before pattern source = some after := by
  induction depth with
  | zero =>
      intro bound sort before after source pattern
      exact leaves_mem_iff choices bound before after source pattern
  | succ depth ih =>
      intro bound sort before after source pattern
      constructor
      · intro found
        refine ⟨?_, terms_matched choices _ bound before after source pattern found⟩
        rcases List.mem_append.mp found with leaf | rigid
        · exact List.mem_append_left _ ((leaves_mem_iff choices bound before after source pattern).mp leaf).1
        · cases source with
          | var position => simp at rigid
          | op constructor children =>
              obtain ⟨⟨patterns, final⟩, present, equal⟩ := List.mem_map.mp rigid
              cases equal
              exact List.mem_append_right _ (List.mem_map.mpr ⟨patterns,
                arguments_shape (terms choices depth) (shapes choices depth)
                  (fun bound _ before after source pattern found => (ih bound before after source pattern).mp found |>.1)
                  bound before children patterns after present, rfl⟩)
      · rintro ⟨present, matched⟩
        rcases List.mem_append.mp present with leaf | rigid
        · exact List.mem_append_left _ ((leaves_mem_iff choices bound before after source pattern).mpr ⟨leaf, matched⟩)
        · cases source with
          | var position => simp at rigid
          | op constructor children =>
              obtain ⟨patterns, raw, equal⟩ := List.mem_map.mp rigid
              cases equal
              rw [smatchAtT.eq_3, dif_pos rfl] at matched
              exact List.mem_append_right _ (List.mem_map.mpr ⟨(patterns, after),
                arguments_complete (terms choices depth) (shapes choices depth)
                  (fun bound _ before after source pattern raw found =>
                    (ih bound before after source pattern).mpr ⟨raw, found⟩)
                  bound before children patterns after raw matched, rfl⟩)

/-- Every generated template independently expands to its guide, using only
the partial captures actually found. Unused parameters need no inhabitants. -/
theorem terms_reconstruct (choices : LeafChoices S M ordinary) (depth : Nat)
    (bound : Ctx S) {sort : S.Srt} (before after : MAcc S M ordinary)
    (source : Term S (bound ++ []) sort)
    (pattern : Term (withMetas S M) (bound ++ ordinary) sort)
    (present : (pattern, after) ∈ terms choices depth bound before source) :
    ScopedTemplates.expandAtT bound after pattern = some source :=
  ScopedTemplates.matched_expandsAtT bound before after after pattern source
    (terms_matched choices depth bound before after source pattern present) (MAccLe.refl _)

private theorem flatMap_filterMap_option {A B C : Type} (items : List A)
    (select : A → Option B) (next : B → List C) :
    (items.filterMap select).flatMap next =
      items.flatMap (fun item => (select item).toList.flatMap next) := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases found : select item <;> simp [found, ih]

/-- Interleaved matching preserves the full ordered candidate account,
including repeated candidates, rather than merely its set of members. -/
theorem arguments_eq_late (generate : Generator S M ordinary) (raw : Shapes S M ordinary)
    (realizes : ∀ (bound : Ctx S) {sort : S.Srt} (before : MAcc S M ordinary)
      (source : Term S (bound ++ []) sort),
      generate bound before source = (raw bound source).filterMap fun pattern =>
        (smatchAtT bound before pattern source).map (pattern, ·)) :
    ∀ {arity : List (List S.Srt × S.Srt)} (bound : Ctx S) (before : MAcc S M ordinary)
      (source : Args S arity (bound ++ [])),
    arguments generate bound before source =
      (shapeArguments raw bound source).filterMap fun patterns =>
        (smatchAtA bound before patterns source).map (patterns, ·)
  | _, bound, before, .nil => by simp [arguments, shapeArguments]
  | _, bound, before, .cons (bs := binders) head tail => by
      simp only [arguments, shapeArguments, realizes, flatMap_filterMap_option,
        List.filterMap_flatMap]
      apply List.flatMap_congr
      intro pattern _
      cases matched : smatchAtT (binders ++ bound) before pattern
        (castTermCtx (List.append_assoc binders bound []).symm head) with
      | none => simp [matched, List.filterMap_map, smatchAtA, cast_roundtrip]
      | some middle =>
          simp only [Option.map_some, Option.toList_some, List.flatMap_singleton]
          rw [arguments_eq_late generate raw realizes bound middle tail]
          simp only [List.map_filterMap, List.filterMap_map, Function.comp_def]
          apply List.filterMap_congr
          intro patterns _
          simp only [smatchAtA, cast_roundtrip, matched]
          cases smatchAtA bound middle patterns tail <;> rfl

theorem terms_eq_late (choices : LeafChoices S M ordinary) (depth : Nat) :
    ∀ (bound : Ctx S) {sort : S.Srt} (before : MAcc S M ordinary)
      (source : Term S (bound ++ []) sort),
    terms choices depth bound before source =
      (shapes choices depth bound source).filterMap fun pattern =>
        (smatchAtT bound before pattern source).map (pattern, ·) := by
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro bound sort before source
      cases source with
      | var position => simp [terms, shapes, leaves]
      | op constructor children =>
          simp only [terms, shapes, List.filterMap_append, leaves]
          congr 1
          rw [arguments_eq_late (terms choices depth) (shapes choices depth) ih]
          simp only [List.map_filterMap, List.filterMap_map, Function.comp_def]
          apply List.filterMap_congr
          intro patterns _
          rw [smatchAtT.eq_3, dif_pos rfl]
          change ((smatchAtA bound before patterns children).map (patterns, ·)).map
              (fun pair => ((Term.op (Sum.inl constructor) pair.1 :
                Term (withMetas S M) (bound ++ ordinary) sort), pair.2)) =
            (smatchAtA bound before patterns children).map
              (fun captures => ((Term.op (Sum.inl constructor) patterns :
                Term (withMetas S M) (bound ++ ordinary) sort), captures))
          cases smatchAtA bound before patterns children <;> rfl

end Mettapedia.Algorithms.Compression.ScopedGuidance
