import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.OSLF.MeTTaIL.ScopedPattern
import Mathlib.Data.List.GetD

/-!
# Canonical forms commute with order-preserving renamings

A capture recovers a metavariable's value by renaming the indices of the captured term: the
spine's local variables become the value's dependencies and the ambient ones move past them.
On a canonical subject, the recovered value is canonical exactly when the renaming keeps the
canonical order. This holds for every strictly monotone renaming of the free indices:

- `lexLe_rename`: comparing serializations is invariant under a strictly monotone renaming, at
  every binder depth (bound indices stay fixed and below the renamed free ones);
- `sortLex_map`, `arrange_map`: sorting, and removing a set's repetitions, commute with every map
  that keeps the order;
- `canon_rename`: the canonical form of a renamed term is the renamed canonical form.

Negative control: an order-reversing renaming does not commute with sorting
(`canon_reverse_not_rename`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax PatternLexOrder
open ContextSubstitution (substitute substituteList lift)

/-! ## Lexicographic comparison of prefix-free codes -/

theorem lexLe_cons_same (x : Nat) (left right : List Nat) : lexLe (x :: left) (x :: right) = lexLe left right := by
  simp [lexLe]

theorem lexLe_cons_ne {x y : Nat} (different : x ≠ y) (left right : List Nat) :
    lexLe (x :: left) (y :: right) = decide (x < y) := by
  simp [lexLe, different]

theorem lexLe_append_same : ∀ (common left right : List Nat), lexLe (common ++ left) (common ++ right) = lexLe left right
  | [], _, _ => rfl
  | x :: common, left, right => by rw [List.cons_append, List.cons_append, lexLe_cons_same, lexLe_append_same]

/-- Two lists neither of which extends the other diverge at a common position. -/
theorem exists_diverge : ∀ (left right : List Nat), ¬ left <+: right → ¬ right <+: left →
    ∃ common x y left' right', left = common ++ x :: left' ∧ right = common ++ y :: right' ∧ x ≠ y
  | [], _, notPrefix, _ => absurd (List.nil_prefix) notPrefix
  | _ :: _, [], _, notPrefix => absurd (List.nil_prefix) notPrefix
  | x :: left, y :: right, notLeft, notRight => by
    by_cases same : x = y
    · subst same
      have notLeft' : ¬ left <+: right := fun extended => notLeft (List.cons_prefix_cons.mpr ⟨rfl, extended⟩)
      have notRight' : ¬ right <+: left := fun extended => notRight (List.cons_prefix_cons.mpr ⟨rfl, extended⟩)
      obtain ⟨common, a, b, left', right', rfl, rfl, different⟩ := exists_diverge left right notLeft' notRight'
      exact ⟨x :: common, a, b, left', right', rfl, rfl, different⟩
    · exact ⟨[], x, y, left, right, rfl, rfl, same⟩

/-- The comparison of two diverging lists does not depend on what follows them. -/
theorem lexLe_independent {left right : List Nat} (notLeft : ¬ left <+: right) (notRight : ¬ right <+: left)
    (after after' rest rest' : List Nat) :
    lexLe (left ++ after) (right ++ rest) = lexLe (left ++ after') (right ++ rest') := by
  obtain ⟨common, x, y, left', right', rfl, rfl, different⟩ := exists_diverge left right notLeft notRight
  simp only [List.append_assoc, List.cons_append, lexLe_append_same, lexLe_cons_ne different]

/-- Codewords of a prefix-free code never extend one another. -/
theorem not_prefix_of_code {β : Type} {code : β → List Nat}
    (prefixFree : ∀ x y (rest rest' : List Nat), code x ++ rest = code y ++ rest' → x = y)
    {x y : β} (different : x ≠ y) : ¬ code x <+: code y := by
  rintro ⟨rest, extended⟩
  exact different (prefixFree x y rest [] (by rw [extended, List.append_nil]))

/-- **Compare one component, then the rest**: the comparison of two prefix-free codewords
followed by continuations is decided by the codewords when they differ, and by the
continuations otherwise. -/
theorem lexLe_component {β : Type} {code : β → List Nat}
    (prefixFree : ∀ x y (rest rest' : List Nat), code x ++ rest = code y ++ rest' → x = y)
    (x y : β) {after rest after' rest' : List Nat} (continued : x = y → lexLe after rest = lexLe after' rest') :
    lexLe (code x ++ after) (code y ++ rest) = lexLe (code x ++ after') (code y ++ rest') := by
  by_cases same : x = y
  · subst same; rw [lexLe_append_same, lexLe_append_same]; exact continued rfl
  · exact lexLe_independent (not_prefix_of_code prefixFree same) (not_prefix_of_code prefixFree (Ne.symm same)) _ _ _ _

theorem serString_prefixFree : ∀ (x y : String) (rest rest' : List Nat), serString x ++ rest = serString y ++ rest' → x = y :=
  fun _ _ _ _ same => (serString_prefix same).1

theorem serOptString_prefixFree :
    ∀ (x y : Option String) (rest rest' : List Nat), serOptString x ++ rest = serOptString y ++ rest' → x = y :=
  fun _ _ _ _ same => (serOptString_prefix same).1

theorem serStringList_prefixFree :
    ∀ (x y : List String) (rest rest' : List Nat), serStringList x ++ rest = serStringList y ++ rest' → x = y :=
  fun _ _ _ _ same => (serStringList_prefix same).1

theorem ser_prefixFree : ∀ (x y : Pattern) (rest rest' : List Nat), ser x ++ rest = ser y ++ rest' → x = y :=
  fun x y _ _ same => (ser_prefix x y same).1

theorem natCode_prefixFree : ∀ (x y : Nat) (rest rest' : List Nat), [x] ++ rest = [y] ++ rest' → x = y := by
  intro x y _ _ same
  simp only [List.singleton_append, List.cons.injEq] at same
  exact same.1

/-! ## Order-preserving renamings -/

/-- `FreeIn index pattern`: the index occurs free in the pattern. -/
inductive FreeIn : Nat → Pattern → Prop where
  | bvar (index : Nat) : FreeIn index (.bvar index)
  | apply {index : Nat} {label : String} {arguments : List Pattern} {argument : Pattern} :
      argument ∈ arguments → FreeIn index argument → FreeIn index (.apply label arguments)
  | lambda {index : Nat} {binder : Option String} {body : Pattern} :
      FreeIn (index + 1) body → FreeIn index (.lambda binder body)
  | multiLambda {index arity : Nat} {binders : List String} {body : Pattern} :
      FreeIn (index + arity) body → FreeIn index (.multiLambda arity binders body)
  | substBody {index : Nat} {body replacement : Pattern} :
      FreeIn (index + 1) body → FreeIn index (.subst body replacement)
  | substReplacement {index : Nat} {body replacement : Pattern} :
      FreeIn index replacement → FreeIn index (.subst body replacement)
  | element {index : Nat} {kind : CollType} {elements : List Pattern} {element : Pattern} {rest : Option String} :
      element ∈ elements → FreeIn index element → FreeIn index (.collection kind elements rest)

/-- The free indices of a pattern lie in a set. -/
def FreeWithin (indices : Set Nat) (pattern : Pattern) : Prop := ∀ index, FreeIn index pattern → index ∈ indices

/-- A renaming of free indices under `cutoff` binders: bound indices stay, free ones are renamed
and moved past the bound ones. -/
def liftIndex (cutoff : Nat) (rename : Nat → Nat) (index : Nat) : Nat :=
  if index < cutoff then index else rename (index - cutoff) + cutoff

/-- The indices under `cutoff` binders that are bound, or free with their outer index in a set. -/
def liftSet (cutoff : Nat) (indices : Set Nat) : Set Nat := {index | index < cutoff ∨ index - cutoff ∈ indices}

theorem liftIndex_strictMonoOn {rename : Nat → Nat} {indices : Set Nat} (mono : StrictMonoOn rename indices)
    (cutoff : Nat) : StrictMonoOn (liftIndex cutoff rename) (liftSet cutoff indices) := by
  intro a inA b inB less
  unfold liftIndex
  by_cases small : a < cutoff <;> by_cases small' : b < cutoff <;> simp only [small, small', if_true, if_false]
  · exact less
  · omega
  · omega
  · have a' : a - cutoff ∈ indices := inA.resolve_left small
    have b' : b - cutoff ∈ indices := inB.resolve_left small'
    have := mono a' b' (show a - cutoff < b - cutoff by omega); omega

theorem FreeWithin.lambda {indices : Set Nat} {binder : Option String} {body : Pattern}
    (within : FreeWithin indices (.lambda binder body)) : FreeWithin (liftSet 1 indices) body := by
  intro index free
  by_cases small : index < 1
  · exact .inl small
  · exact .inr (within _ (.lambda (by rwa [Nat.sub_add_cancel (by omega)])))

theorem FreeWithin.multiLambda {indices : Set Nat} {arity : Nat} {binders : List String} {body : Pattern}
    (within : FreeWithin indices (.multiLambda arity binders body)) : FreeWithin (liftSet arity indices) body := by
  intro index free
  by_cases small : index < arity
  · exact .inl small
  · exact .inr (within _ (.multiLambda (by rwa [Nat.sub_add_cancel (by omega)])))

theorem FreeWithin.substBody {indices : Set Nat} {body replacement : Pattern}
    (within : FreeWithin indices (.subst body replacement)) : FreeWithin (liftSet 1 indices) body := by
  intro index free
  by_cases small : index < 1
  · exact .inl small
  · exact .inr (within _ (.substBody (by rwa [Nat.sub_add_cancel (by omega)])))

theorem FreeWithin.substReplacement {indices : Set Nat} {body replacement : Pattern}
    (within : FreeWithin indices (.subst body replacement)) : FreeWithin indices replacement :=
  fun _ free => within _ (.substReplacement free)

theorem FreeWithin.argument {indices : Set Nat} {label : String} {arguments : List Pattern} {argument : Pattern}
    (within : FreeWithin indices (.apply label arguments)) (member : argument ∈ arguments) :
    FreeWithin indices argument :=
  fun _ free => within _ (.apply member free)

theorem FreeWithin.element {indices : Set Nat} {kind : CollType} {elements : List Pattern} {rest : Option String}
    {element : Pattern} (within : FreeWithin indices (.collection kind elements rest)) (member : element ∈ elements) :
    FreeWithin indices element :=
  fun _ free => within _ (.element member free)

/-- The index renaming as a substitution. -/
abbrev indexRenaming (rename : Nat → Nat) : ContextSubstitution.Assignment := fun index => .bvar (rename index)

theorem lift_renaming (arity : Nat) (rename : Nat → Nat) :
    lift arity (indexRenaming rename) = indexRenaming (liftIndex arity rename) := by
  funext index
  unfold lift liftIndex
  by_cases small : index < arity
  · simp [small]
  · simp [small, Substitution.liftBVars]

/-! ## Comparison is invariant under order-preserving renamings -/

mutual
  theorem lexLe_rename : ∀ (rename : Nat → Nat) (indices : Set Nat), StrictMonoOn rename indices →
      ∀ (left right : Pattern), FreeWithin indices left → FreeWithin indices right → ∀ (rest rest' : List Nat),
      lexLe (ser (substitute (indexRenaming rename) left) ++ rest) (ser (substitute (indexRenaming rename) right) ++ rest') =
        lexLe (ser left ++ rest) (ser right ++ rest')
    | rename, _, mono, .bvar a, .bvar b, withinLeft, withinRight, rest, rest' => by
      simp only [substitute, ser, List.cons_append, List.nil_append, lexLe_cons_same]
      have inA := withinLeft a (.bvar a)
      have inB := withinRight b (.bvar b)
      have same : (rename a == rename b) = (a == b) := by
        simp only [beq_eq_decide, (mono.injOn).eq_iff inA inB]
      simp only [lexLe, mono.lt_iff_lt inA inB, same]
    | _, _, _, .fvar a, .fvar b, _, _, rest, rest' => by simp only [substitute]
    | rename, indices, mono, .apply c args, .apply d args', withinLeft, withinRight, rest, rest' => by
      simp only [substitute, ContextSubstitution.substituteList_eq_map, ser, List.cons_append, List.append_assoc,
        lexLe_cons_same, List.length_map]
      apply lexLe_component serString_prefixFree c d
      intro _
      by_cases lengths : args.length = args'.length
      · rw [lengths, lexLe_cons_same, lexLe_cons_same]
        exact lexLe_renameList rename indices mono args args' (fun _ member => withinLeft.argument member)
          (fun _ member => withinRight.argument member) lengths rest rest'
      · rw [lexLe_cons_ne lengths, lexLe_cons_ne lengths]
    | rename, indices, mono, .lambda a body, .lambda b body', withinLeft, withinRight, rest, rest' => by
      simp only [substitute, lift_renaming, ser, List.cons_append, List.append_assoc, lexLe_cons_same]
      apply lexLe_component serOptString_prefixFree a b
      intro _
      exact lexLe_rename _ _ (liftIndex_strictMonoOn mono 1) body body' withinLeft.lambda withinRight.lambda rest rest'
    | rename, indices, mono, .multiLambda n bs body, .multiLambda m cs body', withinLeft, withinRight, rest, rest' => by
      simp only [substitute, lift_renaming, ser, List.cons_append, List.append_assoc, lexLe_cons_same]
      by_cases arities : n = m
      · subst arities
        rw [lexLe_cons_same, lexLe_cons_same]
        apply lexLe_component serStringList_prefixFree bs cs
        intro _
        exact lexLe_rename _ _ (liftIndex_strictMonoOn mono n) body body' withinLeft.multiLambda
          withinRight.multiLambda rest rest'
      · rw [lexLe_cons_ne arities, lexLe_cons_ne arities]
    | rename, indices, mono, .subst body replacement, .subst body' replacement', withinLeft, withinRight, rest, rest' => by
      simp only [substitute, lift_renaming, ser, List.cons_append, List.append_assoc, lexLe_cons_same]
      rw [lexLe_rename _ _ (liftIndex_strictMonoOn mono 1) body body' withinLeft.substBody withinRight.substBody]
      apply lexLe_component ser_prefixFree body body'
      intro _
      exact lexLe_rename rename indices mono replacement replacement' withinLeft.substReplacement
        withinRight.substReplacement rest rest'
    | rename, indices, mono, .collection k es r, .collection k' es' r', withinLeft, withinRight, rest, rest' => by
      simp only [substitute, ContextSubstitution.substituteList_eq_map, ser, List.cons_append, List.append_assoc,
        lexLe_cons_same, List.length_map]
      by_cases kinds : collectionTag k = collectionTag k'
      · rw [kinds, lexLe_cons_same, lexLe_cons_same]
        by_cases lengths : es.length = es'.length
        · rw [lengths, lexLe_cons_same, lexLe_cons_same]
          rw [lexLe_renameList rename indices mono es es' (fun _ member => withinLeft.element member)
            (fun _ member => withinRight.element member) lengths]
        · rw [lexLe_cons_ne lengths, lexLe_cons_ne lengths]
      · rw [lexLe_cons_ne kinds, lexLe_cons_ne kinds]
    | _, _, _, .bvar _, .fvar _, _, _, _, _ | _, _, _, .bvar _, .apply _ _, _, _, _, _
    | _, _, _, .bvar _, .lambda _ _, _, _, _, _
    | _, _, _, .bvar _, .multiLambda _ _ _, _, _, _, _ | _, _, _, .bvar _, .subst _ _, _, _, _, _
    | _, _, _, .bvar _, .collection _ _ _, _, _, _, _
    | _, _, _, .fvar _, .bvar _, _, _, _, _ | _, _, _, .fvar _, .apply _ _, _, _, _, _
    | _, _, _, .fvar _, .lambda _ _, _, _, _, _
    | _, _, _, .fvar _, .multiLambda _ _ _, _, _, _, _ | _, _, _, .fvar _, .subst _ _, _, _, _, _
    | _, _, _, .fvar _, .collection _ _ _, _, _, _, _
    | _, _, _, .apply _ _, .bvar _, _, _, _, _ | _, _, _, .apply _ _, .fvar _, _, _, _, _
    | _, _, _, .apply _ _, .lambda _ _, _, _, _, _
    | _, _, _, .apply _ _, .multiLambda _ _ _, _, _, _, _ | _, _, _, .apply _ _, .subst _ _, _, _, _, _
    | _, _, _, .apply _ _, .collection _ _ _, _, _, _, _
    | _, _, _, .lambda _ _, .bvar _, _, _, _, _ | _, _, _, .lambda _ _, .fvar _, _, _, _, _
    | _, _, _, .lambda _ _, .apply _ _, _, _, _, _
    | _, _, _, .lambda _ _, .multiLambda _ _ _, _, _, _, _ | _, _, _, .lambda _ _, .subst _ _, _, _, _, _
    | _, _, _, .lambda _ _, .collection _ _ _, _, _, _, _
    | _, _, _, .multiLambda _ _ _, .bvar _, _, _, _, _ | _, _, _, .multiLambda _ _ _, .fvar _, _, _, _, _
    | _, _, _, .multiLambda _ _ _, .apply _ _, _, _, _, _ | _, _, _, .multiLambda _ _ _, .lambda _ _, _, _, _, _
    | _, _, _, .multiLambda _ _ _, .subst _ _, _, _, _, _ | _, _, _, .multiLambda _ _ _, .collection _ _ _, _, _, _, _
    | _, _, _, .subst _ _, .bvar _, _, _, _, _ | _, _, _, .subst _ _, .fvar _, _, _, _, _
    | _, _, _, .subst _ _, .apply _ _, _, _, _, _
    | _, _, _, .subst _ _, .lambda _ _, _, _, _, _ | _, _, _, .subst _ _, .multiLambda _ _ _, _, _, _, _
    | _, _, _, .subst _ _, .collection _ _ _, _, _, _, _
    | _, _, _, .collection _ _ _, .bvar _, _, _, _, _ | _, _, _, .collection _ _ _, .fvar _, _, _, _, _
    | _, _, _, .collection _ _ _, .apply _ _, _, _, _, _ | _, _, _, .collection _ _ _, .lambda _ _, _, _, _, _
    | _, _, _, .collection _ _ _, .multiLambda _ _ _, _, _, _, _ | _, _, _, .collection _ _ _, .subst _ _, _, _, _, _ => by
      simp [substitute, ser, lexLe]

  theorem lexLe_renameList : ∀ (rename : Nat → Nat) (indices : Set Nat), StrictMonoOn rename indices →
      ∀ (left right : List Pattern), (∀ item ∈ left, FreeWithin indices item) → (∀ item ∈ right, FreeWithin indices item) →
      left.length = right.length → ∀ (rest rest' : List Nat),
      lexLe (serList (left.map (substitute (indexRenaming rename))) ++ rest)
          (serList (right.map (substitute (indexRenaming rename))) ++ rest') =
        lexLe (serList left ++ rest) (serList right ++ rest')
    | _, _, _, [], [], _, _, _, _, _ => by simp [serList]
    | _, _, _, _ :: _, [], _, _, lengths, _, _ => by simp at lengths
    | _, _, _, [], _ :: _, _, _, lengths, _, _ => by simp at lengths
    | rename, indices, mono, a :: left, b :: right, withinLeft, withinRight, lengths, rest, rest' => by
      simp only [List.map_cons, serList, List.append_assoc]
      rw [lexLe_rename rename indices mono a b (withinLeft a (.head _)) (withinRight b (.head _))]
      apply lexLe_component ser_prefixFree a b
      intro _
      exact lexLe_renameList rename indices mono left right (fun item member => withinLeft item (.tail _ member))
        (fun item member => withinRight item (.tail _ member)) (by simpa using lengths) rest rest'
end

theorem patternLe_rename {rename : Nat → Nat} {indices : Set Nat} (mono : StrictMonoOn rename indices)
    {left right : Pattern} (withinLeft : FreeWithin indices left) (withinRight : FreeWithin indices right) :
    PatternLe (substitute (indexRenaming rename) left) (substitute (indexRenaming rename) right) ↔ PatternLe left right := by
  unfold PatternLe
  have same := lexLe_rename rename indices mono left right withinLeft withinRight [] []
  simp only [List.append_nil] at same
  rw [same]

/-! ## Sorting and canonical forms commute with order-preserving maps -/

/-- **Sorting commutes with every map that keeps the order of the sorted items.** -/
theorem sortLex_map {f : Pattern → Pattern} {patterns : List Pattern}
    (keeps : ∀ left ∈ patterns, ∀ right ∈ patterns, PatternLe (f left) (f right) ↔ PatternLe left right) :
    sortLex (patterns.map f) = (sortLex patterns).map f := by
  have members : ∀ item, item ∈ sortLex patterns → item ∈ patterns := fun item member =>
    (sortLex_perm patterns).mem_iff.mp member
  refine List.Perm.eq_of_pairwise' (sortLex_pairwise _) ?_
    ((sortLex_perm _).trans ((sortLex_perm patterns).symm.map f))
  rw [List.pairwise_map]
  exact (sortLex_pairwise patterns).imp_of_mem fun inLeft inRight ordered =>
    (keeps _ (members _ inLeft) _ (members _ inRight)).mpr ordered

/-- Removing repetitions commutes with a map that is injective on the list. -/
theorem dedup_map_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β} :
    ∀ {items : List α}, (∀ left ∈ items, ∀ right ∈ items, f left = f right → left = right) →
      (items.map f).dedup = items.dedup.map f
  | [], _ => rfl
  | item :: rest, injective => by
    have tail := dedup_map_of_injOn (items := rest) fun left inLeft right inRight =>
      injective left (.tail _ inLeft) right (.tail _ inRight)
    rw [List.map_cons]
    by_cases member : item ∈ rest
    · rw [List.dedup_cons_of_mem member, List.dedup_cons_of_mem (List.mem_map_of_mem member), tail]
    · have image : f item ∉ rest.map f := by
        intro inImage
        obtain ⟨other, inRest, same⟩ := List.mem_map.mp inImage
        exact member (injective other (.tail _ inRest) item (.head _) same ▸ inRest)
      rw [List.dedup_cons_of_notMem member, List.dedup_cons_of_notMem image, List.map_cons, tail]

/-- **Arranging commutes with every map that keeps the order of the items**: such a map is
injective on them, so it also commutes with removing a set's repetitions. -/
theorem arrange_map {f : Pattern → Pattern} {patterns : List Pattern}
    (keeps : ∀ left ∈ patterns, ∀ right ∈ patterns, PatternLe (f left) (f right) ↔ PatternLe left right)
    (kind : CollType) : arrange kind (patterns.map f) = (arrange kind patterns).map f := by
  cases kind with
  | vec => rfl
  | hashBag => exact sortLex_map keeps
  | hashSet =>
    rw [arrange_set, arrange_set, sortLex_map keeps]
    apply dedup_map_of_injOn
    intro left inLeft right inRight same
    have inLeft' := (sortLex_perm patterns).mem_iff.mp inLeft
    have inRight' := (sortLex_perm patterns).mem_iff.mp inRight
    have reflexive : ∀ pattern, PatternLe pattern pattern := fun pattern => lexLe_refl (ser pattern)
    exact Std.Antisymm.antisymm (r := PatternLe) left right
      ((keeps left inLeft' right inRight').mp (by rw [same]; exact reflexive _))
      ((keeps right inRight' left inLeft').mp (by rw [same]; exact reflexive _))

theorem freeIn_bvar {index other : Nat} : FreeIn index (.bvar other) ↔ index = other := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact .bvar _

theorem freeIn_apply {index : Nat} {label : String} {arguments : List Pattern} :
    FreeIn index (.apply label arguments) ↔ ∃ argument ∈ arguments, FreeIn index argument := by
  constructor
  · rintro (_ | ⟨member, free⟩); exact ⟨_, member, free⟩
  · rintro ⟨_, member, free⟩; exact .apply member free

theorem freeIn_lambda {index : Nat} {binder : Option String} {body : Pattern} :
    FreeIn index (.lambda binder body) ↔ FreeIn (index + 1) body := by
  constructor
  · rintro (_ | _ | free); exact free
  · exact .lambda

theorem freeIn_multiLambda {index arity : Nat} {binders : List String} {body : Pattern} :
    FreeIn index (.multiLambda arity binders body) ↔ FreeIn (index + arity) body := by
  constructor
  · rintro (_ | _ | _ | free); exact free
  · exact .multiLambda

theorem freeIn_subst {index : Nat} {body replacement : Pattern} :
    FreeIn index (.subst body replacement) ↔ FreeIn (index + 1) body ∨ FreeIn index replacement := by
  constructor
  · rintro (_ | _ | _ | _ | free | free)
    · exact .inl free
    · exact .inr free
  · rintro (free | free)
    · exact .substBody free
    · exact .substReplacement free

theorem freeIn_collection {index : Nat} {kind : CollType} {elements : List Pattern} {rest : Option String} :
    FreeIn index (.collection kind elements rest) ↔ ∃ element ∈ elements, FreeIn index element := by
  constructor
  · rintro (_ | _ | _ | _ | _ | _ | ⟨member, free⟩); exact ⟨_, member, free⟩
  · rintro ⟨_, member, free⟩; exact .element member free

private theorem exists_middle {P Q : Pattern → Prop} {before after : List Pattern} {x y : Pattern}
    (same : P x ↔ Q y) (others : ∀ item, P item ↔ Q item) :
    (∃ item ∈ before ++ x :: after, P item) ↔ (∃ item ∈ before ++ y :: after, Q item) := by
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨item, (inBefore | rfl | inAfter), holds⟩
    · exact ⟨item, .inl inBefore, (others item).mp holds⟩
    · exact ⟨y, .inr (.inl rfl), same.mp holds⟩
    · exact ⟨item, .inr (.inr inAfter), (others item).mp holds⟩
  · rintro ⟨item, (inBefore | rfl | inAfter), holds⟩
    · exact ⟨item, .inl inBefore, (others item).mpr holds⟩
    · exact ⟨x, .inr (.inl rfl), same.mpr holds⟩
    · exact ⟨item, .inr (.inr inAfter), (others item).mpr holds⟩

/-- A permutation keeps the free indices. -/
theorem BagStep.freeIn {left right : Pattern} (step : BagStep left right) :
    ∀ index, FreeIn index left ↔ FreeIn index right := by
  induction step with
  | permute _ permutation =>
    intro index
    simp only [freeIn_collection]
    exact ⟨fun ⟨item, member, free⟩ => ⟨item, permutation.mem_iff.mp member, free⟩,
      fun ⟨item, member, free⟩ => ⟨item, permutation.mem_iff.mpr member, free⟩⟩
  | members same =>
    intro index
    simp only [freeIn_collection]
    exact ⟨fun ⟨item, member, free⟩ => ⟨item, (same item).mp member, free⟩,
      fun ⟨item, member, free⟩ => ⟨item, (same item).mpr member, free⟩⟩
  | apply _ ih =>
    intro index
    simp only [freeIn_apply]
    exact exists_middle (ih index) (fun _ => Iff.rfl)
  | lambda _ ih => intro index; simp only [freeIn_lambda]; exact ih _
  | multiLambda _ ih => intro index; simp only [freeIn_multiLambda]; exact ih _
  | substBody _ ih => intro index; simp only [freeIn_subst]; rw [ih]
  | substReplacement _ ih => intro index; simp only [freeIn_subst]; rw [ih]
  | element _ ih =>
    intro index
    simp only [freeIn_collection]
    exact exists_middle (ih index) (fun _ => Iff.rfl)

theorem freeIn_canon (index : Nat) (pattern : Pattern) : FreeIn index (canon pattern) ↔ FreeIn index pattern := by
  have related := to_canon pattern
  suffices keeps : ∀ left right, Relation.EqvGen BagStep left right → (FreeIn index left ↔ FreeIn index right) from
    (keeps _ _ related).symm
  intro left right related
  induction related with
  | rel _ _ step => exact step.freeIn index
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- Canonical forms keep the free indices. -/
theorem FreeWithin.canon {indices : Set Nat} : ∀ {pattern : Pattern}, FreeWithin indices pattern →
    FreeWithin indices (canon pattern) := by
  intro pattern within index free
  exact within index ((freeIn_canon index pattern).mp free)

/-- **The canonical form of a renamed term is the renamed canonical form**, for every renaming
that keeps the order of the term's free indices. -/
theorem canon_rename : ∀ (rename : Nat → Nat) (indices : Set Nat), StrictMonoOn rename indices →
    ∀ pattern : Pattern, FreeWithin indices pattern →
    canon (substitute (indexRenaming rename) pattern) = substitute (indexRenaming rename) (canon pattern)
  | _, _, _, .bvar index, _ => by simp only [substitute, canon]
  | _, _, _, .fvar name, _ => by simp only [substitute, canon]
  | rename, indices, mono, .apply label arguments, within => by
    simp only [substitute, ContextSubstitution.substituteList_eq_map, canon_apply, List.map_map]
    congr 1
    apply List.map_congr_left
    intro item member
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact canon_rename rename indices mono item (within.argument member)
  | rename, indices, mono, .lambda binder body, within => by
    simp only [substitute, lift_renaming, canon]
    rw [canon_rename _ _ (liftIndex_strictMonoOn mono 1) body within.lambda]
  | rename, indices, mono, .multiLambda arity binders body, within => by
    simp only [substitute, lift_renaming, canon]
    rw [canon_rename _ _ (liftIndex_strictMonoOn mono arity) body within.multiLambda]
  | rename, indices, mono, .subst body replacement, within => by
    simp only [substitute, lift_renaming, canon]
    rw [canon_rename _ _ (liftIndex_strictMonoOn mono 1) body within.substBody,
      canon_rename rename indices mono replacement within.substReplacement]
  | rename, indices, mono, .collection kind elements rest, within => by
    simp only [substitute, ContextSubstitution.substituteList_eq_map, canon_collection]
    have each : elements.map (canon ∘ substitute (indexRenaming rename)) =
        elements.map (substitute (indexRenaming rename) ∘ canon) := by
      apply List.map_congr_left
      intro item member
      have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      exact canon_rename rename indices mono item (within.element member)
    rw [List.map_map, each, ← List.map_map]
    rw [arrange_map]
    intro left inLeft right inRight
    obtain ⟨left₀, member₀, rfl⟩ := List.mem_map.mp inLeft
    obtain ⟨right₀, member₁, rfl⟩ := List.mem_map.mp inRight
    exact patternLe_rename mono (within.element member₀).canon (within.element member₁).canon
termination_by _ _ _ pattern => sizeOf pattern

/-! ## Renaming and scope -/

theorem FreeIn.rename {rename : Nat → Nat} : ∀ {index : Nat} {pattern : Pattern}, FreeIn index pattern →
    FreeIn (rename index) (substitute (indexRenaming rename) pattern) := by
  intro index pattern free
  induction free generalizing rename with
  | bvar index => exact .bvar _
  | apply member _ ih =>
    simp only [substitute, ContextSubstitution.substituteList_eq_map]
    exact .apply (List.mem_map_of_mem member) ih
  | @lambda index _ _ _ ih =>
    simp only [substitute, lift_renaming]
    have := ih (rename := liftIndex 1 rename)
    simp only [liftIndex, show ¬ index + 1 < 1 by omega, if_false, Nat.add_sub_cancel] at this
    exact .lambda this
  | @multiLambda index arity _ _ _ ih =>
    simp only [substitute, lift_renaming]
    have := ih (rename := liftIndex arity rename)
    simp only [liftIndex, show ¬ index + arity < arity by omega, if_false, Nat.add_sub_cancel] at this
    exact .multiLambda this
  | @substBody index _ _ _ ih =>
    simp only [substitute, lift_renaming]
    have := ih (rename := liftIndex 1 rename)
    simp only [liftIndex, show ¬ index + 1 < 1 by omega, if_false, Nat.add_sub_cancel] at this
    exact .substBody this
  | substReplacement _ ih =>
    simp only [substitute]
    exact .substReplacement ih
  | element member _ ih =>
    simp only [substitute, ContextSubstitution.substituteList_eq_map]
    exact .element (List.mem_map_of_mem member) ih

theorem FreeIn.lt_of_scoped : ∀ {index : Nat} {pattern : Pattern}, FreeIn index pattern →
    ∀ {depth : Nat}, pattern.isWellScopedAt depth = true → index < depth := by
  intro index pattern free
  induction free with
  | bvar index => intro depth inScope; simpa [Pattern.isWellScopedAt] using inScope
  | apply member _ ih =>
    intro depth inScope
    exact ih ((Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope _ member)
  | lambda _ ih => intro depth inScope; have := ih (depth := depth + 1) inScope; omega
  | multiLambda _ ih => intro depth inScope; have := ih inScope; omega
  | substBody _ ih =>
    intro depth inScope
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
    have := ih inScope.1; omega
  | substReplacement _ ih =>
    intro depth inScope
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
    exact ih inScope.2
  | element member _ ih =>
    intro depth inScope
    exact ih ((Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope _ member)

/-! ## Recovering a value from a canonical subject -/

open RuleBinding

/-- The recovery assignment renames indices. -/
def recoveryIndex (depth dependencies ambient : Nat) (indices : List Nat) (index : Nat) : Nat :=
  if index < depth then (if index ∈ indices then indices.idxOf index else dependencies + ambient)
  else dependencies + (index - depth)

theorem recoveryAssignment_eq (depth dependencies ambient : Nat) (indices : List Nat) :
    recoveryAssignment depth dependencies ambient indices = indexRenaming (recoveryIndex depth dependencies ambient indices) := by
  funext index
  simp only [recoveryAssignment, recoveryIndex, indexRenaming]
  split_ifs <;> rfl

theorem idxOf_lt_idxOf : ∀ {indices : List Nat}, indices.Pairwise (· < ·) → ∀ {a b : Nat}, a ∈ indices → b ∈ indices →
    a < b → indices.idxOf a < indices.idxOf b
  | [], _, _, _, member, _, _ => absurd member List.not_mem_nil
  | x :: rest, increasing, a, b, inA, inB, less => by
    rw [List.pairwise_cons] at increasing
    rcases List.mem_cons.mp inA with rfl | inA'
    · have : b ≠ a := by omega
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm this)]
      omega
    · rcases List.mem_cons.mp inB with rfl | inB'
      · have := increasing.1 a inA'; omega
      · have aNe : a ≠ x := fun same => by have := increasing.1 a inA'; omega
        have bNe : b ≠ x := fun same => by have := increasing.1 b inB'; omega
        rw [List.idxOf_cons_ne _ (Ne.symm aNe), List.idxOf_cons_ne _ (Ne.symm bNe)]
        exact Nat.succ_lt_succ (idxOf_lt_idxOf increasing.2 inA' inB' less)

private theorem mapM_mem {f : Pattern → Option Nat} : ∀ {arguments : List Pattern} {found : List Nat},
    arguments.mapM f = some found → ∀ index ∈ found, ∃ argument ∈ arguments, f argument = some index
  | [], found, mapped => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at mapped
    subst mapped; simp
  | argument :: arguments, found, mapped => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at mapped
    obtain ⟨head, image, tail, mappedTail, rfl⟩ := mapped
    intro index member
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨argument, .head _, image⟩
    · obtain ⟨other, inArguments, otherImage⟩ := mapM_mem mappedTail index inTail
      exact ⟨other, .tail _ inArguments, otherImage⟩

/-- The spine's local variables, all below the occurrence depth. -/
theorem variableSpine?_lt {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (spine : variableSpine? depth arguments = some indices) : ∀ index ∈ indices, index < depth := by
  unfold variableSpine? at spine
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at spine
  obtain ⟨found, mapped, rest⟩ := spine
  split at rest <;> [cases rest; cases rest]
  intro index member
  obtain ⟨argument, _, image⟩ := mapM_mem mapped index member
  split at image
  · split at image
    · cases image; assumption
    · cases image
  · cases image

private theorem mapM_bvars {f : Pattern → Option Nat} (onlyVariables : ∀ argument index, f argument = some index → argument = .bvar index) :
    ∀ {arguments : List Pattern} {found : List Nat}, arguments.mapM f = some found → arguments = found.map Pattern.bvar
  | [], found, mapped => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at mapped; subst mapped; rfl
  | argument :: arguments, found, mapped => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at mapped
    obtain ⟨head, image, tail, mappedTail, rfl⟩ := mapped
    rw [onlyVariables _ _ image, mapM_bvars onlyVariables mappedTail]
    rfl

/-- A variable spine's arguments are its local variables. -/
theorem variableSpine?_arguments {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (spine : variableSpine? depth arguments = some indices) : arguments = indices.map Pattern.bvar := by
  unfold variableSpine? at spine
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at spine
  obtain ⟨found, mapped, rest⟩ := spine
  have arguments_eq := mapM_bvars (fun argument index image => by
    split at image
    · split at image
      · cases image; rfl
      · cases image
    · cases image) mapped
  split at rest
  · cases rest; exact arguments_eq
  · cases rest

/-- With a variable spine, instantiation renames indices. -/
theorem occurrenceAssignment_eq {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (spine : variableSpine? depth arguments = some indices) (dependencies : Nat) :
    occurrenceAssignment dependencies depth arguments =
      indexRenaming fun index => if index < dependencies then indices.getD index 0 else depth + (index - dependencies) := by
  rw [variableSpine?_arguments spine]
  funext index
  unfold occurrenceAssignment
  by_cases small : index < dependencies
  · simp only [small, if_true, indexRenaming, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases indices[index]? <;> rfl
  · simp only [small, if_false, indexRenaming]

/-- An increasing local-variable spine, followed by the ambient variables,
is a strictly increasing renaming of the entire contextual body. -/
theorem occurrenceIndex_strictMono {depth : Nat} {indices : List Nat}
    (increasing : indices.Pairwise (· < ·))
    (below : ∀ index ∈ indices, index < depth) :
    StrictMono (fun index => if index < indices.length then indices.getD index 0
      else depth + (index - indices.length)) := by
  intro first second less
  by_cases firstLocal : first < indices.length <;> by_cases secondLocal : second < indices.length
  · simp only [firstLocal, secondLocal, if_true, List.getD_eq_getElem _ _ firstLocal,
      List.getD_eq_getElem _ _ secondLocal]
    exact increasing.rel_get_of_lt (a := ⟨first, firstLocal⟩) (b := ⟨second, secondLocal⟩) less
  · have bounded := below indices[first] (List.getElem_mem firstLocal)
    simp only [firstLocal, secondLocal, if_true, if_false, List.getD_eq_getElem _ _ firstLocal]
    omega
  · omega
  · simp only [firstLocal, secondLocal, if_false]
    omega

/-- Instantiation along an increasing variable spine commutes exactly with
canonicalization. Arbitrary term-valued occurrence substitutions are not
covered by this renaming law. -/
theorem instantiateValue?_canon {value : ContextualValue} {ambient depth : Nat}
    {arguments : List Pattern} {indices : List Nat} {result : Pattern}
    (spine : variableSpine? depth arguments = some indices)
    (increasing : indices.Pairwise (· < ·))
    (read : instantiateValue? value ambient depth arguments = some result) :
    instantiateValue? { value with body := canon value.body } ambient depth arguments = some (canon result) := by
  obtain ⟨other, otherRead, _⟩ := instantiateValue?_same
    (show ValueSame value { value with body := canon value.body } from
      ⟨rfl, rfl, (canon_idempotent value.body).symm⟩) ambient depth arguments result read
  obtain ⟨_, arity, _, _, sourceBody, _⟩ :=
    (instantiateValue?_eq_some_iff _ _ _ _ _).mp read
  obtain ⟨_, _, _, _, targetBody, _⟩ :=
    (instantiateValue?_eq_some_iff _ _ _ _ _).mp otherRead
  have length : indices.length = value.dependencies.length := by
    simpa only [variableSpine?_arguments spine, List.length_map] using arity
  have normalized : canon result = other := by
    rw [← sourceBody, ← targetBody, occurrenceAssignment_eq spine, ← length]
    exact canon_rename _ Set.univ
      ((occurrenceIndex_strictMono increasing (variableSpine?_lt spine)).strictMonoOn Set.univ)
      value.body (fun _ _ => Set.mem_univ _)
  simpa only [normalized] using otherRead

/-- **On a canonical subject, a capture with an increasing spine recovers the canonical form of
the value it recovers from the subject.** -/
theorem recoverValue?_canon {dependencies : List TypeExpr} {ambient depth : Nat} {arguments : List Pattern}
    {target : Pattern} {value : ContextualValue}
    (found : recoverValue? dependencies ambient depth arguments target = some value)
    (increasing : ∀ indices, variableSpine? depth arguments = some indices → indices.Pairwise (· < ·)) :
    recoverValue? dependencies ambient depth arguments (canon target) =
      some { value with body := canon value.body } := by
  obtain ⟨recovered, recoveredFound, _⟩ := recoverValue?_same (canon_idempotent target).symm
    dependencies ambient depth arguments value found
  rw [recoveredFound]
  unfold recoverValue? at found recoveredFound
  split at found <;> [cases found; skip]
  split at recoveredFound <;> [cases recoveredFound; skip]
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found recoveredFound
  obtain ⟨indices, spine, found⟩ := found
  obtain ⟨indices', spine', recoveredFound⟩ := recoveredFound
  rw [spine] at spine'
  cases spine'
  split at found <;> [cases found; skip]
  split at recoveredFound <;> [cases recoveredFound; skip]
  split at found <;> [skip; cases found]
  split at recoveredFound <;> [skip; cases recoveredFound]
  rename_i lengths _ forward _
  cases found
  cases recoveredFound
  obtain ⟨_, _, bodyScoped, _, _, _⟩ := (instantiateValue?_eq_some_iff _ _ _ _ _).mp (by simpa using forward)
  simp only [Option.some.injEq, ContextualValue.mk.injEq, true_and]
  rw [recoveryAssignment_eq]
  symm
  apply canon_rename _ {index | FreeIn index target} _ target (fun _ free => free)
  intro a inA b inB less
  have local_or_ambient : ∀ index, FreeIn index target → index ∈ indices ∨ depth ≤ index := by
    intro index free
    by_contra neither
    push Not at neither
    have image := free.rename (rename := recoveryIndex depth dependencies.length ambient indices)
    rw [← recoveryAssignment_eq] at image
    have outside := image.lt_of_scoped bodyScoped
    simp only [recoveryIndex, neither.2, if_true, neither.1, if_false] at outside
    omega
  have below := variableSpine?_lt spine
  have lengthsEq : indices.length = dependencies.length := by simpa using lengths
  unfold recoveryIndex
  rcases local_or_ambient a inA with localA | ambientA <;> rcases local_or_ambient b inB with localB | ambientB
  · simp only [below a localA, below b localB, localA, localB, if_true]
    exact idxOf_lt_idxOf (increasing indices spine) localA localB less
  · have := List.idxOf_lt_length_iff.mpr localA
    simp only [below a localA, localA, if_true, show ¬ b < depth by omega, if_false]
    omega
  · have := below b localB; omega
  · simp only [show ¬ a < depth by omega, show ¬ b < depth by omega, if_false]
    omega

/-- Negative control: reversing two free indices does not commute with sorting. -/
theorem canon_reverse_not_rename :
    canon (substitute (indexRenaming fun index => 1 - index)
        (.collection .hashBag [.bvar 0, .bvar 1] none)) ≠
      substitute (indexRenaming fun index => 1 - index) (canon (.collection .hashBag [.bvar 0, .bvar 1] none)) := by
  have bvar : ∀ index, canon (.bvar index) = .bvar index := fun index => by rw [canon]
  simp only [substitute, ContextSubstitution.substituteList_eq_map, List.map_cons, List.map_nil, canon_collection,
    bvar, arrange_bag]
  decide

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
