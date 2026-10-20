import Mettapedia.OSLF.MeTTaIL.LawNormalInstantiation
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

/-!
# Reflective substitution respects the collection laws

A law move rearranges a collection's elements; it never changes a constructor application, a
binder or an index. Hence law-equal terms have the same shape above their collections
(`LawSame.apply_inv`, `LawSame.bvar_inv`), the quote-drop normal form maps law-equal terms to
law-equal terms (`normalizeReflective_lawSame`), and so does reflective binder elimination
(`reflectiveOperation_lawSame`). Every binder operation of a plan respects the laws
(`binderOperation_lawSame`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws ReflectiveSubstitution

variable {laws : List Laws}

/-! ## Law-equal terms have the same shape above their collections -/

theorem forall₂_lawSame_refl (items : List Pattern) : List.Forall₂ (LawSame laws) items items :=
  List.forall₂_same.mpr fun _ _ => .refl _

theorem forall₂_lawSame_symm : ∀ {left right : List Pattern}, List.Forall₂ (LawSame laws) left right →
    List.Forall₂ (LawSame laws) right left
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => .cons (.symm _ _ head) (forall₂_lawSame_symm tail)

theorem forall₂_lawSame_trans : ∀ {first second third : List Pattern}, List.Forall₂ (LawSame laws) first second →
    List.Forall₂ (LawSame laws) second third → List.Forall₂ (LawSame laws) first third
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons head tail, .cons head' tail' =>
    .cons (.trans _ _ _ head head') (forall₂_lawSame_trans tail tail')

theorem LawStep.apply_inv {label : String} {arguments : List Pattern} {other : Pattern}
    (step : LawStep laws (.apply label arguments) other) :
    ∃ arguments', other = .apply label arguments' ∧ List.Forall₂ (LawSame laws) arguments arguments' := by
  cases step with
  | apply inner =>
    exact ⟨_, rfl, List.rel_append (forall₂_lawSame_refl _) (.cons (.rel _ _ inner) (forall₂_lawSame_refl _))⟩

theorem LawStep.apply_inv' {label : String} {arguments : List Pattern} {other : Pattern}
    (step : LawStep laws other (.apply label arguments)) :
    ∃ arguments', other = .apply label arguments' ∧ List.Forall₂ (LawSame laws) arguments arguments' := by
  cases step with
  | apply inner =>
    exact ⟨_, rfl, List.rel_append (forall₂_lawSame_refl _) (.cons (.symm _ _ (.rel _ _ inner)) (forall₂_lawSame_refl _))⟩

/-- **Law-equal terms agree on a constructor application**, with pointwise law-equal arguments. -/
theorem LawSame.apply_inv {label : String} {arguments : List Pattern} {other : Pattern}
    (same : LawSame laws (.apply label arguments) other) :
    ∃ arguments', other = .apply label arguments' ∧ List.Forall₂ (LawSame laws) arguments arguments' := by
  have chain : Relation.ReflTransGen (Relation.SymmGen (LawStep laws)) (.apply label arguments) other := by
    rw [Relation.EqvGen.reflTransGen_symmGen]; exact same
  clear same
  induction chain with
  | refl => exact ⟨arguments, rfl, forall₂_lawSame_refl _⟩
  | tail _ step ih =>
    obtain ⟨middle, rfl, toMiddle⟩ := ih
    rcases step with forward | backward
    · obtain ⟨next, rfl, toNext⟩ := forward.apply_inv
      exact ⟨next, rfl, forall₂_lawSame_trans toMiddle toNext⟩
    · obtain ⟨next, rfl, toNext⟩ := backward.apply_inv'
      exact ⟨next, rfl, forall₂_lawSame_trans toMiddle toNext⟩

/-- Law-equal terms agree on an index. -/
theorem LawSame.bvar_inv {index : Nat} {other : Pattern} (same : LawSame laws (.bvar index) other) :
    other = .bvar index := by
  have chain : Relation.ReflTransGen (Relation.SymmGen (LawStep laws)) (.bvar index) other := by
    rw [Relation.EqvGen.reflTransGen_symmGen]; exact same
  clear same
  induction chain with
  | refl => rfl
  | tail _ step ih =>
    subst ih
    rcases step with forward | backward
    · cases forward
    · cases backward

/-! ## The quote-drop normal form -/

theorem normalizeReflectiveList_map (declaration : ReflectivePresentationDecl) :
    ∀ items : List Pattern, normalizeReflectiveList declaration items = items.map (normalizeReflective declaration)
  | [] => by rw [normalizeReflectiveList]; rfl
  | item :: rest => by rw [normalizeReflectiveList, normalizeReflectiveList_map declaration rest]; rfl

theorem finish_nil (declaration : ReflectivePresentationDecl) (label : String) :
    finishNormalizeReflectiveApply declaration label [] = .apply label [] := by
  unfold finishNormalizeReflectiveApply; split <;> rfl

theorem finish_long (declaration : ReflectivePresentationDecl) (label : String) (first second : Pattern)
    (rest : List Pattern) :
    finishNormalizeReflectiveApply declaration label (first :: second :: rest) = .apply label (first :: second :: rest) := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · rename_i same; simp at same
    · rfl
  · rfl

theorem finish_plain (declaration : ReflectivePresentationDecl) (label : String) {first : Pattern}
    (notShaped : ¬ ∃ drop name, first = .apply drop [name]) :
    finishNormalizeReflectiveApply declaration label [first] = .apply label [first] := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · rename_i drop name same
      simp only [List.cons.injEq, and_true] at same
      exact absurd ⟨drop, name, same⟩ notShaped
    · rfl
  · rfl

theorem finish_drop (declaration : ReflectivePresentationDecl) (label drop : String) (name : Pattern) :
    finishNormalizeReflectiveApply declaration label [.apply drop [name]] =
      if label == declaration.quoteConstructor && drop == declaration.dropConstructor then name
      else .apply label [.apply drop [name]] := by
  unfold finishNormalizeReflectiveApply
  by_cases quote : label == declaration.quoteConstructor <;> by_cases dropped : drop == declaration.dropConstructor <;>
    simp [quote, dropped]

/-- The quote-drop step at a constructor maps pointwise law-equal arguments to law-equal results. -/
theorem finishNormalizeReflectiveApply_lawSame (declaration : ReflectivePresentationDecl) (label : String)
    {arguments arguments' : List Pattern} (pointwise : List.Forall₂ (LawSame laws) arguments arguments') :
    LawSame laws (finishNormalizeReflectiveApply declaration label arguments)
      (finishNormalizeReflectiveApply declaration label arguments') := by
  cases pointwise with
  | nil => rw [finish_nil]; exact .refl _
  | @cons first first' rest rest' head tail =>
    cases tail with
    | @cons second second' more more' secondSame moreSame =>
      rw [finish_long, finish_long]
      exact lawSame_apply_congr _ (.cons head (.cons secondSame moreSame))
    | nil =>
      by_cases shaped : ∃ drop name, first = .apply drop [name]
      · obtain ⟨drop, name, rfl⟩ := shaped
        obtain ⟨arguments'', rfl, inner⟩ := head.apply_inv
        cases inner with
        | cons nameSame rest =>
          cases rest
          rw [finish_drop, finish_drop]
          split
          · exact nameSame
          · exact lawSame_apply_congr _ (.cons (lawSame_apply_congr _ (.cons nameSame .nil)) .nil)
      · have notShaped' : ¬ ∃ drop name, first' = .apply drop [name] := by
          rintro ⟨drop, name, rfl⟩
          obtain ⟨arguments'', rfl, inner⟩ := LawSame.apply_inv (Relation.EqvGen.symm _ _ head)
          cases inner with
          | cons _ rest => cases rest; exact shaped ⟨drop, _, rfl⟩
        rw [finish_plain declaration label shaped, finish_plain declaration label notShaped']
        exact lawSame_apply_congr _ (.cons head .nil)

/-- **The quote-drop normal form maps a law move to law-equal terms.** -/
theorem LawStep.normalizeReflective (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (step : LawStep laws left right) :
    LawSame laws (ReflectiveSubstitution.normalizeReflective declaration left)
      (ReflectiveSubstitution.normalizeReflective declaration right) := by
  induction step with
  | permute unordered permutation =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map]
    exact .rel _ _ (.permute unordered (permutation.map _))
  | members same =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map]
    exact .rel _ _ (.members (members_map same _))
  | flatten found =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map, List.map_append, List.map_cons]
    exact .rel _ _ (.flatten found)
  | @unit kind law label before after rest found unit =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map, List.map_append, List.map_cons,
      List.map_nil]
    rw [finish_nil]
    exact .rel _ _ (.unit found unit)
  | apply _ ih =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map, List.map_append, List.map_cons]
    exact finishNormalizeReflectiveApply_lawSame declaration _
      (List.rel_append (forall₂_lawSame_refl _) (.cons ih (forall₂_lawSame_refl _)))
  | lambda _ ih => simp only [ReflectiveSubstitution.normalizeReflective]; exact lawSame_lambda_congr _ ih
  | multiLambda _ ih => simp only [ReflectiveSubstitution.normalizeReflective]; exact lawSame_multiLambda_congr _ _ ih
  | substBody _ ih =>
    simp only [ReflectiveSubstitution.normalizeReflective]; exact lawSame_subst_congr ih (.refl _)
  | substReplacement _ ih =>
    simp only [ReflectiveSubstitution.normalizeReflective]; exact lawSame_subst_congr (.refl _) ih
  | element _ ih =>
    simp only [ReflectiveSubstitution.normalizeReflective, normalizeReflectiveList_map, List.map_append, List.map_cons]
    exact lawSame_collection_congr _ _ (List.rel_append (forall₂_lawSame_refl _) (.cons ih (forall₂_lawSame_refl _)))

theorem normalizeReflective_lawSame (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (same : LawSame laws left right) :
    LawSame laws (ReflectiveSubstitution.normalizeReflective declaration left)
      (ReflectiveSubstitution.normalizeReflective declaration right) := by
  induction same with
  | rel _ _ step => exact step.normalizeReflective declaration
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-! ## Reflective binder elimination -/

open ReflectiveInstantiation in
/-- The drop case of reflective elimination: activate a substituted quote. -/
def dropResult (declaration : ReflectivePresentationDecl) (constructor : String) (name : Pattern) (matched : Bool) :
    Pattern :=
  match name, matched with
  | .apply quote [process], true => if quote == declaration.quoteConstructor then process else .apply constructor [name]
  | _, _ => .apply constructor [name]

open ReflectiveInstantiation in
theorem instantiate_quote (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement : Pattern)
    {constructor : String} (payload : Pattern) (quote : (constructor == declaration.quoteConstructor) = true) :
    instantiate declaration depth replacement (.apply constructor [payload]) =
      (nameMark declaration depth replacement (.apply constructor [payload])).1 := by
  rw [instantiate]; simp [quote]

open ReflectiveInstantiation in
theorem instantiate_drop (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement : Pattern)
    {constructor : String} (payload : Pattern) (notQuote : (constructor == declaration.quoteConstructor) = false)
    (drop : (constructor == declaration.dropConstructor) = true) :
    instantiate declaration depth replacement (.apply constructor [payload]) =
      dropResult declaration constructor (nameMark declaration depth replacement payload).1
        (nameMark declaration depth replacement payload).2 := by
  rw [instantiate]; simp only [notQuote, drop, Bool.false_eq_true, if_false, if_true]; rfl

open ReflectiveInstantiation in
theorem instantiate_plainOne (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement : Pattern)
    {constructor : String} (payload : Pattern) (notQuote : (constructor == declaration.quoteConstructor) = false)
    (notDrop : (constructor == declaration.dropConstructor) = false) :
    instantiate declaration depth replacement (.apply constructor [payload]) =
      .apply constructor [instantiate declaration depth replacement payload] := by
  rw [instantiate]; simp [notQuote, notDrop]

open ReflectiveInstantiation in
theorem instantiateList_map' (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement : Pattern) :
    ∀ items : List Pattern, instantiateList declaration depth replacement items =
      items.map (instantiate declaration depth replacement)
  | [] => by rw [instantiateList]; rfl
  | item :: rest => by rw [instantiateList, instantiateList_map' declaration depth replacement rest]; rfl

open ReflectiveInstantiation in
theorem instantiate_many (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement : Pattern)
    (constructor : String) {arguments : List Pattern} (notOne : arguments.length ≠ 1) :
    instantiate declaration depth replacement (.apply constructor arguments) =
      .apply constructor (arguments.map (instantiate declaration depth replacement)) := by
  match arguments, notOne with
  | [], _ => rw [instantiate, instantiateList_map']; intro _ same; cases same
  | _ :: _ :: _, _ => rw [instantiate, instantiateList_map']; intro _ same; simp at same

theorem dropResult_shaped (declaration : ReflectivePresentationDecl) (constructor quote : String) (process : Pattern) :
    dropResult declaration constructor (.apply quote [process]) true =
      if quote == declaration.quoteConstructor then process else .apply constructor [.apply quote [process]] := rfl

theorem dropResult_plain (declaration : ReflectivePresentationDecl) (constructor : String) {name : Pattern} {matched : Bool}
    (plain : (¬ ∃ quote process, name = .apply quote [process]) ∨ matched = false) :
    dropResult declaration constructor name matched = .apply constructor [name] := by
  unfold dropResult
  split
  · rename_i quote process
    rcases plain with notShaped | unmatched
    · exact absurd ⟨quote, process, rfl⟩ notShaped
    · cases unmatched
  · rfl

theorem dropResult_lawSame (declaration : ReflectivePresentationDecl) (constructor : String) {name name' : Pattern}
    (matched : Bool) (same : LawSame laws name name') :
    LawSame laws (dropResult declaration constructor name matched) (dropResult declaration constructor name' matched) := by
  cases matched with
  | false =>
    rw [dropResult_plain declaration constructor (.inr rfl), dropResult_plain declaration constructor (.inr rfl)]
    exact lawSame_apply_congr _ (.cons same .nil)
  | true =>
    by_cases shaped : ∃ quote process, name = .apply quote [process]
    · obtain ⟨quote, process, rfl⟩ := shaped
      obtain ⟨arguments, rfl, inner⟩ := same.apply_inv
      cases inner with
      | cons processSame rest =>
        cases rest
        rw [dropResult_shaped, dropResult_shaped]
        split
        · exact processSame
        · exact lawSame_apply_congr _ (.cons same .nil)
    · have shaped' : ¬ ∃ quote process, name' = .apply quote [process] := by
        rintro ⟨quote, process, rfl⟩
        obtain ⟨arguments, rfl, inner⟩ := LawSame.apply_inv (Relation.EqvGen.symm _ _ same)
        cases inner with
        | cons _ rest => cases rest; exact shaped ⟨quote, _, rfl⟩
      rw [dropResult_plain declaration constructor (.inl shaped), dropResult_plain declaration constructor (.inl shaped')]
      exact lawSame_apply_congr _ (.cons same .nil)

open ReflectiveInstantiation in
/-- Names with law-equal quote-drop normal forms mark the same way: the same index, or no index. -/
theorem nameMark_names (declaration : ReflectivePresentationDecl) (depth : Nat) (replacement : Pattern)
    {name name' : Pattern}
    (same : LawSame laws (ReflectiveSubstitution.normalizeReflective declaration name)
      (ReflectiveSubstitution.normalizeReflective declaration name')) :
    nameMark declaration depth replacement name = nameMark declaration depth replacement name' ∨
      ∃ marked marked', nameMark declaration depth replacement name = (marked, false) ∧
        nameMark declaration depth replacement name' = (marked', false) ∧ LawSame laws marked marked' := by
  unfold nameMark
  split
  · rename_i index found
    rw [found] at same
    rw [same.bvar_inv]
    exact .inl rfl
  · rename_i normalized notIndex
    split
    · rename_i index found'
      rw [found'] at same
      exact absurd (LawSame.bvar_inv (Relation.EqvGen.symm _ _ same)) (notIndex index)
    · exact .inr ⟨_, _, rfl, rfl, same⟩

theorem instantiateBVarAt_lawSame_replacement {replacement replacement' : Pattern}
    (same : LawSame laws replacement replacement') (depth index : Nat) :
    LawSame laws (Substitution.instantiateBVarAt depth replacement (.bvar index))
      (Substitution.instantiateBVarAt depth replacement' (.bvar index)) := by
  unfold Substitution.instantiateBVarAt
  split
  · exact .refl _
  · split
    · exact LawSame.lift (fun step => step.liftBVars 0 depth) same
    · exact .refl _

open ReflectiveInstantiation in
theorem nameMark_replacement (declaration : ReflectivePresentationDecl) (depth : Nat) {replacement replacement' : Pattern}
    (same : LawSame laws replacement replacement') (name : Pattern) :
    (nameMark declaration depth replacement name).2 = (nameMark declaration depth replacement' name).2 ∧
      LawSame laws (nameMark declaration depth replacement name).1 (nameMark declaration depth replacement' name).1 := by
  unfold nameMark
  split
  · exact ⟨rfl, instantiateBVarAt_lawSame_replacement same depth _⟩
  · exact ⟨rfl, .refl _⟩

open ReflectiveInstantiation in
/-- **Reflective elimination maps a law move in the body to law-equal results.** -/
theorem LawStep.instantiate (declaration : ReflectivePresentationDecl) {body body' : Pattern}
    (step : LawStep laws body body') : ∀ (depth : Nat) (replacement : Pattern),
      LawSame laws (ReflectiveInstantiation.instantiate declaration depth replacement body)
        (ReflectiveInstantiation.instantiate declaration depth replacement body') := by
  induction step with
  | permute unordered permutation =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate, instantiateList_map',
      instantiateList_map']
    exact .rel _ _ (.permute unordered (permutation.map _))
  | members same =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate, instantiateList_map',
      instantiateList_map']
    exact .rel _ _ (.members (members_map same _))
  | @flatten kind law before inner after rest found =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate, instantiateList_map',
      instantiateList_map']
    simp only [List.map_append, List.map_cons]
    rw [ReflectiveInstantiation.instantiate, instantiateList_map']
    exact .rel _ _ (.flatten found)
  | @unit kind law label before after rest found unit =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate, instantiateList_map',
      instantiateList_map']
    simp only [List.map_append, List.map_cons]
    rw [instantiate_many declaration depth replacement label (by simp), List.map_nil]
    exact .rel _ _ (.unit found unit)
  | @apply label before after argument changed inner ih =>
    intro depth replacement
    by_cases single : before = [] ∧ after = []
    · obtain ⟨rfl, rfl⟩ := single
      simp only [List.nil_append]
      cases quote : label == declaration.quoteConstructor
      · cases drop : label == declaration.dropConstructor
        · rw [instantiate_plainOne declaration depth replacement _ quote drop,
            instantiate_plainOne declaration depth replacement _ quote drop]
          exact lawSame_apply_congr _ (.cons (ih depth replacement) .nil)
        · rw [instantiate_drop declaration depth replacement _ quote drop,
            instantiate_drop declaration depth replacement _ quote drop]
          rcases nameMark_names declaration depth replacement (inner.normalizeReflective declaration) with
            equal | ⟨marked, marked', first, second, same⟩
          · rw [equal]; exact .refl _
          · rw [first, second]
            exact dropResult_lawSame declaration label false same
      · rw [instantiate_quote declaration depth replacement _ quote, instantiate_quote declaration depth replacement _ quote]
        have normalSame := (LawStep.apply (label := label) (before := []) (after := []) inner).normalizeReflective declaration
        rcases nameMark_names declaration depth replacement normalSame with equal | ⟨marked, marked', first, second, same⟩
        · simp only [List.nil_append] at equal
          rw [equal]; exact .refl _
        · simp only [List.nil_append] at first second
          rw [first, second]
          exact same
    · have notOne : (before ++ argument :: after).length ≠ 1 := by
        intro one; apply single
        simp only [List.length_append, List.length_cons] at one
        exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
      have notOne' : (before ++ changed :: after).length ≠ 1 := by simpa using notOne
      rw [instantiate_many declaration depth replacement label notOne,
        instantiate_many declaration depth replacement label notOne']
      simp only [List.map_append, List.map_cons]
      exact lawSame_apply_congr _ (List.rel_append (forall₂_lawSame_refl _) (.cons (ih depth replacement)
        (forall₂_lawSame_refl _)))
  | lambda _ ih =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]
    exact lawSame_lambda_congr _ (ih _ _)
  | multiLambda _ ih =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]
    exact lawSame_multiLambda_congr _ _ (ih _ _)
  | substBody _ ih =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]
    exact lawSame_subst_congr (ih _ _) (.refl _)
  | substReplacement _ ih =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]
    exact lawSame_subst_congr (.refl _) (ih _ _)
  | element _ ih =>
    intro depth replacement
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate, instantiateList_map',
      instantiateList_map']
    simp only [List.map_append, List.map_cons]
    exact lawSame_collection_congr _ _ (List.rel_append (forall₂_lawSame_refl _) (.cons (ih depth replacement)
      (forall₂_lawSame_refl _)))

open ReflectiveInstantiation in
/-- **Reflective elimination maps law-equal replacements to law-equal results.** -/
theorem instantiate_replacement (declaration : ReflectivePresentationDecl) {replacement replacement' : Pattern}
    (same : LawSame laws replacement replacement') : ∀ (body : Pattern) (depth : Nat),
      LawSame laws (ReflectiveInstantiation.instantiate declaration depth replacement body)
        (ReflectiveInstantiation.instantiate declaration depth replacement' body)
  | .bvar index, depth => by
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]
    exact instantiateBVarAt_lawSame_replacement same depth index
  | .fvar _, depth => by rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]; exact .refl _
  | .apply label arguments, depth => by
    by_cases one : arguments.length = 1
    · match arguments, one with
      | [payload], _ =>
        cases quote : label == declaration.quoteConstructor
        · cases drop : label == declaration.dropConstructor
          · rw [instantiate_plainOne declaration depth _ _ quote drop, instantiate_plainOne declaration depth _ _ quote drop]
            have : sizeOf payload < sizeOf (Pattern.apply label [payload]) := by
              have := List.sizeOf_lt_of_mem (List.mem_singleton_self payload)
              simp only [Pattern.apply.sizeOf_spec]; omega
            exact lawSame_apply_congr _ (.cons (instantiate_replacement declaration same payload depth) .nil)
          · rw [instantiate_drop declaration depth _ _ quote drop, instantiate_drop declaration depth _ _ quote drop]
            obtain ⟨flags, names⟩ := nameMark_replacement declaration depth same payload
            rw [flags]
            exact dropResult_lawSame declaration label _ names
        · rw [instantiate_quote declaration depth _ _ quote, instantiate_quote declaration depth _ _ quote]
          exact (nameMark_replacement declaration depth same _).2
    · rw [instantiate_many declaration depth _ label one, instantiate_many declaration depth _ label one]
      apply lawSame_apply_congr
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_same.mpr
      intro item member
      have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      exact instantiate_replacement declaration same item depth
  | .lambda binder body, depth => by
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]
    exact lawSame_lambda_congr _ (instantiate_replacement declaration same body (depth + 1))
  | .multiLambda arity binders body, depth => by
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]
    exact lawSame_multiLambda_congr _ _ (instantiate_replacement declaration same body (depth + arity))
  | .subst body value, depth => by
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate]
    exact lawSame_subst_congr (instantiate_replacement declaration same body (depth + 1))
      (instantiate_replacement declaration same value depth)
  | .collection kind elements rest, depth => by
    rw [ReflectiveInstantiation.instantiate, ReflectiveInstantiation.instantiate, instantiateList_map',
      instantiateList_map']
    apply lawSame_collection_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
    exact instantiate_replacement declaration same item depth
termination_by body => sizeOf body

theorem instantiate_lawSame (declaration : ReflectivePresentationDecl) (depth : Nat) {replacement replacement' body body' : Pattern}
    (sameReplacement : LawSame laws replacement replacement') (sameBody : LawSame laws body body') :
    LawSame laws (ReflectiveInstantiation.instantiate declaration depth replacement body)
      (ReflectiveInstantiation.instantiate declaration depth replacement' body') := by
  refine .trans _ _ _ ?_ (instantiate_replacement declaration sameReplacement body' depth)
  induction sameBody with
  | rel _ _ step => exact step.instantiate declaration depth replacement
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem normalizeReflectiveReplacement_lawSame (declaration : ReflectivePresentationDecl) {replacement replacement' : Pattern}
    (same : LawSame laws replacement replacement') :
    LawSame laws (normalizeReflectiveReplacement declaration replacement)
      (normalizeReflectiveReplacement declaration replacement') := by
  by_cases shaped : ∃ constructor payload, replacement = .apply constructor [payload]
  · obtain ⟨constructor, payload, rfl⟩ := shaped
    obtain ⟨arguments, rfl, inner⟩ := same.apply_inv
    cases inner with
    | cons payloadSame rest =>
      cases rest
      unfold normalizeReflectiveReplacement
      by_cases quote : (constructor == declaration.quoteConstructor) = true
      · simp only [quote, if_true]
        exact lawSame_apply_congr _ (.cons (normalizeReflective_lawSame declaration payloadSame) .nil)
      · simp only [quote, Bool.false_eq_true, if_false]
        exact normalizeReflective_lawSame declaration same
  · have shaped' : ¬ ∃ constructor payload, replacement' = .apply constructor [payload] := by
      rintro ⟨constructor, payload, rfl⟩
      obtain ⟨arguments, rfl, inner⟩ := LawSame.apply_inv (Relation.EqvGen.symm _ _ same)
      cases inner with
      | cons _ rest => cases rest; exact shaped ⟨constructor, _, rfl⟩
    have plain : ∀ term : Pattern, (¬ ∃ constructor payload, term = .apply constructor [payload]) →
        normalizeReflectiveReplacement declaration term = ReflectiveSubstitution.normalizeReflective declaration term := by
      intro term notShaped
      unfold normalizeReflectiveReplacement
      split
      · rename_i constructor payload
        exact absurd ⟨constructor, payload, rfl⟩ notShaped
      · rfl
    rw [plain _ shaped, plain _ shaped']
    exact normalizeReflective_lawSame declaration same

/-- **Reflective binder elimination respects the collection laws.** -/
theorem reflectiveOperation_lawSame (declaration : ReflectivePresentationDecl) {replacement replacement' body body' : Pattern}
    (sameReplacement : LawSame laws replacement replacement') (sameBody : LawSame laws body body') :
    LawSame laws (ScopedRuleInstantiation.reflectiveOperation declaration replacement body)
      (ScopedRuleInstantiation.reflectiveOperation declaration replacement' body') :=
  instantiate_lawSame declaration 0 (normalizeReflectiveReplacement_lawSame declaration sameReplacement) sameBody

/-- **Every binder operation of a plan respects the collection laws.** -/
theorem binderOperation_lawSame (profile : Reflection.ReflectionProfile) (rule : RewriteRule)
    {replacement replacement' body body' : Pattern}
    (sameReplacement : LawSame laws replacement replacement') (sameBody : LawSame laws body body') :
    LawSame laws (ScopedReflectiveExecution.binderOperation profile rule replacement body)
      (ScopedReflectiveExecution.binderOperation profile rule replacement' body') := by
  unfold ScopedReflectiveExecution.binderOperation
  cases substitutionPresentationForRule? profile rule with
  | none => exact instantiateBVar_lawSame sameReplacement sameBody
  | some declaration => exact reflectiveOperation_lawSame declaration sameReplacement sameBody

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
