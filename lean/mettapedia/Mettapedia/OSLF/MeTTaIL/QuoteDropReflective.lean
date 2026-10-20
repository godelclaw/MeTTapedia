import Mettapedia.OSLF.MeTTaIL.QuoteDropMatching

/-!
# Reflective substitution and the quote-drop equation

Reflective substitution treats a quoted name as opaque: it compares the name's quote-drop normal
form with the substituted index and otherwise leaves it alone. Every drop of a well-sorted term
is applied to a name: an index, a free name or a quotation (`dropsNamed`). On such terms,
eliminating a binder from a term and from its quote-drop normal form gives quote-drop equal
results (`instantiate_normal`): a collapsed quotation `@(*n)` and its name `n` are treated alike,
because the substitution looks only at normal forms of names.

- `isName_normal`: the normal form of a name whose drops are applied to names is a name;
- `dropsNamed_normal`: the normal form keeps that property;
- `instantiate_normal`: binder elimination commutes with the normal form up to quote-drop
  equality;
- `reflectiveOperation_normal`: so does the reflective binder operation, for replacements with one
  normalized form.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteDrop

open Syntax ReflectiveSubstitution ReflectiveInstantiation CanonicalBags

variable {declaration : ReflectivePresentationDecl}

variable (declaration) in
/-- A name: an index, a free name or a quotation. -/
def isName : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply label [_] => label == declaration.quoteConstructor
  | _ => false

variable (declaration) in
/-- A single argument is a name. -/
def singleName : List Pattern → Bool
  | [argument] => isName declaration argument
  | _ => true

variable (declaration) in
/-- Every drop is applied to a name. -/
def dropsNamed : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply label arguments =>
      (label != declaration.dropConstructor || singleName declaration arguments) &&
      arguments.attach.all fun ⟨argument, _⟩ => dropsNamed argument
  | .lambda _ body => dropsNamed body
  | .multiLambda _ _ body => dropsNamed body
  | .subst body replacement => dropsNamed body && dropsNamed replacement
  | .collection _ elements _ => elements.attach.all fun ⟨element, _⟩ => dropsNamed element
decreasing_by all_goals sizeOf_pattern_dec

theorem dropsNamed_args {label : String} {arguments : List Pattern}
    (named : dropsNamed declaration (.apply label arguments) = true) :
    ∀ argument ∈ arguments, dropsNamed declaration argument = true := by
  rw [dropsNamed] at named
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at named
  exact named.2

theorem dropsNamed_drop {name : Pattern}
    (named : dropsNamed declaration (.apply declaration.dropConstructor [name]) = true) : isName declaration name = true := by
  rw [dropsNamed] at named
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, singleName] at named
  exact named.1

theorem dropsNamed_of_apply {label : String} {arguments : List Pattern}
    (each : ∀ argument ∈ arguments, dropsNamed declaration argument = true)
    (atDrop : label = declaration.dropConstructor → ∀ argument, arguments = [argument] → isName declaration argument = true) :
    dropsNamed declaration (.apply label arguments) = true := by
  rw [dropsNamed]
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_attach, true_implies,
    Subtype.forall]
  refine ⟨?_, each⟩
  by_cases dropped : label = declaration.dropConstructor
  · right
    match arguments, atDrop dropped with
    | [argument], named => simpa [singleName] using named argument rfl
    | [], _ => rfl
    | _ :: _ :: _, _ => rfl
  · exact .inl dropped

theorem dropsNamed_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    (named : dropsNamed declaration (.collection kind elements rest) = true) :
    ∀ element ∈ elements, dropsNamed declaration element = true := by
  rw [dropsNamed] at named
  simpa using named

theorem plain_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (name : Pattern) :
    finishNormalizeReflectiveApply declaration declaration.dropConstructor [name] =
      .apply declaration.dropConstructor [name] := by
  unfold finishNormalizeReflectiveApply
  rw [if_neg (by simpa using distinct)]

theorem finish_quote_plain {payload : Pattern} (notDrop : ∀ name, payload ≠ .apply declaration.dropConstructor [name]) :
    finishNormalizeReflectiveApply declaration declaration.quoteConstructor [payload] =
      .apply declaration.quoteConstructor [payload] := by
  by_cases shaped : ∃ drop name, payload = .apply drop [name]
  · obtain ⟨drop, name, rfl⟩ := shaped
    rw [finish_drop]
    have different : drop ≠ declaration.dropConstructor := fun same => notDrop name (by rw [same])
    simp [different]
  · exact finish_plain declaration _ shaped

theorem isName_not_drop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) {pattern name : Pattern}
    (nameShaped : isName declaration pattern = true) : pattern ≠ .apply declaration.dropConstructor [name] := by
  rintro rfl
  simp [isName, distinct] at nameShaped

/-- **The normal form of a name is a name**, and a normal form is a drop only for a drop. -/
theorem normal_shape_bounded (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) :
    ∀ (bound : Nat) (pattern : Pattern), sizeOf pattern < bound → dropsNamed declaration pattern = true →
      (isName declaration pattern = true → isName declaration (normal declaration pattern) = true) ∧
      (∀ name, normal declaration pattern = .apply declaration.dropConstructor [name] →
        ∃ argument, pattern = .apply declaration.dropConstructor [argument] ∧ normal declaration argument = name)
  | 0, _, small, _ => absurd small (Nat.not_lt_zero _)
  | _ + 1, .bvar index, _, _ => by
    refine ⟨fun _ => by rw [normal_bvar]; rfl, fun name same => ?_⟩
    rw [normal_bvar] at same; cases same
  | _ + 1, .fvar label, _, _ => by
    refine ⟨fun _ => by rw [normal_fvar]; rfl, fun name same => ?_⟩
    rw [normal_fvar] at same; cases same
  | _ + 1, .lambda binder body, _, _ => by
    refine ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => ?_⟩
    rw [normal_lambda] at same; cases same
  | _ + 1, .multiLambda arity binders body, _, _ => by
    refine ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => ?_⟩
    rw [normal_multiLambda] at same; cases same
  | _ + 1, .subst body replacement, _, _ => by
    refine ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => ?_⟩
    rw [normal_subst] at same; cases same
  | _ + 1, .collection kind elements rest, _, _ => by
    refine ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => ?_⟩
    rw [normal_collection] at same; cases same
  | bound + 1, .apply label arguments, small, named => by
    by_cases quoted : label = declaration.quoteConstructor
    · subst quoted
      rcases arguments with _ | ⟨payload, _ | ⟨second, rest⟩⟩
      · rw [normal_apply, List.map_nil, finish_nil]
        exact ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => by simp at same⟩
      rotate_left
      · rw [normal_apply, List.map_cons, List.map_cons, finish_long]
        exact ⟨fun nameShaped => by simp [isName] at nameShaped, fun name same => by simp at same⟩
      · have payloadNamed := dropsNamed_args named payload (by simp)
        rw [normal_apply, List.map_cons, List.map_nil]
        by_cases dropShaped : ∃ name, normal declaration payload = .apply declaration.dropConstructor [name]
        · obtain ⟨name, payloadNormal⟩ := dropShaped
          have payloadSmall : sizeOf payload < bound := by simp at small; omega
          obtain ⟨argument, rfl, argumentNormal⟩ :=
            (normal_shape_bounded distinct bound payload payloadSmall payloadNamed).2 name payloadNormal
          have argumentNamed := dropsNamed_args payloadNamed argument (by simp)
          have argumentName := dropsNamed_drop payloadNamed
          have argumentSmall : sizeOf argument < bound := by simp at small; omega
          have resultName := (normal_shape_bounded distinct bound argument argumentSmall argumentNamed).1 argumentName
          rw [payloadNormal, finish_drop]
          simp only [beq_self_eq_true, Bool.and_self, if_true]
          rw [← argumentNormal]
          exact ⟨fun _ => resultName, fun other same => absurd same (isName_not_drop distinct resultName)⟩
        · have plain : finishNormalizeReflectiveApply declaration declaration.quoteConstructor [normal declaration payload] =
              .apply declaration.quoteConstructor [normal declaration payload] :=
            finish_quote_plain (fun name same => dropShaped ⟨name, same⟩)
          rw [plain]
          exact ⟨fun _ => by simp [isName], fun name same => by simp at same; exact absurd same.1 distinct.symm⟩
    · rw [normal_apply, finish_not_quote quoted]
      refine ⟨fun nameShaped => ?_, fun name same => ?_⟩
      · match arguments, nameShaped with
        | [_], nameShaped => simp [isName, quoted] at nameShaped
        | [], nameShaped => simp [isName] at nameShaped
        | _ :: _ :: _, nameShaped => simp [isName] at nameShaped
      simp only [Pattern.apply.injEq] at same
      obtain ⟨rfl, mapped⟩ := same
      match arguments, mapped with
      | [argument], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        exact ⟨argument, rfl, mapped⟩

/-- **The normal form of a name is a name**, and a normal form is a drop only for a drop. -/
theorem normal_shape (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (pattern : Pattern)
    (named : dropsNamed declaration pattern = true) :
    (isName declaration pattern = true → isName declaration (normal declaration pattern) = true) ∧
      (∀ name, normal declaration pattern = .apply declaration.dropConstructor [name] →
        ∃ argument, pattern = .apply declaration.dropConstructor [argument] ∧ normal declaration argument = name) :=
  normal_shape_bounded distinct (sizeOf pattern + 1) pattern (Nat.lt_succ_self _) named

/-! ## Binder elimination -/

theorem nameMark_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (depth : Nat)
    (replacement name : Pattern) :
    nameMark declaration depth replacement (normal declaration name) = nameMark declaration depth replacement name := by
  unfold nameMark
  rw [show normalizeReflective declaration (normalizeReflective declaration name) = normalizeReflective declaration name
    from normal_idempotent distinct name]

theorem beq_false_of_ne' {label other : String} (different : label ≠ other) : (label == other) = false := by
  simpa using different

/-- **Binder elimination ignores the quote-drop normal form** of a term whose drops are applied
to names: reflective substitution looks at names only through their normal forms. -/
theorem instantiate_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor) (pattern : Pattern) :
    dropsNamed declaration pattern = true → ∀ depth replacement,
      instantiate declaration depth replacement pattern = instantiate declaration depth replacement (normal declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ depth replacement; rw [normal_bvar]
  | hfvar name => intro _ depth replacement; rw [normal_fvar]
  | happly label arguments ih =>
    intro named depth replacement
    have each := dropsNamed_args named
    by_cases single : arguments.length = 1
    · match arguments, single with
      | [payload], _ =>
        by_cases quoted : label = declaration.quoteConstructor
        · subst quoted
          -- the whole quotation is a name; reflective substitution sees only its normal form
          have normalName := (normal_shape distinct _ named).1 (by simp [isName])
          rw [instantiate_quote declaration depth replacement payload (by simp)]
          generalize normalEq : normal declaration (.apply declaration.quoteConstructor [payload]) = normalized at normalName
          have marked : nameMark declaration depth replacement (.apply declaration.quoteConstructor [payload]) =
              nameMark declaration depth replacement normalized := by
            rw [← normalEq, nameMark_normal distinct]
          have idem : normal declaration normalized = normalized := by
            rw [← normalEq]; exact normal_idempotent distinct _
          rw [marked]
          cases normalized with
          | bvar index => simp only [nameMark, normal_bvar, ReflectiveInstantiation.instantiate]
          | fvar name => simp only [nameMark, normal_fvar, ReflectiveInstantiation.instantiate]
          | apply inner arguments' =>
            match arguments', normalName with
            | [payload'], normalName =>
              have innerQuote : inner = declaration.quoteConstructor := by simpa [isName] using normalName
              subst innerQuote
              rw [instantiate_quote declaration depth replacement payload' (by simp)]
            | [], normalName => simp [isName] at normalName
            | _ :: _ :: _, normalName => simp [isName] at normalName
          | _ => simp [isName] at normalName
        · by_cases dropped : label = declaration.dropConstructor
          · subst dropped
            rw [normal_apply, List.map_cons, List.map_nil, plain_drop distinct,
              instantiate_drop declaration depth replacement payload (beq_false_of_ne' distinct) (by simp),
              instantiate_drop declaration depth replacement (normal declaration payload) (beq_false_of_ne' distinct)
                (by simp), nameMark_normal distinct]
          · rw [normal_apply, List.map_cons, List.map_nil, finish_not_quote quoted,
              instantiate_plainOne declaration depth replacement payload (beq_false_of_ne' quoted)
                (beq_false_of_ne' dropped),
              instantiate_plainOne declaration depth replacement (normal declaration payload) (beq_false_of_ne' quoted)
                (beq_false_of_ne' dropped), ih payload (by simp) (each payload (by simp)) depth replacement]
    · have finishPlain : finishNormalizeReflectiveApply declaration label (arguments.map (normal declaration)) =
          .apply label (arguments.map (normal declaration)) := by
        match arguments, single with
        | [], _ => exact finish_nil declaration label
        | _ :: _ :: _, _ => exact finish_long declaration label _ _ _
      rw [normal_apply, finishPlain, instantiate_many declaration depth replacement label single,
        instantiate_many declaration depth replacement label (by simpa using single), List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => ih argument member (each argument member) depth replacement
  | hlambda binder body ih =>
    intro named depth replacement
    rw [normal_lambda]
    simp only [ReflectiveInstantiation.instantiate]
    rw [ih (by rw [dropsNamed] at named; exact named)]
  | hmultiLambda arity binders body ih =>
    intro named depth replacement
    rw [normal_multiLambda]
    simp only [ReflectiveInstantiation.instantiate]
    rw [ih (by rw [dropsNamed] at named; exact named)]
  | hsubst body value bodyIH valueIH =>
    intro named depth replacement
    rw [dropsNamed, Bool.and_eq_true] at named
    rw [normal_subst]
    simp only [ReflectiveInstantiation.instantiate]
    rw [bodyIH named.1, valueIH named.2]
  | hcollection kind elements rest ih =>
    intro named depth replacement
    have each := dropsNamed_collection named
    rw [normal_collection]
    simp only [ReflectiveInstantiation.instantiate, instantiateList_map', List.map_map]
    congr 1
    exact List.map_congr_left fun element member => ih element member (each element member) depth replacement

/-- **The reflective binder operation commutes with the normal form of its body**, for a
replacement with one normalized form. -/
theorem reflectiveOperation_normal (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {replacement replacement' body : Pattern}
    (sameReplacement : normalizeReflectiveReplacement declaration replacement =
      normalizeReflectiveReplacement declaration replacement')
    (named : dropsNamed declaration body = true) :
    ScopedRuleInstantiation.reflectiveOperation declaration replacement body =
      ScopedRuleInstantiation.reflectiveOperation declaration replacement' (normal declaration body) := by
  unfold ScopedRuleInstantiation.reflectiveOperation
  rw [sameReplacement]
  exact instantiate_normal distinct body named 0 _

/-- An explicit quotation's normalized replacement depends only on the normal form of what it quotes. -/
theorem normalizeReflectiveReplacement_quote (payload payload' : Pattern)
    (same : normal declaration payload = normal declaration payload') :
    normalizeReflectiveReplacement declaration (.apply declaration.quoteConstructor [payload]) =
      normalizeReflectiveReplacement declaration (.apply declaration.quoteConstructor [payload']) := by
  simp only [normalizeReflectiveReplacement, beq_self_eq_true, if_true]
  exact congrArg (fun inner => Pattern.apply declaration.quoteConstructor [inner]) same

/-- **Ordinary binder elimination maps forward quote-drop chains to forward chains.** -/
theorem instantiateBVar_quoteDrop {replacement replacement' body body' : Pattern}
    (forwardReplacement : QuoteDropForward declaration replacement replacement')
    (forwardBody : QuoteDropForward declaration body body') :
    QuoteDropForward declaration (Substitution.instantiateBVar replacement body)
      (Substitution.instantiateBVar replacement' body') := by
  rw [← ContextSubstitution.substitute_single_eq_instantiateBVar,
    ← ContextSubstitution.substitute_single_eq_instantiateBVar]
  refine (forwardBody.substitute _).trans (quoteDropForward_substitute_assignment body' ?_)
  intro index
  cases index with
  | zero => exact forwardReplacement
  | succ => exact .refl

end Mettapedia.OSLF.MeTTaIL.QuoteDrop
