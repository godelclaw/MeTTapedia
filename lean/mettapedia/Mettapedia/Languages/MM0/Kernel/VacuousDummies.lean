import Mettapedia.Languages.MM0.Kernel.Unfolding

/-!
# Definitions up to vacuous dummies

A dummy of a definition that does not occur in its body is vacuous. An unfolding gives it a
fresh image, and that image then appears nowhere in the result. The canonical form of a body
keeps exactly the dummies that occur, in declared order, and renumbers them to follow the
parameters (`Definition.Body.canonical`). Two definitions that differ only in vacuous dummies
have the same canonical form.

* **Every unfolding survives.** An unfolding of a body is an unfolding of its canonical form
  with the images of the kept dummies, and it yields the same expression
  (`Definition.unfold?_canonical`).
* **And back.** An unfolding of the canonical form is an unfolding of the body as soon as the
  target context supplies fresh images for the vacuous positions; merging those images with
  the kept ones gives the same expression (`Definition.unfold?_of_canonical`).
* **Distinct dummies stay distinct.** Renumbering sends different kept dummies to different
  variables (`Preterm.renumber_var_injective`). One dummy used twice is never identified with
  two dummies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

/-! ## Selecting and merging by a mask -/

/-- The entries at the positions that the mask marks `true`. -/
def selectBy {α : Type} : List Bool → List α → List α
  | true :: mask, value :: values => value :: selectBy mask values
  | false :: mask, _ :: values => selectBy mask values
  | _, _ => []

/-- Interleave kept entries at `true` positions with extra entries at `false` positions. -/
def mergeBy {α : Type} : List Bool → List α → List α → List α
  | true :: mask, value :: kept, extra => value :: mergeBy mask kept extra
  | false :: mask, kept, value :: extra => value :: mergeBy mask kept extra
  | _, _, _ => []

@[simp] theorem selectBy_nil_right {α : Type} (mask : List Bool) : selectBy mask ([] : List α) = [] := by
  cases mask with
  | nil => rfl
  | cons marked mask => cases marked <;> rfl

theorem selectBy_mergeBy {α : Type} :
    ∀ (mask : List Bool) (kept extra : List α), kept.length = mask.count true →
      extra.length = mask.count false → selectBy mask (mergeBy mask kept extra) = kept
  | [], kept, _, keptLength, _ => by
      simp only [List.count_nil, List.length_eq_zero_iff] at keptLength
      subst kept
      rfl
  | true :: mask, [], _, keptLength, _ => by simp at keptLength
  | true :: mask, value :: kept, extra, keptLength, extraLength => by
      simp only [List.count_cons_self, List.length_cons, Nat.add_right_cancel_iff] at keptLength
      simp only [List.count_cons, beq_iff_eq, Bool.true_eq_false, ↓reduceIte, Nat.add_zero] at extraLength
      simp [mergeBy, selectBy, selectBy_mergeBy mask kept extra keptLength extraLength]
  | false :: mask, kept, [], _, extraLength => by simp at extraLength
  | false :: mask, kept, value :: extra, keptLength, extraLength => by
      simp only [List.count_cons, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at keptLength
      simp only [List.count_cons_self, List.length_cons, Nat.add_right_cancel_iff] at extraLength
      simp [mergeBy, selectBy, selectBy_mergeBy mask kept extra keptLength extraLength]

theorem mergeBy_length {α : Type} :
    ∀ (mask : List Bool) (kept extra : List α), kept.length = mask.count true →
      extra.length = mask.count false → (mergeBy mask kept extra).length = mask.length
  | [], _, _, _, _ => rfl
  | true :: mask, [], _, keptLength, _ => by simp at keptLength
  | true :: mask, value :: kept, extra, keptLength, extraLength => by
      simp only [List.count_cons_self, List.length_cons, Nat.add_right_cancel_iff] at keptLength
      simp only [List.count_cons, beq_iff_eq, Bool.true_eq_false, ↓reduceIte, Nat.add_zero] at extraLength
      simp [mergeBy, mergeBy_length mask kept extra keptLength extraLength]
  | false :: mask, kept, [], _, extraLength => by simp at extraLength
  | false :: mask, kept, value :: extra, keptLength, extraLength => by
      simp only [List.count_cons, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at keptLength
      simp only [List.count_cons_self, List.length_cons, Nat.add_right_cancel_iff] at extraLength
      simp [mergeBy, mergeBy_length mask kept extra keptLength extraLength]

theorem selectBy_length {α : Type} :
    ∀ (mask : List Bool) (values : List α), mask.length = values.length →
      (selectBy mask values).length = mask.count true
  | [], [], _ => rfl
  | [], _ :: _, lengths => by simp at lengths
  | _ :: _, [], lengths => by simp at lengths
  | true :: mask, _ :: values, lengths => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      simp [selectBy, selectBy_length mask values lengths]
  | false :: mask, _ :: values, lengths => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      simp [selectBy, selectBy_length mask values lengths]

/-- A kept position has fewer kept positions before it than the mask has in all. -/
theorem count_take_lt_count :
    ∀ (mask : List Bool) (position : Nat), mask[position]? = some true →
      (mask.take position).count true < mask.count true
  | [], _, marked => by simp at marked
  | true :: _, 0, _ => by simp
  | false :: _, 0, marked => by simp at marked
  | marked :: mask, position + 1, kept => by
      simp only [List.getElem?_cons_succ] at kept
      have inner := count_take_lt_count mask position kept
      cases marked <;> simp [List.take_succ_cons, inner]

/-- A kept entry sits in the selection after the kept entries before it. -/
theorem selectBy_getElem? {α : Type} :
    ∀ (mask : List Bool) (values : List α) (position : Nat),
      mask.length = values.length → mask[position]? = some true →
        (selectBy mask values)[(mask.take position).count true]? = values[position]?
  | [], _, _, _, marked => by simp at marked
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | true :: mask, value :: values, 0, _, _ => by simp [selectBy]
  | false :: mask, value :: values, 0, _, marked => by simp at marked
  | true :: mask, value :: values, position + 1, lengths, marked => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      simp only [List.getElem?_cons_succ] at marked
      simp [selectBy, List.take_succ_cons, selectBy_getElem? mask values position lengths marked]
  | false :: mask, value :: values, position + 1, lengths, marked => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      simp only [List.getElem?_cons_succ] at marked
      simp [selectBy, List.take_succ_cons, selectBy_getElem? mask values position lengths marked]

/-- Kept entries before a position are fewer than kept entries before a later kept one. -/
theorem count_take_lt_of_lt :
    ∀ (mask : List Bool) (first second : Nat), first < second → mask[first]? = some true →
      (mask.take first).count true < (mask.take second).count true
  | [], _, _, _, marked => by simp at marked
  | true :: _, 0, second + 1, _, _ => by simp [List.take_succ_cons]
  | false :: _, 0, _ + 1, _, marked => by simp at marked
  | marked :: mask, first + 1, second + 1, before, kept => by
      simp only [List.getElem?_cons_succ] at kept
      have inner := count_take_lt_of_lt mask first second (by omega) kept
      cases marked <;> simp [List.take_succ_cons, inner]
  | _ :: _, _ + 1, 0, before, _ => by omega

namespace Preterm

/-- Syntactic occurrence of a variable, decided. -/
def mentions (index : Nat) : Preterm → Bool
  | .var other => other == index
  | .term _ => false
  | .app function argument => function.mentions index || argument.mentions index

theorem mentions_iff (index : Nat) (expression : Preterm) :
    expression.mentions index = true ↔ Occurs index expression := by
  induction expression with
  | var other =>
      constructor
      · intro found
        have same : other = index := by simpa [mentions] using found
        subst same
        exact .var
      · intro found
        cases found
        simp [mentions]
  | term other =>
      simp only [mentions, Bool.false_eq_true, false_iff]
      intro found
      cases found
  | app function argument functionIff argumentIff =>
      simp only [mentions, Bool.or_eq_true, functionIff, argumentIff]
      constructor
      · rintro (found | found)
        · exact .function found
        · exact .argument found
      · intro found
        cases found with
        | function found => exact Or.inl found
        | argument found => exact Or.inr found

/-- Parameters keep their indices; a kept dummy moves to the parameters' end plus the number
of kept dummies before it; a dummy outside the mask is refused. -/
def renumber (arity : Nat) (mask : List Bool) : Preterm → Option Preterm
  | .var index =>
      if index < arity then some (.var index)
      else if mask[index - arity]? = some true then
        some (.var (arity + (mask.take (index - arity)).count true))
      else none
  | .term index => some (.term index)
  | .app function argument => do
      let function' ← renumber arity mask function
      let argument' ← renumber arity mask argument
      pure (.app function' argument')

/-- **Renumbering never merges two variables.** -/
theorem renumber_var_injective {arity : Nat} {mask : List Bool} {firstIndex secondIndex : Nat}
    {image : Preterm} (firstImage : renumber arity mask (.var firstIndex) = some image)
    (secondImage : renumber arity mask (.var secondIndex) = some image) :
    firstIndex = secondIndex := by
  have kept : ∀ {index : Nat}, renumber arity mask (.var index) = some image →
      (index < arity ∧ image = .var index) ∨
        (arity ≤ index ∧ mask[index - arity]? = some true ∧
          image = .var (arity + (mask.take (index - arity)).count true)) := by
    intro index renumbered
    simp only [renumber] at renumbered
    by_cases parameter : index < arity
    · simp only [parameter, ↓reduceIte, Option.some.injEq] at renumbered
      exact Or.inl ⟨parameter, renumbered.symm⟩
    · by_cases marked : mask[index - arity]? = some true
      · simp only [parameter, marked, ↓reduceIte, Option.some.injEq] at renumbered
        exact Or.inr ⟨by omega, marked, renumbered.symm⟩
      · simp [parameter, marked] at renumbered
  rcases kept firstImage with ⟨firstParameter, firstEq⟩ | ⟨firstOutside, firstKept, firstEq⟩ <;>
    rcases kept secondImage with ⟨secondParameter, secondEq⟩ | ⟨secondOutside, secondKept, secondEq⟩
  · rw [firstEq, Preterm.var.injEq] at secondEq
    exact secondEq
  · rw [firstEq, Preterm.var.injEq] at secondEq
    omega
  · rw [firstEq, Preterm.var.injEq] at secondEq
    omega
  · rw [firstEq, Preterm.var.injEq] at secondEq
    have counts : (mask.take (firstIndex - arity)).count true =
        (mask.take (secondIndex - arity)).count true := by omega
    rcases Nat.lt_trichotomy (firstIndex - arity) (secondIndex - arity) with less | same | greater
    · exact absurd counts (Nat.ne_of_lt (count_take_lt_of_lt mask _ _ less firstKept))
    · omega
    · exact absurd counts.symm (Nat.ne_of_lt (count_take_lt_of_lt mask _ _ greater secondKept))

/-- **Substituting into a renumbered body agrees with substituting into the body.** The
kept images replace the full images; parameters are untouched. -/
theorem substitute_renumber {arity : Nat} {mask : List Bool} {arguments : List Preterm}
    {images : List Nat} (arityEq : arguments.length = arity) (lengthEq : mask.length = images.length) :
    ∀ {expression renumbered : Preterm}, renumber arity mask expression = some renumbered →
      renumbered.substitute
          (Substitution.ofList (Definition.substitutionValues arguments (selectBy mask images))) =
        expression.substitute (Substitution.ofList (Definition.substitutionValues arguments images)) := by
  intro expression
  induction expression with
  | var index =>
      intro renumbered renumbering
      simp only [renumber] at renumbering
      split at renumbering
      · rename_i parameter
        simp only [Option.some.injEq] at renumbering
        subst renumbered
        have bounded : index < arguments.length := by omega
        simp [substitute, Substitution.ofList, Definition.substitutionValues,
          List.getElem?_append_left bounded]
      · rename_i outside
        split at renumbering
        · rename_i kept
          simp only [Option.some.injEq] at renumbering
          subst renumbered
          have selected := selectBy_getElem? mask images (index - arity) lengthEq kept
          have notLeft : arguments.length ≤ index := by omega
          have notLeft' : arguments.length ≤ arity + (mask.take (index - arity)).count true := by omega
          simp only [substitute, Substitution.ofList, Definition.substitutionValues,
            List.getElem?_append_right notLeft, List.getElem?_append_right notLeft', List.getElem?_map,
            arityEq, Nat.add_sub_cancel_left, selected]
        · simp at renumbering
  | term index =>
      intro renumbered renumbering
      simp only [renumber, Option.some.injEq] at renumbering
      subst renumbered
      rfl
  | app function argument functionIh argumentIh =>
      intro renumbered renumbering
      simp only [renumber] at renumbering
      obtain ⟨function', functionRenumbered, afterFunction⟩ := Option.bind_eq_some_iff.mp renumbering
      obtain ⟨argument', argumentRenumbered, output⟩ := Option.bind_eq_some_iff.mp afterFunction
      simp only [Option.pure_def, Option.some.injEq] at output
      subst renumbered
      simp [substitute, functionIh functionRenumbered, argumentIh argumentRenumbered]

end Preterm

namespace Definition

/-- For each dummy, whether its variable occurs in the body. -/
def Body.usage (arity : Nat) (body : Body) : List Bool :=
  (List.range body.dummies.length).map fun position => body.expression.mentions (arity + position)

theorem Body.usage_length (arity : Nat) (body : Body) : (body.usage arity).length = body.dummies.length := by
  simp [Body.usage]

/-- The body with exactly the dummies it uses, in declared order, renumbered after the
`arity` parameters. A body that mentions a variable beyond its dummies has none. -/
def Body.canonical (arity : Nat) (body : Body) : Option Body :=
  (Preterm.renumber arity (body.usage arity) body.expression).map fun expression =>
    ⟨selectBy (body.usage arity) body.dummies, expression⟩

theorem Body.canonical_eq_some_iff (arity : Nat) (body result : Body) :
    body.canonical arity = some result ↔
      result.dummies = selectBy (body.usage arity) body.dummies ∧
        Preterm.renumber arity (body.usage arity) body.expression = some result.expression := by
  cases result with
  | mk dummies expression =>
      simp only [Body.canonical, Option.map_eq_some_iff, Body.mk.injEq]
      constructor
      · rintro ⟨expression', renumbered, rfl, rfl⟩
        exact ⟨rfl, renumbered⟩
      · rintro ⟨rfl, renumbered⟩
        exact ⟨expression, renumbered, rfl, rfl⟩

/-- Fewer parameter images leave every dummy image fresh. -/
theorem FreshDummies.weaken {target : Context} {arguments arguments' : List Preterm}
    {sorts images : List Nat} (fresh : FreshDummies target arguments sorts images)
    (subset : ∀ expression ∈ arguments', expression ∈ arguments) :
    FreshDummies target arguments' sorts images := by
  induction fresh generalizing arguments' with
  | nil => exact .nil _
  | cons lookup freshFor _ ih =>
      refine .cons lookup (fun expression member => freshFor expression (subset expression member)) ?_
      apply ih
      intro expression member
      rcases List.mem_append.mp member with earlier | last
      · exact List.mem_append_left _ (subset expression earlier)
      · exact List.mem_append_right _ last

/-- Any selection of fresh dummy images is fresh. -/
theorem FreshDummies.select {target : Context} {arguments : List Preterm} {sorts images : List Nat}
    (fresh : FreshDummies target arguments sorts images) :
    ∀ (mask : List Bool), mask.length = sorts.length →
      FreshDummies target arguments (selectBy mask sorts) (selectBy mask images) := by
  induction fresh with
  | nil => intro mask _; simpa using FreshDummies.nil (target := target) _
  | @cons arguments sort image sorts images lookup freshFor tail ih =>
      intro mask lengths
      cases mask with
      | nil => simp at lengths
      | cons marked mask =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
          cases marked with
          | true => exact .cons lookup freshFor (ih mask lengths)
          | false =>
              exact FreshDummies.weaken (ih mask lengths)
                (fun expression member => List.mem_append_left _ member)

/-- **Every unfolding of a body is an unfolding of its canonical form.** The images of the
vacuous dummies are dropped, and the result is the same expression. -/
theorem unfold?_canonical {signature : TermSignature} {definitions canonicalDefinitions : Signature}
    {target : Context} {symbol : Nat} {arguments : List Preterm} {images : List Nat}
    {declaration : TermDecl} {body canonicalBody : Body} {result : Preterm}
    (declared : signature symbol = some declaration) (original : definitions symbol = some body)
    (canonical : canonicalDefinitions symbol = some canonicalBody)
    (canonicalized : body.canonical declaration.arguments.length = some canonicalBody)
    (unfolded : unfold? signature definitions target symbol arguments images = some result) :
    unfold? signature canonicalDefinitions target symbol arguments
      (selectBy (body.usage declaration.arguments.length) images) = some result := by
  obtain ⟨dummiesEq, renumbered⟩ := (Body.canonical_eq_some_iff _ body canonicalBody).mp canonicalized
  cases (unfold_eq_some_iff signature definitions target symbol arguments images result).mp unfolded with
  | intro declared' original' typed fresh substituted =>
      rw [declared] at declared'
      cases declared'
      rw [original] at original'
      cases original'
      have arity := typed.length_eq
      have lengths : (body.usage declaration.arguments.length).length = images.length := by
        rw [Body.usage_length]
        exact fresh.length_eq
      apply (unfold_eq_some_iff signature canonicalDefinitions target symbol arguments _ result).mpr
      refine .intro declared canonical typed ?_ ?_
      · rw [dummiesEq]
        exact fresh.select _ (Body.usage_length _ _)
      · apply Preterm.substitute_sound
        rw [Preterm.substitute_renumber arity lengths renumbered]
        exact substituted.eval

/-- **An unfolding of the canonical form is an unfolding of the body** once the target
context supplies images for the vacuous positions that, merged with the kept images, are
fresh for the body's dummies. -/
theorem unfold?_of_canonical {signature : TermSignature} {definitions canonicalDefinitions : Signature}
    {target : Context} {symbol : Nat} {arguments : List Preterm} {kept extra : List Nat}
    {declaration : TermDecl} {body canonicalBody : Body} {result : Preterm}
    (declared : signature symbol = some declaration) (original : definitions symbol = some body)
    (canonical : canonicalDefinitions symbol = some canonicalBody)
    (canonicalized : body.canonical declaration.arguments.length = some canonicalBody)
    (keptLength : kept.length = (body.usage declaration.arguments.length).count true)
    (extraLength : extra.length = (body.usage declaration.arguments.length).count false)
    (merged : FreshDummies target arguments body.dummies
      (mergeBy (body.usage declaration.arguments.length) kept extra))
    (unfolded : unfold? signature canonicalDefinitions target symbol arguments kept = some result) :
    unfold? signature definitions target symbol arguments
      (mergeBy (body.usage declaration.arguments.length) kept extra) = some result := by
  obtain ⟨_, renumbered⟩ := (Body.canonical_eq_some_iff _ body canonicalBody).mp canonicalized
  cases (unfold_eq_some_iff signature canonicalDefinitions target symbol arguments kept result).mp
      unfolded with
  | intro declared' canonical' typed _ substituted =>
      rw [declared] at declared'
      cases declared'
      rw [canonical] at canonical'
      cases canonical'
      have arity := typed.length_eq
      have lengths : (body.usage declaration.arguments.length).length =
          (mergeBy (body.usage declaration.arguments.length) kept extra).length := by
        rw [mergeBy_length _ kept extra keptLength extraLength]
      apply (unfold_eq_some_iff signature definitions target symbol arguments _ result).mpr
      refine .intro declared original typed merged ?_
      apply Preterm.substitute_sound
      rw [← Preterm.substitute_renumber arity lengths renumbered,
        selectBy_mergeBy _ kept extra keptLength extraLength]
      exact substituted.eval

end Definition

/-! ## Controls -/

namespace VacuousDummiesControls

open Definition

/-- `pair d0` with arguments `x` and dummies `d0 d1`: `d1` is vacuous. -/
def withVacuous : Body := ⟨[1, 0], .app (.app (.term 0) (.var 0)) (.var 1)⟩

/-- `pair x d` with one parameter and dummies `d0 d1 d2`, of which `d0` and `d2` occur. -/
def gapped : Body := ⟨[1, 0, 1], .app (.app (.term 0) (.var 3)) (.var 1)⟩

/-- The parts of a canonical form, for comparison. -/
def parts (body : Option Body) : Option (List Nat × Preterm) :=
  body.map fun body => (body.dummies, body.expression)

theorem withVacuous_canonical :
    parts (withVacuous.canonical 1) = some ([1], .app (.app (.term 0) (.var 0)) (.var 1)) := by
  decide

theorem gapped_canonical :
    parts (gapped.canonical 1) = some ([1, 1], .app (.app (.term 0) (.var 2)) (.var 1)) := by
  decide

/-- A body that uses every dummy is its own canonical form. -/
theorem full_canonical :
    parts ((⟨[1, 1], .app (.app (.term 0) (.var 1)) (.var 2)⟩ : Body).canonical 1) =
      some ([1, 1], .app (.app (.term 0) (.var 1)) (.var 2)) := by
  decide

/-- One dummy used twice keeps one dummy; two dummies keep two, so the two bodies differ. -/
theorem one_dummy_is_not_two :
    parts ((⟨[1], .app (.app (.term 0) (.var 0)) (.var 0)⟩ : Body).canonical 0) ≠
      parts ((⟨[1, 1], .app (.app (.term 0) (.var 0)) (.var 1)⟩ : Body).canonical 0) := by
  decide

/-- A variable beyond the dummies has no canonical form. -/
theorem out_of_scope_refused : parts ((⟨[1], .var 5⟩ : Body).canonical 1) = none := by
  decide

end VacuousDummiesControls

end Mettapedia.Languages.MM0.Kernel
