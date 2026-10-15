import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mettapedia.GSLT.LanguageDef.ProofSystems
import Mettapedia.Languages.MM0.Kernel.ProofChecking
import Mettapedia.Languages.MM0.Kernel.TheoryAdmission
import Mettapedia.Languages.MM0.Kernel.FirstOrderEnumeration

/-!
# The MM0 kernel is a proof system in the sense of Cook and Reckhow

The kernel's checker `ProofWitness.proof?` computes the conclusion of a witness, so it
is a proof system in Cook and Reckhow's function form: a context, hypotheses and a
witness determine the sequent they prove (`functionForm_exact`). It never searches.
Each theorem application names the theorem and its arguments, and each conversion names
its steps. `derives_iff_checked` makes it exact for kernel derivability.

This module measures the work. Every function the checker calls gets a time function
in the style of Nipkow et al., defined equation by equation: one unit per call, the
times of the calls it makes, and explicit charges for primitive operations.

* A list lookup at position `i` costs `min i length + 1`.
* A signature lookup costs one, as a table access.
* A comparison of two expressions costs the sum of their sizes.
* A union of finite sets `A` and `B` costs `(|A| + 1) * (|B| + 1)`.
* Where the checker stops early at a failed conjunction, the time function may charge
  the rest anyway; it bounds the time from above.

The result is a polynomial bound. Let `N` be the size of the witness, the context and
the hypotheses, plus the width of the theory (its largest theorem statement with its
context, and its largest definition body with its dummies). Computing the conclusion
takes time at most `1024 * (N + 1) ^ 6` (`proofTime_le`). So for every theory of
bounded width, and in particular for every finite theory, the checker is a proof system
in Cook and Reckhow's sense (`proofSystem`, `Theory.proofSystem`).

Expressions are trees here, without the sharing of the binary format. For the binary
format, `Formats.MMB.MachineCost` counts the reference machine's transitions, which are
linear in the proof for fixed tables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

/-! ## Sizes -/

namespace Preterm

/-- The number of nodes of an expression. -/
def size : Preterm → Nat
  | .var _ => 1
  | .term _ => 1
  | .app function argument => function.size + argument.size + 1

theorem one_le_size (expression : Preterm) : 1 ≤ expression.size := by
  cases expression <;> simp [size]

end Preterm

/-- The total size of a list of expressions. -/
def sizes (expressions : List Preterm) : Nat := (expressions.map Preterm.size).sum

theorem size_le_sizes {expressions : List Preterm} {expression : Preterm}
    (member : expression ∈ expressions) : expression.size ≤ sizes expressions := by
  unfold sizes
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨expression, member, rfl⟩)

theorem sizes_cons (expression : Preterm) (expressions : List Preterm) :
    sizes (expression :: expressions) = expression.size + sizes expressions := by
  simp [sizes]

/-- The number of dependencies a binder records. -/
def Binder.dependencyCount : Binder → Nat
  | .bound _ => 0
  | .regular _ dependencies => dependencies.card

/-- The size of a context: its length plus all recorded dependencies. -/
def contextWeight (context : Context) : Nat :=
  context.length + (context.map Binder.dependencyCount).sum

namespace Cost

/-! ## Primitive charges -/

/-- A lookup at position `index` walks the list up to that position or its end. -/
def lookupTime {α : Type} (list : List α) (index : Nat) : Nat := min index list.length + 1

theorem lookupTime_le {α : Type} (list : List α) (index : Nat) :
    lookupTime list index ≤ list.length + 1 := by
  unfold lookupTime; omega

/-! ## Substitution -/

/-- Time of `Preterm.substitute (Substitution.ofList values)`. -/
def substituteTime (values : List Preterm) : Preterm → Nat
  | .var index => lookupTime values index + 1
  | .term _ => 1
  | .app function argument =>
      substituteTime values function + 1 +
        match function.substitute (Substitution.ofList values) with
        | none => 0
        | some _ => substituteTime values argument

theorem substituteTime_le (values : List Preterm) (expression : Preterm) :
    substituteTime values expression ≤ expression.size * (values.length + 2) := by
  induction expression with
  | var index => simp only [substituteTime, Preterm.size]; have := lookupTime_le values index; omega
  | term _ => simp only [substituteTime, Preterm.size]; omega
  | app function argument ihFunction ihArgument =>
      simp only [substituteTime, Preterm.size]
      have choice : (match function.substitute (Substitution.ofList values) with
          | none => 0
          | some _ => substituteTime values argument) ≤ substituteTime values argument := by
        split <;> omega
      nlinarith

/-- A substituted expression is at most the source size times one more than the total
size of the values. -/
theorem size_substitute {values : List Preterm} {expression result : Preterm}
    (substituted : expression.substitute (Substitution.ofList values) = some result) :
    result.size ≤ expression.size * (sizes values + 1) := by
  induction expression generalizing result with
  | var index =>
      simp only [Preterm.substitute, Substitution.ofList] at substituted
      have member : result ∈ values := List.mem_of_getElem? substituted
      have := size_le_sizes member
      simp only [Preterm.size]
      omega
  | term index =>
      simp only [Preterm.substitute, Option.some.injEq] at substituted
      subst substituted
      simp [Preterm.size]
  | app function argument ihFunction ihArgument =>
      simp only [Preterm.substitute, Option.bind_eq_bind] at substituted
      cases first : function.substitute (Substitution.ofList values) with
      | none => simp [first] at substituted
      | some function' =>
          cases second : argument.substitute (Substitution.ofList values) with
          | none => simp [first, second] at substituted
          | some argument' =>
              simp only [first, second, Option.bind_some, Option.pure_def,
                Option.some.injEq] at substituted
              subst substituted
              have left := ihFunction first
              have right := ihArgument second
              simp only [Preterm.size]
              nlinarith

/-- Time of `Substitution.substituteList (Substitution.ofList values)`. -/
def substituteListTime (values : List Preterm) : List Preterm → Nat
  | [] => 1
  | expression :: expressions =>
      substituteTime values expression + 1 +
        match expression.substitute (Substitution.ofList values) with
        | none => 0
        | some _ => substituteListTime values expressions

theorem substituteListTime_le (values : List Preterm) (expressions : List Preterm) :
    substituteListTime values expressions ≤
      (sizes expressions + expressions.length + 1) * (values.length + 2) := by
  induction expressions with
  | nil => simp [substituteListTime, sizes]
  | cons expression expressions ih =>
      simp only [substituteListTime, sizes_cons, List.length_cons]
      have head := substituteTime_le values expression
      have choice : (match expression.substitute (Substitution.ofList values) with
          | none => 0
          | some _ => substituteListTime values expressions) ≤
            substituteListTime values expressions := by
        split <;> omega
      nlinarith

theorem sizes_substituteList {values expressions results : List Preterm}
    (substituted : Substitution.substituteList (Substitution.ofList values) expressions = some results) :
    sizes results ≤ sizes expressions * (sizes values + 1) := by
  induction expressions generalizing results with
  | nil =>
      simp only [Substitution.substituteList, Option.some.injEq] at substituted
      subst substituted
      simp [sizes]
  | cons expression expressions ih =>
      simp only [Substitution.substituteList, Option.bind_eq_bind] at substituted
      cases first : expression.substitute (Substitution.ofList values) with
      | none => simp [first] at substituted
      | some result =>
          cases rest : Substitution.substituteList (Substitution.ofList values) expressions with
          | none => simp [first, rest] at substituted
          | some results' =>
              simp only [first, rest, Option.bind_some, Option.pure_def,
                Option.some.injEq] at substituted
              subst substituted
              have head := size_substitute first
              have tail := ih rest
              simp only [sizes_cons]
              nlinarith

/-! ## Typing -/

/-- Time of `Preterm.boundSort?`. -/
def boundSortTime (context : Context) : Preterm → Nat
  | .var index => lookupTime context index + 1
  | _ => 1

theorem boundSortTime_le (context : Context) (expression : Preterm) :
    boundSortTime context expression ≤ context.length + 2 := by
  cases expression with
  | var index => simp only [boundSortTime]; have := lookupTime_le context index; omega
  | term _ => simp [boundSortTime]
  | app _ _ => simp [boundSortTime]

/-- Time of `Preterm.infer`. -/
def inferTime (signature : TermSignature) (context : Context) : Preterm → Nat
  | .var index => lookupTime context index + 1
  | .term _ => 2
  | .app function argument =>
      inferTime signature context function + 1 +
        match Preterm.infer signature context function with
        | some (.bound _ :: _, _) => boundSortTime context argument + 1
        | some (.regular _ _ :: _, _) => inferTime signature context argument + 1
        | _ => 0

theorem inferTime_le (signature : TermSignature) (context : Context) (expression : Preterm) :
    inferTime signature context expression ≤ expression.size * (context.length + 3) := by
  induction expression with
  | var index => simp only [inferTime, Preterm.size]; have := lookupTime_le context index; omega
  | term _ => simp only [inferTime, Preterm.size]; omega
  | app function argument ihFunction ihArgument =>
      simp only [inferTime, Preterm.size]
      have bounded := boundSortTime_le context argument
      have positive := Preterm.one_le_size argument
      have choice : (match Preterm.infer signature context function with
          | some (.bound _ :: _, _) => boundSortTime context argument + 1
          | some (.regular _ _ :: _, _) => inferTime signature context argument + 1
          | _ => 0) ≤ argument.size * (context.length + 3) + 1 := by
        split
        · have widened : context.length + 2 ≤ argument.size * (context.length + 3) := by nlinarith
          exact Nat.add_le_add_right (bounded.trans widened) 1
        · exact Nat.add_le_add_right ihArgument 1
        · exact Nat.zero_le _
      nlinarith

/-- Time of `Preterm.checkBinder`. -/
def checkBinderTime (signature : TermSignature) (context : Context) (expression : Preterm) :
    Binder → Nat
  | .bound _ => boundSortTime context expression + 1
  | .regular _ _ => inferTime signature context expression + 1

theorem checkBinderTime_le (signature : TermSignature) (context : Context) (expression : Preterm)
    (binder : Binder) :
    checkBinderTime signature context expression binder ≤
      expression.size * (context.length + 3) + 1 := by
  have positive := Preterm.one_le_size expression
  cases binder with
  | bound _ => simp only [checkBinderTime]; have := boundSortTime_le context expression; nlinarith
  | regular _ _ => simp only [checkBinderTime]; have := inferTime_le signature context expression; omega

/-- Time of `Substitution.checkArguments`. -/
def checkArgumentsTime (signature : TermSignature) (context : Context) :
    List Preterm → Context → Nat
  | [], [] => 1
  | expression :: expressions, binder :: binders =>
      checkBinderTime signature context expression binder + 1 +
        if Preterm.checkBinder signature context expression binder then
          checkArgumentsTime signature context expressions binders
        else 0
  | _, _ => 1

theorem checkArgumentsTime_le (signature : TermSignature) (context : Context)
    (expressions : List Preterm) (binders : Context) :
    checkArgumentsTime signature context expressions binders ≤
      (sizes expressions + 1) * (context.length + 3) + 2 * expressions.length := by
  induction expressions generalizing binders with
  | nil => cases binders <;> simp [checkArgumentsTime, sizes]
  | cons expression expressions ih =>
      cases binders with
      | nil => simp [checkArgumentsTime]; nlinarith
      | cons binder binders =>
          simp only [checkArgumentsTime, sizes_cons, List.length_cons]
          have head := checkBinderTime_le signature context expression binder
          have tail := ih binders
          have choice : (if Preterm.checkBinder signature context expression binder then
              checkArgumentsTime signature context expressions binders else 0) ≤
                checkArgumentsTime signature context expressions binders := by
            split <;> omega
          nlinarith

/-! ## Supports and admissible substitution -/

/-- The dependencies a binder records, as a set. -/
def binderDependencies : Binder → Finset Nat
  | .bound _ => ∅
  | .regular _ dependencies => dependencies

/-- Every index a support can mention: the positions of the context and the recorded
dependencies. -/
def contextIndices (context : Context) : Finset Nat :=
  Finset.range context.length ∪ (context.map binderDependencies).foldr (· ∪ ·) ∅

theorem card_foldr_union_le (sets : List (Finset Nat)) :
    (sets.foldr (· ∪ ·) ∅).card ≤ (sets.map Finset.card).sum := by
  induction sets with
  | nil => simp
  | cons set sets ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem card_contextIndices_le (context : Context) :
    (contextIndices context).card ≤ contextWeight context := by
  unfold contextIndices contextWeight
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · simp
  · refine (card_foldr_union_le _).trans (le_of_eq ?_)
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro binder _
    cases binder <;> rfl

theorem subset_foldr_union {sets : List (Finset Nat)} {set : Finset Nat} (member : set ∈ sets) :
    set ⊆ sets.foldr (· ∪ ·) ∅ := by
  induction sets with
  | nil => cases member
  | cons first sets ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Finset.subset_union_left
      · exact (ih later).trans Finset.subset_union_right

theorem support_subset {context : Context} {expression : Preterm} {support : Finset Nat}
    (computed : Preterm.support? context expression = some support) :
    support ⊆ contextIndices context := by
  induction expression generalizing support with
  | var index =>
      simp only [Preterm.support?, Option.bind_eq_bind] at computed
      cases lookup : context[index]? with
      | none => simp [lookup] at computed
      | some binder =>
          have position : index < context.length := (List.getElem?_eq_some_iff.mp lookup).1
          cases binder with
          | bound sort =>
              simp only [lookup, Option.bind_some, Option.pure_def, Option.some.injEq] at computed
              subst computed
              intro element member
              rw [Finset.mem_singleton] at member
              subst member
              exact Finset.mem_union_left _ (Finset.mem_range.mpr position)
          | regular sort dependencies =>
              simp only [lookup, Option.bind_some, Option.pure_def, Option.some.injEq] at computed
              subst computed
              refine Finset.subset_union_right.trans' (subset_foldr_union ?_)
              exact List.mem_map.mpr ⟨.regular sort dependencies, List.mem_of_getElem? lookup, rfl⟩
  | term index =>
      simp only [Preterm.support?, Option.some.injEq] at computed
      subst computed
      exact Finset.empty_subset _
  | app function argument ihFunction ihArgument =>
      simp only [Preterm.support?, Option.bind_eq_bind] at computed
      cases left : Preterm.support? context function with
      | none => simp [left] at computed
      | some leftSupport =>
          cases right : Preterm.support? context argument with
          | none => simp [left, right] at computed
          | some rightSupport =>
              simp only [left, right, Option.bind_some, Option.pure_def,
                Option.some.injEq] at computed
              subst computed
              exact Finset.union_subset (ihFunction left) (ihArgument right)

theorem card_support_le {context : Context} {expression : Preterm} {support : Finset Nat}
    (computed : Preterm.support? context expression = some support) :
    support.card ≤ contextWeight context :=
  (Finset.card_le_card (support_subset computed)).trans (card_contextIndices_le context)

/-- Time of `Preterm.support?`. A union is charged the product of the two sizes. -/
def supportTime (context : Context) : Preterm → Nat
  | .var index => lookupTime context index + 1
  | .term _ => 1
  | .app function argument =>
      supportTime context function + 1 +
        match Preterm.support? context function with
        | none => 0
        | some left =>
            supportTime context argument +
              match Preterm.support? context argument with
              | none => 0
              | some right => (left.card + 1) * (right.card + 1)

theorem supportTime_le (context : Context) (expression : Preterm) :
    supportTime context expression ≤
      expression.size * (context.length + 2 + (contextWeight context + 1) ^ 2) := by
  induction expression with
  | var index => simp only [supportTime, Preterm.size]; have := lookupTime_le context index; nlinarith
  | term _ => simp only [supportTime, Preterm.size]; nlinarith
  | app function argument ihFunction ihArgument =>
      simp only [supportTime, Preterm.size]
      have choice : (match Preterm.support? context function with
          | none => 0
          | some left =>
              supportTime context argument +
                match Preterm.support? context argument with
                | none => 0
                | some right => (left.card + 1) * (right.card + 1)) ≤
            supportTime context argument + (contextWeight context + 1) ^ 2 := by
        cases left : Preterm.support? context function with
        | none => exact Nat.zero_le _
        | some leftSupport =>
            simp only []
            cases right : Preterm.support? context argument with
            | none => simp
            | some rightSupport =>
                simp only []
                have leftCard := card_support_le left
                have rightCard := card_support_le right
                have product : (leftSupport.card + 1) * (rightSupport.card + 1) ≤
                    (contextWeight context + 1) ^ 2 := by
                  rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
                omega
      nlinarith

/-- Time of deciding `Binder.DependsOn`: a membership test in the recorded
dependencies. -/
def dependsOnTime : Binder → Nat
  | .bound _ => 1
  | .regular _ dependencies => dependencies.card + 1

theorem dependsOnTime_le (binder : Binder) : dependsOnTime binder ≤ binder.dependencyCount + 1 := by
  cases binder <;> simp [dependsOnTime, Binder.dependencyCount]

/-- Time of `Substitution.checkPair`. -/
def checkPairTime (target : Context) (formalBound : Nat) (other : Substitution.Entry) : Nat :=
  dependsOnTime other.1.1 + 1 +
    if other.1.1.DependsOn other.2 formalBound then 0
    else
      supportTime target other.1.2 +
        match Preterm.support? target other.1.2 with
        | none => 0
        | some support => support.card + 1

/-- Time of `Substitution.checkRow`; `List.all` is charged for every element. -/
def checkRowTime (target : Context) (allEntries : List Substitution.Entry)
    (entry : Substitution.Entry) : Nat :=
  match entry.1 with
  | (.bound _, .var _) =>
      1 + (allEntries.map fun other => checkPairTime target entry.2 other + 1).sum
  | _ => 1

/-- Time of `Substitution.checkAdmissible`: check the arguments, build the entries, then
check every row. -/
def checkAdmissibleTime (signature : TermSignature) (formal target : Context)
    (expressions : List Preterm) : Nat :=
  checkArgumentsTime signature target expressions formal + 1 +
    if Substitution.checkArguments signature target expressions formal then
      formal.length + expressions.length + 1 +
        ((Substitution.entries formal expressions).map fun entry =>
          checkRowTime target (Substitution.entries formal expressions) entry + 1).sum
    else 0

theorem mem_entries {formal : Context} {expressions : List Preterm} {entry : Substitution.Entry}
    (member : entry ∈ Substitution.entries formal expressions) :
    entry.1.1 ∈ formal ∧ entry.1.2 ∈ expressions := by
  unfold Substitution.entries at member
  have pair := List.fst_mem_of_mem_zipIdx member
  exact ⟨List.of_mem_zip pair |>.1, List.of_mem_zip pair |>.2⟩

theorem length_entries_le (formal : Context) (expressions : List Preterm) :
    (Substitution.entries formal expressions).length ≤ expressions.length := by
  simp [Substitution.entries]

theorem sum_map_le_of_le {α : Type} {list : List α} {f : α → Nat} {bound : Nat}
    (each : ∀ x ∈ list, f x ≤ bound) : (list.map f).sum ≤ list.length * bound := by
  induction list with
  | nil => simp
  | cons x list ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have head := each x (List.mem_cons_self ..)
      have tail := ih (fun y member => each y (List.mem_cons_of_mem _ member))
      nlinarith

/-- One budget for an admissibility check: the sizes of both contexts and of the
substituted expressions, and their number. -/
theorem checkAdmissibleTime_le (signature : TermSignature) (formal target : Context)
    (expressions : List Preterm) {budget : Nat}
    (formalSmall : contextWeight formal ≤ budget) (targetSmall : contextWeight target ≤ budget)
    (expressionsSmall : sizes expressions ≤ budget) :
    checkAdmissibleTime signature formal target expressions ≤ 32 * (budget + 1) ^ 5 := by
  have targetLength : target.length ≤ budget := (Nat.le_add_right _ _).trans targetSmall
  have formalLength : formal.length ≤ budget := (Nat.le_add_right _ _).trans formalSmall
  have expressionsLength : expressions.length ≤ budget := by
    refine le_trans ?_ expressionsSmall
    unfold sizes
    have := sum_map_le_of_le (list := expressions) (f := fun _ => 1) (bound := 1) (fun _ _ => le_refl _)
    calc expressions.length = (expressions.map fun _ => 1).sum := by simp
      _ ≤ (expressions.map Preterm.size).sum :=
          List.sum_le_sum (fun expression _ => Preterm.one_le_size expression)
  have arguments := checkArgumentsTime_le signature target expressions formal
  -- one support check
  have pairBound : ∀ entry other : Substitution.Entry, other ∈ Substitution.entries formal expressions →
      checkPairTime target entry.2 other ≤ 6 * (budget + 1) ^ 3 := by
    intro entry other member
    obtain ⟨binderMember, expressionMember⟩ := mem_entries member
    have binderSmall : other.1.1.dependencyCount ≤ budget := by
      refine le_trans ?_ formalSmall
      unfold contextWeight
      exact (List.le_sum_of_mem (List.mem_map.mpr ⟨_, binderMember, rfl⟩)).trans (Nat.le_add_left _ _)
    have expressionSmall := (size_le_sizes expressionMember).trans expressionsSmall
    have supportBound := supportTime_le target other.1.2
    have dependsBound := dependsOnTime_le other.1.1
    unfold checkPairTime
    have rest : (if other.1.1.DependsOn other.2 entry.2 then 0
        else supportTime target other.1.2 +
          match Preterm.support? target other.1.2 with
          | none => 0
          | some support => support.card + 1) ≤
        supportTime target other.1.2 + (contextWeight target + 1) := by
      split
      · exact Nat.zero_le _
      · cases computed : Preterm.support? target other.1.2 with
        | none => simp
        | some support => have := card_support_le computed; simp only []; omega
    have widen : other.1.2.size * (target.length + 2 + (contextWeight target + 1) ^ 2) ≤
        budget * (3 * (budget + 1) ^ 2) := by
      apply Nat.mul_le_mul expressionSmall
      have : (contextWeight target + 1) ^ 2 ≤ (budget + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      nlinarith
    nlinarith
  have rowBound : ∀ entry ∈ Substitution.entries formal expressions,
      checkRowTime target (Substitution.entries formal expressions) entry ≤
        1 + budget * (6 * (budget + 1) ^ 3 + 1) := by
    intro entry _
    unfold checkRowTime
    split
    · have sum := sum_map_le_of_le (list := Substitution.entries formal expressions)
        (f := fun other => checkPairTime target entry.2 other + 1)
        (bound := 6 * (budget + 1) ^ 3 + 1)
        (fun other member => Nat.add_le_add_right (pairBound entry other member) 1)
      have count := (length_entries_le formal expressions).trans expressionsLength
      have : (Substitution.entries formal expressions).length * (6 * (budget + 1) ^ 3 + 1) ≤
          budget * (6 * (budget + 1) ^ 3 + 1) := Nat.mul_le_mul_right _ count
      omega
    · omega
  unfold checkAdmissibleTime
  have rows := sum_map_le_of_le (list := Substitution.entries formal expressions)
    (f := fun entry => checkRowTime target (Substitution.entries formal expressions) entry + 1)
    (bound := 2 + budget * (6 * (budget + 1) ^ 3 + 1))
    (fun entry member => by have := rowBound entry member; omega)
  have count := (length_entries_le formal expressions).trans expressionsLength
  have rowsTotal : ((Substitution.entries formal expressions).map fun entry =>
      checkRowTime target (Substitution.entries formal expressions) entry + 1).sum ≤
        budget * (2 + budget * (6 * (budget + 1) ^ 3 + 1)) :=
    rows.trans (Nat.mul_le_mul_right _ count)
  have choice : (if Substitution.checkArguments signature target expressions formal then
      formal.length + expressions.length + 1 +
        ((Substitution.entries formal expressions).map fun entry =>
          checkRowTime target (Substitution.entries formal expressions) entry + 1).sum
      else 0) ≤ 3 * budget + 1 + budget * (2 + budget * (6 * (budget + 1) ^ 3 + 1)) := by
    split <;> omega
  have argumentsSmall : (sizes expressions + 1) * (target.length + 3) + 2 * expressions.length ≤
      (budget + 1) * (budget + 3) + 2 * budget := by
    have := Nat.mul_le_mul (Nat.add_le_add_right expressionsSmall 1)
      (Nat.add_le_add_right targetLength 3)
    omega
  have final : (budget + 1) * (budget + 3) + 2 * budget + 1 +
      (3 * budget + 1 + budget * (2 + budget * (6 * (budget + 1) ^ 3 + 1))) ≤
        32 * (budget + 1) ^ 5 := by
    have one : 1 ≤ budget + 1 := by omega
    nlinarith [pow_pos (Nat.succ_pos budget) 2, pow_pos (Nat.succ_pos budget) 3,
      pow_pos (Nat.succ_pos budget) 4, pow_pos (Nat.succ_pos budget) 5]
  omega

/-! ## Theorem instances -/

/-- The size of a theorem's statement: its hypotheses and its conclusion. -/
def _root_.Mettapedia.Languages.MM0.Kernel.TheoremDecl.statementSize (declaration : TheoremDecl) :
    Nat :=
  sizes declaration.hypotheses + declaration.conclusion.size

/-- Time of `TheoremDecl.instantiate?`. -/
def instantiateTime (signature : TermSignature) (target : Context) (declaration : TheoremDecl)
    (arguments : List Preterm) : Nat :=
  checkAdmissibleTime signature declaration.arguments target arguments + 1 +
    if Substitution.checkAdmissible signature declaration.arguments target arguments then
      substituteListTime arguments declaration.hypotheses + 1 +
        match Substitution.substituteList (Substitution.ofList arguments) declaration.hypotheses with
        | none => 0
        | some _ => substituteTime arguments declaration.conclusion
    else 0

/-- A theorem's instance is at most its statement times one more than the size of the
arguments. -/
theorem instance_size_le {signature : TermSignature} {target : Context} {declaration : TheoremDecl}
    {arguments : List Preterm} {instantiation : TheoremInstance}
    (instantiated : declaration.instantiate? signature target arguments = some instantiation) :
    sizes instantiation.hypotheses + instantiation.conclusion.size ≤
      declaration.statementSize * (sizes arguments + 1) := by
  unfold TheoremDecl.instantiate? at instantiated
  split at instantiated
  · simp only [Option.bind_eq_bind] at instantiated
    cases hypotheses : Substitution.substituteList (Substitution.ofList arguments)
        declaration.hypotheses with
    | none => simp [hypotheses] at instantiated
    | some results =>
        cases conclusion : declaration.conclusion.substitute (Substitution.ofList arguments) with
        | none => simp [hypotheses, conclusion] at instantiated
        | some result =>
            simp only [hypotheses, conclusion, Option.bind_some, Option.pure_def,
              Option.some.injEq] at instantiated
            subst instantiated
            have first := sizes_substituteList hypotheses
            have second := size_substitute conclusion
            unfold TheoremDecl.statementSize
            simp only []
            nlinarith
  · cases instantiated

theorem instantiateTime_le (signature : TermSignature) (target : Context) (declaration : TheoremDecl)
    (arguments : List Preterm) {budget : Nat}
    (formalSmall : contextWeight declaration.arguments ≤ budget)
    (targetSmall : contextWeight target ≤ budget) (argumentsSmall : sizes arguments ≤ budget)
    (statementSmall : declaration.statementSize ≤ budget) :
    instantiateTime signature target declaration arguments ≤ 64 * (budget + 1) ^ 5 := by
  have admissible := checkAdmissibleTime_le signature declaration.arguments target arguments
    formalSmall targetSmall argumentsSmall
  have argumentsLength : arguments.length ≤ budget := by
    refine le_trans ?_ argumentsSmall
    calc arguments.length = (arguments.map fun _ => 1).sum := by simp
      _ ≤ (arguments.map Preterm.size).sum :=
          List.sum_le_sum (fun expression _ => Preterm.one_le_size expression)
  have hypothesesSmall : sizes declaration.hypotheses + declaration.hypotheses.length ≤ 2 * budget := by
    have lengthSmall : declaration.hypotheses.length ≤ sizes declaration.hypotheses := by
      calc declaration.hypotheses.length = (declaration.hypotheses.map fun _ => 1).sum := by simp
        _ ≤ (declaration.hypotheses.map Preterm.size).sum :=
            List.sum_le_sum (fun expression _ => Preterm.one_le_size expression)
    unfold TheoremDecl.statementSize at statementSmall
    omega
  have conclusionSmall : declaration.conclusion.size ≤ budget := by
    unfold TheoremDecl.statementSize at statementSmall; omega
  have hypothesesTime := substituteListTime_le arguments declaration.hypotheses
  have conclusionTime := substituteTime_le arguments declaration.conclusion
  unfold instantiateTime
  have rest : (if Substitution.checkAdmissible signature declaration.arguments target arguments then
      substituteListTime arguments declaration.hypotheses + 1 +
        match Substitution.substituteList (Substitution.ofList arguments) declaration.hypotheses with
        | none => 0
        | some _ => substituteTime arguments declaration.conclusion
      else 0) ≤ (2 * budget + 1) * (budget + 2) + 1 + budget * (budget + 2) := by
    split
    · have first : substituteListTime arguments declaration.hypotheses ≤ (2 * budget + 1) * (budget + 2) :=
        hypothesesTime.trans (Nat.mul_le_mul (by omega) (by omega))
      have second : substituteTime arguments declaration.conclusion ≤ budget * (budget + 2) :=
        conclusionTime.trans (Nat.mul_le_mul conclusionSmall (by omega))
      split <;> omega
    · exact Nat.zero_le _
  have final : (2 * budget + 1) * (budget + 2) + 1 + budget * (budget + 2) + 1 ≤ 32 * (budget + 1) ^ 5 := by
    nlinarith [pow_pos (Nat.succ_pos budget) 2, pow_pos (Nat.succ_pos budget) 3,
      pow_pos (Nat.succ_pos budget) 4, pow_pos (Nat.succ_pos budget) 5]
  omega

/-! ## Freshness of dummies and unfolding -/

theorem size_applyArgs (function : Preterm) (arguments : List Preterm) :
    (Preterm.applyArgs function arguments).size = function.size + sizes arguments + arguments.length := by
  induction arguments generalizing function with
  | nil => simp [sizes]
  | cons argument arguments ih =>
      simp only [Preterm.applyArgs, ih, Preterm.size, sizes_cons, List.length_cons]
      ring

theorem length_le_sizes (expressions : List Preterm) : expressions.length ≤ sizes expressions := by
  calc expressions.length = (expressions.map fun _ => 1).sum := by simp
    _ ≤ (expressions.map Preterm.size).sum :=
        List.sum_le_sum (fun expression _ => Preterm.one_le_size expression)

/-- Time of `Preterm.checkFreshFor`: compute the support, then test membership. -/
def freshForTime (target : Context) (expression : Preterm) : Nat :=
  supportTime target expression + 1 +
    match Preterm.support? target expression with
    | none => 0
    | some support => support.card + 1

/-- The cost of one dummy step, for arguments of total size `total` and number `count`. -/
def dummyStep (target : Context) (total count : Nat) : Nat :=
  target.length + 4 + total * (target.length + 2 + (contextWeight target + 1) ^ 2) +
    count * (contextWeight target + 4)

theorem freshForTime_le (target : Context) (expression : Preterm) :
    freshForTime target expression ≤
      expression.size * (target.length + 2 + (contextWeight target + 1) ^ 2) + contextWeight target + 2 := by
  have support := supportTime_le target expression
  unfold freshForTime
  cases computed : Preterm.support? target expression with
  | none => simp only []; omega
  | some set => have := card_support_le computed; simp only []; omega

/-- Time of `checkDummies`; each conjunction is charged in full. -/
def checkDummiesTime (target : Context) : List Preterm → List Nat → List Nat → Nat
  | _, [], [] => 1
  | arguments, _ :: sorts, image :: images =>
      lookupTime target image + 2 +
        (arguments.map fun argument => freshForTime target argument + 1).sum +
          arguments.length + 1 + checkDummiesTime target (arguments ++ [.var image]) sorts images
  | _, _, _ => 1

theorem dummyStep_mono (target : Context) {total total' count count' : Nat}
    (totalLe : total ≤ total') (countLe : count ≤ count') :
    dummyStep target total count ≤ dummyStep target total' count' := by
  unfold dummyStep
  have := Nat.mul_le_mul_right (target.length + 2 + (contextWeight target + 1) ^ 2) totalLe
  have := Nat.mul_le_mul_right (contextWeight target + 4) countLe
  omega

theorem dummyStep_pos (target : Context) (total count : Nat) : 1 ≤ dummyStep target total count := by
  unfold dummyStep; omega

theorem freshSum_le (target : Context) (arguments : List Preterm) :
    (arguments.map fun argument => freshForTime target argument + 1).sum ≤
      sizes arguments * (target.length + 2 + (contextWeight target + 1) ^ 2) +
        arguments.length * (contextWeight target + 3) := by
  induction arguments with
  | nil => simp
  | cons argument arguments ih =>
      simp only [List.map_cons, List.sum_cons, sizes_cons, List.length_cons]
      have := freshForTime_le target argument
      nlinarith

theorem checkDummiesTime_le (target : Context) (sorts images : List Nat) :
    ∀ arguments : List Preterm, checkDummiesTime target arguments sorts images ≤
      (sorts.length + 1) *
        dummyStep target (sizes arguments + sorts.length) (arguments.length + sorts.length) := by
  induction sorts generalizing images with
  | nil =>
      intro arguments
      cases images <;>
        simp only [checkDummiesTime, List.length_nil, Nat.add_zero, Nat.zero_add, Nat.one_mul] <;>
        exact dummyStep_pos _ _ _
  | cons sort sorts ih =>
      intro arguments
      have positive := dummyStep_pos target (sizes arguments + (sort :: sorts).length)
        (arguments.length + (sort :: sorts).length)
      cases images with
      | nil =>
          simp only [checkDummiesTime]
          exact positive.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      | cons image images =>
          simp only [checkDummiesTime, List.length_cons]
          have rest := ih images (arguments ++ [.var image])
          have grown : sizes (arguments ++ [.var image]) = sizes arguments + 1 := by
            simp [sizes, Preterm.size]
          rw [grown, List.length_append, List.length_singleton] at rest
          have fresh := freshSum_le target arguments
          have lookup := lookupTime_le target image
          have step : lookupTime target image + 2 +
              (arguments.map fun argument => freshForTime target argument + 1).sum +
                arguments.length + 1 ≤ dummyStep target (sizes arguments) arguments.length := by
            have split : arguments.length * (contextWeight target + 4) =
                arguments.length * (contextWeight target + 3) + arguments.length := by ring
            unfold dummyStep
            omega
          have widened := dummyStep_mono target (total := sizes arguments)
            (total' := sizes arguments + (sorts.length + 1))
            (count := arguments.length) (count' := arguments.length + (sorts.length + 1))
            (by omega) (by omega)
          have same : dummyStep target (sizes arguments + 1 + sorts.length)
              (arguments.length + 1 + sorts.length) =
                dummyStep target (sizes arguments + (sorts.length + 1))
                  (arguments.length + (sorts.length + 1)) := by
            congr 1 <;> omega
          rw [same] at rest
          generalize dummyStep target (sizes arguments + (sorts.length + 1))
            (arguments.length + (sorts.length + 1)) = bound at rest widened ⊢
          have expand : (sorts.length + 1 + 1) * bound = (sorts.length + 1) * bound + bound := by ring
          omega

/-- Time of `Definition.unfold?`; once both lookups succeed, every check is charged. -/
def unfoldTime (signature : TermSignature) (definitions : Definition.Signature) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) : Nat :=
  1 + match signature symbol with
    | none => 0
    | some declaration =>
        1 + match definitions symbol with
          | none => 0
          | some body =>
              checkArgumentsTime signature target arguments declaration.arguments + 1 +
                checkDummiesTime target arguments body.dummies images + 1 +
                  (arguments.length + images.length + 1) +
                    substituteTime (Definition.substitutionValues arguments images) body.expression

theorem sizes_vars (images : List Nat) : sizes (images.map Preterm.var) = images.length := by
  induction images with
  | nil => rfl
  | cons image images ih => simp only [List.map_cons, sizes_cons, ih, Preterm.size, List.length_cons]; omega

theorem sizes_substitutionValues (arguments : List Preterm) (images : List Nat) :
    sizes (Definition.substitutionValues arguments images) = sizes arguments + images.length := by
  unfold Definition.substitutionValues
  rw [← sizes_vars images]
  simp [sizes, List.sum_append]

/-- An unfolded definition is at most its body times one more than the size of the
arguments and dummy images. -/
theorem unfold_size_le {signature : TermSignature} {definitions : Definition.Signature}
    {target : Context} {symbol : Nat} {arguments : List Preterm} {images : List Nat}
    {body : Definition.Body} {result : Preterm} (lookup : definitions symbol = some body)
    (unfolded : Definition.unfold? signature definitions target symbol arguments images = some result) :
    result.size ≤ body.expression.size * (sizes arguments + images.length + 1) := by
  unfold Definition.unfold? at unfolded
  simp only [Option.bind_eq_bind, lookup, Option.bind_some] at unfolded
  cases declared : signature symbol with
  | none => simp [declared] at unfolded
  | some declaration =>
      simp only [declared, Option.bind_some] at unfolded
      split at unfolded
      · have := size_substitute unfolded
        rw [sizes_substitutionValues] at this
        omega
      · cases unfolded

/-- The width of a theory for checking: a bound on its theorem statements, the weights of
their contexts, its definition bodies and their dummies. -/
structure WidthBound (theorems : TheoremSignature) (definitions : Definition.Signature)
    (width : Nat) : Prop where
  statement : ∀ index declaration, theorems index = some declaration →
    declaration.statementSize ≤ width
  binders : ∀ index declaration, theorems index = some declaration →
    contextWeight declaration.arguments ≤ width
  body : ∀ symbol body, definitions symbol = some body → body.expression.size ≤ width
  dummies : ∀ symbol body, definitions symbol = some body → body.dummies.length ≤ width

theorem unfoldTime_le (signature : TermSignature) (definitions : Definition.Signature)
    (target : Context) (symbol : Nat) (arguments : List Preterm) (images : List Nat)
    {width budget : Nat} (bodySmall : ∀ body, definitions symbol = some body →
      body.expression.size ≤ width ∧ body.dummies.length ≤ width)
    (widthSmall : width ≤ budget) (targetSmall : contextWeight target ≤ budget)
    (argumentsSmall : sizes arguments + images.length ≤ budget) :
    unfoldTime signature definitions target symbol arguments images ≤ 256 * (budget + 1) ^ 5 := by
  have targetLength : target.length ≤ budget := (Nat.le_add_right _ _).trans targetSmall
  have argumentsLength := length_le_sizes arguments
  unfold unfoldTime
  cases declared : signature symbol with
  | none => simp only []; nlinarith [pow_pos (Nat.succ_pos budget) 5]
  | some declaration =>
      simp only []
      cases defined : definitions symbol with
      | none => simp only []; nlinarith [pow_pos (Nat.succ_pos budget) 5]
      | some body =>
          simp only []
          obtain ⟨bodySize, dummyCount⟩ := bodySmall body defined
          have checks := checkArgumentsTime_le signature target arguments declaration.arguments
          have dummies := checkDummiesTime_le target body.dummies images arguments
          have substitution := substituteTime_le (Definition.substitutionValues arguments images)
            body.expression
          have valuesLength : (Definition.substitutionValues arguments images).length ≤ 2 * budget := by
            simp only [Definition.substitutionValues, List.length_append, List.length_map]
            omega
          have stepBound : dummyStep target (sizes arguments + body.dummies.length)
              (arguments.length + body.dummies.length) ≤ 32 * (budget + 1) ^ 3 := by
            unfold dummyStep
            have weight : (contextWeight target + 1) ^ 2 ≤ (budget + 1) ^ 2 :=
              Nat.pow_le_pow_left (by omega) 2
            have total : sizes arguments + body.dummies.length ≤ 2 * budget := by omega
            have count : arguments.length + body.dummies.length ≤ 2 * budget := by omega
            have first := Nat.mul_le_mul total (show target.length + 2 + (contextWeight target + 1) ^ 2 ≤
              3 * (budget + 1) ^ 2 by nlinarith)
            have second := Nat.mul_le_mul count (show contextWeight target + 4 ≤ 4 * (budget + 1) by omega)
            nlinarith [pow_pos (Nat.succ_pos budget) 2, pow_pos (Nat.succ_pos budget) 3]
          have dummiesTotal : checkDummiesTime target arguments body.dummies images ≤
              (budget + 1) * (32 * (budget + 1) ^ 3) :=
            dummies.trans (Nat.mul_le_mul (by omega) stepBound)
          have checksTotal : checkArgumentsTime signature target arguments declaration.arguments ≤
              (budget + 1) * (budget + 3) + 2 * budget := by
            have := Nat.mul_le_mul (show sizes arguments + 1 ≤ budget + 1 by omega)
              (show target.length + 3 ≤ budget + 3 by omega)
            omega
          have substitutionTotal : substituteTime (Definition.substitutionValues arguments images)
              body.expression ≤ budget * (2 * budget + 2) :=
            substitution.trans (Nat.mul_le_mul (by omega) (by omega))
          nlinarith [pow_pos (Nat.succ_pos budget) 2, pow_pos (Nat.succ_pos budget) 3,
            pow_pos (Nat.succ_pos budget) 4, pow_pos (Nat.succ_pos budget) 5]

/-! ## Conversion witnesses -/

mutual

/-- The size of a conversion witness: its nodes, the expressions it names and the dummy
images it supplies. -/
def convSize (witness : ConvWitness) : Nat :=
  match witness with
  | .refl expression => expression.size + 1
  | .symm child => convSize child + 1
  | .trans first second => convSize first + convSize second + 1
  | .congruence _ children => convSizes children + 1
  | .unfold _ arguments images => sizes arguments + images.length + 1
termination_by structural witness

def convSizes (children : List ConvWitness) : Nat :=
  match children with
  | [] => 0
  | child :: children => convSize child + convSizes children
termination_by structural children

end

theorem one_le_convSize (witness : ConvWitness) : 1 ≤ convSize witness := by
  cases witness <;> simp [convSize]

mutual

/-- The two sides of a conversion are bounded by the witness size: their sizes plus two
are at most `width + 4` times the witness size. -/
theorem conversion_size_le {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {width : Nat}
    (bodySmall : ∀ symbol body, definitions symbol = some body → body.expression.size ≤ width)
    (witness : ConvWitness) {result : ConversionResult}
    (accepted : ConvWitness.conversion? signature definitions context witness = some result) :
    result.left.size + result.right.size + 2 ≤ (width + 4) * convSize witness := by
  match witness with
  | .refl expression =>
      simp only [ConvWitness.conversion?, Option.bind_eq_bind] at accepted
      cases inferred : Preterm.infer signature context expression with
      | none => simp [inferred] at accepted
      | some type =>
          obtain ⟨remaining, sort⟩ := type
          simp only [inferred, Option.bind_some] at accepted
          split at accepted
          · simp only [Option.some.injEq] at accepted
            subst accepted
            simp only [convSize]
            nlinarith
          · cases accepted
  | .symm child =>
      simp only [ConvWitness.conversion?, Option.bind_eq_bind] at accepted
      cases inner : ConvWitness.conversion? signature definitions context child with
      | none => simp [inner] at accepted
      | some childResult =>
          simp only [inner, Option.bind_some, Option.pure_def, Option.some.injEq] at accepted
          subst accepted
          have := conversion_size_le bodySmall child inner
          simp only [convSize]
          nlinarith
  | .trans first second =>
      simp only [ConvWitness.conversion?, Option.bind_eq_bind] at accepted
      cases leftResult : ConvWitness.conversion? signature definitions context first with
      | none => simp [leftResult] at accepted
      | some left =>
          cases rightResult : ConvWitness.conversion? signature definitions context second with
          | none => simp [leftResult, rightResult] at accepted
          | some right =>
              simp only [leftResult, rightResult, Option.bind_some] at accepted
              split at accepted
              · simp only [Option.some.injEq] at accepted
                subst accepted
                have firstBound := conversion_size_le bodySmall first leftResult
                have secondBound := conversion_size_le bodySmall second rightResult
                simp only [convSize]
                nlinarith
              · cases accepted
  | .congruence symbol children =>
      simp only [ConvWitness.conversion?, Option.bind_eq_bind] at accepted
      cases declared : signature symbol with
      | none => simp [declared] at accepted
      | some declaration =>
          cases sides : ConvWitness.arguments? signature definitions context children
              declaration.arguments with
          | none => simp [declared, sides] at accepted
          | some pair =>
              obtain ⟨lefts, rights⟩ := pair
              simp only [declared, sides, Option.bind_some, Option.pure_def,
                Option.some.injEq] at accepted
              subst accepted
              have list := arguments_size_le bodySmall children declaration.arguments sides
              simp only [size_applyArgs, Preterm.size, convSize]
              nlinarith
  | .unfold symbol arguments images =>
      simp only [ConvWitness.conversion?, Option.bind_eq_bind] at accepted
      cases declared : signature symbol with
      | none => simp [declared] at accepted
      | some declaration =>
          cases unfolded : Definition.unfold? signature definitions context symbol arguments images with
          | none => simp [declared, unfolded] at accepted
          | some unfoldedResult =>
              simp only [declared, unfolded, Option.bind_some] at accepted
              split at accepted
              · simp only [Option.some.injEq] at accepted
                subst accepted
                cases defined : definitions symbol with
                | none =>
                    simp [Definition.unfold?, declared, defined] at unfolded
                | some body =>
                    have resultBound := unfold_size_le defined unfolded
                    have bodyBound := bodySmall symbol body defined
                    have widened := Nat.mul_le_mul_right (sizes arguments + images.length + 1) bodyBound
                    have argumentsLength := length_le_sizes arguments
                    simp only [size_applyArgs, Preterm.size, convSize]
                    nlinarith
              · cases accepted
termination_by structural witness

theorem arguments_size_le {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {width : Nat}
    (bodySmall : ∀ symbol body, definitions symbol = some body → body.expression.size ≤ width)
    (children : List ConvWitness) (binders : Context) {lefts rights : List Preterm}
    (accepted : ConvWitness.arguments? signature definitions context children binders =
      some (lefts, rights)) :
    sizes lefts + sizes rights + lefts.length + rights.length ≤ (width + 4) * convSizes children := by
  match children, binders with
  | [], [] =>
      simp only [ConvWitness.arguments?, Option.some.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      simp [sizes]
  | child :: children, binder :: binders =>
      simp only [ConvWitness.arguments?, Option.bind_eq_bind] at accepted
      cases inner : ConvWitness.conversion? signature definitions context child with
      | none => simp [inner] at accepted
      | some result =>
          simp only [inner, Option.bind_some] at accepted
          split at accepted
          · cases rest : ConvWitness.arguments? signature definitions context children binders with
            | none => simp [rest] at accepted
            | some pair =>
                obtain ⟨restLefts, restRights⟩ := pair
                simp only [rest] at accepted
                obtain ⟨rfl, rfl⟩ := accepted
                have head := conversion_size_le bodySmall child inner
                have tail := arguments_size_le bodySmall children binders rest
                simp only [sizes_cons, List.length_cons, convSizes]
                nlinarith
          · cases accepted
  | [], _ :: _ => simp [ConvWitness.arguments?] at accepted
  | _ :: _, [] => simp [ConvWitness.arguments?] at accepted
termination_by structural children

end

/-! ## Time of conversion checking -/

mutual

/-- Time of `ConvWitness.conversion?`. -/
def conversionTime (signature : TermSignature) (definitions : Definition.Signature) (context : Context)
    (witness : ConvWitness) : Nat :=
  match witness with
  | .refl expression => inferTime signature context expression + 2
  | .symm child => conversionTime signature definitions context child + 1
  | .trans first second =>
      conversionTime signature definitions context first + 1 +
        match ConvWitness.conversion? signature definitions context first with
        | none => 0
        | some left =>
            conversionTime signature definitions context second +
              match ConvWitness.conversion? signature definitions context second with
              | none => 0
              | some right => left.right.size + right.left.size + 2
  | .congruence symbol children =>
      2 + match signature symbol with
        | none => 0
        | some declaration =>
            argumentsTime signature definitions context children declaration.arguments +
              match ConvWitness.arguments? signature definitions context children
                  declaration.arguments with
              | none => 0
              | some (left, right) => left.length + right.length + 2
  | .unfold symbol arguments images =>
      2 + match signature symbol with
        | none => 0
        | some _ =>
            unfoldTime signature definitions context symbol arguments images +
              match Definition.unfold? signature definitions context symbol arguments images with
              | none => 0
              | some result => inferTime signature context result + arguments.length + 3
termination_by structural witness

/-- Time of `ConvWitness.arguments?`; once a child converts, both of its binder checks and
the rest are charged. -/
def argumentsTime (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (children : List ConvWitness) (binders : Context) : Nat :=
  match children, binders with
  | [], [] => 1
  | child :: children, binder :: binders =>
      conversionTime signature definitions context child + 1 +
        match ConvWitness.conversion? signature definitions context child with
        | none => 0
        | some result =>
            checkBinderTime signature context result.left binder +
              checkBinderTime signature context result.right binder + 2 +
                argumentsTime signature definitions context children binders
  | _, _ => 1
termination_by structural children

end

/-- What one converted child costs its parent beyond its own conversion: the two binder
checks. -/
def conversionExtra (width budget : Nat) : Nat := (width + 4) * budget * (budget + 3) + 6

/-- The charge per unit of conversion witness. -/
def conversionCharge (width budget : Nat) : Nat :=
  conversionExtra width budget + 256 * (budget + 1) ^ 5 + width * (budget + 1) * (budget + 3) +
    (width + 4) * budget + 2 * budget + 10

mutual

theorem conversionTime_le {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {width budget : Nat}
    (bodySmall : ∀ symbol body, definitions symbol = some body →
      body.expression.size ≤ width ∧ body.dummies.length ≤ width)
    (widthSmall : width ≤ budget) (contextSmall : contextWeight context ≤ budget)
    (witness : ConvWitness) (small : convSize witness ≤ budget) :
    conversionTime signature definitions context witness + conversionExtra width budget ≤
      convSize witness * conversionCharge width budget := by
  have contextLength : context.length ≤ budget := (Nat.le_add_right _ _).trans contextSmall
  have bodySize : ∀ symbol body, definitions symbol = some body → body.expression.size ≤ width :=
    fun symbol body defined => (bodySmall symbol body defined).1
  match witness with
  | .refl expression =>
      have inferred := inferTime_le signature context expression
      simp only [convSize] at small ⊢
      simp only [conversionTime]
      have : expression.size * (context.length + 3) ≤ expression.size * conversionCharge width budget :=
        Nat.mul_le_mul_left _ (by unfold conversionCharge; omega)
      have : 2 + conversionExtra width budget ≤ conversionCharge width budget := by
        unfold conversionCharge; omega
      nlinarith
  | .symm child =>
      have inner := conversionTime_le (signature := signature) bodySmall widthSmall contextSmall child
        (by simp only [convSize] at small; omega)
      simp only [conversionTime, convSize]
      have : 1 ≤ conversionCharge width budget := by unfold conversionCharge; omega
      nlinarith
  | .trans first second =>
      simp only [convSize] at small
      have firstBound := conversionTime_le (signature := signature) bodySmall widthSmall contextSmall first (by omega)
      have secondBound := conversionTime_le (signature := signature) bodySmall widthSmall contextSmall second (by omega)
      have compare : (match ConvWitness.conversion? signature definitions context first with
          | none => 0
          | some left =>
              conversionTime signature definitions context second +
                match ConvWitness.conversion? signature definitions context second with
                | none => 0
                | some right => left.right.size + right.left.size + 2) ≤
            conversionTime signature definitions context second + (width + 4) * budget := by
        cases leftResult : ConvWitness.conversion? signature definitions context first with
        | none => exact Nat.zero_le _
        | some left =>
            simp only []
            cases rightResult : ConvWitness.conversion? signature definitions context second with
            | none => simp
            | some right =>
                simp only []
                have leftSize := conversion_size_le bodySize first leftResult
                have rightSize := conversion_size_le bodySize second rightResult
                have total : (width + 4) * convSize first + (width + 4) * convSize second ≤
                    (width + 4) * budget := by
                  rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
                omega
      simp only [conversionTime, convSize]
      have : (width + 4) * budget + 1 ≤ conversionCharge width budget + conversionExtra width budget := by
        unfold conversionCharge; omega
      nlinarith
  | .congruence symbol children =>
      simp only [convSize] at small
      simp only [conversionTime, convSize]
      cases declared : signature symbol with
      | none =>
          simp only []
          have : 2 + conversionExtra width budget ≤ conversionCharge width budget := by
            unfold conversionCharge; omega
          nlinarith
      | some declaration =>
          simp only []
          have list := argumentsTime_le (signature := signature) bodySmall widthSmall contextSmall children
            declaration.arguments (by omega)
          have lengths : (match ConvWitness.arguments? signature definitions context children
              declaration.arguments with
              | none => 0
              | some (left, right) => left.length + right.length + 2) ≤ (width + 4) * budget + 2 := by
            cases sides : ConvWitness.arguments? signature definitions context children
                declaration.arguments with
            | none => simp
            | some pair =>
                obtain ⟨lefts, rights⟩ := pair
                simp only []
                have sized := arguments_size_le bodySize children declaration.arguments sides
                have widened : (width + 4) * convSizes children ≤ (width + 4) * budget :=
                  Nat.mul_le_mul_left _ (by omega)
                omega
          have : (width + 4) * budget + 5 + conversionExtra width budget ≤
              conversionCharge width budget := by
            unfold conversionCharge; omega
          nlinarith
  | .unfold symbol arguments images =>
      simp only [convSize] at small
      simp only [conversionTime, convSize]
      cases declared : signature symbol with
      | none =>
          simp only []
          have : 2 + conversionExtra width budget ≤ conversionCharge width budget := by
            unfold conversionCharge; omega
          nlinarith
      | some declaration =>
          simp only []
          have unfolding := unfoldTime_le signature definitions context symbol arguments images
            (fun body defined => bodySmall symbol body defined) widthSmall contextSmall (by omega)
          have argumentsLength := length_le_sizes arguments
          have resultCost : (match Definition.unfold? signature definitions context symbol arguments images with
              | none => 0
              | some result => inferTime signature context result + arguments.length + 3) ≤
                width * (budget + 1) * (budget + 3) + budget + 3 := by
            cases unfolded : Definition.unfold? signature definitions context symbol arguments images with
            | none => simp
            | some result =>
                simp only []
                cases defined : definitions symbol with
                | none => simp [Definition.unfold?, declared, defined] at unfolded
                | some body =>
                    have resultSize := unfold_size_le defined unfolded
                    have bodyBound := (bodySmall symbol body defined).1
                    have inferred := inferTime_le signature context result
                    have sizeBound : result.size ≤ width * (budget + 1) :=
                      resultSize.trans (Nat.mul_le_mul bodyBound (by omega))
                    have := Nat.mul_le_mul sizeBound (show context.length + 3 ≤ budget + 3 by omega)
                    omega
          have : 2 + 256 * (budget + 1) ^ 5 + (width * (budget + 1) * (budget + 3) + budget + 3) +
              conversionExtra width budget ≤ conversionCharge width budget := by
            unfold conversionCharge; omega
          nlinarith
termination_by structural witness

theorem argumentsTime_le {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {width budget : Nat}
    (bodySmall : ∀ symbol body, definitions symbol = some body →
      body.expression.size ≤ width ∧ body.dummies.length ≤ width)
    (widthSmall : width ≤ budget) (contextSmall : contextWeight context ≤ budget)
    (children : List ConvWitness) (binders : Context) (small : convSizes children ≤ budget) :
    argumentsTime signature definitions context children binders ≤
      convSizes children * conversionCharge width budget + 1 := by
  have contextLength : context.length ≤ budget := (Nat.le_add_right _ _).trans contextSmall
  have bodySize : ∀ symbol body, definitions symbol = some body → body.expression.size ≤ width :=
    fun symbol body defined => (bodySmall symbol body defined).1
  match children, binders with
  | [], [] => simp [argumentsTime, convSizes]
  | child :: children, binder :: binders =>
      simp only [convSizes] at small
      have head := conversionTime_le (signature := signature) bodySmall widthSmall contextSmall child (by omega)
      have tail := argumentsTime_le (signature := signature) bodySmall widthSmall contextSmall children binders (by omega)
      simp only [argumentsTime, convSizes]
      have checks : (match ConvWitness.conversion? signature definitions context child with
          | none => 0
          | some result =>
              checkBinderTime signature context result.left binder +
                checkBinderTime signature context result.right binder + 2 +
                  argumentsTime signature definitions context children binders) + 1 ≤
            conversionExtra width budget + argumentsTime signature definitions context children binders := by
        cases converted : ConvWitness.conversion? signature definitions context child with
        | none => simp only []; unfold conversionExtra; omega
        | some result =>
            simp only []
            have sized := conversion_size_le bodySize child converted
            have leftCheck := checkBinderTime_le signature context result.left binder
            have rightCheck := checkBinderTime_le signature context result.right binder
            have sidesSmall : result.left.size + result.right.size ≤ (width + 4) * budget :=
              by have := Nat.mul_le_mul_left (width + 4) (show convSize child ≤ budget by omega); omega
            have product := Nat.mul_le_mul sidesSmall (show context.length + 3 ≤ budget + 3 by omega)
            unfold conversionExtra
            nlinarith
      nlinarith
  | [], _ :: _ => simp [argumentsTime]
  | _ :: _, [] => simp [argumentsTime]
termination_by structural children

end

theorem conversionCharge_le {width budget : Nat} (widthSmall : width ≤ budget) :
    conversionCharge width budget ≤ 512 * (budget + 1) ^ 5 := by
  unfold conversionCharge conversionExtra
  have one : 1 ≤ budget + 1 := by omega
  have w : width + 4 ≤ 4 * (budget + 1) := by omega
  have first := Nat.mul_le_mul (Nat.mul_le_mul w (show budget ≤ budget + 1 by omega))
    (show budget + 3 ≤ 3 * (budget + 1) by omega)
  have second := Nat.mul_le_mul (Nat.mul_le_mul widthSmall (le_refl (budget + 1)))
    (show budget + 3 ≤ 3 * (budget + 1) by omega)
  have third := Nat.mul_le_mul w (show budget ≤ budget + 1 by omega)
  nlinarith [pow_pos (Nat.succ_pos budget) 2, pow_pos (Nat.succ_pos budget) 3,
    pow_pos (Nat.succ_pos budget) 4, pow_pos (Nat.succ_pos budget) 5]

/-! ## Time of proof checking -/

mutual

/-- The size of a proof witness: its nodes, its arguments and its conversion witnesses. -/
def proofSize (witness : ProofWitness) : Nat :=
  match witness with
  | .hyp _ => 1
  | .theoremApp _ arguments children => sizes arguments + proofSizes children + 1
  | .conversion step child => convSize step + proofSize child + 1
termination_by structural witness

def proofSizes (children : List ProofWitness) : Nat :=
  match children with
  | [] => 0
  | child :: children => proofSize child + proofSizes children
termination_by structural children

end

theorem one_le_proofSize (witness : ProofWitness) : 1 ≤ proofSize witness := by
  cases witness <;> simp [proofSize]

mutual

/-- Time of `ProofWitness.proof?`. -/
def proofTime (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) : Nat :=
  match witness with
  | .hyp index => lookupTime hypotheses index + 1
  | .theoremApp index arguments children =>
      2 + match theorems index with
        | none => 0
        | some declaration =>
            instantiateTime signature context declaration arguments +
              match declaration.instantiate? signature context arguments with
              | none => 0
              | some instantiation =>
                  childrenTime signature definitions theorems context hypotheses children +
                    match ProofWitness.children? signature definitions theorems context hypotheses
                        children with
                    | none => 0
                    | some premises => sizes premises + sizes instantiation.hypotheses + 1
  | .conversion step child =>
      1 + conversionTime signature definitions context step +
        match ConvWitness.conversion? signature definitions context step with
        | none => 0
        | some converted =>
            proofTime signature definitions theorems context hypotheses child +
              match ProofWitness.proof? signature definitions theorems context hypotheses child with
              | none => 0
              | some conclusion => conclusion.size + converted.left.size + 1
termination_by structural witness

/-- Time of `ProofWitness.children?`. -/
def childrenTime (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (children : List ProofWitness) : Nat :=
  match children with
  | [] => 1
  | child :: children =>
      proofTime signature definitions theorems context hypotheses child + 1 +
        match ProofWitness.proof? signature definitions theorems context hypotheses child with
        | none => 0
        | some _ => childrenTime signature definitions theorems context hypotheses children
termination_by structural children

end

/-- A bound on every conclusion the checker computes from a witness of size at most
`budget`. -/
def conclusionBound (hypotheses : List Preterm) (width budget : Nat) : Nat :=
  sizes hypotheses + width * (budget + 1) + (width + 4) * budget

theorem conclusion_size_le {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {width budget : Nat} (bound : WidthBound theorems definitions width)
    {witness : ProofWitness} (small : proofSize witness ≤ budget) {conclusion : Preterm}
    (computed : ProofWitness.proof? signature definitions theorems context hypotheses witness =
      some conclusion) :
    conclusion.size ≤ conclusionBound hypotheses width budget := by
  unfold conclusionBound
  cases witness with
  | hyp index =>
      simp only [ProofWitness.proof?] at computed
      have := size_le_sizes (List.mem_of_getElem? computed)
      omega
  | theoremApp index arguments children =>
      simp only [proofSize] at small
      simp only [ProofWitness.proof?, Option.bind_eq_bind] at computed
      cases declared : theorems index with
      | none => simp [declared] at computed
      | some declaration =>
          cases instantiated : declaration.instantiate? signature context arguments with
          | none => simp [declared, instantiated] at computed
          | some instantiation =>
              cases premises : ProofWitness.children? signature definitions theorems context
                  hypotheses children with
              | none => simp [declared, premises] at computed
              | some results =>
                  simp only [declared, instantiated, premises, Option.bind_some] at computed
                  split at computed
                  · simp only [Option.some.injEq] at computed
                    subst computed
                    have sized := instance_size_le instantiated
                    have statement := bound.statement index declaration declared
                    have widened := Nat.mul_le_mul statement
                      (show sizes arguments + 1 ≤ budget + 1 by omega)
                    omega
                  · cases computed
  | conversion step child =>
      simp only [proofSize] at small
      simp only [ProofWitness.proof?, Option.bind_eq_bind] at computed
      cases converted : ConvWitness.conversion? signature definitions context step with
      | none => simp [converted] at computed
      | some result =>
          cases inner : ProofWitness.proof? signature definitions theorems context hypotheses child with
          | none => simp [converted, inner] at computed
          | some childConclusion =>
              simp only [converted, inner, Option.bind_some] at computed
              split at computed
              · simp only [Option.some.injEq] at computed
                subst computed
                have sized := conversion_size_le (fun symbol body defined => bound.body symbol body defined)
                  step converted
                have widened := Nat.mul_le_mul_left (width + 4) (show convSize step ≤ budget by omega)
                omega
              · cases computed

theorem premises_size_le {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {width budget : Nat} (bound : WidthBound theorems definitions width) :
    ∀ (children : List ProofWitness) (premises : List Preterm), proofSizes children ≤ budget →
      ProofWitness.children? signature definitions theorems context hypotheses children = some premises →
        sizes premises ≤ proofSizes children * conclusionBound hypotheses width budget
  | [], premises, _, computed => by
      simp only [ProofWitness.children?, Option.some.injEq] at computed
      subst computed
      simp [sizes]
  | child :: children, premises, small, computed => by
      simp only [proofSizes] at small
      simp only [ProofWitness.children?, Option.bind_eq_bind] at computed
      cases head : ProofWitness.proof? signature definitions theorems context hypotheses child with
      | none => simp [head] at computed
      | some conclusion =>
          cases tail : ProofWitness.children? signature definitions theorems context hypotheses children with
          | none => simp [head, tail] at computed
          | some rest =>
              simp only [head, tail, Option.bind_some, Option.pure_def, Option.some.injEq] at computed
              subst computed
              have first := conclusion_size_le (budget := budget) bound (by omega) head
              have second := premises_size_le (budget := budget) bound children rest (by omega) tail
              have positive := one_le_proofSize child
              simp only [sizes_cons, proofSizes]
              nlinarith

/-- The charge per unit of proof witness. -/
def proofCharge (hypotheses : List Preterm) (width budget : Nat) : Nat :=
  conversionCharge width budget + 64 * (budget + 1) ^ 5 +
    budget * conclusionBound hypotheses width budget + width * (budget + 1) +
      conclusionBound hypotheses width budget + (width + 4) * budget + sizes hypotheses + 10

mutual

theorem proofTime_le_charge {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {width budget : Nat} (bound : WidthBound theorems definitions width)
    (widthSmall : width ≤ budget) (contextSmall : contextWeight context ≤ budget)
    (witness : ProofWitness) (small : proofSize witness ≤ budget) :
    proofTime signature definitions theorems context hypotheses witness + 1 ≤
      proofSize witness * proofCharge hypotheses width budget := by
  have bodySmall : ∀ symbol body, definitions symbol = some body →
      body.expression.size ≤ width ∧ body.dummies.length ≤ width :=
    fun symbol body defined => ⟨bound.body symbol body defined, bound.dummies symbol body defined⟩
  match witness with
  | .hyp index =>
      simp only [proofTime, proofSize]
      have lookup := lookupTime_le hypotheses index
      have count := length_le_sizes hypotheses
      unfold proofCharge
      omega
  | .theoremApp index arguments children =>
      simp only [proofSize] at small
      simp only [proofTime, proofSize]
      cases declared : theorems index with
      | none =>
          simp only []
          have charge : 3 ≤ proofCharge hypotheses width budget := by unfold proofCharge; omega
          have := Nat.le_mul_of_pos_left (proofCharge hypotheses width budget)
            (show 0 < sizes arguments + proofSizes children + 1 by omega)
          omega
      | some declaration =>
          simp only []
          have instantiation := instantiateTime_le signature context declaration arguments
            ((bound.binders index declaration declared).trans widthSmall) contextSmall (by omega)
            ((bound.statement index declaration declared).trans widthSmall)
          have list := childrenTime_le_charge (signature := signature) (definitions := definitions)
            (theorems := theorems) (context := context) (hypotheses := hypotheses) bound widthSmall
            contextSmall children (by omega)
          have rest : (match declaration.instantiate? signature context arguments with
              | none => 0
              | some instantiation =>
                  childrenTime signature definitions theorems context hypotheses children +
                    match ProofWitness.children? signature definitions theorems context hypotheses
                        children with
                    | none => 0
                    | some premises => sizes premises + sizes instantiation.hypotheses + 1) ≤
              childrenTime signature definitions theorems context hypotheses children +
                budget * conclusionBound hypotheses width budget + width * (budget + 1) + 1 := by
            cases instantiated : declaration.instantiate? signature context arguments with
            | none => simp
            | some instance_ =>
                simp only []
                cases premises : ProofWitness.children? signature definitions theorems context
                    hypotheses children with
                | none => simp only []; omega
                | some results =>
                    simp only []
                    have premisesSize := premises_size_le (budget := budget) bound children results (by omega) premises
                    have premisesWide := Nat.mul_le_mul_right (conclusionBound hypotheses width budget)
                      (show proofSizes children ≤ budget by omega)
                    have instanceSize := instance_size_le instantiated
                    have statement := bound.statement index declaration declared
                    have instanceWide := Nat.mul_le_mul statement
                      (show sizes arguments + 1 ≤ budget + 1 by omega)
                    omega
          have charge : 64 * (budget + 1) ^ 5 + budget * conclusionBound hypotheses width budget +
              width * (budget + 1) + 5 ≤ proofCharge hypotheses width budget := by
            unfold proofCharge; omega
          nlinarith
  | .conversion step child =>
      simp only [proofSize] at small
      simp only [proofTime, proofSize]
      have conversionBound := conversionTime_le (signature := signature) bodySmall widthSmall
        contextSmall step (by omega)
      have chargeLe : conversionCharge width budget ≤ proofCharge hypotheses width budget := by
        unfold proofCharge; omega
      have conversionWide := Nat.mul_le_mul_left (convSize step) chargeLe
      have rest : (match ConvWitness.conversion? signature definitions context step with
          | none => 0
          | some converted =>
              proofTime signature definitions theorems context hypotheses child +
                match ProofWitness.proof? signature definitions theorems context hypotheses child with
                | none => 0
                | some conclusion => conclusion.size + converted.left.size + 1) ≤
            proofTime signature definitions theorems context hypotheses child +
              conclusionBound hypotheses width budget + (width + 4) * budget + 1 := by
        cases converted : ConvWitness.conversion? signature definitions context step with
        | none => simp
        | some result =>
            simp only []
            cases inner : ProofWitness.proof? signature definitions theorems context hypotheses child with
            | none => simp only []; omega
            | some conclusion =>
                simp only []
                have conclusionSize := conclusion_size_le (budget := budget) bound (by omega) inner
                have leftSize := conversion_size_le (fun symbol body defined => bound.body symbol body defined)
                  step converted
                have leftWide := Nat.mul_le_mul_left (width + 4) (show convSize step ≤ budget by omega)
                omega
      have childBound := proofTime_le_charge (signature := signature) (definitions := definitions)
        (theorems := theorems) (context := context) (hypotheses := hypotheses) bound widthSmall
        contextSmall child (by omega)
      have charge : conclusionBound hypotheses width budget + (width + 4) * budget + 3 ≤
          proofCharge hypotheses width budget := by
        unfold proofCharge; omega
      nlinarith
termination_by structural witness

theorem childrenTime_le_charge {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {width budget : Nat} (bound : WidthBound theorems definitions width)
    (widthSmall : width ≤ budget) (contextSmall : contextWeight context ≤ budget)
    (children : List ProofWitness) (small : proofSizes children ≤ budget) :
    childrenTime signature definitions theorems context hypotheses children ≤
      proofSizes children * proofCharge hypotheses width budget + 1 := by
  match children with
  | [] => simp [childrenTime, proofSizes]
  | child :: children =>
      simp only [proofSizes] at small
      have head := proofTime_le_charge (signature := signature) (definitions := definitions)
        (theorems := theorems) (context := context) (hypotheses := hypotheses) bound widthSmall
        contextSmall child (by omega)
      have tail := childrenTime_le_charge (signature := signature) (definitions := definitions)
        (theorems := theorems) (context := context) (hypotheses := hypotheses) bound widthSmall
        contextSmall children (by omega)
      simp only [childrenTime, proofSizes]
      have rest : (match ProofWitness.proof? signature definitions theorems context hypotheses child with
          | none => 0
          | some _ => childrenTime signature definitions theorems context hypotheses children) ≤
            childrenTime signature definitions theorems context hypotheses children := by
        split <;> omega
      nlinarith
termination_by structural children

end

/-- The input measure of a check: the witness, the context, the hypotheses and the width
of the theory. -/
def checkMeasure (context : Context) (hypotheses : List Preterm) (witness : ProofWitness)
    (width : Nat) : Nat :=
  proofSize witness + contextWeight context + sizes hypotheses + width

theorem proofCharge_le {hypotheses : List Preterm} {width budget : Nat}
    (widthSmall : width ≤ budget) (hypothesesSmall : sizes hypotheses ≤ budget) :
    proofCharge hypotheses width budget ≤ 1024 * (budget + 1) ^ 5 := by
  have conversion := conversionCharge_le widthSmall
  unfold proofCharge conclusionBound
  have w4 : width + 4 ≤ 4 * (budget + 1) := by omega
  have product1 := Nat.mul_le_mul widthSmall (le_refl (budget + 1))
  have product2 := Nat.mul_le_mul w4 (show budget ≤ budget + 1 by omega)
  have bound : sizes hypotheses + width * (budget + 1) + (width + 4) * budget ≤ 6 * (budget + 1) ^ 2 := by
    nlinarith
  have product3 := Nat.mul_le_mul (show budget ≤ budget + 1 by omega) bound
  nlinarith [pow_pos (Nat.succ_pos budget) 2, pow_pos (Nat.succ_pos budget) 3,
    pow_pos (Nat.succ_pos budget) 4, pow_pos (Nat.succ_pos budget) 5]

/-- **The checker runs in polynomial time.** With `N` the size of the witness, the context
and the hypotheses plus the width of the theory, the checker computes the conclusion in
time at most `1024 * (N + 1) ^ 6`. -/
theorem proofTime_le {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {width : Nat} (bound : WidthBound theorems definitions width)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness) :
    proofTime signature definitions theorems context hypotheses witness ≤
      1024 * (checkMeasure context hypotheses witness width + 1) ^ 6 := by
  set measure := checkMeasure context hypotheses witness width with measureDef
  have charged := proofTime_le_charge (signature := signature) (definitions := definitions)
    (theorems := theorems) (context := context) (hypotheses := hypotheses) (budget := measure) bound
    (by rw [measureDef]; unfold checkMeasure; omega) (by rw [measureDef]; unfold checkMeasure; omega)
    witness (by rw [measureDef]; unfold checkMeasure; omega)
  have charge := proofCharge_le (hypotheses := hypotheses) (width := width) (budget := measure)
    (by rw [measureDef]; unfold checkMeasure; omega) (by rw [measureDef]; unfold checkMeasure; omega)
  have sizeSmall : proofSize witness ≤ measure + 1 := by rw [measureDef]; unfold checkMeasure; omega
  have product := Nat.mul_le_mul sizeSmall charge
  have expand : (measure + 1) * (1024 * (measure + 1) ^ 5) = 1024 * (measure + 1) ^ 6 := by ring
  omega

/-! ## The checker as a proof system -/

/-- A claim of the kernel: a context, hypotheses, and the expression to derive. -/
structure Sequent where
  context : Context
  hypotheses : List Preterm
  expression : Preterm

/-- The size of a sequent. -/
def sequentSize (sequent : Sequent) : Nat :=
  contextWeight sequent.context + sizes sequent.hypotheses + sequent.expression.size

/-- Time of `ProofWitness.check`: compute the conclusion, then compare it. -/
def checkTime (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (sequent : Sequent) (witness : ProofWitness) : Nat :=
  proofTime signature definitions theorems sequent.context sequent.hypotheses witness + 1 +
    match ProofWitness.proof? signature definitions theorems sequent.context sequent.hypotheses
        witness with
    | none => 0
    | some conclusion => conclusion.size + sequent.expression.size

/-- The kernel's checker with its sizes and time function. -/
def kernelChecker (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) :
    GSLT.LanguageDef.ProofSystems.TimedChecker Sequent ProofWitness where
  check sequent witness := ProofWitness.check signature definitions theorems sequent.context
    sequent.hypotheses witness sequent.expression
  claimSize := sequentSize
  certificateSize := proofSize
  time := checkTime signature definitions theorems

theorem checkTime_le {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {width : Nat} (bound : WidthBound theorems definitions width)
    (sequent : Sequent) (witness : ProofWitness) :
    checkTime signature definitions theorems sequent witness ≤
      2048 * (sequentSize sequent + proofSize witness + width + 1) ^ 6 := by
  set measure := sequentSize sequent + proofSize witness + width with measureDef
  have measured : checkMeasure sequent.context sequent.hypotheses witness width ≤ measure := by
    rw [measureDef]; unfold checkMeasure sequentSize; omega
  have proving := proofTime_le (signature := signature) bound sequent.context sequent.hypotheses witness
  have widened : (checkMeasure sequent.context sequent.hypotheses witness width + 1) ^ 6 ≤
      (measure + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have comparison : (match ProofWitness.proof? signature definitions theorems sequent.context
      sequent.hypotheses witness with
      | none => 0
      | some conclusion => conclusion.size + sequent.expression.size) ≤
        conclusionBound sequent.hypotheses width measure + measure := by
    cases computed : ProofWitness.proof? signature definitions theorems sequent.context
        sequent.hypotheses witness with
    | none => simp
    | some conclusion =>
        simp only []
        have := conclusion_size_le (budget := measure) bound (by rw [measureDef]; omega) computed
        have : sequent.expression.size ≤ measure := by rw [measureDef]; unfold sequentSize; omega
        omega
  have small : conclusionBound sequent.hypotheses width measure + measure + 1 ≤ 1024 * (measure + 1) ^ 6 := by
    unfold conclusionBound
    have hyps : sizes sequent.hypotheses ≤ measure := by rw [measureDef]; unfold sequentSize; omega
    have widthSmall : width ≤ measure := by rw [measureDef]; omega
    have product1 := Nat.mul_le_mul widthSmall (le_refl (measure + 1))
    have product2 := Nat.mul_le_mul (show width + 4 ≤ 4 * (measure + 1) by omega)
      (show measure ≤ measure + 1 by omega)
    nlinarith [pow_pos (Nat.succ_pos measure) 2, pow_pos (Nat.succ_pos measure) 3,
      pow_pos (Nat.succ_pos measure) 4, pow_pos (Nat.succ_pos measure) 5,
      pow_pos (Nat.succ_pos measure) 6]
  unfold checkTime
  omega

/-- **MM0's kernel is a proof system in the sense of Cook and Reckhow**, for every theory of
bounded width: exact for derivability, and polynomial in time. -/
def proofSystem (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (width : Nat) (bound : WidthBound theorems definitions width) :
    GSLT.LanguageDef.ProofSystems.ProofSystem Sequent ProofWitness
      (fun sequent => Derives signature definitions theorems sequent.context sequent.hypotheses
        sequent.expression) where
  toTimedChecker := kernelChecker signature definitions theorems
  authority :=
    { sound := fun _ _ accepted => ProofWitness.check_sound accepted
      complete := fun sequent derived =>
        (derives_iff_checked signature definitions theorems sequent.context sequent.hypotheses
          sequent.expression).mp derived }
  polynomialTime := by
    refine ⟨2048 * (Polynomial.X + Polynomial.C (width + 1)) ^ 6, fun input => ?_⟩
    have := checkTime_le (signature := signature) bound input.1 input.2
    simp only [GSLT.LanguageDef.ProofSystems.SizedChecker.inputSize, kernelChecker,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_ofNat]
    have same : sequentSize input.1 + proofSize input.2 + width + 1 =
        sequentSize input.1 + proofSize input.2 + (width + 1) := by ring
    rw [same] at this
    exact this

/-- Cook and Reckhow's function form of the kernel: a context, hypotheses and a witness
determine the sequent they prove. -/
def functionForm (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) :
    GSLT.LanguageDef.ProofSystems.FunctionForm Sequent (Context × List Preterm × ProofWitness) where
  conclusion? input :=
    (ProofWitness.proof? signature definitions theorems input.1 input.2.1 input.2.2).map
      fun expression => ⟨input.1, input.2.1, expression⟩

/-- The sequents the function form reaches are exactly the derivable ones. -/
theorem functionForm_exact (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (sequent : Sequent) :
    (∃ input, (functionForm signature definitions theorems).conclusion? input = some sequent) ↔
      Derives signature definitions theorems sequent.context sequent.hypotheses sequent.expression := by
  constructor
  · rintro ⟨⟨context, hypotheses, witness⟩, computed⟩
    simp only [functionForm, Option.map_eq_some_iff] at computed
    obtain ⟨expression, proved, rfl⟩ := computed
    exact ProofWitness.check_sound (witness := witness) (by simp [ProofWitness.check, proved])
  · intro derived
    obtain ⟨witness, accepted⟩ := (derives_iff_checked signature definitions theorems sequent.context
      sequent.hypotheses sequent.expression).mp derived
    refine ⟨(sequent.context, sequent.hypotheses, witness), ?_⟩
    have proved : ProofWitness.proof? signature definitions theorems sequent.context sequent.hypotheses
        witness = some sequent.expression := by
      simpa [ProofWitness.check] using accepted
    simp [functionForm, proved]

/-! ## Finite theories -/

theorem le_foldr_max_of_mem {values : List Nat} {value : Nat} (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact le_max_left _ _
      · exact (ih later).trans (le_max_right _ _)

/-- The width of a finite theory: its largest theorem statement with its context, plus
its largest definition body with its dummies. -/
def _root_.Mettapedia.Languages.MM0.Kernel.Theory.width (theory : Theory) : Nat :=
  (theory.theorems.map fun entry => entry.2.statementSize + contextWeight entry.2.arguments).foldr
      max 0 +
    (theory.definitions.map fun entry => entry.2.expression.size + entry.2.dummies.length).foldr max 0

theorem _root_.Mettapedia.Languages.MM0.Kernel.Theory.widthBound (theory : Theory) :
    WidthBound theory.theoremSignature theory.definitionSignature theory.width := by
  have theoremBound : ∀ index declaration, theory.theoremSignature index = some declaration →
      declaration.statementSize + contextWeight declaration.arguments ≤ theory.width := by
    intro index declaration found
    have member := FirstOrderEnumeration.mem_of_lookup found
    have bounded := le_foldr_max_of_mem (values := theory.theorems.map fun entry =>
      entry.2.statementSize + contextWeight entry.2.arguments)
      (List.mem_map.mpr ⟨(index, declaration), member, rfl⟩)
    dsimp only at bounded
    unfold Theory.width
    omega
  have definitionBound : ∀ symbol body, theory.definitionSignature symbol = some body →
      body.expression.size + body.dummies.length ≤ theory.width := by
    intro symbol body found
    have member := FirstOrderEnumeration.mem_of_lookup found
    have bounded := le_foldr_max_of_mem (values := theory.definitions.map fun entry =>
      entry.2.expression.size + entry.2.dummies.length) (List.mem_map.mpr ⟨(symbol, body), member, rfl⟩)
    dsimp only at bounded
    unfold Theory.width
    omega
  exact
    { statement := fun index declaration found => by have := theoremBound index declaration found; omega
      binders := fun index declaration found => by have := theoremBound index declaration found; omega
      body := fun symbol body found => by have := definitionBound symbol body found; omega
      dummies := fun symbol body found => by have := definitionBound symbol body found; omega }

/-- Every finite MM0 theory's kernel is a proof system in the sense of Cook and Reckhow. -/
def _root_.Mettapedia.Languages.MM0.Kernel.Theory.proofSystem (theory : Theory) :
    GSLT.LanguageDef.ProofSystems.ProofSystem Sequent ProofWitness
      (fun sequent => Derives theory.termSignature theory.definitionSignature theory.theoremSignature
        sequent.context sequent.hypotheses sequent.expression) :=
  Cost.proofSystem theory.termSignature theory.definitionSignature theory.theoremSignature
    theory.width theory.widthBound

/-! ## Controls -/

/-- One sort, one constant, and one axiom asserting the constant. -/
def controlTheory : Theory where
  sorts := [(0, ⟨false, false, true, false⟩)]
  terms := [(0, ⟨[], 0, ∅⟩)]
  theorems := [(0, ⟨[], [], .term 0⟩)]

/-- The axiom applied with no arguments proves the constant. -/
example : (Theory.proofSystem controlTheory).check ⟨[], [], .term 0⟩ (.theoremApp 0 [] []) = true := by
  simp [Theory.proofSystem, Cost.proofSystem, kernelChecker, ProofWitness.check, ProofWitness.proof?,
    ProofWitness.children?, controlTheory, Theory.theoremSignature, TheoremDecl.instantiate?,
    Substitution.checkAdmissible, Substitution.checkArguments, Substitution.entries,
    Substitution.substituteList, Preterm.substitute]

/-- The same witness does not prove a variable. -/
example : (Theory.proofSystem controlTheory).check ⟨[], [], .var 0⟩ (.theoremApp 0 [] []) = false := by
  simp [Theory.proofSystem, Cost.proofSystem, kernelChecker, ProofWitness.check, ProofWitness.proof?,
    ProofWitness.children?, controlTheory, Theory.theoremSignature, TheoremDecl.instantiate?,
    Substitution.checkAdmissible, Substitution.checkArguments, Substitution.entries,
    Substitution.substituteList, Preterm.substitute]

example : proofSize (.theoremApp 0 [] []) = 1 := rfl

example : controlTheory.width = 1 := by
  simp [Theory.width, controlTheory, TheoremDecl.statementSize, sizes, contextWeight, Preterm.size]

end Cost

end Mettapedia.Languages.MM0.Kernel
