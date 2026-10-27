import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraCanonicalForms

/-!
# The bag normal form, computed

`normalForm` sorts the contents of a bag with a merge sort, which the kernel does not reduce. `fastNormalForm` sorts
them by insertion on pattern codes (`sortByCode`) and recurses structurally, so the kernel evaluates it; it is the
normal form (`fastNormalForm_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ComputedNormalForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode (sortPatterns patternCode patternCode_injective)
open Mettapedia.GSLT.LanguageDef.BagNormalForm

/-- Sorting by code, by insertion. The kernel reduces it, unlike the merge sort of `sortPatterns`. -/
def sortByCode (patterns : List Pattern) : List Pattern :=
  patterns.insertionSort fun first second => patternCode first ≤ patternCode second

theorem sortByCode_eq (patterns : List Pattern) : sortByCode patterns = sortPatterns patterns := by
  let relation : Pattern → Pattern → Prop := fun first second => patternCode first ≤ patternCode second
  let : Std.Total relation := ⟨fun first second => Nat.le_total (patternCode first) (patternCode second)⟩
  let : IsTrans Pattern relation := ⟨fun _ _ _ firstLe secondLe => Nat.le_trans firstLe secondLe⟩
  let : Std.Antisymm relation :=
    ⟨fun first second firstLe secondLe => patternCode_injective (Nat.le_antisymm firstLe secondLe)⟩
  exact (List.mergeSort_eq_insertionSort relation patterns).symm

variable (unit : String)

mutual
  /-- The normal form of a bag algebra with a unit, computed by structural recursion. -/
  def fastNormalForm : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => .apply label (fastNormalFormList arguments)
    | .lambda binder body => .lambda binder (fastNormalForm body)
    | .multiLambda arity binders body => .multiLambda arity binders (fastNormalForm body)
    | .subst body replacement => .subst (fastNormalForm body) (fastNormalForm replacement)
    | .collection kind elements rest =>
        if kind = .hashBag ∧ rest = none then
          collapse unit (sortByCode (bagContents unit (fastNormalFormList elements)))
        else
          .collection kind (fastNormalFormList elements) rest

  def fastNormalFormList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => fastNormalForm pattern :: fastNormalFormList patterns
end

theorem fastNormalFormList_eq_map (patterns : List Pattern) :
    fastNormalFormList unit patterns = patterns.map (fastNormalForm unit) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [fastNormalFormList, recurse]

/-- **The computed normal form is the normal form.** -/
theorem fastNormalForm_eq (pattern : Pattern) : fastNormalForm unit pattern = normalForm (some unit) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [fastNormalForm, normalForm]
  | hfvar name => simp [fastNormalForm, normalForm]
  | happly label arguments recurse =>
    rw [fastNormalForm, normalForm_apply, fastNormalFormList_eq_map]
    congr 1
    exact List.map_congr_left recurse
  | hlambda binder body recurse => simp [fastNormalForm, normalForm, recurse]
  | hmultiLambda arity binders body recurse => simp [fastNormalForm, normalForm, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
    simp [fastNormalForm, normalForm, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
    have mapped : fastNormalFormList unit elements = elements.map (normalForm (some unit)) := by
      rw [fastNormalFormList_eq_map]
      exact List.map_congr_left recurse
    by_cases closed : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := closed
      rw [normalForm_bag]
      simp only [fastNormalForm, and_self, if_true, mapped, normalizeBag, sortByCode_eq]
    · simp [fastNormalForm, normalForm, closed, mapped]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ComputedNormalForm
