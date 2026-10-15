import Mettapedia.OSLF.Syntax.RhoIntrinsicReadbackRoundtrip

/-!
# Parallel normalization preserves intrinsic readback classes

The optional readback values compose by the actual quotient parallel former.
Its associative, commutative and unit laws come from the source equations.
Consequently flattening bags, removing null occurrences and sorting preserve
the readback class, including failure of a component's sorted readback.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

def closeTriple {context : Ctx sig} (first second third : Term sig context Srt.pr) :
    Sub sig [Srt.pr, Srt.pr, Srt.pr] context
  | _, .zero => first
  | _, .succ .zero => second
  | _, .succ (.succ .zero) => third

theorem parallel_associates_raw {context : Ctx sig}
    (first second third : Term sig context Srt.pr) :
    EqClosure rhoSourceE (parallel (parallel first second) third)
      (parallel first (parallel second third)) := by
  simpa [rhoSourceE, assocPar, ContextualAssignment.instantiate,
    ContextualAssignment.instantiateArgs, instantiate, instantiateArgs,
    bind, bindArgs, liftSub, parallel, closeTriple]
    using (EqClosure.ax_closed (E := rhoSourceE) (Γ := context) 1 contDiscard
      (closeTriple first second third))

theorem join_associates {context : Ctx sig} (first second third : Process context) :
    join (join first second) third = join first (join second third) := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      induction third using Quotient.inductionOn with
      | _ third => exact Quotient.sound (parallel_associates_raw first second third)

def merge {context : Ctx sig} : Option (Process context) → Option (Process context) →
    Option (Process context)
  | some first, some second => some (join first second)
  | _, _ => none

theorem merge_associates {context : Ctx sig} (first second third : Option (Process context)) :
    merge (merge first second) third = merge first (merge second third) := by
  cases first <;> cases second <;> cases third <;> simp [merge, join_associates]

theorem merge_commutes {context : Ctx sig} (first second : Option (Process context)) :
    merge first second = merge second first := by
  cases first <;> cases second <;> simp [merge, join_commutes]

theorem merge_zero_left {context : Ctx sig} (value : Option (Process context)) :
    merge (some (zero context)) value = value := by
  cases value <;> simp [merge, join_zero_left]

theorem merge_zero_right {context : Ctx sig} (value : Option (Process context)) :
    merge value (some (zero context)) = value := by
  cases value <;> simp [merge, join_zero_right]

def readNameClass (context : Ctx sig) (pattern : Pattern) : Option (Name context) :=
  (readName context pattern).map project

def readProcessClass (context : Ctx sig) (pattern : Pattern) : Option (Process context) :=
  (readProcess context pattern).map project

def readProcessesClass (context : Ctx sig) (patterns : List Pattern) :
    Option (Process context) := (readProcesses context patterns).map project

theorem readProcessesClass_nil (context : Ctx sig) :
    readProcessesClass context [] = some (zero context) := rfl

theorem readProcessesClass_cons (context : Ctx sig) (head : Pattern) (tail : List Pattern) :
    readProcessesClass context (head :: tail) =
      merge (readProcessClass context head) (readProcessesClass context tail) := by
  cases firstRead : readProcess context head <;>
    cases remainingRead : readProcesses context tail <;>
    simp [readProcessesClass, readProcessClass, readProcesses, firstRead, remainingRead,
      merge, join_project]

theorem readProcessesClass_singleton (context : Ctx sig) (pattern : Pattern) :
    readProcessesClass context [pattern] = readProcessClass context pattern := by
  rw [readProcessesClass_cons, readProcessesClass_nil, merge_zero_right]

theorem readProcessesClass_append (context : Ctx sig) (first second : List Pattern) :
    readProcessesClass context (first ++ second) =
      merge (readProcessesClass context first) (readProcessesClass context second) := by
  induction first with
  | nil => exact (merge_zero_left _).symm
  | cons head tail ih =>
    simp only [List.cons_append, readProcessesClass_cons, ih, merge_associates]

theorem readProcessesClass_permutation (context : Ctx sig) {first second : List Pattern}
    (permutation : first.Perm second) :
    readProcessesClass context first = readProcessesClass context second := by
  induction permutation with
  | nil => rfl
  | cons head permutation ih => simp only [readProcessesClass_cons, ih]
  | swap first second tail =>
    simp only [readProcessesClass_cons]
    rw [← merge_associates, merge_commutes (readProcessClass context second)
      (readProcessClass context first), merge_associates]
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem readProcessesClass_splice (context : Ctx sig) (pattern : Pattern) :
    readProcessesClass context (bagSplice pattern) = readProcessClass context pattern := by
  cases pattern with
  | collection kind elements rest =>
    cases kind <;> cases rest <;> rfl
  | _ => exact readProcessesClass_singleton context _

theorem readProcessesClass_flatten (context : Ctx sig) (patterns : List Pattern) :
    readProcessesClass context (patterns.flatMap bagSplice) =
      readProcessesClass context patterns := by
  induction patterns with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, readProcessesClass_append, readProcessesClass_splice,
      ih, readProcessesClass_cons]

theorem readProcessClass_zero (context : Ctx sig) :
    readProcessClass context (.apply "PZero" []) = some (zero context) := rfl

theorem readProcessesClass_filter_zero (context : Ctx sig) (patterns : List Pattern) :
    readProcessesClass context (patterns.filter fun pattern => pattern ≠ .apply "PZero" []) =
      readProcessesClass context patterns := by
  induction patterns with
  | nil => rfl
  | cons head tail ih =>
    by_cases headZero : head = .apply "PZero" []
    · subst head
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte,
        ih, readProcessesClass_cons, readProcessClass_zero, merge_zero_left]
    · simp only [List.filter_cons, ne_eq, headZero, not_false_eq_true, decide_true,
        ↓reduceIte, readProcessesClass_cons, ih]

theorem readProcessesClass_normalizeBag (context : Ctx sig) (patterns : List Pattern) :
    readProcessesClass context (normalizeBagElements patterns) =
      readProcessesClass context patterns := by
  unfold normalizeBagElements
  rw [readProcessesClass_permutation context (sortPatterns_perm _).symm,
    readProcessesClass_filter_zero, readProcessesClass_flatten]

theorem readProcessClass_collapseBag (context : Ctx sig) (patterns : List Pattern) :
    readProcessClass context (collapseBag patterns) = readProcessesClass context patterns := by
  cases patterns with
  | nil => rfl
  | cons first remaining =>
    cases remaining with
    | nil => exact (readProcessesClass_singleton context first).symm
    | cons second tail => rfl

theorem readProcessClass_normalizedBag (context : Ctx sig) (patterns : List Pattern) :
    readProcessClass context (collapseBag (normalizeBagElements patterns)) =
      readProcessesClass context patterns := by
  rw [readProcessClass_collapseBag, readProcessesClass_normalizeBag]

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
