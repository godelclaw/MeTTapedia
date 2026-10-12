import Mettapedia.OSLF.Syntax.RhoScopedParallelContexts
import Mettapedia.OSLF.Syntax.RhoScopedEquationEventControls

/-!
# Complete readout of the declared rho reaction contexts

Every permitted original binding path is a parallel context at the same
ambient variable scope. Its complete action is adjoining one original
process class. Conversely every such class is realized by a permitted raw
path. The readout includes both parallel positions and arbitrary stored
siblings; no input, payload, drop or quotation position is enabled.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedParallelPathReadout

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres ScopedEncoding ScopedEquationContexts
open RhoScopedEquationContextControls RhoScopedEquationEventControls
open RhoEquationConstructorControls
open Mettapedia.CategoryTheory.GroundPath

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

abbrev Allowed {source target : Scope sig} (path : BindingContext sig source target) :=
  FramePermission.PermittedPath
    (framePermission sig (uniformSlotPermission sig parallelPermission)) path

abbrev ParallelSiblings (context : Ctx sig) (selected : Fin 2) :=
  (other : Fin (sig.arity Op.par).length) → other ≠ selected →
    Term sig (((sig.arity Op.par).get other).1 ++ context) ((sig.arity Op.par).get other).2

theorem scope_readout {source target : Scope sig} (path : BindingContext sig source target)
    (allowed : Allowed path) : source = target := by
  induction path with
  | nil => rfl
  | cons previous frame ih =>
    cases allowed with
    | cons previousAllowed frameAllowed =>
      cases frame with
      | slot context sort operator position siblings =>
        cases operator <;> try exact False.elim frameAllowed
        case par =>
          fin_cases position <;> exact ih previousAllowed

theorem fill_left_slot (context : Ctx sig)
    (siblings : ParallelSiblings context 0)
    (value : Term sig context Srt.pr) :
    (BindingFrame.slot context Srt.pr Op.par 0 siblings).fill value =
      parallel value (siblings 1 (by decide)) := by
  simp [BindingFrame.fill, assembleArguments, parallel]

theorem fill_right_slot (context : Ctx sig)
    (siblings : ParallelSiblings context 1)
    (value : Term sig context Srt.pr) :
    (BindingFrame.slot context Srt.pr Op.par 1 siblings).fill value =
      parallel (siblings 0 (by decide)) value := by
  simp [BindingFrame.fill, assembleArguments, parallel]

theorem fillClass_cons {source middle target : Scope sig}
    (path : BindingContext sig source middle) (frame : BindingFrame sig middle target)
    (value : State rhoSourceE source) :
    fillClass rhoSourceE (path.cons frame) value =
      fillClass rhoSourceE ((.nil : BindingContext sig middle middle).cons frame)
        (fillClass rhoSourceE path value) := by
  induction value using Quotient.inductionOn with
  | _ value => rfl

theorem left_slot_readout (context : Ctx sig)
    (siblings : ParallelSiblings context 0)
    (value : Process context) :
    fillClass rhoSourceE
      ((.nil : BindingContext sig (context, Srt.pr) (context, Srt.pr)).cons
        (BindingFrame.slot context Srt.pr Op.par 0 siblings)) value =
      join value (project (siblings 1 (by decide))) := by
  induction value using Quotient.inductionOn with
  | _ value =>
    exact congrArg (fun term : Term sig context Srt.pr => (project term : Process context))
      (fill_left_slot context siblings value)

theorem right_slot_readout (context : Ctx sig)
    (siblings : ParallelSiblings context 1)
    (value : Process context) :
    fillClass rhoSourceE
      ((.nil : BindingContext sig (context, Srt.pr) (context, Srt.pr)).cons
        (BindingFrame.slot context Srt.pr Op.par 1 siblings)) value =
      join value (project (siblings 0 (by decide))) := by
  induction value using Quotient.inductionOn with
  | _ value =>
    exact (congrArg (fun term : Term sig context Srt.pr => (project term : Process context))
      (fill_right_slot context siblings value)).trans
      ((join_project (siblings 0 (by decide)) value).symm.trans
        (join_commutes (project (siblings 0 (by decide))) (project value)))

theorem join_assoc {context : Ctx sig} (first second third : Process context) :
    join (join first second) third = join first (join second third) := by
  apply RhoScopedParallelInventory.read_injective context
  rw [RhoScopedParallelInventory.read_join, RhoScopedParallelInventory.read_join,
    RhoScopedParallelInventory.read_join, RhoScopedParallelInventory.read_join, add_assoc]

/-- The readout is for the whole context action, rather than one supplied endpoint. -/
theorem complete_path_readout {context : Ctx sig} {target : Scope sig}
    (path : BindingContext sig (context, Srt.pr) target) (allowed : Allowed path) :
    ∃ _same : target = (context, Srt.pr), ∃ surrounding : Process context,
      ∀ value : Process context,
        HEq (fillClass rhoSourceE path value) (join value surrounding) := by
  induction path with
  | nil =>
    refine ⟨rfl, zero context, ?_⟩
    intro value
    apply heq_of_eq
    simp only [fillClass_identity, join_zero_right]
  | cons previous frame ih =>
    cases allowed with
    | cons previousAllowed frameAllowed =>
      obtain ⟨same, surrounding, reads⟩ := ih previousAllowed
      cases frame with
      | slot original sort operator position siblings =>
        cases operator <;> try exact False.elim frameAllowed
        case par =>
          fin_cases position
          · have contexts := congrArg Prod.fst same
            dsimp at contexts
            subst original
            refine ⟨rfl, join surrounding (project (siblings 1 (by decide))), ?_⟩
            intro value
            apply heq_of_eq
            rw [fillClass_cons, eq_of_heq (reads value)]
            exact (left_slot_readout context siblings _).trans (join_assoc _ _ _)
          · have contexts := congrArg Prod.fst same
            dsimp at contexts
            subst original
            refine ⟨rfl, join surrounding (project (siblings 0 (by decide))), ?_⟩
            intro value
            apply heq_of_eq
            rw [fillClass_cons, eq_of_heq (reads value)]
            exact (right_slot_readout context siblings _).trans (join_assoc _ _ _)

theorem fixed_scope_readout {context : Ctx sig}
    (path : BindingContext sig (context, Srt.pr) (context, Srt.pr)) (allowed : Allowed path) :
    ∃ surrounding : Process context, ∀ value : Process context,
      fillClass rhoSourceE path value = join value surrounding := by
  obtain ⟨_, surrounding, reads⟩ := complete_path_readout path allowed
  exact ⟨surrounding, fun value => eq_of_heq (reads value)⟩

theorem every_surrounding_realized {context : Ctx sig} (surrounding : Process context) :
    ∃ path : BindingContext sig (context, Srt.pr) (context, Srt.pr),
      Allowed path ∧ ∀ value : Process context,
        fillClass rhoSourceE path value = join value surrounding := by
  induction surrounding using Quotient.inductionOn with
  | _ term =>
    refine ⟨single (parallelFrame context term), .cons (.nil _) (by trivial), ?_⟩
    intro value
    exact left_slot_readout context _ value

end Mettapedia.OSLF.Binding.RhoScopedParallelPathReadout
