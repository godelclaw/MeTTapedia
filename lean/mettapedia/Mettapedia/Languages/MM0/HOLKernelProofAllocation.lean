import Mettapedia.Languages.MM0.HOLKernelSignature
import Mettapedia.Languages.MM0.Kernel.ContextExtension
import Mettapedia.Logic.HOL.ProofSyntaxBindingDepth

/-!
# Finite native allocation for a retained HOL proof

A canonical source bank precedes one working and one temporary bank for
every proof node. A working bank has an additional root slot, so its tail
can be the canonical bank of a binding child. All allocated variables have
the declared native object sort; existing context positions are unchanged.

The construction proves slot availability and separation. It supplies no
recursive proof compiler or bound on the execution cost of native checking.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofAllocation
open Kernel HOLKernelSyntax

structure Layout where
  width : Nat
  frames : Nat
  widthPositive : 0 < width

namespace Layout
def stride (layout : Layout) : Nat := 2 * (layout.width + 1)
def workDepth (layout : Layout) (frame : Nat) : Nat := layout.width + frame * layout.stride
def temporaryDepth (layout : Layout) (frame : Nat) : Nat := layout.workDepth frame + layout.width + 1
def limit (layout : Layout) : Nat := layout.workDepth layout.frames
def names (initial : Context) (offset : Nat) : Nat := initial.length + offset
def target (layout : Layout) (initial : Context) (object : Nat) : Context := initial.appendBounds object layout.limit

theorem names_injective (initial : Context) : Function.Injective (names initial) := by
  intro first second same
  exact Nat.add_left_cancel same

theorem workDepth_mono (layout : Layout) {first second : Nat} (ordered : first ≤ second) :
    layout.workDepth first ≤ layout.workDepth second :=
  Nat.add_le_add_left (Nat.mul_le_mul_right layout.stride ordered) layout.width

theorem next_workDepth (layout : Layout) (frame : Nat) :
    layout.workDepth (frame + 1) = layout.temporaryDepth frame + layout.width + 1 := by
  simp only [workDepth, temporaryDepth, Nat.add_mul, Nat.one_mul, stride]
  omega

theorem source_slot_lt (layout : Layout) {offset : Nat} (smaller : offset < layout.width) : offset < layout.limit := by
  have start := layout.workDepth_mono (Nat.zero_le layout.frames)
  simp only [workDepth, Nat.zero_mul, Nat.add_zero] at start
  exact Nat.lt_of_lt_of_le smaller start

theorem work_slot_lt (layout : Layout) {frame offset : Nat}
    (active : frame < layout.frames) (smaller : offset < layout.width + 1) :
    layout.workDepth frame + offset < layout.limit := by
  have upper := layout.workDepth_mono (Nat.succ_le_of_lt active)
  rw [layout.next_workDepth] at upper
  change layout.temporaryDepth frame + layout.width + 1 ≤ layout.limit at upper
  have positive := layout.widthPositive
  simp only [temporaryDepth] at upper
  omega

theorem temporary_slot_lt (layout : Layout) {frame offset : Nat}
    (active : frame < layout.frames) (smaller : offset < layout.width + 1) :
    layout.temporaryDepth frame + offset < layout.limit := by
  have upper := layout.workDepth_mono (Nat.succ_le_of_lt active)
  rw [layout.next_workDepth] at upper
  change layout.temporaryDepth frame + layout.width + 1 ≤ layout.limit at upper
  omega

theorem work_temporary_apart (layout : Layout) (frame : Nat) {first second : Nat}
    (firstSmall : first < layout.width + 1) :
    layout.workDepth frame + first ≠ layout.temporaryDepth frame + second := by
  simp only [temporaryDepth]
  omega

theorem frame_separation (layout : Layout) {first second : Nat} (ordered : first < second) :
    layout.temporaryDepth first + layout.width + 1 ≤ layout.workDepth second := by
  rw [← layout.next_workDepth first]
  exact layout.workDepth_mono (Nat.succ_le_of_lt ordered)

theorem source_before_temporary (layout : Layout) {source frame first second : Nat}
    (sourceBefore : source + layout.width ≤ layout.workDepth frame)
    (firstSmall : first < layout.width) :
    source + first ≠ layout.temporaryDepth frame + second := by
  simp only [temporaryDepth]
  omega

theorem child_source_before_next_frame (layout : Layout) {first second : Nat} (ordered : first < second) :
    (layout.workDepth first + 1) + layout.width ≤ layout.workDepth second := by
  have before := layout.frame_separation ordered
  simp only [temporaryDepth] at before
  omega

theorem slot (layout : Layout) (initial : Context) (object offset : Nat) (smaller : offset < layout.limit) :
    (layout.target initial object)[names initial offset]? = some (.bound object) :=
  Context.appendBounds_lookup initial object layout.limit offset smaller

theorem sourceSlots (layout : Layout) (initial : Context) (object : Nat) {source frame : Nat}
    (active : frame < layout.frames) (sourceBefore : source + layout.width ≤ layout.workDepth frame) :
    ∀ offset < layout.width, (layout.target initial object)[names initial (source + offset)]? = some (.bound object) := by
  intro offset smaller
  apply layout.slot
  have workBound := layout.work_slot_lt active (offset := 0) (by omega)
  omega

theorem workSlots (layout : Layout) (initial : Context) (object : Nat) {frame : Nat} (active : frame < layout.frames) :
    ∀ offset < layout.width + 1,
      (layout.target initial object)[names initial (layout.workDepth frame + offset)]? = some (.bound object) :=
  fun _ smaller => layout.slot initial object _ (layout.work_slot_lt active smaller)

theorem temporarySlots (layout : Layout) (initial : Context) (object : Nat) {frame : Nat} (active : frame < layout.frames) :
    ∀ offset < layout.width + 1,
      (layout.target initial object)[names initial (layout.temporaryDepth frame + offset)]? = some (.bound object) :=
  fun _ smaller => layout.slot initial object _ (layout.temporary_slot_lt active smaller)

theorem target_wellFormed {sorts : SortSignature} {terms : TermSignature} (layout : Layout)
    (signature : Signature sorts terms) {initial : Context} (formed : Context.WellFormed sorts initial) :
    Context.WellFormed sorts (layout.target initial signature.ids.object) :=
  Context.appendBounds_wellFormed formed signature.objectDeclared rfl _

theorem old_expression_independent {sorts : SortSignature} {terms : TermSignature}
    {initial remaining : Context} {expression : Preterm} {result : Nat}
    (layout : Layout) (typed : Preterm.HasType terms initial expression remaining result)
    (formed : Context.WellFormed sorts initial) (object offset : Nat) :
    ¬ Preterm.HasVar (layout.target initial object) (names initial offset) expression :=
  typed.independent_appendedBound formed object layout.limit offset
end Layout

universe u v
def forProof {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
    {gamma : Mettapedia.Logic.HOL.Ctx Base} {assumptions : List (Mettapedia.Logic.HOL.Formula Const gamma)}
    {conclusion : Mettapedia.Logic.HOL.Formula Const gamma}
    (proof : Mettapedia.Logic.HOL.ProofSyntax Const assumptions conclusion) : Layout :=
  ⟨proof.binderBudget, proof.nodeCount, proof.binderBudget_pos⟩

namespace Controls
def layout : Layout := ⟨2, 3, by decide⟩
theorem nontrivial_allocation : layout.limit = 20 ∧ layout.workDepth 0 = 2 ∧ layout.temporaryDepth 0 = 5 := by decide
theorem child_bank_fits : (layout.workDepth 0 + 1) + layout.width ≤ layout.workDepth 1 := by decide
theorem retained_positions : (layout.target [.bound 2, .regular 2 {0}] 2)[1]? = some (.regular 2 {0}) := by decide
theorem final_slot_present : (layout.target [] 2)[19]? = some (.bound 2) := by decide
theorem first_outside_slot_missing : (layout.target [] 2)[20]? = none := by decide
theorem distinct_frame_roots : layout.workDepth 0 ≠ layout.workDepth 1 := by decide
end Controls

#print axioms Layout.work_slot_lt
#print axioms Layout.temporary_slot_lt
#print axioms Layout.child_source_before_next_frame
#print axioms Layout.target_wellFormed
#print axioms Layout.old_expression_independent
#print axioms forProof
end Mettapedia.Languages.MM0.HOLKernelProofAllocation
