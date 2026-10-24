import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RuleSkeleton
import Mettapedia.GSLT.Dynamics.ContextIndexedSwitching
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Scoped multi-hole contexts across execution representations

The existing rho `Skeleton` has arbitrarily nested message/parallel shapes,
constant quoted names, and any number of reads, including repeated reads.
This module compiles that syntax to a stack program, independently executes
the program, and connects a list-frontier tree evaluator to an indexed-frontier
executor. Both read the current activation environment at execution time.

The simulation preserves the whole pending occurrence list, full activation
keys, environment, and ordered output. Environment replacement (including
rollback), publication and cancellation are explicit boundary operations.
This is a context-assembly fragment, not the concurrent rho reaction scheduler,
the source rho compiler, or the semantics of a MeTTa quotation form.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators.ScopedContextSwitching

open Mettapedia.GSLT.Dynamics
open RegionHolePlan RepresentationSwitching OrderedOccurrenceBodyAlgebra
open Mettapedia.GraphTheory.Representation
open Mettapedia.GSLT.Core.NonFactorization

/-! ## An independently executed compilation -/

inductive Instruction where
  | read (channel : Comb)
  | literal (value : Comb)
  | pair
  | message
  deriving DecidableEq, Repr

def compile : Skeleton → List Instruction
  | .read channel => [.read channel]
  | .const value => [.literal value]
  | .nodePar left right => compile left ++ compile right ++ [.pair]
  | .nodeMsg left right => compile left ++ compile right ++ [.message]

def execute (env : Comb → Comb) : List Instruction → List Comb → Option (List Comb)
  | [], stack => some stack
  | .read channel :: rest, stack => execute env rest (env channel :: stack)
  | .literal value :: rest, stack => execute env rest (value :: stack)
  | .pair :: rest, right :: left :: stack => execute env rest (.par left right :: stack)
  | .message :: rest, right :: left :: stack => execute env rest (.mm left right :: stack)
  | .pair :: _, _ => none
  | .message :: _, _ => none

theorem execute_append (env : Comb → Comb) (first second : List Instruction)
    (stack : List Comb) :
    execute env (first ++ second) stack =
      (execute env first stack).bind (execute env second) := by
  induction first generalizing stack with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction with
      | read channel => simpa [execute] using ih (env channel :: stack)
      | literal value => simpa [execute] using ih (value :: stack)
      | pair | message =>
          cases stack with
          | nil => rfl
          | cons right stack =>
              cases stack with
              | nil => rfl
              | cons left stack => simp [execute, ih]

/-- Compilation is stack-polymorphic: an unrelated caller suffix survives. -/
theorem execute_compile (skeleton : Skeleton) (env : Comb → Comb) (stack : List Comb) :
    execute env (compile skeleton) stack = some (skeleton.fill env :: stack) := by
  induction skeleton generalizing stack with
  | read channel => rfl
  | const value => rfl
  | nodePar left right ihLeft ihRight | nodeMsg left right ihLeft ihRight =>
      simp [compile, execute_append, ihLeft, ihRight, execute, Skeleton.fill]

theorem compile_length (skeleton : Skeleton) :
    (compile skeleton).length = skeleton.cost := by
  induction skeleton <;> simp_all [compile, Skeleton.cost, Nat.add_assoc]

/-- Uniform relabeling of read coordinates has a contravariant environment
action. One environment supplies the entire context, including nested names. -/
def renameReads (rename : Comb → Comb) : Skeleton → Skeleton
  | .read channel => .read (rename channel)
  | .const value => .const value
  | .nodePar left right => .nodePar (renameReads rename left) (renameReads rename right)
  | .nodeMsg left right => .nodeMsg (renameReads rename left) (renameReads rename right)

theorem fill_renameReads (skeleton : Skeleton) (rename env : Comb → Comb) :
    (renameReads rename skeleton).fill env = skeleton.fill (env ∘ rename) := by
  induction skeleton <;> simp_all [renameReads, Skeleton.fill, Function.comp_def]

/-! ## Instance of the language-independent switching contract -/

/-- The compiler certificate discharges the generic kernel's local obligation.
Uncompiled malformed stacks may fail; compiled templates never do. -/
def kernel (program : Nat → Skeleton) : ContextIndexedSwitching.Kernel Comb Comb where
  Code := List Instruction
  source index env := (program index).fill env
  prepared index := compile (program index)
  execute code env := ((execute env code []).getD []).headD .nil
  correct index env := by simp [execute_compile]

/-! ## Nested quotations, repeated reads, and mixed-instance controls -/

def leftChannel : Comb := .nil
def rightChannel : Comb := .kk .nil

def nestedContext : Skeleton :=
  .nodePar
    (.nodeMsg (.read leftChannel) (.read rightChannel))
    (.nodeMsg (.read leftChannel)
      (.nodeMsg (.read rightChannel) (.const (.ev (.kk .nil)))))

def firstEnvironment : Comb → Comb := fun channel =>
  if channel = leftChannel then .kk .nil else .ev .nil

def secondEnvironment : Comb → Comb := fun channel =>
  if channel = leftChannel then .kk (.kk .nil) else .ev (.ev .nil)

/-- The entire compiled nested body uses one activation environment. Reads
may repeat without introducing a second environment authority. -/
theorem nested_context_exact :
    execute firstEnvironment (compile nestedContext) [] =
      some [.par (.mm (.kk .nil) (.ev .nil))
        (.mm (.kk .nil) (.mm (.ev .nil) (.ev (.kk .nil))))] := by decide

/-- One source instantiation expands to nine independently executed stack
instructions. The simulation therefore is not a one-step correspondence. -/
theorem instantiation_is_not_one_stack_step : (compile nestedContext).length = 9 := by decide

/-- Correct per-atom assembly does not license joining atoms from different
instances into one quotation. -/
theorem mixed_instances_change_quotation :
    (.par (.mm (firstEnvironment leftChannel) (firstEnvironment rightChannel))
      (.mm (secondEnvironment leftChannel)
        (.mm (secondEnvironment rightChannel) (.ev (.kk .nil))))) ≠
      nestedContext.fill firstEnvironment := by decide

theorem malformed_program_refuses : execute firstEnvironment [.message] [] = none := rfl

/-- Hygienic coordinate transport can be implemented without materializing
the body. The inverse is required on read coordinates, not on all names. -/
theorem compile_renamed_exact (skeleton : Skeleton) (rename : Comb → Comb)
    (original fresh : Comb → Comb)
    (agrees : ∀ channel ∈ skeleton.readChannels, fresh (rename channel) = original channel) :
    execute fresh (compile (renameReads rename skeleton)) [] =
      some [skeleton.fill original] := by
  rw [execute_compile, fill_renameReads]
  exact congrArg (fun value => some [value]) ((skeleton.fill_eq_iff _ _).2 agrees)

/-- A renamed compiled context can reproduce an environment exactly iff that
environment factors through the renamed coordinates it actually reads.
Names outside this support need no recovery law. -/
theorem compile_renamed_iff_factors (skeleton : Skeleton) (rename original : Comb → Comb) :
    (∃ fresh : Comb → Comb,
      execute fresh (compile (renameReads rename skeleton)) [] =
        some [skeleton.fill original]) ↔
      Factors (fun channel : {channel // channel ∈ skeleton.readChannels} => rename channel.val)
        (fun channel => original channel.val) := by
  simp only [execute_compile, fill_renameReads, Option.some.injEq, List.cons.injEq,
    and_true, skeleton.fill_eq_iff]
  constructor
  · rintro ⟨fresh, agrees⟩
    exact ⟨fresh, fun channel => agrees channel.val channel.property⟩
  · rintro ⟨fresh, agrees⟩
    exact ⟨fresh, fun channel present => agrees ⟨channel, present⟩⟩

/-- No adapter after a coordinate collision can restore two distinguishable
read values. This applies to computed addresses and foreign constructor names
at the same observer boundary. -/
theorem compile_renamed_impossible_of_collision (skeleton : Skeleton)
    (rename original : Comb → Comb) {left right : Comb}
    (leftRead : left ∈ skeleton.readChannels) (rightRead : right ∈ skeleton.readChannels)
    (collapsed : rename left = rename right) (distinguished : original left ≠ original right) :
    ¬ ∃ fresh : Comb → Comb,
      execute fresh (compile (renameReads rename skeleton)) [] =
        some [skeleton.fill original] := by
  let collision : NonTrivialFiber
      (fun channel : {channel // channel ∈ skeleton.readChannels} => rename channel.val)
      (fun channel => original channel.val) :=
    ⟨⟨left, leftRead⟩, ⟨right, rightRead⟩, collapsed, distinguished⟩
  exact fun completion => collision.not_factors
    ((compile_renamed_iff_factors skeleton rename original).1 completion)

/-- The independently executed nested quotation cannot be recovered after
its two distinct channels have been collapsed to one. -/
theorem collapsed_nested_reads_refused :
    ¬ ∃ fresh : Comb → Comb,
      execute fresh (compile (renameReads (fun _ => leftChannel) nestedContext)) [] =
        some [nestedContext.fill firstEnvironment] := by
  exact compile_renamed_impossible_of_collision nestedContext _ firstEnvironment
    (left := leftChannel) (right := rightChannel)
    (by simp [nestedContext, Skeleton.readChannels])
    (by simp [nestedContext, Skeleton.readChannels]) rfl (by decide)

/-! ## One prepared body, separate activation environments -/

/-- Recycling one handle does not identify successive activations. -/
def activation (generation : Nat) : ContextIndexedSwitching.ActivationKey :=
  ⟨7, generation⟩

/-- Both jobs use the same immutable nested body; only their environments
and physical output occurrences differ. -/
def pairedActivations : ContextIndexedSwitching.TreeState Comb Comb where
  store key := if key = activation 0 then firstEnvironment else secondEnvironment
  pending := [⟨activation 0, 0, 10⟩, ⟨activation 1, 0, 11⟩]
  published := []

/-- The independent stack executor reuses one prepared body while retaining
the two activation identities, correlated reads and ordered publications. -/
theorem shared_code_separate_activations :
    (ContextIndexedSwitching.repeats
      (ContextIndexedSwitching.indexedStep (kernel (fun _ => nestedContext))) 2
      (ContextIndexedSwitching.encode pairedActivations)).published =
      [⟨activation 0, 10, nestedContext.fill firstEnvironment⟩,
        ⟨activation 1, 11, nestedContext.fill secondEnvironment⟩] ∧
      nestedContext.fill firstEnvironment ≠ nestedContext.fill secondEnvironment := by
  have transported := congrArg ContextIndexedSwitching.TreeState.published
    (ContextIndexedSwitching.decode_repeats (kernel (fun _ => nestedContext)) 2
      (ContextIndexedSwitching.encode pairedActivations))
  constructor
  · simpa [ContextIndexedSwitching.decode, ContextIndexedSwitching.repeats,
      ContextIndexedSwitching.treeStep, ContextIndexedSwitching.encode,
      pairedActivations, kernel, activation] using transported
  · decide

/-- An update to another generation of this same handle cannot affect either
pending job. The complete residual and publication state commutes. -/
theorem other_generation_update_commutes (replacement : Comb → Comb) (count : Nat) :
    ContextIndexedSwitching.repeats
        (ContextIndexedSwitching.treeStep (kernel (fun _ => nestedContext))) count
        (ContextIndexedSwitching.treeBoundary
          (.environment (fun store => store.replace (activation 2) replacement)) pairedActivations) =
      ContextIndexedSwitching.treeBoundary
        (.environment (fun store => store.replace (activation 2) replacement))
        (ContextIndexedSwitching.repeats
          (ContextIndexedSwitching.treeStep (kernel (fun _ => nestedContext))) count pairedActivations) := by
  apply ContextIndexedSwitching.repeats_replace_other
  intro job present
  simp only [pairedActivations, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;> decide

#print axioms execute_compile
#print axioms compile_length
#print axioms fill_renameReads
#print axioms compile_renamed_exact
#print axioms mixed_instances_change_quotation
#print axioms compile_renamed_iff_factors
#print axioms compile_renamed_impossible_of_collision
#print axioms collapsed_nested_reads_refused
#print axioms shared_code_separate_activations
#print axioms other_generation_update_commutes

end Mettapedia.Languages.ProcessCalculi.RhoCombinators.ScopedContextSwitching
