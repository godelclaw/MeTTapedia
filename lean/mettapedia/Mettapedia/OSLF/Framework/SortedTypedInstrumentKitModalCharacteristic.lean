import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitObservationComparison
import Mettapedia.GSLT.Logic.InterfaceModalLogic
import Mathlib.Data.List.OfFn

/-!
# Finite modal characteristic assays in an actual typed instrument kit

The observer is a finite formula built only from the admitted ask/get
arrows, truth and conjunction. Its semantics is the actual kit IPO relation,
independent of structural satisfaction and bisimilarity. Successful ask
recovers the entire tuple. Each finite child test then recovers its whole
class and earns purity before a competing original get firing is excluded.

The constructor recursion needs hereditary source-head permission. The
tested right value is arbitrary supported native syntax, and all original
reaction declarations and administrative origins remain explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit.Modal

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.InterfaceModalLogic

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}
variable (opened : Policy source Parallel)

def inspect (head : SourceHead source Parallel) (permission : opened head)
    (children : (position : Fin (headArity head)) →
      Formula (Object opened) (interface opened (.original (headInput head position)))) :
    Formula (Object opened) (interface opened (.original (headOutput head))) :=
  .diamond (probeArrow opened (.ask head) permission)
    (Formula.conjList (List.ofFn (fun position =>
      .diamond (probeArrow opened (.get head position) permission) (children position))))

def characteristic {sort : source.Srt} (supplied : Term source Parallel sort) :
    StructuralObservations.Supported opened supplied →
      Formula (Object opened) (interface opened (.original sort)) :=
  @Term.rec source Parallel
    (fun sort supplied => StructuralObservations.Supported opened supplied →
      Formula (Object opened) (interface opened (.original sort)))
    (fun {sort} parallel permission => inspect opened (.unit sort parallel) permission (fun absent => Fin.elim0 absent))
    (fun {sort} parallel _first _second firstRead secondRead permission =>
      inspect opened (.properCut sort parallel) permission.1
        (Fin.cases (firstRead permission.2.1) (fun _ => secondRead permission.2.2)))
    (fun constructor _arguments children permission => inspect opened (.ordinary constructor) permission.1
      (fun position => children position (permission.2 position))) sort supplied

variable (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))

private theorem inspect_iff (origins : Nonempty NativeOrigins) (head : SourceHead source Parallel)
    (permission : opened head)
    (arguments : (position : Fin (headArity head)) → Term source Parallel (headInput head position))
    (tests : (position : Fin (headArity head)) →
      Formula (Object opened) (interface opened (.original (headInput head position))))
    (readouts : ∀ position
      (right : ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position)))
      (rightSupported : ClassSupported opened right),
      Holds (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) (tests position)
        (value right rightSupported) ↔ classOf (embed (arguments position)) = right)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (rightSupported : ClassSupported opened right) :
    Holds (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (inspect opened head permission tests) (value right rightSupported) ↔
        classOf (sourceNode head (fun position => embed (arguments position))) = right := by
  obtain ⟨origin⟩ := origins
  let rules := categoryRules (NativeOrigins := NativeOrigins) originalRules opened
  let embedded : Arguments head := fun position => embed (arguments position)
  have children : ∀ position, Supported opened (embedded position) :=
    fun position => embed_supported opened (arguments position)
  constructor
  · rintro ⟨matched, step, holds⟩
    obtain ⟨matchedArrow, matchedSupport⟩ := matched
    cases matchedArrow with
    | value matched =>
      have matchedSupported := value_class_supported opened matched matchedSupport
      obtain ⟨_matchedOrigin, before, rightRead, wholeTarget⟩ :=
        ask_step_readout opened originalRules head permission right rightSupported matched matchedSupported step
      subst matched
      have beforeChildren : ∀ position, Supported opened (before position) :=
        ((bundle_supported_iff opened head before).mp
          ((classOf_supported_iff opened (bundle head before)).mp matchedSupported)).2
      have eachTest := List.forall_mem_ofFn_iff.mp
        ((holds_conjList rules _ _).mp holds)
      have coordinates : ∀ position, classOf (embedded position) = classOf (before position) := by
        intro position
        obtain ⟨after, afterStep, afterHolds⟩ := eachTest position
        obtain ⟨afterArrow, afterSupport⟩ := after
        cases afterArrow with
        | value after =>
          have afterSupported := value_class_supported opened after afterSupport
          have recovered := (readouts position after afterSupported).mp afterHolds
          have pureAfter : classObserverCount after = 0 := by
            rw [← recovered]
            exact classObserverCount_embedding (classOf (arguments position))
          have coordinate := (get_pure_result_readout opened originalRules
            head before position permission beforeChildren after afterSupported pureAfter afterStep).2
          exact recovered.trans coordinate
      exact (sourceNode_class_congruence head embedded before coordinates).trans rightRead.symm
  · intro same
    subst right
    refine ⟨value (classOf (bundle head embedded))
      ⟨_, (bundle_supported_iff opened head embedded).mpr ⟨permission, children⟩, rfl⟩,
      ask_step opened originalRules origin head embedded permission children, ?_⟩
    apply (holds_conjList rules _ _).mpr
    rw [List.forall_mem_ofFn_iff]
    intro position
    exact ⟨value (classOf (embedded position)) ⟨_, children position, rfl⟩,
      get_step opened originalRules origin head embedded position permission children,
      (readouts position _ ⟨_, children position, rfl⟩).mpr rfl⟩

theorem characteristic_iff (origins : Nonempty NativeOrigins) {sort : source.Srt}
    (supplied : Term source Parallel sort) :
    ∀ (permitted : StructuralObservations.Supported opened supplied)
      (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
      (rightSupported : ClassSupported opened right),
      Holds (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
        (characteristic opened supplied permitted) (value right rightSupported) ↔
          classOf (embed supplied) = right := by
  apply @Term.rec source Parallel
    (fun sort supplied => ∀ (permitted : StructuralObservations.Supported opened supplied)
      (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
      (rightSupported : ClassSupported opened right),
      Holds (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
        (characteristic opened supplied permitted) (value right rightSupported) ↔
          classOf (embed supplied) = right) (t := supplied)
  · intro sort parallel permitted right rightSupported
    exact inspect_iff opened originalRules origins (.unit sort parallel) permitted
      (fun absent => Fin.elim0 absent) (fun absent => Fin.elim0 absent)
      (fun absent => Fin.elim0 absent) right rightSupported
  · intro sort parallel first second firstInduction secondInduction permitted right rightSupported
    let arguments : Fin 2 → Term source Parallel sort := Fin.cases first (fun _ => second)
    let tests : Fin 2 → Formula (Object opened) (interface opened (.original sort)) :=
      Fin.cases (characteristic opened first permitted.2.1) (fun _ => characteristic opened second permitted.2.2)
    have readouts : ∀ position
        (after : ValueClass (source := source) (Parallel := Parallel) (.original sort))
        (afterSupported : ClassSupported opened after),
        Holds (categoryRules (NativeOrigins := NativeOrigins) originalRules opened) (tests position)
          (value after afterSupported) ↔ classOf (embed (arguments position)) = after := by
      intro position
      fin_cases position
      · exact firstInduction permitted.2.1
      · exact secondInduction permitted.2.2
    exact inspect_iff opened originalRules origins (.properCut sort parallel) permitted.1
      arguments tests readouts right rightSupported
  · intro constructor arguments children permitted right rightSupported
    exact inspect_iff opened originalRules origins (.ordinary constructor) permitted.1 arguments
      (fun position => characteristic opened (arguments position) (permitted.2 position))
      (fun position => children position (permitted.2 position)) right rightSupported

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit.Modal
