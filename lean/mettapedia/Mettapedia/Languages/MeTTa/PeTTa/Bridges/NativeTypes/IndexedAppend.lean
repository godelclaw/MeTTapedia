import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialMeaning
import Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend

/-!
# Length observations of completed emitted append packets

Only a packet containing exactly one expression array is observed. Each
element contributes one marker, so this observation retains length and
multiplicity, but deliberately forgets payload and order. The append theorem
separately retains the complete ordered payload. The target spatial checker
uses the shared formula and its existing resumable strategy.

The two evaluator phases have their own checked libraries. The native gate
qualifies their concatenation and the engine's array-to-bag adapter; these
theorems do not identify an arbitrary C implementation with the Lean evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppend

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes
open Decision.Spatial
open Mettapedia.GSLT.LanguageDef IndexedInductive IndexedInductiveNatVec

def marker : Pattern := .apply "Element" []

def observe (values : List Atom) : List Pattern := values.map (fun _ => marker)

def observePacket : List Atom → Option (List Pattern)
  | [.expression values] => some (observe values)
  | _ => none

theorem observe_length (values : List Atom) : (observe values).length = values.length :=
  List.length_map _

/-- Completion is checked before the array is exposed as an observation. -/
theorem observe_completed (before after : Effects.State) (left right answers input output : List Atom)
    (completed : ∃ fuel, Eval.run IndexedInductiveAppend.library.runtime fuel
      {state := before, control := .evaluate []
        (IndexedInductiveAppend.appendCall (.expression left) (.expression right))} =
      .complete after answers input output) :
    observePacket answers = some (observe (left ++ right)) ∧
      after = before ∧ input = [] ∧ output = [] := by
  obtain ⟨state, packet, inputs, outputs⟩ :=
    (IndexedInductiveAppend.append_completed_iff before after left right answers input output).mp completed
  exact ⟨by rw [packet]; rfl, state, inputs, outputs⟩

def session (count : Nat) (values : List Atom) : Execution.Session :=
  .begin (BagModel.sizeExactly count) (observe values) (Consumers.IndexedAppend.sizeExactly_admitted count)

theorem eventually_length_iff (before : Effects.State) (count : Nat) (values : List Atom) :
    (∃ work, SpatialRuntime.ReadCompletes before ((session count values).resume work) (some true)) ↔
      values.length = count :=
  (SpatialRuntime.eventually_positive_iff before (session count values)).trans
    ((BagModel.sizeExactly_iff count (observe values)).trans (by rw [observe_length]))

theorem eventually_wrong_length_iff (before : Effects.State) (count : Nat) (values : List Atom) :
    (∃ work, SpatialRuntime.ReadCompletes before ((session count values).resume work) (some false)) ↔
      values.length ≠ count :=
  (SpatialRuntime.eventually_negative_iff before (session count values)).trans
    (not_congr ((BagModel.sizeExactly_iff count (observe values)).trans (by rw [observe_length])))

theorem completed_append_length_iff (before after : Effects.State) (count : Nat)
    (left right values input output : List Atom)
    (completed : ∃ fuel, Eval.run IndexedInductiveAppend.library.runtime fuel
      {state := before, control := .evaluate []
        (IndexedInductiveAppend.appendCall (.expression left) (.expression right))} =
      .complete after [.expression values] input output) :
    (∃ work, SpatialRuntime.ReadCompletes after ((session count values).resume work) (some true)) ↔
      left.length + right.length = count := by
  have packet := ((IndexedInductiveAppend.append_completed_iff before after left right
    [.expression values] input output).mp completed).2.1
  have same : values = left ++ right := by simpa only [List.cons.injEq, Atom.expression.injEq,
    and_true] using packet
  rw [eventually_length_iff, same, List.length_append]

/-- The same observation is about the original indexed-polynomial append,
not merely an unrelated array fixture. -/
theorem source_append_length_iff (before : Effects.State) (count : Nat) {n m : Natural.Carrier}
    (left : Vectors.Vector Atom n) (right : Vectors.Vector Atom m) :
    (∃ work, SpatialRuntime.ReadCompletes before
      ((session count (VectorArray.encode (Vectors.append left right)).val.toList).resume work)
      (some true)) ↔ Natural.toNat n + Natural.toNat m = count := by
  rw [eventually_length_iff, Array.length_toList, (VectorArray.encode (Vectors.append left right)).property,
    Natural.toNat_add]

theorem unfinished (before : Effects.State) (count : Nat) (values : List Atom) :
    SpatialRuntime.ReadCompletes before (session count values) none :=
  (SpatialRuntime.read_completes_iff _ _ _).mpr rfl

theorem resume_add (count : Nat) (values : List Atom) (first more : Nat) :
    ((session count values).resume first).resume more = (session count values).resume (first + more) :=
  (session count values).resume_add first more

/-- A driver can bound each invocation without changing the final cursor.
The total is strategy work; host allocation and instruction costs are separate. -/
theorem resume_rounds (start : Execution.Session) (rounds : List Nat) :
    rounds.foldl Execution.Session.resume start = start.resume rounds.sum := by
  induction rounds generalizing start with
  | nil => rfl
  | cons first rest ih =>
    rw [List.foldl_cons, ih, Execution.Session.resume_add, List.sum_cons]

#print axioms completed_append_length_iff
#print axioms source_append_length_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppend
