import Mettapedia.OSLF.Syntax.SignatureMorphismSlots
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# Controls: forgetting the sorts of the reflective calculus

The reflective calculus has two sorts, names and processes. Forgetting the distinction is a morphism of binding
signatures onto a one-sorted signature with the same operators (`erase`). It identifies the two sorts, so it is not an
inclusion of a sub-signature.

- **The communication rule is carried to a positioned rewrite of the one-sorted calculus** (`erasedComm`). Its hole
  is still used exactly once, by the general theorem and by computation.
- **The slots are kept**: the channel is still a rely parameter and not a local one, and the payload is still a local
  parameter.
- **A morphism keeps the hole where an instantiation erases it** (`morphism_keeps_the_hole`). The context whose hole
  is a metavariable's argument is carried to a one-hole context. Instantiating that metavariable by a body that
  discards its argument erases the hole (`RhoSchema.instInto_destroys_position`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSortErasure

open RhoSchema

/-- **The one-sorted reflective calculus**: the same operators, every sort forgotten. -/
abbrev untyped : Signature where
  Srt := Unit
  Op := fun _ => Σ s : RhoSchema.Srt, RhoSchema.Op s
  arity := fun o => mapArities (fun _ => ()) (sig.arity o.2)

/-- **Forgetting the sorts.** -/
def erase : SigMor sig untyped where
  sortMap := fun _ => ()
  opMap := fun o => ⟨_, o⟩
  carriesArity := fun _ => rfl

/-- Names and processes are distinct sorts, and forgetting identifies them. -/
theorem erase_identifies_sorts : Srt.nm ≠ Srt.pr ∧ erase.sortMap Srt.nm = erase.sortMap Srt.pr :=
  ⟨by decide, rfl⟩

/-- The morphism on the signature the rule schema is written in. -/
abbrev eraseSchema : SigMor schemaSig (withMetas untyped (erase.mapMetas metas)) := erase.withMetas metas

/-- **The communication rule of the one-sorted calculus**, carried with its position. -/
def erasedComm : PositionedRewrite (withMetas untyped (erase.mapMetas metas)) := eraseSchema.onRewrite comm

/-- The carried context uses its hole exactly once. -/
theorem erasedComm_hole_occurs : holeCount erasedComm.position.ctxt = 1 := erasedComm.position.linear

/-- The same, by computation. -/
theorem erasedComm_hole_occurs_computed : holeCount erasedComm.position.ctxt = 1 := by decide

/-- **The channel is still a rely parameter.** -/
theorem erased_channel_is_rely : erasedComm.RelyParameter (mapVar eraseSchema.sortMap _ (Var.zero : Var G _)) :=
  (eraseSchema.relyParameter_onRewrite comm Var.zero).mpr channel_is_rely

/-- The channel is still not a local parameter. -/
theorem erased_channel_not_local :
    ¬ erasedComm.LocalParameter (mapVar eraseSchema.sortMap _ (Var.zero : Var G _)) :=
  fun isLocal => channel_not_local ((eraseSchema.localParameter_onRewrite comm Var.zero).mp isLocal)

/-- **The payload is still a local parameter.** -/
theorem erased_payload_is_local :
    erasedComm.LocalParameter (mapVar eraseSchema.sortMap _ (Var.succ Var.zero : Var G _)) :=
  (eraseSchema.localParameter_onRewrite comm (Var.succ Var.zero)).mpr payload_is_local

/-- The morphism on the signature with a unary metavariable over processes. -/
abbrev eraseDiscard : SigMor (withMetas sig discardMetas) (withMetas untyped (erase.mapMetas discardMetas)) :=
  erase.withMetas discardMetas

/-- **A morphism keeps the hole where an instantiation erases it.** The context whose hole is the metavariable's
argument is carried to a one-hole context, while instantiating the metavariable by a body that discards its argument
leaves no hole. -/
theorem morphism_keeps_the_hole :
    holeCount (eraseDiscard.onTerm metaHoleCtxt) = 1 ∧ holeCount (instInto discardBody metaHoleCtxt) = 0 :=
  ⟨(holeCount_mapTerm eraseDiscard metaHoleCtxt).trans metaHoleCtxt_linear, instInto_discard_erases⟩

end Mettapedia.OSLF.Binding.RhoSortErasure
