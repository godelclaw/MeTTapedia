import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipKernel
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle

/-!
# Three readings of a native type of the membership language

A forward native type of the membership language is read three ways, each constructed on its own:
- **operationally** (`runs`): the sets denoted by the hereditary terms that have it, which the front door decides on
  terms;
- **intensionally** (`predicateOf`): its translation, a predicate of set theory, which every package over the set
  theory types as a function from the sets to the propositions (`nativePredicate_typed`);
- **extensionally** (`extensionOf`): the hereditarily finite sets at which a predicate of set theory is true in the
  model whose individuals are all the sets.

The two ways from a native type to sets agree (`readings_agree`), by the correctness of the translation and the
bounded morphism from terms to sets, not by definition. So they form a triangle (`triangle`).

Positive example: the sets with at least three members include `3` (`three_runs`). Negative example: the triangle
is not exact. Holding everywhere and being well founded are different native types with the same sets
(`triangle_loses`), since every set is well founded (`wellFounded_everywhere`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol model fullDomains)
open Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity (Closed triangleOfThree triangleOfThree_loses)
open Mettapedia.Computability.ComputationalTrinity (Comparison)

/-- The hereditarily finite sets: those the hereditary terms denote. -/
def hfSets : Set ZFSet.{0} := {x | ∃ term, IsHF term ∧ zfOf term = x}

/-- The forward native types, the ones that terms and the sets they denote share. -/
abbrev ForwardType := {formula : Formula 0 // formula.forward = true}

/-- **The operational reading**: the sets denoted by the hereditary terms that have the native type. -/
def runs (formula : ForwardType) : Set ZFSet.{0} :=
  {x | ∃ term, IsHF term ∧ zfOf term = x ∧ Membership.sat Env.closed formula.1 term}

/-- **The intensional reading**: the native type's translation, a predicate of set theory. -/
def predicateOf (formula : ForwardType) : Term Symbol [] (Ty.arr setTy .prop) :=
  Relational.translate zfRelations formula.1

/-- The valuation of the empty context. -/
def noValuation : model.{0}.Valuation [] := fun v => nomatch v

/-- **The extensional reading**: the hereditarily finite sets at which a predicate of set theory is true. -/
def extensionOf (predicate : Term Symbol [] (Ty.arr setTy .prop)) : Set ZFSet.{0} :=
  {x | x ∈ hfSets ∧ (model.{0}.denote predicate noValuation x).down}

/-- **The two ways from a native type to sets agree.** -/
theorem readings_agree (formula : ForwardType) : extensionOf (predicateOf formula) = runs formula := by
  ext x
  constructor
  · rintro ⟨⟨term, holds, rfl⟩, inside⟩
    exact ⟨term, holds, rfl, (sat_iff_extensional formula.2 holds).mpr
      ((Relational.denote_translate_closed fullDomains zfRelations_interprets formula.1 noValuation _).mp inside)⟩
  · rintro ⟨term, holds, rfl, inside⟩
    exact ⟨⟨term, holds, rfl⟩, (Relational.denote_translate_closed fullDomains zfRelations_interprets formula.1
      noValuation _).mpr ((sat_iff_extensional formula.2 holds).mp inside)⟩

/-- **The triangle of the three readings.** -/
def triangle : Comparison.{0, 0, 1} Closed :=
  triangleOfThree (fun formula : ULift.{1} ForwardType => ULift.up.{1} (predicateOf formula.down))
    (fun predicate => extensionOf predicate.down) (fun formula => runs formula.down)
    (fun formula => readings_agree formula.down)

/-- Positive example: `3` has at least three members, read on terms and in sets. -/
theorem three_runs : zfOf three ∈ runs ⟨.atLeast 3 .forward .any .top, rfl⟩ :=
  ⟨three, three_holds, rfl, ask_proved three_members_answer⟩

/-- **Every set is well founded**: every descent along membership ends. -/
theorem wellFounded_everywhere (x : ZFSet.{0}) :
    extensional.sat Env.closed (.mu (.necessarily .any (.var 0))) x := by
  intro closed isClosed
  induction x using ZFSet.inductionOn with
  | h x below => exact isClosed x fun next step => below next step.2

/-- Negative example: **the triangle is not exact**. Holding everywhere and being well founded are different
native types with the same sets. -/
theorem triangle_loses : triangle.LosesProgramInformation := by
  refine triangleOfThree_loses _ _ _ _ (left := ULift.up ⟨.top, rfl⟩)
    (right := ULift.up ⟨.mu (.necessarily .any (.var 0)), rfl⟩)
    (fun same => nomatch congrArg Subtype.val (ULift.up.inj same)) ?_
  ext x
  constructor
  · rintro ⟨term, holds, rfl, -⟩
    exact ⟨term, holds, rfl, (sat_iff_extensional rfl holds).mpr (wellFounded_everywhere _)⟩
  · rintro ⟨term, holds, rfl, -⟩
    exact ⟨term, holds, rfl, trivial⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
