import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipe
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceNativeReceipts
import Mettapedia.GSLT.Causality.Mazurkiewicz

/-!
# Checked primitive rewrite squares and existing causal traces

Four original firing receipts authorize a particular commuting square. Each
edge is replayed against its actual source. Literal endpoint closure, stable
original site labels and prefix-incomparable physical addresses are checked
separately. The accepted data construct the existing independence tile and
its existing Mazurkiewicz swap; full local evidence remains in event fibres.

The checker does not search for residual firings, infer a missing side, or
assert universal commutation. In particular, overlapping addresses refuse this
independence policy even if all four submitted edges are individually valid.
Equation-aware administrative paths and changed effect/provider worlds are
not identified by a primitive square. No execution-time bound is asserted.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeParallel
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Core.InteractionEvent

/-- Literal ordinary addresses are independent when neither selects an
ancestor of the other. Independence alone does not establish commutation. -/
def AddressIndependent (first second : List Nat) : Prop :=
  ¬ first.IsPrefix second ∧ ¬ second.IsPrefix first

instance (first second : List Nat) : Decidable (AddressIndependent first second) :=
  inferInstanceAs (Decidable (¬ first.IsPrefix second ∧ ¬ second.IsPrefix first))

def siteIndependence (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) :
    SiteIndependence (GeneralOccurrenceNativeReceipts.interaction plan bound type) where
  indep first second := AddressIndependent first.2.1 second.2.1
  symm _ _ independent := ⟨independent.2,independent.1⟩
  irrefl _site independent := independent.1 ⟨[],List.append_nil _⟩

/-- Original stable site projection, already used by the original interaction
presentation. Full local proof evidence remains in the event fibre. -/
def siteOf (receipt : GeneralRuleJobs.Receipt) : Nat × List Nat × List TypingFrame :=
  (receipt.job.declaration.declarationIndex,receipt.job.site.address,receipt.job.site.typingFrames)

/-- Four explicitly supplied original residual firings, not a search request
for finding or guessing a commuting square. -/
structure Square where
  first : GeneralRuleJobs.Receipt
  second : GeneralRuleJobs.Receipt
  otherFirst : GeneralRuleJobs.Receipt
  otherSecond : GeneralRuleJobs.Receipt
  deriving Repr

/-- Independent original source authority for every edge, literal endpoint
closure and retained site identities authorize this particular swap. -/
def Square.Valid (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (square : Square) : Prop :=
  square.first.Valid plan bound type source ∧
  square.second.Valid plan bound type square.first.target ∧
  square.otherFirst.Valid plan bound type source ∧
  square.otherSecond.Valid plan bound type square.otherFirst.target ∧
  AddressIndependent square.first.job.site.address square.otherFirst.job.site.address ∧
  square.second.target = square.otherSecond.target ∧
  siteOf square.first = siteOf square.otherSecond ∧
  siteOf square.otherFirst = siteOf square.second

/-- Each edge is checked against its actual original source. Literal closure,
site identity and prefix independence are checked after those four replays. -/
def Square.check (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (square : Square) : Bool :=
  GeneralRewriteRecipe.checkFiring plan bound type source square.first &&
  GeneralRewriteRecipe.checkFiring plan bound type square.first.target square.second &&
  GeneralRewriteRecipe.checkFiring plan bound type source square.otherFirst &&
  GeneralRewriteRecipe.checkFiring plan bound type square.otherFirst.target square.otherSecond &&
  decide (AddressIndependent square.first.job.site.address square.otherFirst.job.site.address) &&
  decide (square.second.target = square.otherSecond.target) &&
  decide (siteOf square.first = siteOf square.otherSecond) &&
  decide (siteOf square.otherFirst = siteOf square.second)

theorem Square.check_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (square : Square) :
    square.check plan bound type source = true ↔ square.Valid plan bound type source := by
  simp only [Square.check,Square.Valid,Bool.and_eq_true,decide_eq_true_eq,
    GeneralRewriteRecipe.checkFiring_exact,and_assoc]

/-- A primitive receipt is the original occurrence event with an empty
administrative conversion path. -/
def firingEvent (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) {source : Pattern}
    (receipt : GeneralRuleJobs.Receipt) (valid : receipt.Valid plan bound type source) :
    (GeneralOccurrenceNativeReceipts.interaction plan bound type).Enabled source :=
  GeneralOccurrenceNativeReceipts.asInteraction plan bound type
    ⟨⟨source,[],receipt⟩,⟨.nil source,valid⟩⟩

/-- Construct the existing independence tile from four independently valid
source edges. No universal commutation axiom is added. -/
def Square.tile (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    {source : Pattern} (square : Square) (valid : square.Valid plan bound type source) :
    IndependenceTile (GeneralOccurrenceNativeReceipts.interaction plan bound type)
      (siteIndependence plan bound type) source where
  first := firingEvent plan bound type square.first valid.1
  second := firingEvent plan bound type square.second valid.2.1
  altFirst := firingEvent plan bound type square.otherFirst valid.2.2.1
  altSecond := firingEvent plan bound type square.otherSecond valid.2.2.2.1
  independent := valid.2.2.2.2.1
  close := valid.2.2.2.2.2.1
  sameFirst := valid.2.2.2.2.2.2.1
  sameSecond := valid.2.2.2.2.2.2.2

/-- Total checked square admission constructs the original tile only after
all four supplied residual firings and literal boundary conditions pass. -/
def Square.checkedTile (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (square : Square) :
    Option (IndependenceTile (GeneralOccurrenceNativeReceipts.interaction plan bound type)
      (siteIndependence plan bound type) source) :=
  if checked : square.check plan bound type source then
    some (square.tile plan bound type ((square.check_exact _ _ _ _).mp checked))
  else none

theorem Square.checkedTile_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (square : Square) :
    (square.checkedTile plan bound type source).isSome = true ↔ square.Valid plan bound type source := by
  unfold Square.checkedTile
  split
  · rename_i checked
    exact ⟨fun _ => (square.check_exact _ _ _ _).mp checked,fun _ => rfl⟩
  · rename_i refused
    constructor
    · intro impossible;cases impossible
    · intro valid;exact (refused ((square.check_exact _ _ _ _).mpr valid)).elim

/-- The admitted square yields exactly an existing Mazurkiewicz generator. -/
theorem Square.diamond (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    {source : Pattern} (square : Square) (valid : square.Valid plan bound type source) :
    Mettapedia.GSLT.Causality.Mazurkiewicz.DiamondEq (siteIndependence plan bound type)
      (square.tile plan bound type valid).path (square.tile plan bound type valid).pathSwap' :=
  .swap (square.tile plan bound type valid)

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeParallel
