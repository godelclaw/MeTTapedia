import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeListResultEvidence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeFormationReadback
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation

/-!
# Independent replay and open callers of the List result projection

The certificate is checked against the original closed program and product
type. Regularity and telescope inversion recover the full input context.
Typed callers may supply an arbitrary List and its supplied relational bundle;
neither input is assumed to be a constructor spine.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeListResultView
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration RussellTarski NativeIndexedFamilies

local instance : DecidableRel rules.headTyping :=
  fun a b => inferInstanceAs (Decidable (Tower.rules.headTyping a b))
local instance : DecidablePred rules.isUniverse :=
  fun a => inferInstanceAs (Decidable (Tower.rules.isUniverse a))
local instance : ∀ a b c, Decidable (rules.join a b c) :=
  fun a b c => inferInstanceAs (Decidable (Tower.rules.join a b c))
local instance : DecidableRel rules.cumulative :=
  fun a b => inferInstanceAs (Decidable (Tower.rules.cumulative a b))
local instance : DecidableRel rules.headEq := LevelTower.instDecidableHeadEq

set_option maxRecDepth 8192 in
theorem programme_replayed : FormationSensitiveElaboration.replay rules decoder .nil
    programme programmeType Evidence.submission = true := by decide +kernel

theorem programme_typed : FormationSensitive.Judgment rules .nil programme programmeType :=
  FormationSensitiveElaboration.replay_sound rules decoder programme_replayed

def inputContext : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (sortTm level)) (sortTm level))
    (Intrinsic.listApp (.var 1)))
    (bundleType (.var 2) (constantPredicate (.var 1)) (.var 0))

theorem input_context_formed : FormationSensitive.ContextFormation rules inputContext := by
  obtain ⟨level, isUniverse, formed⟩ := programme_typed.regularity
    (FormationSensitive.towerUniverseRegularity.includeSignature instantiation.signature)
  have formation : FormationSensitive.Typing rules .nil
      (TelescopeAbstraction.closeType inputContext (Intrinsic.listApp (.var 2))) (.head level) :=
    formed.typing
  exact (TelescopeAbstraction.formation_of_closeType inputContext isUniverse formation).1

def application {n : Nat} (sigma : Sub Tower.Head 4 n) : Tower.Tm n :=
  TelescopeAbstraction.applyClosed inputContext sigma (liftClosed programme)

theorem application_typed {n : Nat} {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation rules context) {sigma : Sub Tower.Head 4 n}
    (typed : FormationSensitive.CtxMor rules inputContext context sigma) :
    FormationSensitive.Judgment rules context (application sigma)
      (subst sigma (Intrinsic.listApp (.var 2))) := by
  refine ⟨formed, ?_⟩
  exact FormationCheckedTelescopePrograms.apply_typed typed
    (FormationCheckedTelescopePrograms.liftClosed_typing programme_typed.typing context)

theorem neutral_assignment : FormationSensitive.CtxMor rules inputContext inputContext ids := by
  intro index
  simpa only [subst_ids, ids] using
    (FormationSensitive.Typing.var (R := rules) (Γ := inputContext) index)

theorem neutral_application : FormationSensitive.Judgment rules inputContext (application ids)
    (Intrinsic.listApp (.var 2)) := by
  simpa only [subst_ids] using application_typed input_context_formed neutral_assignment

/-- The target declaration environment is instantiated along with the proof.
The original proof-relevant List/identity/relator roots are retained. -/
def levelInstance (theta : Nat → Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat) :
    LevelInstance instantiation.signature theta where
  computation := instantiation.signature.computation
  computationMap := by
    intro n left right retained
    obtain ⟨evidence⟩ := retained
    exact ⟨IntrinsicRelatorLevels.mapCombinedIotaEvidence (substLevelsHead theta) evidence⟩

theorem programme_levels (theta : Nat → Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat) :
    FormationSensitive.Judgment (levelInstance theta).rules .nil
      (substLevelsTm theta programme) (substLevelsTm theta programmeType) :=
  (levelInstance theta).refinedJudgment programme_typed

namespace Controls

set_option maxRecDepth 8192 in
theorem changed_result_refused : FormationSensitiveElaboration.replay rules decoder .nil
    programme (sortTm Tower.zero) Evidence.submission = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("List result program replays at its polymorphic product type",
    FormationSensitiveElaboration.replay rules decoder .nil programme programmeType Evidence.submission),
   ("List result certificate refuses a changed displayed type",
    !(FormationSensitiveElaboration.replay rules decoder .nil programme (sortTm Tower.zero) Evidence.submission))]

end Controls

#print axioms programme_replayed
#print axioms programme_typed
#print axioms input_context_formed
#print axioms application_typed
#print axioms neutral_application
#print axioms Controls.changed_result_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeListResultView
