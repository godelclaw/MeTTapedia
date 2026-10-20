import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial
import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceControls
import Mettapedia.OSLF.NativeTypes.Executable

/-! Shared-runtime controls for completed MeTTa answer observations. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial.Controls

open Mettapedia.Languages.MeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.NativeTypes.Decision.Reference
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.OSLF.NativeTypes.Instances
open Mettapedia.OSLF.NativeTypes.Runtime
open PeTTa.MeTTaZeroExtension.NativeControls (a b)

def firstOrigin : Pattern := .apply "Observation" [.apply "Origin1" [], b]
def secondOrigin : Pattern := .apply "Observation" [.apply "Origin2" [], b]
def sourceSpace : PeTTa.PeTTaSpace := {facts := [firstOrigin, secondOrigin], rules := []}
def pattern : Pattern := .apply "Observation" [.fvar "origin", .fvar "value"]
def template : Pattern := .fvar "value"

theorem source_origins_distinct : firstOrigin ≠ secondOrigin := by decide

theorem source_answer_bag : sourceSpace.spaceMatch pattern template = [b, b] := by
  simp [PeTTa.PeTTaSpace.spaceMatch, PeTTa.PeTTaSpace.storedAtoms,
    PeTTa.PeTTaSpace.storedRuleAtoms, sourceSpace, firstOrigin, secondOrigin,
    pattern, template, b, matchPattern, matchArgs, mergeBindings, applyBindings]

def session (formula : Core.Formula BagModel.Leaf) (fuel : Nat) :=
  Executable.search SpatialBag.installed formula
    (BagModel.encode (answers sourceSpace pattern template)) fuel

def completePacket (fuel : Nat) := session (packetFormula [b, b]) fuel

theorem two_copies_have_source_types :
    MeTTaSpace.QueryMember sourceSpace pattern template b 0 ∧
      MeTTaSpace.QueryMember sourceSpace pattern template b 1 ∧
      ¬ MeTTaSpace.QueryMember sourceSpace pattern template b 2 := by
  simp [MeTTaSpace.queryMember_iff, source_answer_bag]

theorem occurrence_formula_uses_real_source :
    BagModel.holds (occurrenceFormula b 1) (answers sourceSpace pattern template) :=
  (occurrence_meaning _ _ _ _ _).mpr two_copies_have_source_types.2.1

theorem singleton_is_not_two_copies :
    ¬ BagModel.holds (.atom (.singleton b)) [b, b] := by
  simp [BagModel.holds, Core.denotation, BagModel.tests, Core.Test.ofBoolean,
    BagModel.predicate]

theorem singleton_cuts_cannot_share_an_occurrence :
    ¬ BagModel.holds (occurrenceFormula b 1) [b] := by
  rw [occurrenceFormula, BagModel.atLeast_iff]
  simp

theorem packet_formula_rejects_missing_source_copy :
    ¬ BagModel.holds (packetFormula [b]) (answers sourceSpace pattern template) := by
  rw [packetFormula, BagModel.packet_iff]
  simp [answers, source_answer_bag]

theorem packet_formula_preserves_enumeration_permutation :
    BagModel.holds (packetFormula [a, b]) [b, a] := by
  rw [packetFormula, BagModel.packet_iff, Multiset.coe_eq_coe]
  exact List.Perm.swap _ _ []

theorem interrupted_search_resumes (first more : Nat) :
    completePacket (first + more) = Executable.resume more (completePacket first) :=
  Runtime.search_resume SpatialBag.driver SpatialBag.engine (packetFormula [b, b])
    (BagModel.encode (answers sourceSpace pattern template)) first more

theorem rejected_article_preserves_shared_meaning :
    MeTTaSpace.checkArticle PeTTa.MeTTaZeroExtension.NativeControls.duplicateRules
      MeTTaSpace.Controls.spaceTerm MeTTaSpace.Controls.pattern MeTTaSpace.Controls.template b
      (MeTTaSpace.Controls.article 2) = false ∧
    Runtime.Description.Meaning SpatialBag.driver (occurrenceFormula b 0)
      (BagModel.encode (answers PeTTa.MeTTaZeroExtension.NativeControls.duplicateRules
        MeTTaSpace.Controls.pattern MeTTaSpace.Controls.template)) :=
  ⟨MeTTaSpace.Controls.rejected_article_does_not_refute.1,
    (public_occurrence_meaning _ _ _ _ _).mpr
      MeTTaSpace.Controls.rejected_article_does_not_refute.2⟩

/-- These run the installed shared runtime, including its admission and
retained session, on the actual completed query observation. -/
def checks : List (String × Bool) :=
  [ ("MeTTaSpaceSpatial.packet-complete", decide ((completePacket 300).readout = .judgment (.decided true)))
  , ("MeTTaSpaceSpatial.packet-missing-copy", decide ((session (packetFormula [b]) 300).readout = .judgment (.decided false)))
  , ("MeTTaSpaceSpatial.packet-extra-copy", decide ((session (packetFormula [b, b, b]) 300).readout = .judgment (.decided false)))
  , ("MeTTaSpaceSpatial.packet-wrong-value", decide ((session (packetFormula [a, b]) 300).readout = .judgment (.decided false)))
  , ("MeTTaSpaceSpatial.second-copy", decide ((session (occurrenceFormula b 1) 300).readout = .judgment (.decided true)))
  , ("MeTTaSpaceSpatial.third-copy-absent", decide ((session (occurrenceFormula b 2) 300).readout = .judgment (.decided false)))
  , ("MeTTaSpaceSpatial.singleton-is-exact", decide ((session (.atom (.singleton b)) 300).readout = .judgment (.decided false)))
  , ("MeTTaSpaceSpatial.exhausted-is-unknown", decide ((completePacket 0).readout = .judgment .unknown))
  , ("MeTTaSpaceSpatial.interrupted-is-unknown", decide ((completePacket 2).readout = .judgment .unknown))
  , ("MeTTaSpaceSpatial.resume-result", decide ((Runtime.resume 298 (completePacket 2)).readout = (completePacket 300).readout))
  , ("MeTTaSpaceSpatial.resume-budget", decide ((Runtime.resume 298 (completePacket 2)).spent = (completePacket 300).spent))
  , ("MeTTaSpaceSpatial.structural-evidence", !(completePacket 300).spatialObservations.isEmpty)
  , ("MeTTaSpaceSpatial.no-invented-steps", (completePacket 300).observations.isEmpty)
  , ("MeTTaSpaceSpatial.undeclared-cut-refused", match session (.separating 1 .top .top) 300 with
      | .refusedFormula _ _ => true
      | _ => false)
  , ("MeTTaSpaceSpatial.wrong-source-refused", match Runtime.search SpatialBag.driver SpatialBag.engine
        (.atom .emp) b 300 with
      | .refusedSource _ => true
      | _ => false)
  , ("MeTTaSpaceSpatial.empty-accepted", decide ((Runtime.search SpatialBag.driver SpatialBag.engine
        (packetFormula []) (BagModel.encode []) 100).readout = .judgment (.decided true)))
  , ("MeTTaSpaceSpatial.empty-split-accepted", decide ((Runtime.search SpatialBag.driver SpatialBag.engine
        (.separating 0 (.atom .emp) (.atom .emp)) (BagModel.encode []) 100).readout = .judgment (.decided true)))
  , ("MeTTaSpaceSpatial.packet-reordered", decide ((Runtime.search SpatialBag.driver SpatialBag.engine
        (packetFormula [a, b]) (BagModel.encode [b, a]) 300).readout = .judgment (.decided true)))
  , ("MeTTaSpaceSpatial.origins-retained-in-source", decide (firstOrigin ≠ secondOrigin))
  , ("MeTTaSpaceSpatial.rejected-evidence-does-not-refute", MeTTaSpace.checkArticle
      PeTTa.MeTTaZeroExtension.NativeControls.duplicateRules MeTTaSpace.Controls.spaceTerm
      MeTTaSpace.Controls.pattern MeTTaSpace.Controls.template b (MeTTaSpace.Controls.article 2) == false &&
        decide ((Executable.search SpatialBag.installed (occurrenceFormula b 0)
          (BagModel.encode (answers PeTTa.MeTTaZeroExtension.NativeControls.duplicateRules
            MeTTaSpace.Controls.pattern MeTTaSpace.Controls.template)) 300).readout =
              .judgment (.decided true)))
  ]

end Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial.Controls
