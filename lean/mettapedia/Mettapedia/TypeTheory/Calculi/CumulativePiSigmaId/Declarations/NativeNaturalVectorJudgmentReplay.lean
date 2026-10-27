import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.JudgmentCompleteness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.SchemaJudgmentCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextChecking

/-!
# Finite annotated judgment replay for the original Nat/Vec profile

The original four rows provide a complete decoder of annotated roots and their
actual argument premises. The forty-rule declarative judgment then has exact
finite tree and shared-graph witnesses. This checks source judgments; it does
not extend the separate HOL interpretation to every source rule or former.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.Annotated.JudgmentReplay

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated

instance (enabled : ComputationProfiles.Selection) : DecidableRel (ComputationProfiles.rules enabled).headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
instance (enabled : ComputationProfiles.Selection) : DecidablePred (ComputationProfiles.rules enabled).isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
instance (enabled : ComputationProfiles.Selection) : ∀ u v w, Decidable ((ComputationProfiles.rules enabled).join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
instance (enabled : ComputationProfiles.Selection) : DecidableRel (ComputationProfiles.rules enabled).cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
instance (enabled : ComputationProfiles.Selection) : DecidableRel (ComputationProfiles.rules enabled).headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def decoder (enabled : ComputationProfiles.Selection) : Checking.RootDecoder (church enabled).computation :=
  SchemaJudgmentCode.decoder (church enabled).constantType NativeNaturalVectorFamilies.Checking.table enabled

abbrev interface (enabled : ComputationProfiles.Selection) := Checking.interface (church enabled) (decoder enabled)
abbrev Witness (enabled : ComputationProfiles.Selection) := (interface enabled).W
abbrev Certificate (enabled : ComputationProfiles.Selection) := Logic.Derivation (CStatement Tower.Head) (Witness enabled)

def check (enabled : ComputationProfiles.Selection) (certificate : Certificate enabled)
    (statement : CStatement Tower.Head) : Bool :=
  certificate.valid (interface enabled) && decide (certificate.concl = statement)

theorem check_sound (enabled : ComputationProfiles.Selection) {certificate : Certificate enabled}
    {statement : CStatement Tower.Head} (accepted : check enabled certificate statement = true) :
    CDerivable (church enabled) statement := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨valid, same⟩ := accepted
  rw [← same]
  exact Checking.derives_sound (church enabled) (decoder enabled)
    (certificate.valid_sound (interface enabled) valid)

theorem check_complete (enabled : ComputationProfiles.Selection) {statement : CStatement Tower.Head}
    (derived : CDerivable (church enabled) statement) :
    ∃ certificate : Certificate enabled, check enabled certificate statement = true := by
  obtain ⟨certificate, valid, same⟩ :=
    (Checking.derivable_iff_checked_tree (church enabled) (decoder enabled) statement).mp derived
  exact ⟨certificate, by simp [check, valid, same]⟩

theorem checked_iff (enabled : ComputationProfiles.Selection) (statement : CStatement Tower.Head) :
    (∃ certificate : Certificate enabled, check enabled certificate statement = true) ↔
      CDerivable (church enabled) statement :=
  ⟨fun ⟨_, accepted⟩ => check_sound enabled accepted, check_complete enabled⟩

theorem checked_graph_iff (enabled : ComputationProfiles.Selection) (statement : CStatement Tower.Head) :
    (∃ (nodes : List (DerivationGraph.Node (CStatement Tower.Head) (Witness enabled) Unit))
      (cache : Array (CStatement Tower.Head)) (root : Nat),
      DerivationGraph.replay (interface enabled) nodes = some cache ∧ cache[root]? = some statement) ↔
      CDerivable (church enabled) statement :=
  (Checking.derivable_iff_checked_graph (church enabled) (decoder enabled) statement).symm

abbrev ContextCertificate (enabled : ComputationProfiles.Selection) (n : Nat) :=
  Checking.ContextCode Tower.Head (Witness enabled) n

def checkContext (enabled : ComputationProfiles.Selection) {n : Nat} (context : CCtx Tower.Head n)
    (certificate : ContextCertificate enabled n) : Bool :=
  Checking.checkContext (church enabled) (decoder enabled) context certificate

theorem context_sound (enabled : ComputationProfiles.Selection) {n : Nat} {context : CCtx Tower.Head n}
    {certificate : ContextCertificate enabled n} (accepted : checkContext enabled context certificate = true) :
    CCtxFormed (church enabled) context :=
  Checking.checkContext_sound (church enabled) (decoder enabled) certificate accepted

theorem context_complete (enabled : ComputationProfiles.Selection) {n : Nat} {context : CCtx Tower.Head n}
    (formed : CCtxFormed (church enabled) context) :
    ∃ certificate : ContextCertificate enabled n, checkContext enabled context certificate = true :=
  Checking.checkContext_complete (church enabled) (decoder enabled) formed

#print axioms decoder
#print axioms check_sound
#print axioms check_complete
#print axioms checked_graph_iff

end Programs.Annotated.JudgmentReplay
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
