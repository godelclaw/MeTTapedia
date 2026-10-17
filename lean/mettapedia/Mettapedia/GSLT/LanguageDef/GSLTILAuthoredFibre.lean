import Mettapedia.GSLT.LanguageDef.GSLTILNativeKernel
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeComposition

/-!
# An authored rewrite fibre in the native command kernel

One explicitly named stage installs the original equation-saturated authored
rewrite relation. Local evidence is an original rewrite recipe; direct replay
earns the dispatcher's checking and source-coverage contracts. No successor
catalog or enumeration is required. No transport routes are installed.

The public authored boundary compiles the retained snapshot and permissions.
Finite command journals witness literal sequential runs. Equation-only
endpoint equivalence remains explicit in semantic traces; it is not silently
added as a command reduction or a zero-length literal journal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.AuthoredFibre

open Mettapedia.OSLF.MeTTaIL
open Syntax GeneralExecutionAdmission GeneralRewriteRecipeComposition

variable (stage : Pattern) (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

def source : NativeKernel.Source where
  fibre actualStage first last := actualStage = stage ∧
    (GeneralOccurrenceSemantics.gslt plan bound type).Step first last
  transport _ _ _ _ _ _ := False

def evidence : NativeKernel.LocalEvidence where
  FibreProof := GeneralRewriteRecipe.StepTrace
  TransportProof := Empty
  fibre recipe actualStage first last := actualStage = stage ∧
    GeneralRewriteRecipe.StepTrace.Valid plan bound type first last recipe
  transport proof := Empty.elim proof

def checking : NativeKernel.LocalChecking (evidence stage plan bound type) where
  fibre recipe actualStage first last := decide (actualStage = stage) &&
    GeneralRewriteRecipe.check plan bound type first last recipe
  transport proof := Empty.elim proof
  fibre_exact recipe actualStage first last := by
    change ((decide (actualStage = stage) &&
      GeneralRewriteRecipe.check plan bound type first last recipe) = true) ↔
        actualStage = stage ∧ GeneralRewriteRecipe.StepTrace.Valid plan bound type first last recipe
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact and_congr Iff.rfl (GeneralRewriteRecipe.check_exact plan bound type first last recipe)
  transport_exact proof := Empty.elim proof

theorem coverage : NativeKernel.LocalCoverage (source stage plan bound type) (evidence stage plan bound type) where
  fibre actualStage first last := by
    constructor
    · rintro ⟨same, step⟩
      obtain ⟨recipe, valid⟩ := (GeneralRewriteRecipe.exists_valid_iff_step plan bound type first last).mpr step
      exact ⟨recipe, same, valid⟩
    · rintro ⟨recipe, same, valid⟩
      exact ⟨same, (GeneralRewriteRecipe.exists_valid_iff_step plan bound type first last).mp ⟨recipe, valid⟩⟩
  transport _ _ _ _ _ _ := by
    constructor
    · intro impossible
      exact impossible.elim
    · rintro ⟨proof, _⟩
      exact proof.elim

/-- Command replay specializes the existing dispatcher without changing its
three rules or treating unavailable transports as realizations. -/
theorem exists_checked_iff_runs (first last : NativeKernel.Command) :
    (∃ journal, NativeKernel.check (checking stage plan bound type) first last journal = true) ↔
      NativeKernel.Runs (source stage plan bound type) first last :=
  NativeKernel.accepted_iff_runs (coverage stage plan bound type) (checking stage plan bound type) first last

def atJournal (trace : GeneralRewriteRecipeComposition.Trace) : NativeKernel.Journal (evidence stage plan bound type) :=
  trace.map (fun link => .fibre link.next link.step)

def underneathJournal (trace : GeneralRewriteRecipeComposition.Trace) : NativeKernel.Journal (evidence stage plan bound type) :=
  trace.map (fun link => .underneath link.next link.step)

theorem replay_at (first : Pattern) (trace : GeneralRewriteRecipeComposition.Trace) :
    NativeKernel.replay (checking stage plan bound type) (.at stage first)
      (atJournal stage plan bound type trace) =
      (GeneralRewriteRecipeComposition.Trace.replay plan bound type first trace).map (NativeKernel.Command.at stage) := by
  induction trace generalizing first with
  | nil => rfl
  | cons link rest ih =>
      simp only [atJournal, List.map_cons, NativeKernel.replay, NativeKernel.executeEntry,
        checking, decide_true, Bool.true_and, GeneralRewriteRecipeComposition.Trace.replay]
      cases accepted : GeneralRewriteRecipe.check plan bound type first link.next link.step <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_none,
          Option.map_none, Option.bind_some]
      exact ih link.next

theorem replay_underneath (kind route targetStage first : Pattern) (trace : GeneralRewriteRecipeComposition.Trace) :
    NativeKernel.replay (checking stage plan bound type) (.via kind route stage targetStage first)
      (underneathJournal stage plan bound type trace) =
      (GeneralRewriteRecipeComposition.Trace.replay plan bound type first trace).map
        (NativeKernel.Command.via kind route stage targetStage) := by
  induction trace generalizing first with
  | nil => rfl
  | cons link rest ih =>
      simp only [underneathJournal, List.map_cons, NativeKernel.replay, NativeKernel.executeEntry,
        checking, decide_true, Bool.true_and, GeneralRewriteRecipeComposition.Trace.replay]
      cases accepted : GeneralRewriteRecipe.check plan bound type first link.next link.step <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_none,
          Option.map_none, Option.bind_some]
      exact ih link.next

theorem check_at_iff (first last : Pattern) (trace : GeneralRewriteRecipeComposition.Trace) :
    NativeKernel.check (checking stage plan bound type) (.at stage first) (.at stage last)
      (atJournal stage plan bound type trace) = true ↔ GeneralRewriteRecipeComposition.Trace.Valid plan bound type trace first last := by
  rw [NativeKernel.check, replay_at]
  simp only [decide_eq_true_eq, Option.map_eq_some_iff]
  constructor
  · rintro ⟨target, replayed, same⟩
    have equal : target = last := by cases same; rfl
    subst target
    exact (GeneralRewriteRecipeComposition.Trace.replay_exact plan bound type trace first last).mp replayed
  · intro valid
    exact ⟨last, (GeneralRewriteRecipeComposition.Trace.replay_exact plan bound type trace first last).mpr valid, rfl⟩

theorem check_underneath_iff (kind route targetStage first last : Pattern) (trace : GeneralRewriteRecipeComposition.Trace) :
    NativeKernel.check (checking stage plan bound type) (.via kind route stage targetStage first)
      (.via kind route stage targetStage last) (underneathJournal stage plan bound type trace) = true ↔
      GeneralRewriteRecipeComposition.Trace.Valid plan bound type trace first last := by
  rw [NativeKernel.check, replay_underneath]
  simp only [decide_eq_true_eq, Option.map_eq_some_iff]
  constructor
  · rintro ⟨target, replayed, same⟩
    have equal : target = last := by cases same; rfl
    subst target
    exact (GeneralRewriteRecipeComposition.Trace.replay_exact plan bound type trace first last).mp replayed
  · intro valid
    exact ⟨last, (GeneralRewriteRecipeComposition.Trace.replay_exact plan bound type trace first last).mpr valid, rfl⟩

/-- Source declaration authority enters through the actual authored compiler,
not through a caller-supplied adequacy predicate. -/
theorem authored_coverage (snapshot : Snapshot) (permissions : Permissions) :
    NativeKernel.LocalCoverage
      (source stage (compile snapshot permissions) bound type)
      (evidence stage (compile snapshot permissions) bound type) :=
  coverage stage (compile snapshot permissions) bound type

theorem authored_exists_checked_iff_runs (snapshot : Snapshot) (permissions : Permissions)
    (first last : NativeKernel.Command) :
    (∃ journal, NativeKernel.check (checking stage (compile snapshot permissions) bound type) first last journal = true) ↔
      NativeKernel.Runs (source stage (compile snapshot permissions) bound type) first last :=
  exists_checked_iff_runs stage (compile snapshot permissions) bound type first last

end Mettapedia.GSLT.LanguageDef.GSLTIL.AuthoredFibre
