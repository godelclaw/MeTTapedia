import Mettapedia.OSLF.Syntax.ScopedBindingEquationSaturation
import Mettapedia.OSLF.Syntax.RhoEquationConstructorControls
import Mettapedia.GSLT.Logic.RelativePushout

/-!+# Complete rho context actions and the raw minimality boundary

Parallel-with-null and quote-after-drop act as identities on every supplied
source equation class. Their raw paths still have different lengths. The
actual semantic context quotient identifies these complete actions, while
retaining nontrivial actions such as adjoining an output. An explicit bound
is minimal after this quotient and is not minimal before it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedEquationContextControls

open _root_.CategoryTheory ScopedEncoding ScopedEquationContexts RhoSchema
open Mettapedia.GSLT IndexedContextActionQuotient RelativePushout
open RhoEquationConstructorControls

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

def processInterface (context : Ctx sig) : ScopedEquationContexts.ContextCategory sig :=
  (context, Srt.pr)

def nameInterface (context : Ctx sig) : ScopedEquationContexts.ContextCategory sig :=
  (context, Srt.nm)

def parallelFrame (context : Ctx sig) (sibling : Term sig context Srt.pr) :
    BindingFrame sig (context, Srt.pr) (context, Srt.pr) :=
  .slot context Srt.pr Op.par 0 (Fin.cases (fun absent => False.elim (absent rfl))
    (fun previous _ => by
      have only : previous = 0 := @Subsingleton.elim (Fin 1) inferInstance previous 0
      subst previous
      exact sibling))

def single {source target : Scope sig} (frame : BindingFrame sig source target) :
    BindingContext sig source target := (.nil : BindingContext sig source source).cons frame

def unitContext (context : Ctx sig) : BindingContext sig (context, Srt.pr) (context, Srt.pr) :=
  single (parallelFrame context null)

theorem unit_filling {context : Ctx sig} (value : Term sig context Srt.pr) :
    fillContext (unitContext context) value = parallel value null := rfl

theorem unit_complete_action {context : Ctx sig} (value : TermQ rhoSourceE context Srt.pr) :
    fillClass rhoSourceE (unitContext context) value = value := by
  induction value using Quotient.inductionOn with
  | _ value =>
    exact Quotient.sound (parallel_null_equation value)

theorem unit_context_identified (context : Ctx sig) :
    (projection (ScopedEquationContexts.action rhoSourceE)).map (unitContext context) =
      (projection (ScopedEquationContexts.action rhoSourceE)).map (𝟙 (processInterface context)) := by
  apply (context_eq_iff (ScopedEquationContexts.action rhoSourceE) _ _).mpr
  intro value
  exact (unit_complete_action value).trans (fillClass_identity rhoSourceE value).symm

def dropFrame (context : Ctx sig) : BindingFrame sig (context, Srt.nm) (context, Srt.pr) :=
  .slot context Srt.pr Op.drp 0 (fun other absent =>
    False.elim (absent (@Subsingleton.elim (Fin 1) inferInstance other 0)))

def quoteFrame (context : Ctx sig) : BindingFrame sig (context, Srt.pr) (context, Srt.nm) :=
  .slot context Srt.nm Op.quo 0 (fun other absent =>
    False.elim (absent (@Subsingleton.elim (Fin 1) inferInstance other 0)))

def quoteDropContext (context : Ctx sig) :
    BindingContext sig (context, Srt.nm) (context, Srt.nm) :=
  (single (dropFrame context)).comp (single (quoteFrame context))

def closeName {context : Ctx sig} (value : Term sig context Srt.nm) :
    Sub sig [Srt.nm] context
  | _, .zero => value

theorem quote_drop_open_equation {context : Ctx sig} (value : Term sig context Srt.nm) :
    EqClosure rhoSourceE (fillContext (quoteDropContext context) value) value := by
  simpa [quoteDropContext, single, dropFrame, quoteFrame, fillContext,
    Mettapedia.CategoryTheory.GroundPath.Action.path, BindingFrame.fill, bindingAction,
    assembleArguments, rhoSourceE, quoteDrop, instantiate, instantiateArgs,
    bind, bindArgs, liftSub, closeName] using
    (EqClosure.ax_closed (E := rhoSourceE) (Γ := context) 3 contDiscard (closeName value))

theorem quote_drop_complete_action {context : Ctx sig}
    (value : TermQ rhoSourceE context Srt.nm) :
    fillClass rhoSourceE (quoteDropContext context) value = value := by
  induction value using Quotient.inductionOn with
  | _ value => exact Quotient.sound (quote_drop_open_equation value)

theorem quote_drop_context_identified (context : Ctx sig) :
    (projection (ScopedEquationContexts.action rhoSourceE)).map (quoteDropContext context) =
      (projection (ScopedEquationContexts.action rhoSourceE)).map (𝟙 (nameInterface context)) := by
  apply (context_eq_iff (ScopedEquationContexts.action rhoSourceE) _ _).mpr
  intro value
  exact (quote_drop_complete_action value).trans (fillClass_identity rhoSourceE value).symm

theorem raw_unit_context_distinct (context : Ctx sig) :
    unitContext context ≠ (𝟙 (processInterface context) : BindingContext sig _ _) := by
  intro same
  have lengths := congrArg Quiver.Path.length same
  change (1 : Nat) = 0 at lengths
  cases lengths

theorem raw_quote_drop_context_distinct (context : Ctx sig) :
    quoteDropContext context ≠ (𝟙 (nameInterface context) : BindingContext sig _ _) := by
  intro same
  have lengths := congrArg Quiver.Path.length same
  change (2 : Nat) = 0 at lengths
  cases lengths

theorem raw_length_does_not_descend (context : Ctx sig) :
    ¬ ∃ reading :
        (((projection (ScopedEquationContexts.action rhoSourceE)).obj (context, Srt.pr)) ⟶
          ((projection (ScopedEquationContexts.action rhoSourceE)).obj (context, Srt.pr))) → Nat,
      ∀ path : BindingContext sig (context, Srt.pr) (context, Srt.pr),
        reading ((projection (ScopedEquationContexts.action rhoSourceE)).map path) = path.length := by
  rintro ⟨reading, readout⟩
  have identityRead : reading ((projection (ScopedEquationContexts.action rhoSourceE)).map
      (𝟙 (processInterface context))) = 0 := readout (.nil : BindingContext sig _ _)
  have same := (readout (unitContext context)).symm.trans
    ((congrArg reading (unit_context_identified context)).trans identityRead)
  change (1 : Nat) = 0 at same
  cases same

/-- Adjoining an actual output is not an identity action in this quotient. -/
theorem output_context_not_identified :
    (projection (ScopedEquationContexts.action rhoSourceE)).map (single (parallelFrame [] RhoSourceOutputPredicate.output)) ≠
      (projection (ScopedEquationContexts.action rhoSourceE)).map (𝟙 (processInterface [])) := by
  intro same
  have all := (context_eq_iff (ScopedEquationContexts.action rhoSourceE) _ _).mp same
  have counts := congrArg RhoSourceOutputPredicate.count (all (project nilP))
  change (1 : Nat) = 0 at counts
  cases counts

private theorem identity_bound_minimal {C : Type} [Category C] (object : C)
    (square : (𝟙 object) ≫ (𝟙 object) = (𝟙 object) ≫ (𝟙 object)) :
    IsIdemPushout (𝟙 object) (𝟙 object) (𝟙 object) (𝟙 object) square := by
  intro candidate
  refine ⟨candidate.inl, ⟨by simp [Candidate.self], ?_, ?_⟩, ?_⟩
  · simpa [Candidate.self] using candidate.comm
  · simpa [Candidate.self] using candidate.fac_left
  · rintro alternative ⟨left, _, _⟩
    exact (Category.id_comp alternative).symm.trans left

theorem raw_unit_bound_not_minimal (context : Ctx sig)
    (square : (𝟙 (processInterface context)) ≫ unitContext context =
      (𝟙 (processInterface context)) ≫ unitContext context) :
    ¬ IsIdemPushout (𝟙 (processInterface context)) (𝟙 (processInterface context))
      (unitContext context) (unitContext context) square := by
  intro minimal
  let smaller : Candidate (𝟙 (processInterface context)) (𝟙 (processInterface context))
      (unitContext context) (unitContext context) :=
    { apex := (context, Srt.pr)
      inl := 𝟙 _
      inr := 𝟙 _
      down := unitContext context
      comm := rfl
      fac_left := Category.id_comp _
      fac_right := Category.id_comp _ }
  obtain ⟨section_, split⟩ := minimal.down_splits smaller
  have lengths := congrArg Quiver.Path.length split
  change (section_.comp (unitContext context)).length = 0 at lengths
  rw [Quiver.Path.length_comp] at lengths
  change section_.length + 1 = 0 at lengths
  omega

theorem quotient_unit_bound_minimal (context : Ctx sig)
    (square :
      (𝟙 ((projection (ScopedEquationContexts.action rhoSourceE)).obj (context, Srt.pr))) ≫
          (projection (ScopedEquationContexts.action rhoSourceE)).map (unitContext context) =
      (𝟙 ((projection (ScopedEquationContexts.action rhoSourceE)).obj (context, Srt.pr))) ≫
          (projection (ScopedEquationContexts.action rhoSourceE)).map (unitContext context)) :
    IsIdemPushout (𝟙 _) (𝟙 _)
      ((projection (ScopedEquationContexts.action rhoSourceE)).map (unitContext context))
      ((projection (ScopedEquationContexts.action rhoSourceE)).map (unitContext context)) square := by
  have identifies := (unit_context_identified context).trans
    ((projection (ScopedEquationContexts.action rhoSourceE)).map_id (processInterface context))
  simpa only [identifies, processInterface] using
    (identity_bound_minimal ((projection (ScopedEquationContexts.action rhoSourceE)).obj
      (context, Srt.pr)) rfl)

end Mettapedia.OSLF.Binding.RhoScopedEquationContextControls
