import Mettapedia.OSLF.Syntax.ScopedBindingContexts

/-!
# Capture-avoiding substitution on complete binding-context paths

Substituting the outer context lifts the supplied variable substitution under
each selected argument's declared binders. The recursive construction returns
the resulting hole context, its complete variable substitution and the entire
transformed path. Its filling square is proved from the independent term
substitution and ordered-argument operations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

variable {S : Binding.Signature}

theorem bindArgs_assemble {context destination : Binding.Ctx S}
    (sigma : Binding.Sub S context destination) :
    ∀ (declarations : List (List S.Srt × S.Srt))
      (arguments : (position : Fin declarations.length) →
        Binding.Term S ((declarations.get position).1 ++ context)
          (declarations.get position).2),
      Binding.bindArgs sigma (assembleArguments context declarations arguments) =
        assembleArguments destination declarations (fun position =>
          Binding.bind (Binding.liftSub sigma (declarations.get position).1) (arguments position))
  | [], _ => rfl
  | _ :: tail, arguments => by
      exact congrArg (Binding.Args.cons
        (Binding.bind (Binding.liftSub sigma _) (arguments 0)))
          (bindArgs_assemble sigma tail (fun position => arguments position.succ))

def substituteFrameSlot {context destination : Binding.Ctx S} {sort : S.Srt}
    (operator : S.Op sort) (position : Fin (S.arity operator).length)
    (siblings : (other : Fin (S.arity operator).length) → other ≠ position →
      Binding.Term S (((S.arity operator).get other).1 ++ context)
        ((S.arity operator).get other).2)
    (sigma : Binding.Sub S context destination) :
    BindingFrame S (((S.arity operator).get position).1 ++ destination,
      ((S.arity operator).get position).2) (destination, sort) :=
  .slot destination sort operator position (fun other absent =>
    Binding.bind (Binding.liftSub sigma ((S.arity operator).get other).1) (siblings other absent))

theorem substituteFrameSlot_fill {context destination : Binding.Ctx S} {sort : S.Srt}
    (operator : S.Op sort) (position : Fin (S.arity operator).length)
    (siblings : (other : Fin (S.arity operator).length) → other ≠ position →
      Binding.Term S (((S.arity operator).get other).1 ++ context)
        ((S.arity operator).get other).2)
    (sigma : Binding.Sub S context destination)
    (supplied : Binding.Term S (((S.arity operator).get position).1 ++ context)
      ((S.arity operator).get position).2) :
    Binding.bind sigma ((BindingFrame.slot context sort operator position siblings).fill supplied) =
      (substituteFrameSlot operator position siblings sigma).fill
        (Binding.bind (Binding.liftSub sigma ((S.arity operator).get position).1) supplied) := by
  change Binding.Term.op operator (Binding.bindArgs sigma
    (assembleArguments context (S.arity operator) (fun other =>
      if same : other = position then same.symm ▸ supplied else siblings other same))) = _
  rw [bindArgs_assemble]
  apply congrArg (Binding.Term.op operator)
  apply congrArg (assembleArguments destination (S.arity operator))
  funext other
  by_cases same : other = position
  · subst other
    simp only [dite_true]
  · simp only [dif_neg same]

def fillContext {source target : Scope S} (context : BindingContext S source target)
    (supplied : Binding.Term S source.1 source.2) : Binding.Term S target.1 target.2 :=
  @Mettapedia.CategoryTheory.GroundPath.Action.path (Scope S) (bindingFrameQuiver S)
    (bindingAction S) source target context supplied

/-- Computed data only: no filling or substitution law is a structure field. -/
structure SubstitutedContext (S : Binding.Signature) (source : Scope S)
    (targetSort : S.Srt) (destination : Binding.Ctx S) where
  holeContext : Binding.Ctx S
  holeVariables : Binding.Sub S source.1 holeContext
  path : BindingContext S (holeContext, source.2) (destination, targetSort)

def substituteContext {source target : Scope S} (context : BindingContext S source target)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    SubstitutedContext S source target.2 destination :=
  @Quiver.Path.rec (Scope S) (bindingFrameQuiver S) source
    (fun target _ => (destination : Binding.Ctx S) → Binding.Sub S target.1 destination →
      SubstitutedContext S source target.2 destination)
    (fun destination sigma =>
      ⟨destination, sigma, @Quiver.Path.nil (Scope S) (bindingFrameQuiver S) _⟩)
    (fun _ frame inductionHypothesis destination sigma => by
      cases frame with
      | slot original sort operator position siblings =>
        let inner := inductionHypothesis (((S.arity operator).get position).1 ++ destination)
          (Binding.liftSub sigma ((S.arity operator).get position).1)
        exact ⟨inner.holeContext, inner.holeVariables,
          @Quiver.Path.cons (Scope S) (bindingFrameQuiver S) _ _ _ inner.path
            (substituteFrameSlot operator position siblings sigma)⟩)
    target context destination sigma

theorem substituteContext_fill {source target : Scope S} (context : BindingContext S source target) :
    ∀ (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination)
      (supplied : Binding.Term S source.1 source.2),
      Binding.bind sigma (fillContext context supplied) =
        fillContext (substituteContext context destination sigma).path
          (Binding.bind (substituteContext context destination sigma).holeVariables supplied) := by
  induction context with
  | nil => intro destination sigma supplied; rfl
  | cons previous frame inductionHypothesis =>
    intro destination sigma supplied
    cases frame with
    | slot original sort operator position siblings =>
      change Binding.bind sigma
        ((BindingFrame.slot original sort operator position siblings).fill
          (fillContext previous supplied)) =
        (substituteFrameSlot operator position siblings sigma).fill
          (fillContext (substituteContext previous
            (((S.arity operator).get position).1 ++ destination)
            (Binding.liftSub sigma ((S.arity operator).get position).1)).path
            (Binding.bind (substituteContext previous
              (((S.arity operator).get position).1 ++ destination)
              (Binding.liftSub sigma ((S.arity operator).get position).1)).holeVariables supplied))
      exact (substituteFrameSlot_fill operator position siblings sigma (fillContext previous supplied)).trans
        (congrArg (substituteFrameSlot operator position siblings sigma).fill
          (inductionHypothesis (((S.arity operator).get position).1 ++ destination)
            (Binding.liftSub sigma ((S.arity operator).get position).1) supplied))

end Mettapedia.OSLF.Binding.ScopedEncoding
