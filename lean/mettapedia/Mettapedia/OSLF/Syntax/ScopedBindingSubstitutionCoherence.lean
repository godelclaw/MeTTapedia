import Mettapedia.OSLF.Syntax.ScopedBindingContextSubstitution

/-!
# Identity and composition of full binding-path substitution

The equations compare the computed hole context, every inherited variable
image and the whole resulting path. They use lifted substitution and the
actual term substitution laws, without cancelling a ground filling action.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

variable {S : Binding.Signature}

theorem substituteFrameSlot_identity {context : Binding.Ctx S} {sort : S.Srt}
    (operator : S.Op sort) (position : Fin (S.arity operator).length)
    (siblings : (other : Fin (S.arity operator).length) → other ≠ position →
      Binding.Term S (((S.arity operator).get other).1 ++ context)
        ((S.arity operator).get other).2) :
    substituteFrameSlot operator position siblings (fun _ value => .var value) =
      BindingFrame.slot context sort operator position siblings := by
  apply congrArg (BindingFrame.slot context sort operator position)
  funext other absent
  rw [Binding.liftSub_var, Binding.bind_id]

theorem substituteFrameSlot_composition {context middle destination : Binding.Ctx S} {sort : S.Srt}
    (operator : S.Op sort) (position : Fin (S.arity operator).length)
    (siblings : (other : Fin (S.arity operator).length) → other ≠ position →
      Binding.Term S (((S.arity operator).get other).1 ++ context)
        ((S.arity operator).get other).2)
    (first : Binding.Sub S context middle) (second : Binding.Sub S middle destination) :
    substituteFrameSlot operator position siblings (fun sort value => Binding.bind second (first sort value)) =
      substituteFrameSlot operator position (fun other absent =>
        Binding.bind (Binding.liftSub first ((S.arity operator).get other).1) (siblings other absent)) second := by
  apply congrArg (BindingFrame.slot destination sort operator position)
  funext other absent
  exact (congrArg (fun sigma => Binding.bind sigma (siblings other absent))
    (Binding.liftSub_comp first second ((S.arity operator).get other).1)).symm.trans
      (Binding.bind_comp (Binding.liftSub first ((S.arity operator).get other).1)
        (Binding.liftSub second ((S.arity operator).get other).1) (siblings other absent)).symm

theorem substituteContext_identity {source target : Scope S} (context : BindingContext S source target) :
    substituteContext context target.1 (fun _ value => .var value) =
      (⟨source.1, fun _ value => .var value, context⟩ : SubstitutedContext S source target.2 target.1) := by
  induction context with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    cases frame with
    | slot original sort operator position siblings =>
      change
        (let inner := substituteContext previous
            (((S.arity operator).get position).1 ++ original)
            (Binding.liftSub (fun _ value => Binding.Term.var value) ((S.arity operator).get position).1)
         (⟨inner.holeContext, inner.holeVariables,
           @Quiver.Path.cons (Scope S) (bindingFrameQuiver S) _ _ _ inner.path
             (substituteFrameSlot operator position siblings (fun _ value => .var value))⟩ :
           SubstitutedContext S source sort original)) = _
      rw [Binding.liftSub_var, inductionHypothesis, substituteFrameSlot_identity]

def twiceSubstitutedContext {source target : Scope S} (context : BindingContext S source target)
    (middle destination : Binding.Ctx S) (first : Binding.Sub S target.1 middle)
    (second : Binding.Sub S middle destination) : SubstitutedContext S source target.2 destination :=
  let inner := substituteContext context middle first
  let outer := substituteContext inner.path destination second
  ⟨outer.holeContext, fun sort value => Binding.bind outer.holeVariables (inner.holeVariables sort value),
    outer.path⟩

theorem substituteContext_composition {source target : Scope S} (context : BindingContext S source target) :
    ∀ (middle destination : Binding.Ctx S) (first : Binding.Sub S target.1 middle)
      (second : Binding.Sub S middle destination),
      substituteContext context destination (fun sort value => Binding.bind second (first sort value)) =
        twiceSubstitutedContext context middle destination first second := by
  induction context with
  | nil => intro middle destination first second; rfl
  | cons previous frame inductionHypothesis =>
    intro middle destination first second
    cases frame with
    | slot original sort operator position siblings =>
      have lifted := (Binding.liftSub_comp first second ((S.arity operator).get position).1).symm
      have inherited := inductionHypothesis
        (((S.arity operator).get position).1 ++ middle)
        (((S.arity operator).get position).1 ++ destination)
        (Binding.liftSub first ((S.arity operator).get position).1)
        (Binding.liftSub second ((S.arity operator).get position).1)
      let firstInner := substituteContext previous (((S.arity operator).get position).1 ++ middle)
        (Binding.liftSub first ((S.arity operator).get position).1)
      let secondInner := substituteContext firstInner.path
        (((S.arity operator).get position).1 ++ destination)
        (Binding.liftSub second ((S.arity operator).get position).1)
      change
        (let inner := substituteContext previous
            (((S.arity operator).get position).1 ++ destination)
            (Binding.liftSub (fun sort value => Binding.bind second (first sort value))
              ((S.arity operator).get position).1)
         (⟨inner.holeContext, inner.holeVariables,
           @Quiver.Path.cons (Scope S) (bindingFrameQuiver S) _ _ _ inner.path
             (substituteFrameSlot operator position siblings
               (fun sort value => Binding.bind second (first sort value)))⟩ :
           SubstitutedContext S source sort destination)) =
          (⟨secondInner.holeContext,
            fun sort value => Binding.bind secondInner.holeVariables (firstInner.holeVariables sort value),
            @Quiver.Path.cons (Scope S) (bindingFrameQuiver S) _ _ _ secondInner.path
              (substituteFrameSlot operator position (fun other absent =>
                Binding.bind (Binding.liftSub first ((S.arity operator).get other).1)
                  (siblings other absent)) second)⟩ : SubstitutedContext S source sort destination)
      rw [lifted, inherited, substituteFrameSlot_composition]
      rfl

end Mettapedia.OSLF.Binding.ScopedEncoding
