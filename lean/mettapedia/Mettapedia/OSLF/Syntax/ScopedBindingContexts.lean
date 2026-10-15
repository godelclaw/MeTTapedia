import Mettapedia.OSLF.Syntax.ScopedBindingSortedReadout

/-!
# Linear contexts with actual declared binders

A frame selects one operator argument and stores every other intrinsically
scoped sibling. Its hole is in the selected argument's extended context.
Paths compose these frames, without identifying different hole positions
that happen to have the same filled term. Arbitrary substitution contexts
with zero or multiple hole occurrences are not this context grammar.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory

variable (S : Binding.Signature)

inductive BindingFrame : Scope S → Scope S → Type where
  | slot (context : Binding.Ctx S) (sort : S.Srt) (operator : S.Op sort)
      (position : Fin (S.arity operator).length)
      (siblings : (other : Fin (S.arity operator).length) → other ≠ position →
        Binding.Term S (((S.arity operator).get other).1 ++ context)
          ((S.arity operator).get other).2) :
      BindingFrame (((S.arity operator).get position).1 ++ context,
        ((S.arity operator).get position).2) (context, sort)

variable {S}

def BindingFrame.fill {source target : Scope S} (frame : BindingFrame S source target)
    (supplied : Binding.Term S source.1 source.2) : Binding.Term S target.1 target.2 := by
  cases frame with
  | slot context sort operator position siblings =>
    exact .op operator (assembleArguments context (S.arity operator) (fun other =>
      if same : other = position then same.symm ▸ supplied else siblings other same))

@[instance_reducible]
def bindingFrameQuiver (S : Binding.Signature) : Quiver (Scope S) where
  Hom := BindingFrame S

def bindingAction (S : Binding.Signature) :
    @Mettapedia.CategoryTheory.GroundPath.Action (Scope S) (bindingFrameQuiver S) := by
  letI := bindingFrameQuiver S
  exact { Value := fun scope => Binding.Term S scope.1 scope.2, frame := BindingFrame.fill }

abbrev BindingContext (S : Binding.Signature) (source target : Scope S) :=
  @Quiver.Path (Scope S) (bindingFrameQuiver S) source target

abbrev BindingContextObject (S : Binding.Signature) :=
  @Mettapedia.CategoryTheory.GroundPath.Object (Scope S) (bindingFrameQuiver S) (bindingAction S)

abbrev bindingOrigin (S : Binding.Signature) : BindingContextObject S :=
  @Mettapedia.CategoryTheory.GroundPath.Object.origin (Scope S) (bindingFrameQuiver S)
    (bindingAction S)

abbrev bindingInterface (S : Binding.Signature) (scope : Scope S) : BindingContextObject S :=
  @Mettapedia.CategoryTheory.GroundPath.Object.interface (Scope S) (bindingFrameQuiver S)
    (bindingAction S) scope

def bindingContextArrow {source target : Scope S} (context : BindingContext S source target) :
    bindingInterface S source ⟶ bindingInterface S target :=
  @Mettapedia.CategoryTheory.GroundPath.contextArrow (Scope S) (bindingFrameQuiver S)
    (bindingAction S) source target context

def bindingTermArrow {scope : Scope S} (term : Binding.Term S scope.1 scope.2) :
    bindingOrigin S ⟶ bindingInterface S scope :=
  @Mettapedia.CategoryTheory.GroundPath.valueArrow (Scope S) (bindingFrameQuiver S)
    (bindingAction S) scope term

noncomputable section

def encodeFrame {source target : Scope S} :
    BindingFrame S source target → SortedConstructors.Frame (signature S) source target
  | .slot context sort operator position siblings =>
      .slot (signature := signature S) (Constructor.operation (S := S) context sort operator)
        position (fun other absent => encode (siblings other absent))

def decodeFrame {source target : Scope S}
    (frame : SortedConstructors.Frame (signature S) source target) : BindingFrame S source target :=
  @SortedConstructors.Frame.rec (signature S)
    (fun source target _ => BindingFrame S source target)
    (fun constructor position siblings => match constructor with
      | .variable _ _ _ => Fin.elim0 position
      | .operation context sort operator =>
          .slot context sort operator position (fun other absent => decode (siblings other absent)))
    source target frame

theorem decode_encodeFrame {source target : Scope S} (frame : BindingFrame S source target) :
    decodeFrame (encodeFrame frame) = frame := by
  cases frame with
  | slot context sort operator position siblings =>
    apply congrArg (BindingFrame.slot context sort operator position)
    funext other absent
    exact decode_encode (siblings other absent)

theorem encode_decodeFrame {source target : Scope S}
    (frame : SortedConstructors.Frame (signature S) source target) :
    encodeFrame (decodeFrame frame) = frame := by
  apply @SortedConstructors.Frame.rec (signature S)
    (fun source target frame => encodeFrame (decodeFrame frame) = frame) (t := frame)
  intro constructor position siblings
  cases constructor with
  | «variable» context sort originalPosition => exact Fin.elim0 position
  | operation context sort operator =>
    apply congrArg (SortedConstructors.Frame.slot (signature := signature S)
      (Constructor.operation (S := S) context sort operator) position)
    funext other absent
    exact encode_decode (siblings other absent)

theorem encodeFrame_fill {source target : Scope S} (frame : BindingFrame S source target)
    (supplied : Binding.Term S source.1 source.2) :
    encode (frame.fill supplied) = SortedConstructors.Frame.fill (encodeFrame frame) (encode supplied) := by
  cases frame with
  | slot context sort operator position siblings =>
    change SortedConstructors.Term.node (signature := signature S)
        (Constructor.operation (S := S) context sort operator)
        (encodeArguments (assembleArguments context (S.arity operator) (fun other =>
          if same : other = position then same.symm ▸ supplied else siblings other same))) = _
    rw [encodeArguments_assemble]
    apply congrArg (SortedConstructors.Term.node (signature := signature S)
      (Constructor.operation (S := S) context sort operator))
    funext other
    by_cases same : other = position
    · subst other
      simp only [dite_true]
    · simp only [dif_neg same]

def encodeContext {source target : Scope S} (context : BindingContext S source target) :
    SortedConstructors.Context (signature S) source target :=
  @Quiver.Path.rec (Scope S) (bindingFrameQuiver S) source
    (fun target _ => SortedConstructors.Context (signature S) source target)
    (@Quiver.Path.nil (Scope S) (SortedConstructors.frameQuiver (signature S)) source)
    (fun _ frame previous => @Quiver.Path.cons (Scope S)
      (SortedConstructors.frameQuiver (signature S)) _ _ _ previous (encodeFrame frame)) target context

def decodeContext {source target : Scope S}
    (context : SortedConstructors.Context (signature S) source target) : BindingContext S source target :=
  @Quiver.Path.rec (Scope S) (SortedConstructors.frameQuiver (signature S)) source
    (fun target _ => BindingContext S source target)
    (@Quiver.Path.nil (Scope S) (bindingFrameQuiver S) source)
    (fun _ frame previous => @Quiver.Path.cons (Scope S) (bindingFrameQuiver S)
      _ _ _ previous (decodeFrame frame)) target context

theorem decode_encodeContext {source target : Scope S} (context : BindingContext S source target) :
    decodeContext (encodeContext context) = context := by
  induction context with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    change @Quiver.Path.cons (Scope S) (bindingFrameQuiver S) _ _ _
      (decodeContext (encodeContext previous)) (decodeFrame (encodeFrame frame)) = _
    rw [decode_encodeFrame, inductionHypothesis]

theorem encode_decodeContext {source target : Scope S}
    (context : SortedConstructors.Context (signature S) source target) :
    encodeContext (decodeContext context) = context := by
  induction context with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    change @Quiver.Path.cons (Scope S) (SortedConstructors.frameQuiver (signature S)) _ _ _
      (encodeContext (decodeContext previous)) (encodeFrame (decodeFrame frame)) = _
    rw [encode_decodeFrame, inductionHypothesis]

theorem encodeContext_comp {source middle target : Scope S}
    (inner : BindingContext S source middle) (outer : BindingContext S middle target) :
    encodeContext (@Quiver.Path.comp (Scope S) (bindingFrameQuiver S) source middle target inner outer) =
      @Quiver.Path.comp (Scope S) (SortedConstructors.frameQuiver (signature S))
        source middle target (encodeContext inner) (encodeContext outer) := by
  induction outer with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    exact congrArg (fun context => @Quiver.Path.cons (Scope S)
      (SortedConstructors.frameQuiver (signature S)) _ _ _ context (encodeFrame frame)) inductionHypothesis

theorem encodeContext_fill {source target : Scope S} (context : BindingContext S source target)
    (supplied : Binding.Term S source.1 source.2) :
    encode (@Mettapedia.CategoryTheory.GroundPath.Action.path (Scope S) (bindingFrameQuiver S)
      (bindingAction S) source target context supplied) =
      @Mettapedia.CategoryTheory.GroundPath.Action.path (Scope S)
        (SortedConstructors.frameQuiver (signature S)) (SortedConstructors.action (signature S))
        source target (encodeContext context) (encode supplied) := by
  induction context with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    change encode (frame.fill (@Mettapedia.CategoryTheory.GroundPath.Action.path (Scope S)
      (bindingFrameQuiver S) (bindingAction S) _ _ previous supplied)) = _
    exact (encodeFrame_fill frame (@Mettapedia.CategoryTheory.GroundPath.Action.path (Scope S)
      (bindingFrameQuiver S) (bindingAction S) _ _ previous supplied)).trans
        (congrArg (SortedConstructors.Frame.fill (encodeFrame frame)) inductionHypothesis)

def contextEquiv (source target : Scope S) :
    BindingContext S source target ≃ SortedConstructors.Context (signature S) source target where
  toFun := encodeContext
  invFun := decodeContext
  left_inv := decode_encodeContext
  right_inv := encode_decodeContext

end

end Mettapedia.OSLF.Binding.ScopedEncoding
