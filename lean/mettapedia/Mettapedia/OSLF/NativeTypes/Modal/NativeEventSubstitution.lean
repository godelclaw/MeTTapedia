import Mettapedia.OSLF.NativeTypes.Modal.NativeQuerySubstitution

/-!
# Reindexing complete ordered operational histories

Every query origin, child declaration, matcher trace and quantified list index
is retained. Child contexts retain their local binder prefix; substitution
acts beneath that prefix on their actual programs and contextual captures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeEventSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding

mutual
def event (source target : List TypeExpr) (substitution : ContextSubstitution.Assignment) : Event → Event
  | .query index depth row origins => .query index depth row origins
  | .freshness index depth atom subject => .freshness index depth atom (ContextSubstitution.substitute substitution subject)
  | .quantified index depth kind entries => .quantified index depth kind (quantified source target substitution entries)
  | .child index depth declaration bound actualSource actualTarget trace targetTrace captured completed history =>
      let binders := bound.take (bound.length - source.length)
      let newBound := binders ++ target
      let lifted := ContextSubstitution.lift binders.length substitution
      .child index depth declaration newBound
        (ContextSubstitution.substitute lifted actualSource) (ContextSubstitution.substitute lifted actualTarget)
        trace targetTrace (NativeContextualSubstitution.assignment newBound.length lifted captured)
        (NativeContextualSubstitution.assignment newBound.length lifted completed)
        (events bound newBound lifted history)
termination_by original => sizeOf original

def events (source target : List TypeExpr) (substitution : ContextSubstitution.Assignment) : List Event → List Event
  | [] => []
  | head :: tail => event source target substitution head :: events source target substitution tail
termination_by originals => sizeOf originals

def quantified (source target : List TypeExpr) (substitution : ContextSubstitution.Assignment) :
    List (Nat × Pattern × List Event) → List (Nat × Pattern × List Event)
  | [] => []
  | (index, actual, history) :: tail =>
      (index, ContextSubstitution.substitute substitution actual, events source target substitution history) ::
        quantified source target substitution tail
termination_by originals => sizeOf originals
end

theorem local_prefix (binders source : List TypeExpr) :
    (binders ++ source).take ((binders ++ source).length - source.length) = binders := by
  simp only [List.length_append, Nat.add_sub_cancel, List.take_left]

theorem child_unscoped (source target : List TypeExpr) (substitution : ContextSubstitution.Assignment)
    (index depth declaration : Nat) (actualSource actualTarget : Pattern)
    (trace targetTrace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List Event) :
    event source target substitution (.child index depth declaration source actualSource actualTarget trace targetTrace captured completed history) =
      .child index depth declaration target (ContextSubstitution.substitute substitution actualSource)
        (ContextSubstitution.substitute substitution actualTarget) trace targetTrace
        (NativeContextualSubstitution.assignment target.length substitution captured)
        (NativeContextualSubstitution.assignment target.length substitution completed)
        (events source target substitution history) := by
  simp only [event, Nat.sub_self, List.take_zero, List.nil_append, List.length_nil, ContextSubstitution.lift_zero]

theorem child_scoped (source target binders : List TypeExpr) (substitution : ContextSubstitution.Assignment)
    (index depth declaration : Nat) (actualSource actualTarget : Pattern)
    (trace targetTrace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List Event) :
    event source target substitution (.child index depth declaration (binders ++ source) actualSource actualTarget trace targetTrace captured completed history) =
      .child index depth declaration (binders ++ target)
        (ContextSubstitution.substitute (ContextSubstitution.lift binders.length substitution) actualSource)
        (ContextSubstitution.substitute (ContextSubstitution.lift binders.length substitution) actualTarget) trace targetTrace
        (NativeContextualSubstitution.assignment (binders ++ target).length (ContextSubstitution.lift binders.length substitution) captured)
        (NativeContextualSubstitution.assignment (binders ++ target).length (ContextSubstitution.lift binders.length substitution) completed)
        (events (binders ++ source) (binders ++ target) (ContextSubstitution.lift binders.length substitution) history) := by
  simp only [event, local_prefix]

end Mettapedia.OSLF.NativeTypes.Modal.NativeEventSubstitution
