import Mettapedia.OSLF.NativeTypes.Decision.Structural.Matching

/-!
# Suspended matcher controls

Physical bag choices remain distinct even when their bindings agree.
Repeated bindings reject incompatible choices. Vector rests, explicit
substitutions and binder-arity mismatches exercise the same original matcher
comparison beyond the COMM pattern.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Structural.Matching.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling

def equivalent (left right : Pattern) := left == right
def first : Pattern := .apply "A" []
def second : Pattern := .apply "B" []
def pairPattern : Pattern := .collection .hashBag [.fvar "x", .fvar "x"] none
def equalPair : Pattern := .collection .hashBag [first, first] none
def unequalPair : Pattern := .collection .hashBag [first, second] none

def outputs (pattern term : Pattern) (budget : Nat) := (state equivalent pattern term budget).outputs

#guard outputs pairPattern equalPair 0 == []
#guard !(state equivalent pairPattern equalPair 0).closed
#guard outputs pairPattern equalPair 1 == []
#guard outputs pairPattern equalPair 100 == [[("x", first)], [("x", first)]]
#guard (state equivalent pairPattern equalPair 100).closed
#guard outputs pairPattern unequalPair 100 == []
#guard (state equivalent pairPattern unequalPair 100).closed
#guard outputs (.collection .vec [.fvar "x"] (some "rest"))
    (.collection .vec [first, second] none) 100 ==
  [[("rest", .collection .vec [second] none), ("x", first)]]
#guard outputs (.subst (.fvar "body") (.fvar "replacement"))
    (.subst first second) 100 == [[("replacement", second), ("body", first)]]
#guard outputs (.multiLambda 1 ["a"] (.fvar "body"))
    (.multiLambda 2 ["a", "b"] first) 10 == []
#guard (state equivalent (.multiLambda 1 ["a"] (.fvar "body"))
    (.multiLambda 2 ["a", "b"] first) 10).closed
#guard outputs (.lambda (some "a") (.bvar 0)) (.lambda (some "b") (.bvar 0)) 10 == [[]]
#guard outputs (.lambda none (.bvar 0)) (.lambda none (.bvar 1)) 10 == []

theorem physical_duplicates_retained :
    (patternMatches equivalent pairPattern equalPair).flatten =
      [[("x", first)], [("x", first)]] := by
  rw [flatten_matches]
  cbv

theorem incompatible_binding_rejected :
    (patternMatches equivalent pairPattern unequalPair).flatten = [] := by
  rw [flatten_matches]
  cbv

theorem completed_negative_has_no_original_match (budget : Nat)
    (complete : (state equivalent pairPattern unequalPair budget).closed = true) :
    outputs pairPattern unequalPair budget = [] :=
  (closed_readout _ _ complete).trans incompatible_binding_rejected

theorem resume_preserves_matching_alternatives (firstWork moreWork : Nat) :
    state equivalent pairPattern equalPair (firstWork + moreWork) =
      resume moreWork (state equivalent pairPattern equalPair firstWork) :=
  exact_resume equivalent pairPattern equalPair firstWork moreWork

theorem all_pattern_questions_complete (pattern term : Pattern) :
    (state equivalent pattern term (patternMatches equivalent pattern term).workBound).closed = true :=
  effective_completion equivalent pattern term

end Mettapedia.OSLF.NativeTypes.Decision.Structural.Matching.Controls
