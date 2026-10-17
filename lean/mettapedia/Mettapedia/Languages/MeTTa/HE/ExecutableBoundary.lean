import Mettapedia.Languages.MeTTa.HE.Eval
import Mettapedia.Languages.MeTTa.HE.EvalSpec

/-!
# Historical HE certificates and executable stability

The predicates below keep historical `EvalSpec` evidence separate from actual
stable executable membership. A certificate explicitly contains both facts;
stability alone does not construct the historical judgment. The independent
source is `Spec.Eval`, and selected-frame retained execution is treated by its
own constructed correspondence laws.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- `EvalAtomStablyReaches` is the minimal top-level executable stability
    witness. It says that from some cutoff fuel onward, the evaluator keeps
    returning the same result pair. -/
def EvalAtomStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ evalAtom space dispatch atom type_ b fuel live

/-- `EvalAtomCertified` is the historical certificate conjunction for the
    top-level evaluator. It packages both:
    - an explicitly provided historical `EvalAtom` derivation
    - stable executable support from some fuel onward -/
def EvalAtomCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  EvalAtom space dispatch (live := live) atom type_ b r ∧
  EvalAtomStablyReaches space dispatch atom type_ b r live

/-! ## Internal support predicates for the lower 5 evaluator entry points

These are proof-support definitions used by `Correctness.lean`. They are not
part of the public certification boundary. -/

namespace Internal

def InterpretExpressionStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ interpretExpression space dispatch atom type_ b fuel live

/-- Implementation-refined spec boundary for `interpretExpression`. -/
def InterpretExpressionCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  InterpretExpression space dispatch (live := live) atom type_ b r ∧
  InterpretExpressionStablyReaches space dispatch atom type_ b r live

/-- Stable executable witness for `interpretFunction`.
    This boundary follows the evaluator entry point, so it intentionally does
    not quantify over `retType` as an input. -/
def InterpretFunctionStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ interpretFunction space dispatch atom opType b fuel live

/-- Implementation-refined spec boundary for `interpretFunction`.
    The declarative side is uniform across all return-type instantiations. -/
def InterpretFunctionCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  (∀ retType, InterpretFunction space dispatch (live := live) atom opType retType b r) ∧
  InterpretFunctionStablyReaches space dispatch atom opType b r live

/-- Stable executable witness for `interpretArgs`. -/
def InterpretArgsStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ interpretArgs space dispatch args types b fuel live

/-- Implementation-refined spec boundary for `interpretArgs`. -/
def InterpretArgsCertified
    (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  InterpretArgs space dispatch (live := live) args types b r ∧
  InterpretArgsStablyReaches space dispatch args types b r live

/-- Stable executable witness for `interpretTuple`. -/
def InterpretTupleStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ interpretTuple space dispatch atom b fuel live

/-- Implementation-refined spec boundary for `interpretTuple`. -/
def InterpretTupleCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  InterpretTuple space dispatch (live := live) atom b r ∧
  InterpretTupleStablyReaches space dispatch atom b r live

/-- Stable executable witness for `mettaCall`. -/
def MettaCallStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ mettaCall space dispatch atom type_ b fuel live

/-- Implementation-refined spec boundary for `mettaCall`. -/
def MettaCallCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) (live : List Atom := []) : Prop :=
  MettaCall space dispatch (live := live) atom type_ b r ∧
  MettaCallStablyReaches space dispatch atom type_ b r live

end Internal

end Mettapedia.Languages.MeTTa.HE
