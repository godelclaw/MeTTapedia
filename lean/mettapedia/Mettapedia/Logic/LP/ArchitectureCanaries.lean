import Mettapedia.Logic.LP.SLDCompute
import Mettapedia.Logic.LP.RuntimeReadback

/-!
# Architectural canaries: the three executable boundary cases

Each canary pairs an executable `#guard` on the *certified* LP side with an
executable `#guard` on the *runtime* side, keeping the semantic boundaries of
the current architecture permanently red against overclaim:

1. **Freshening** — `p(a) :- q(X).  q(b).  ?- p(X).`  The unscoped executable
   search fails (clause and query share a variable identity), while the
   runtime succeeds by standardizing the activation apart.  The Prop-level
   twin — derivability in `SLDScopedTree` — lives next to the judgment in
   `SLD.lean`; here both behaviors are *executed*.
2. **Cut is not an atom** — `?- !.` against the empty program.  The runtime
   discharges the cut through its builtin classifier; the unscoped search has
   no derivation.  Any refinement theorem must therefore treat cut as
   control, never as an SLD-resolvable atom.
3. **Rational trees** — unifying `pp(X, X)` with the fact `pp(Y, f(Y))`.
   The certified finite unifier rejects by occurs check; the runtime binds a
   cyclic structure and succeeds, and the finite readback of the answer
   honestly reports `notFinite`.  Finite-mode and rational-mode correctness
   are therefore *separate* targets.
-/

namespace Mettapedia.Logic.LP.ArchitectureCanaries

open RuntimeTerm RuntimeQuery RuntimeReadback

inductive CanC | a | b deriving BEq, DecidableEq, Repr
inductive CanR | p | q | pp | cutr deriving DecidableEq, Repr
inductive CanF | f deriving DecidableEq, Repr

def canSig : LPSignature where
  constants := CanC
  vars := Unit
  relationSymbols := CanR
  relationArity
    | .p => 1
    | .q => 1
    | .pp => 2
    | .cutr => 0
  functionSymbols := CanF
  functionArity := fun _ => 1

instance : DecidableEq canSig.vars := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq canSig.constants := inferInstanceAs (DecidableEq CanC)
instance : DecidableEq canSig.functionSymbols := inferInstanceAs (DecidableEq CanF)
instance : DecidableEq canSig.relationSymbols := inferInstanceAs (DecidableEq CanR)
instance : DecidableEq canSig.scoped.vars :=
  inferInstanceAs (DecidableEq (ScopedVar Unit))
instance : DecidableEq canSig.scoped.constants := inferInstanceAs (DecidableEq CanC)
instance : DecidableEq canSig.scoped.functionSymbols :=
  inferInstanceAs (DecidableEq CanF)
instance : DecidableEq canSig.scoped.relationSymbols :=
  inferInstanceAs (DecidableEq CanR)

def unary (symbol : CanR) (t : Term canSig) : Atom canSig where
  symbol := symbol
  args := fun _ => t

def binary (left right : Term canSig) : Atom canSig where
  symbol := .pp
  args := fun index => if index.val = 0 then left else right

def cutAtom : Atom canSig where
  symbol := .cutr
  args := fun index => nomatch index

def fTerm (t : Term canSig) : Term canSig := .app .f (fun _ => t)

def builtins : Builtins canSig where
  isCut
    | .cutr => true
    | _ => false
  cut_arity_zero := by
    intro symbol h
    cases symbol <;> simp_all [canSig]

/-- Pull once with a generous budget and report the shape of the outcome. -/
def firstPull (program : Program canSig) (goals : List (Atom canSig)) :
    Option (Answer canSig) :=
  match openQuery (Memory.empty canSig.scoped) 0 1 goals with
  | .error _ => none
  | .ok state =>
      match pull builtins program 256 state with
      | .answer answer _ => some answer
      | _ => none

/-! ## Canary 1: freshening -/

def freshProg : Program canSig :=
  [ { head := unary .p (.const .a), body := [unary .q (.var ())] },
    { head := unary .q (.const .b), body := [] } ]

def freshQuery : List (Atom canSig) := [unary .p (.var ())]

-- Certified side: the unscoped executable search fails on exactly this
-- program, because query `X` and clause-body `X` collide.
#guard (sldSearch freshProg 16 freshQuery).isSome = false

-- Runtime side: the standardized-apart runtime succeeds, and the answer
-- reads back to the constant `a`.
#guard
  (match firstPull freshProg freshQuery with
    | some answer =>
        match readAnswer answer with
        | .ok [(_, .const CanC.a)] => true
        | _ => false
    | none => false) = true

/-! ## Canary 2: cut is not an atom -/

-- Certified side: the empty program derives nothing.
#guard (sldSearch ([] : Program canSig) 16 [cutAtom]).isSome = false

-- Runtime side: the builtin classifier discharges the cut and the query
-- answers with no bindings at all.
#guard
  (match firstPull [] [cutAtom] with
    | some answer => answer.queryVarMap.isEmpty
    | none => false) = true

/-! ## Canary 3: rational trees -/

def rationalProg : Program canSig :=
  [ { head := binary (.var ()) (fTerm (.var ())), body := [] } ]

def rationalQuery : List (Atom canSig) := [binary (.var ()) (.var ())]

-- Certified side: the finite unifier rejects `X = f(X)` by occurs check.
#guard
  (unifyAtoms (binary (.var ()) (.var ()))
    (binary (.var ()) (fTerm (.var ()))) 64).isSome = false

-- Runtime side: the graph unifier binds a cyclic structure and succeeds;
-- the finite readback of the answer honestly reports `notFinite`.
#guard
  (match firstPull rationalProg rationalQuery with
    | some answer =>
        match readAnswer answer with
        | .error .notFinite => true
        | _ => false
    | none => false) = true

end Mettapedia.Logic.LP.ArchitectureCanaries
