import Mettapedia.Logic.LP.RuntimeUnificationSoundness

/-!
# Finite compound query grounding regression

This fixture runs a real compound query through the canonical demand-driven
runtime.  It inhabits the finite-readback refinement endpoint, rather than
testing only a hand-constructed unifier heap.
-/

namespace Mettapedia.Logic.LP.RuntimeCompoundQueryRegression

open RuntimeTerm RuntimeQuery RuntimeReadback RuntimeMaterialize
open RuntimeUnificationSoundness

inductive CConst where
  | a | b
deriving BEq, DecidableEq, Repr

inductive CVar where
  | x
deriving DecidableEq, Repr

inductive CRel where
  | p
deriving DecidableEq, Repr

inductive CFun where
  | pair
deriving DecidableEq, Repr

def cSig : LPSignature where
  constants := CConst
  vars := CVar
  relationSymbols := CRel
  relationArity := fun _ => 1
  functionSymbols := CFun
  functionArity := fun _ => 2

instance : DecidableEq cSig.vars := inferInstanceAs (DecidableEq CVar)
instance : DecidableEq cSig.constants := inferInstanceAs (DecidableEq CConst)
instance : DecidableEq cSig.functionSymbols := inferInstanceAs (DecidableEq CFun)
instance : DecidableEq cSig.relationSymbols := inferInstanceAs (DecidableEq CRel)

def pairTerm (left right : Term cSig) : Term cSig :=
  .app .pair fun index =>
    match index with
    | ⟨0, _⟩ => left
    | ⟨1, _⟩ => right

def unary (term : Term cSig) : Atom cSig where
  symbol := .p
  args := fun _ => term

def program : Program cSig := [{
  head := unary (pairTerm (.const .a) (.const .b))
  body := []
}]

def query : List (Atom cSig) := [unary (.var .x)]

def builtins : Builtins cSig where
  isCut := fun _ => false
  cut_arity_zero := by simp

/-- Execute and inspect the single public answer. -/
def run : Bool :=
  match openQuery (Memory.empty cSig.scoped) 0 1 query with
  | .error _ => false
  | .ok state =>
      match pull builtins program 32 state with
      | .answer answer _ =>
          match answer.queryVarMap with
          | [(_, address)] =>
              match Heap.readTerm answer.memory.heap address with
              | .ok (.app .pair args) =>
                  match args ⟨0, by simp [cSig]⟩,
                      args ⟨1, by simp [cSig]⟩ with
                  | .const .a, .const .b => true
                  | _, _ => false
              | _ => false
          | _ => false
      | _ => false

-- The live query returns the finite compound in the source clause.
#guard run

/-- Any finitely readable answer from this exact compound program and query
has a standardized-apart SLD derivation with matching public bindings.  The
executable guard above confirms that the answer-producing premise is live. -/
theorem live_finite_compound_answer_is_sld_grounded
    (state : State cSig) (answer : Answer cSig) (resumed : State cSig)
    (hOpen : openQuery (Memory.empty cSig.scoped) 0 1 query = .ok state)
    (hPull : pull builtins program 32 state = .answer answer resumed)
    (hfinite : FiniteReadback answer.memory.heap) :
    ∃ θ : Subst cSig.scoped,
      SLDScopedTree program 1 (queryAtScope 0 query) θ ∧
      ∀ pair ∈ answer.queryVarMap, ∀ term,
        Heap.readTerm answer.memory.heap pair.2 = .ok term →
        θ pair.1 = term :=
  refinementEndpoint_finiteReadback cSig builtins program query state 32
    answer resumed (fun _ => rfl) hOpen hPull hfinite

end Mettapedia.Logic.LP.RuntimeCompoundQueryRegression
