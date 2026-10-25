import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Native proofs for Megalodon's binary-relation equality

The equality body is `forall Q, Q a b -> Q b a`, with `Q` binary.
The proof terms below use the actual Mathdata proof constructors. They are
closed proof combinators; checking their instances retains the chosen type,
conversion budget and native environment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.RelationEqualityProofs

open MathdataKernel

def relationType (type : Tp) : Tp := .arr type (.arr type .prop)

def relationApply (relation first second : Tm) : Tm :=
  .app (.app relation first) second

/-- The beta-expanded body of the actual preamble equality. -/
def equality (type : Tp) (first second : Tm) : Tm :=
  .all (relationType type)
    (.imp (relationApply (.db 0) (Tm.shift 0 1 first) (Tm.shift 0 1 second))
      (relationApply (.db 0) (Tm.shift 0 1 second) (Tm.shift 0 1 first)))

def reflexivityStatement (type : Tp) : Tm :=
  .all type (equality type (.db 0) (.db 0))

def reflexivity (type : Tp) : Pf :=
  .termLam type (.termLam (relationType type)
    (.proofLam (relationApply (.db 0) (.db 1) (.db 1)) (.hyp 0)))

def symmetryStatement (type : Tp) : Tm :=
  .all type (.all type
    (.imp (equality type (.db 1) (.db 0)) (equality type (.db 0) (.db 1))))

def symmetry (type : Tp) : Pf :=
  .termLam type (.termLam type
    (.proofLam (equality type (.db 1) (.db 0))
      (.termLam (relationType type)
        (.proofLam (relationApply (.db 0) (.db 1) (.db 2))
          (.proofApp (.termApp (.hyp 1)
            (.lam type (.lam type (relationApply (.db 2) (.db 0) (.db 1))))) (.hyp 0))))))

/-- Unary predicate transport is obtained by a binary relation that ignores
its second input. No extensionality or choice axiom is imported. -/
def substitutionStatement (type : Tp) : Tm :=
  .all type (.all type (.all (.arr type .prop)
    (.imp (equality type (.db 2) (.db 1))
      (.imp (.app (.db 0) (.db 2)) (.app (.db 0) (.db 1))))))

def substitution (type : Tp) : Pf :=
  .termLam type (.termLam type (.termLam (.arr type .prop)
    (.proofLam (equality type (.db 2) (.db 1))
      (.proofLam (.app (.db 0) (.db 2))
        (.proofApp (.termApp (.hyp 1)
          (.lam type (.lam type (.app (.db 2) (.db 1))))) (.hyp 0))))))

def transitivityStatement (type : Tp) : Tm :=
  .all type (.all type (.all type
    (.imp (equality type (.db 2) (.db 1))
      (.imp (equality type (.db 1) (.db 0)) (equality type (.db 2) (.db 0))))))

/-- Composition uses the proved predicate-substitution combinator, rather
than declaring transitivity as another known proposition. -/
def transitivity (type : Tp) : Pf :=
  .termLam type (.termLam type (.termLam type
    (.proofLam (equality type (.db 2) (.db 1))
      (.proofLam (equality type (.db 1) (.db 0))
        (.proofApp (.proofApp
          (.termApp (.termApp (.termApp (substitution type) (.db 1)) (.db 0))
            (.lam type (equality type (.db 3) (.db 0)))) (.hyp 0)) (.hyp 1))))))

def functionCongruenceStatement (domain result : Tp) : Tm :=
  .all (.arr domain result) (.all (.arr domain result) (.all domain
    (.imp (equality (.arr domain result) (.db 2) (.db 1))
      (equality result (.app (.db 2) (.db 0)) (.app (.db 1) (.db 0))))))

def functionCongruence (domain result : Tp) : Pf :=
  .termLam (.arr domain result) (.termLam (.arr domain result) (.termLam domain
    (.proofLam (equality (.arr domain result) (.db 2) (.db 1))
      (.proofApp (.proofApp
        (.termApp (.termApp (.termApp (substitution (.arr domain result)) (.db 2)) (.db 1))
          (.lam (.arr domain result)
            (equality result (.app (.db 3) (.db 1)) (.app (.db 0) (.db 1))))) (.hyp 0))
        (.termApp (reflexivity result) (.app (.db 2) (.db 0)))))))

def argumentCongruenceStatement (domain result : Tp) : Tm :=
  .all (.arr domain result) (.all domain (.all domain
    (.imp (equality domain (.db 1) (.db 0))
      (equality result (.app (.db 2) (.db 1)) (.app (.db 2) (.db 0))))))

def argumentCongruence (domain result : Tp) : Pf :=
  .termLam (.arr domain result) (.termLam domain (.termLam domain
    (.proofLam (equality domain (.db 1) (.db 0))
      (.proofApp (.proofApp
        (.termApp (.termApp (.termApp (substitution domain) (.db 1)) (.db 0))
          (.lam domain (equality result (.app (.db 3) (.db 2)) (.app (.db 3) (.db 0))))) (.hyp 0))
        (.termApp (reflexivity result) (.app (.db 2) (.db 1)))))))

def propositionEliminationStatement : Tm :=
  .all .prop (.all .prop
    (.imp (equality .prop (.db 1) (.db 0)) (.imp (.db 1) (.db 0))))

def propositionElimination : Pf :=
  .termLam .prop (.termLam .prop
    (.termApp (.termApp (.termApp (substitution .prop) (.db 1)) (.db 0)) (.lam .prop (.db 0))))

def propositionEliminationReverseStatement : Tm :=
  .all .prop (.all .prop
    (.imp (equality .prop (.db 1) (.db 0)) (.imp (.db 0) (.db 1))))

def propositionEliminationReverse : Pf :=
  .termLam .prop (.termLam .prop
    (.proofLam (equality .prop (.db 1) (.db 0))
      (.proofApp (.termApp (.termApp propositionElimination (.db 0)) (.db 1))
        (.proofApp (.termApp (.termApp (symmetry .prop) (.db 1)) (.db 0)) (.hyp 0)))))

theorem reflexivity_infers (environment : Environment) (typeDepth : Nat)
    (type : Tp) (formed : type.plainWellFormed typeDepth = true)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 typeDepth terms hypotheses (reflexivity type) =
      some (reflexivityStatement type) := by
  simp [reflexivity, reflexivityStatement, equality, relationType, relationApply,
    inferProof, inferTerm, Tp.plainWellFormed, formed, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift]

theorem symmetry_infers (environment : Environment) (typeDepth : Nat)
    (type : Tp) (formed : type.plainWellFormed typeDepth = true)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 typeDepth terms hypotheses (symmetry type) =
      some (symmetryStatement type) := by
  simp [symmetry, symmetryStatement, equality, relationType, relationApply,
    inferProof, inferTerm, Tp.plainWellFormed, formed, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift,
    Tm.instantiate, Tm.instantiateAt]

theorem substitution_infers (environment : Environment) (typeDepth : Nat)
    (type : Tp) (formed : type.plainWellFormed typeDepth = true)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 typeDepth terms hypotheses (substitution type) =
      some (substitutionStatement type) := by
  simp [substitution, substitutionStatement, equality, relationType, relationApply,
    inferProof, inferTerm, Tp.plainWellFormed, formed, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift,
    Tm.instantiate, Tm.instantiateAt]

theorem transitivity_infers (environment : Environment) (typeDepth : Nat)
    (type : Tp) (formed : type.plainWellFormed typeDepth = true)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 typeDepth terms hypotheses (transitivity type) =
      some (transitivityStatement type) := by
  simp [transitivity, transitivityStatement, substitutionStatement, equality, relationType, relationApply,
    inferProof, inferTerm, Tp.plainWellFormed, formed, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift,
    Tm.instantiate, Tm.instantiateAt, substitution_infers environment typeDepth type formed]

theorem functionCongruence_infers (environment : Environment) (typeDepth : Nat)
    (domain result : Tp) (domainFormed : domain.plainWellFormed typeDepth = true)
    (resultFormed : result.plainWellFormed typeDepth = true)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 typeDepth terms hypotheses (functionCongruence domain result) =
      some (functionCongruenceStatement domain result) := by
  simp [functionCongruence, functionCongruenceStatement, substitutionStatement, reflexivityStatement, equality, relationType, relationApply,
    inferProof, inferTerm, Tp.plainWellFormed, domainFormed, resultFormed, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt,
    substitution_infers environment typeDepth (.arr domain result) (by simp [Tp.plainWellFormed, domainFormed, resultFormed]),
    reflexivity_infers environment typeDepth result resultFormed]

theorem argumentCongruence_infers (environment : Environment) (typeDepth : Nat)
    (domain result : Tp) (domainFormed : domain.plainWellFormed typeDepth = true)
    (resultFormed : result.plainWellFormed typeDepth = true)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 typeDepth terms hypotheses (argumentCongruence domain result) =
      some (argumentCongruenceStatement domain result) := by
  simp [argumentCongruence, argumentCongruenceStatement, substitutionStatement, reflexivityStatement, equality, relationType, relationApply,
    inferProof, inferTerm, Tp.plainWellFormed, domainFormed, resultFormed, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt,
    substitution_infers environment typeDepth domain domainFormed,
    reflexivity_infers environment typeDepth result resultFormed]

theorem propositionElimination_infers (environment : Environment) (typeDepth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 typeDepth terms hypotheses propositionElimination =
      some propositionEliminationStatement := by
  simp [propositionElimination, propositionEliminationStatement, substitutionStatement,
    equality, relationType, relationApply, inferProof, inferTerm, Tp.plainWellFormed, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt,
    substitution_infers environment typeDepth .prop rfl]

theorem propositionEliminationReverse_infers (environment : Environment) (typeDepth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof environment 32 typeDepth terms hypotheses propositionEliminationReverse =
      some propositionEliminationReverseStatement := by
  simp [propositionEliminationReverse, propositionEliminationReverseStatement,
    propositionEliminationStatement, symmetryStatement, equality, relationType, relationApply,
    inferProof, inferTerm, Tp.plainWellFormed, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    propositionElimination_infers environment typeDepth,
    symmetry_infers environment typeDepth .prop rfl]

namespace Controls

def empty : Environment := {}

theorem formed_instances :
    inferProof empty 32 0 [] [] (reflexivity (.base 0)) = some (reflexivityStatement (.base 0)) ∧
    inferProof empty 32 0 [] [] (symmetry .prop) = some (symmetryStatement .prop) ∧
    inferProof empty 32 0 [] [] (substitution (.arr .prop .prop)) =
      some (substitutionStatement (.arr .prop .prop)) := by
  exact ⟨reflexivity_infers _ _ _ rfl _ _, symmetry_infers _ _ _ rfl _ _,
    substitution_infers _ _ _ rfl _ _⟩

theorem unavailable_type_variable_refused :
    inferProof empty 32 0 [] [] (reflexivity (.var 0)) = none := by decide +kernel

theorem altered_goal_refused :
    checkProof empty 32 0 [] [] (reflexivity (.base 0)) (.all .prop (.db 0)) = false := by
  simp [checkProof, checkNormalizedProof, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    reflexivity_infers empty 0 (.base 0) rfl [] [], reflexivityStatement, equality, relationType,
    relationApply, Tm.shift]

theorem exhausted_budget_refused :
    checkProof empty 0 0 [] [] (symmetry (.base 0)) (symmetryStatement (.base 0)) = false := by
  simp [checkProof, checkNormalizedProof, symmetry, symmetryStatement, equality, relationType,
    relationApply, inferProof, inferTerm, Tp.plainWellFormed, normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt]

end Controls

end Mettapedia.Languages.Megalodon.RelationEqualityProofs
