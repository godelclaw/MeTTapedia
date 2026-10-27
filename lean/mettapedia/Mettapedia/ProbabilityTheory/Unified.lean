import ProbabilityTheory.Cox
import Mettapedia.ProbabilityTheory.Cox.Regraduation
import Mettapedia.ProbabilityTheory.ImpreciseProbability
import KnuthSkilling
-- Note: BeliefFunctions and QuantumProbability imported separately

/-!
# Labels for uncertainty frameworks

This module records a finite taxonomy of declared axiom flags. Equality of
labels proves agreement of those flags, not equivalence of theories or a
probability-representation theorem. Concrete Cox regraduation and ordered
combination are imported separately, with their actual hypotheses.
-/

namespace Mettapedia.ProbabilityTheory.Unified

/-!
## §1: The Axiom Flags

Each theory is characterized by which axioms it satisfies.
-/

/-- The core axiom choices that determine which theory we're in. -/
structure UncertaintyAxioms where
  /-- Is the theory additive? P(A∪B) = P(A) + P(B) for disjoint A, B -/
  additive : Bool
  /-- Is the theory commutative? P(A∧B) = P(B∧A) -/
  commutative : Bool
  /-- Is there a unique probability (precise) or an interval (imprecise)? -/
  precise : Bool
  /-- Is there an identity element? -/
  hasIdentity : Bool
  /-- Is there an inverse (negation) operation? -/
  hasInverse : Bool

/-- Kolmogorov axioms: additive, commutative, precise. -/
def kolmogorovAxioms : UncertaintyAxioms :=
  { additive := true
    commutative := true
    precise := true
    hasIdentity := true
    hasInverse := true }

/-- Cox axioms: derive additivity and commutativity from functional equations. -/
def coxAxioms : UncertaintyAxioms :=
  { additive := true  -- DERIVED
    commutative := true  -- DERIVED
    precise := true
    hasIdentity := true
    hasInverse := true }

/-- Knuth-Skilling: derive additivity from lattice structure.
    Note: K&S doesn't assume inverses, yet derives additivity! -/
def knuthSkillingAxioms : UncertaintyAxioms :=
  { additive := true
    commutative := true
    precise := true
    hasIdentity := true
    hasInverse := false }

/-- Imprecise probability (Walley): sub/super-additive, commutative.
    Uses intervals [P̲(A), P̅(A)] instead of point values. -/
def walleyAxioms : UncertaintyAxioms :=
  { additive := false
    commutative := true
    precise := false
    hasIdentity := true
    hasInverse := true }

/-- Dempster-Shafer: sub/super-additive via belief/plausibility.
    Belief is superadditive, plausibility subadditive.
    No direct inverse; uses Pl(A) = 1 - Bel(¬A). -/
def dempsterShaferAxioms : UncertaintyAxioms :=
  { additive := false
    commutative := true
    precise := false
    hasIdentity := true
    hasInverse := false }

/-- Quantum probability: additive but non-commutative. -/
def quantumAxioms : UncertaintyAxioms :=
  { additive := true
    commutative := false  -- Measurements don't commute!
    precise := true
    hasIdentity := true
    hasInverse := true }

/-!
## §2: The Hypercube Structure

Map axiom configurations to vertices of a hypercube.
-/

/-- A vertex of the hypercube is a bit-vector of axiom choices. -/
structure HypercubeVertex where
  additive : Bool
  commutative : Bool
  precise : Bool
  deriving DecidableEq, Repr

/-- Project axioms onto the 3D hypercube. -/
def toVertex (ax : UncertaintyAxioms) : HypercubeVertex :=
  { additive := ax.additive
    commutative := ax.commutative
    precise := ax.precise }

/-- The 8 vertices of the hypercube. -/
def hypercubeVertices : List HypercubeVertex :=
  [ ⟨true, true, true⟩,    -- Kolmogorov/Cox/K&S
    ⟨true, true, false⟩,   -- ??? (additive imprecise = contradiction?)
    ⟨true, false, true⟩,   -- Quantum
    ⟨true, false, false⟩,  -- Quantum imprecise
    ⟨false, true, true⟩,   -- ??? (subadditive precise)
    ⟨false, true, false⟩,  -- Walley/D-S
    ⟨false, false, true⟩,  -- Non-comm subadditive
    ⟨false, false, false⟩  -- Most general
  ]

/-- Name the vertices by their theory. -/
def vertexName : HypercubeVertex → String
  | ⟨true, true, true⟩ => "Kolmogorov/Cox/K&S"
  | ⟨true, true, false⟩ => "Additive-Imprecise (degenerate)"
  | ⟨true, false, true⟩ => "Quantum"
  | ⟨true, false, false⟩ => "Quantum-Imprecise"
  | ⟨false, true, true⟩ => "Subadditive-Precise (degenerate)"
  | ⟨false, true, false⟩ => "Walley/Dempster-Shafer"
  | ⟨false, false, true⟩ => "Non-commutative-Subadditive"
  | ⟨false, false, false⟩ => "Maximally General"

/-!
## §3: Edges = Refinement Relations

An edge connects two vertices when one theory refines to another.
-/

/-- An edge connects two vertices that differ in exactly one coordinate. -/
def isEdge (v₁ v₂ : HypercubeVertex) : Bool :=
  (v₁.additive != v₂.additive && v₁.commutative == v₂.commutative && v₁.precise == v₂.precise) ||
  (v₁.additive == v₂.additive && v₁.commutative != v₂.commutative && v₁.precise == v₂.precise) ||
  (v₁.additive == v₂.additive && v₁.commutative == v₂.commutative && v₁.precise != v₂.precise)

/-- The refinement direction: more axioms = more refined. -/
def refines (v₁ v₂ : HypercubeVertex) : Bool :=
  isEdge v₁ v₂ &&
  ((v₁.additive && !v₂.additive) ||
   (v₁.commutative && !v₂.commutative) ||
   (v₁.precise && !v₂.precise))

/-!
## Label computations

These computations unfold the declared labels; they establish no semantic existence result.
-/

/-- The authored Cox label has the same flags as the Kolmogorov label. -/
theorem cox_label_eq_kolmogorov_label :
    toVertex coxAxioms = toVertex kolmogorovAxioms := by
  rfl

/-- The authored K&S label has the same flags as the Kolmogorov label. -/
theorem ks_label_eq_kolmogorov_label :
    toVertex knuthSkillingAxioms = toVertex kolmogorovAxioms := by
  rfl

/-- D-S is strictly weaker: sits at the imprecise vertex. -/
theorem ds_at_imprecise_vertex :
    toVertex dempsterShaferAxioms = ⟨false, true, false⟩ := by
  rfl

/-- Quantum sits at the non-commutative vertex. -/
theorem quantum_at_noncomm_vertex :
    toVertex quantumAxioms = ⟨true, false, true⟩ := by
  rfl

/-!
## Reading the flags
-/

/-- Fixing two flags determines the corresponding part of a vertex. -/
theorem vertex_eq_of_axis_values :
    ∀ (v : HypercubeVertex),
      v.additive = true → v.commutative = true →
      v = ⟨true, true, v.precise⟩ := by
  intro v hadd hcomm
  cases v
  simp_all

/-- Toy markers attached to labels, not carriers or models of the theories. -/
def toyVertexMarker : HypercubeVertex → Type
  | ⟨true, true, true⟩ => Unit
  | ⟨true, true, false⟩ => Empty
  | ⟨true, false, true⟩ => Unit
  | ⟨true, false, false⟩ => Unit
  | ⟨false, true, true⟩ => Empty
  | ⟨false, true, false⟩ => Unit
  | ⟨false, false, true⟩ => Unit
  | ⟨false, false, false⟩ => Unit

end Mettapedia.ProbabilityTheory.Unified
