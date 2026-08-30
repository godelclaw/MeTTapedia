import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualTwoFactor

/-!
# Well-founded descent for the residual two-factor obstruction

For a supported perfect matching `sigma`, count the connected components of
its residual two-factor which are not bipartite.  This is an exact natural
number potential: defect zero makes the residual bipartite and hence supplies
a disjoint second matching and a Tait colouring.

The minimum-defect principle isolates the consumer-facing high-width task.  A
uniform wall argument need only give a supported matching of strictly smaller
defect whenever the current defect is positive.  In a Tait counterexample a
minimum-defect supported matching has positive defect and admits no such
descent.  No wall-exclusion or replacement claim is made here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualDefectDescent

open SimpleGraph
open MatchingParity
open GoertzelV24ResidualTwoFactor

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The number of non-bipartite connected components in the residual graph
of a supported perfect matching.  The definition is meaningful for every
pairing; support is required by the theorems which consume it. -/
def residualDefect (G : SimpleGraph V) (sigma : Pairing V) : Nat :=
  {component : (residualGraph G sigma).ConnectedComponent |
    ¬ component.toSimpleGraph.Colorable 2}.ncard

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Residual defect is zero exactly when the whole residual graph is
bipartite. -/
theorem residualDefect_eq_zero_iff_isBipartite (sigma : Pairing V) :
    residualDefect G sigma = 0 ↔ (residualGraph G sigma).IsBipartite := by
  classical
  rw [residualDefect, Set.ncard_eq_zero]
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_not]
  exact SimpleGraph.colorable_iff_forall_connectedComponents.symm

/-- A supported matching has a strict residual-defect descent when another
supported matching has smaller defect. -/
def HasStrictResidualDefectDescent (G : SimpleGraph V) (sigma : Pairing V) : Prop :=
  ∃ tau : Pairing V,
    tau.SupportedBy G ∧ residualDefect G tau < residualDefect G sigma

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The nonempty family of supported pairings contains a member of minimum
residual defect.  Natural-number well-ordering is enough; no enumeration of
pairings is used. -/
theorem exists_supportedPairing_minimal_residualDefect
    (hexists : ∃ sigma : Pairing V, sigma.SupportedBy G) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      ∀ tau : Pairing V, tau.SupportedBy G →
        residualDefect G sigma ≤ residualDefect G tau := by
  let supported : Set (Pairing V) := {sigma | sigma.SupportedBy G}
  have hsupported : supported.Nonempty := by
    obtain ⟨sigma, hsigma⟩ := hexists
    exact ⟨sigma, hsigma⟩
  let sigma := Function.argminOn (residualDefect G) supported hsupported
  refine ⟨sigma, ?_, ?_⟩
  · exact Function.argminOn_mem (residualDefect G) supported hsupported
  · intro tau htau
    exact Function.argminOn_le (residualDefect G) supported
      (show tau ∈ supported by exact htau)

/-- Every supported matching in a cubic Tait counterexample has positive
residual defect. -/
theorem residualDefect_pos_of_not_taitColorable
    (hG : HasCubicIncidentEdgeTriples G) (hnot : ¬ TaitColorable G)
    (sigma : Pairing V) (hsigma : sigma.SupportedBy G) :
    0 < residualDefect G sigma := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hbip : (residualGraph G sigma).IsBipartite :=
    (residualDefect_eq_zero_iff_isBipartite sigma).1 hzero
  exact hnot
    (taitColorable_of_residualGraph_isBipartite hG sigma hsigma hbip)

/-- **Residual-defect descent principle.**  If every positive-defect
supported matching admits a strict supported descent, a finite cubic graph is
Tait colourable. -/
theorem taitColorable_of_residualDefect_descent
    (hG : HasCubicIncidentEdgeTriples G)
    (hexists : ∃ sigma : Pairing V, sigma.SupportedBy G)
    (hdescent : ∀ sigma : Pairing V, sigma.SupportedBy G →
      0 < residualDefect G sigma →
      HasStrictResidualDefectDescent G sigma) :
    TaitColorable G := by
  obtain ⟨sigma, hsigma, hminimal⟩ :=
    exists_supportedPairing_minimal_residualDefect hexists
  by_cases hzero : residualDefect G sigma = 0
  · exact taitColorable_of_residualGraph_isBipartite hG sigma hsigma
      ((residualDefect_eq_zero_iff_isBipartite sigma).1 hzero)
  · obtain ⟨tau, htau, hlt⟩ :=
      hdescent sigma hsigma (Nat.pos_of_ne_zero hzero)
    exact False.elim ((Nat.not_lt_of_ge (hminimal tau htau)) hlt)

/-- A Tait counterexample with an inhabited supported-matching family has a
positive-defect minimizer.  It is the exact locally irreducible object a wall
argument must contradict or replace. -/
theorem exists_positive_minimal_residualDefect_of_not_taitColorable
    (hG : HasCubicIncidentEdgeTriples G) (hnot : ¬ TaitColorable G)
    (hexists : ∃ sigma : Pairing V, sigma.SupportedBy G) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      0 < residualDefect G sigma ∧
      ∀ tau : Pairing V, tau.SupportedBy G →
        residualDefect G sigma ≤ residualDefect G tau := by
  obtain ⟨sigma, hsigma, hminimal⟩ :=
    exists_supportedPairing_minimal_residualDefect hexists
  exact ⟨sigma, hsigma,
    residualDefect_pos_of_not_taitColorable hG hnot sigma hsigma,
    hminimal⟩

/-- Petersen's theorem supplies the inhabited family in the bridge-free cubic
target class, yielding a positive-defect minimizer without an existence
hypothesis. -/
theorem exists_positive_minimal_residualDefect_of_cubic_edgeBridgeFree
    (hCubic : G.IsRegularOfDegree 3)
    (hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1)
    (hnot : ¬ TaitColorable G) :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      0 < residualDefect G sigma ∧
      ∀ tau : Pairing V, tau.SupportedBy G →
        residualDefect G sigma ≤ residualDefect G tau := by
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three fun vertex => by
      rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  exact exists_positive_minimal_residualDefect_of_not_taitColorable
    htriples hnot
      (GoertzelV24PetersenStartingMatching.petersen_supportedPairing hCubic hfree)

/-- Bridge-free cubic specialization of the descent principle. -/
theorem taitColorable_of_cubic_edgeBridgeFree_residualDefect_descent
    (hCubic : G.IsRegularOfDegree 3)
    (hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1)
    (hdescent : ∀ sigma : Pairing V, sigma.SupportedBy G →
      0 < residualDefect G sigma →
      HasStrictResidualDefectDescent G sigma) :
    TaitColorable G := by
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three fun vertex => by
      rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  exact taitColorable_of_residualDefect_descent htriples
    (GoertzelV24PetersenStartingMatching.petersen_supportedPairing hCubic hfree)
    hdescent

end

end GoertzelV24ResidualDefectDescent

end Mettapedia.GraphTheory.FourColor
