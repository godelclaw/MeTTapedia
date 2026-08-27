import Mettapedia.QuantumTheory.YangMills.Dimension16WilsonExtractionCertificate

/-!
# Dimension-sixteen Wilson extraction certificate regressions

Pins the source-policy mismatch, the ten-row transfer table, the failed
displayed bound, and the obstructed as-written verdict.  These checks concern
the v14 action-sector coordinate certificate; they do not turn the explicit
dimension-four observable jets into dimension-sixteen data.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace Dimension16WilsonExtractionCertificateRegression

theorem relation_policy_mismatch_regression :
    v14F4RelationPolicy ≠ v14O9RelationPolicy :=
  v14F4RelationPolicy_ne_v14O9RelationPolicy

theorem divergence_square_membership_mismatch_regression :
    v14F4RelationPolicy.retains .divergenceSquare ≠
      v14O9RelationPolicy.retains .divergenceSquare ∧
    V14ActionOperatorTemplate.divergenceSquare.canonicalDimension ≤ 16 :=
  v14_relationPolicies_disagree_inside_dimensionSixteen

theorem transfer_table_regression :
    v14Dimension16TransferTable =
      [ (.wilsonGaugeObject, .constructed)
      , (.exactBlockBoundaryConvention, .notSupplied)
      , (.actionSectorRelationQuotient, .sourceConflict)
      , (.latticeWilsonRepresentatives, .notSupplied)
      , (.finiteQuotientBasis, .notSupplied)
      , (.dimensionSixteenDualJets, .notSupplied)
      , (.basisJetBiorthogonality, .notSupplied)
      , (.conditioningBound, .displayedBoundRefuted)
      , (.extractionConstant, .notDerived)
      , (.wilsonRecursionConstant, .notDerived)
      ] := by
  rfl

theorem source_certificate_incomplete_regression :
    ¬ V14Dimension16SourceCertificateComplete :=
  not_v14Dimension16SourceCertificateComplete

theorem literal_bound_refuted_regression :
    ¬ V14LiteralDimension16ExtractionBound :=
  not_v14LiteralDimension16ExtractionBound

theorem as_written_verdict_regression :
    (¬ V14Dimension16SourceCertificateComplete) ∧
      v14F4RelationPolicy ≠ v14O9RelationPolicy ∧
      (¬ V14LiteralDimension16ExtractionBound) ∧
      v14Dimension16CertificateStatus .extractionConstant = .notDerived ∧
      v14Dimension16CertificateStatus .wilsonRecursionConstant = .notDerived :=
  v14Dimension16WilsonExtraction_asWritten_obstructed

/--
info: 'Mettapedia.QuantumTheory.YangMills.v14_relationPolicies_disagree_inside_dimensionSixteen' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms v14_relationPolicies_disagree_inside_dimensionSixteen

/--
info: 'Mettapedia.QuantumTheory.YangMills.not_v14Dimension16SourceCertificateComplete' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms not_v14Dimension16SourceCertificateComplete

/--
info: 'Mettapedia.QuantumTheory.YangMills.not_v14LiteralDimension16ExtractionBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms not_v14LiteralDimension16ExtractionBound

/--
info: 'Mettapedia.QuantumTheory.YangMills.v14Dimension16WilsonExtraction_asWritten_obstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms v14Dimension16WilsonExtraction_asWritten_obstructed

end Dimension16WilsonExtractionCertificateRegression
end YangMills
end QuantumTheory
end Mettapedia
