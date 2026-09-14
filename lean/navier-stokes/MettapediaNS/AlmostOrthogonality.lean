import EulerBlowup.Lit.CZ.CZCore.CotlarStein

/-!
# Almost-orthogonality bounds from the Alpöge–Buckmaster development

These are semantic aliases of the imported proofs, not reimplementations.
Both cross-product bounds and both row/column sum bounds remain explicit
in the theorem signatures. Applying the bounds to localized fluid operators
requires establishing those hypotheses for the actual operators.
-/

namespace Mettapedia.Analysis.OperatorAlmostOrthogonality

/-- A finite sum of Hilbert-space operators is bounded using both orders
of the adjoint cross-products and their summable interaction majorant. -/
alias norm_sum_le_of_adjoint_comp := NS.Lit.CZ.cotlarStein

/-- The same almost-orthogonality bound in a general C*-ring. -/
alias norm_sum_le_of_star_mul := NS.Lit.CZ.cstar_cotlarStein

end Mettapedia.Analysis.OperatorAlmostOrthogonality
