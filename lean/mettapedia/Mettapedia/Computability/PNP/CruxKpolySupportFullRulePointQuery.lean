import Mettapedia.Computability.PNP.CruxKpolySupportFullRulePropertyDecoder

/-!
# PNP `Kpoly` support/full-rule anchors: point and query decoders

Point-query and query-family decoder characterizations by reachable support.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a single exact-visible point query is decodable
from observed block-output traces exactly when that point lies in the reachable
support. -/
theorem kpolyCoverage_anchor_supportFullRule_evalDecoder_iff_mem_range
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀) ↔ ∃ phi, visibleOf phi = u₀ :=
  supportFullRule_exists_evalDecoder_iff_mem_range
    visibleOf u₀

/-- Route-coverage anchor: decoding every exact-visible point query from
observed block-output traces is equivalent to full reachable-support
surjectivity. -/
theorem kpolyCoverage_anchor_supportFullRule_all_evalDecoders_iff_surjective
    {Z : Type v} {Block : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ↔ Function.Surjective visibleOf :=
  supportFullRule_all_evalDecoders_iff_visibleOf_surjective
    visibleOf

/-- Route-coverage anchor: a whole family of exact-visible point queries is
decodable from observed block-output traces exactly when every queried point is
in reachable support. -/
theorem kpolyCoverage_anchor_supportFullRule_queryDecoder_iff_forall_mem_range
    {Z : Type v} {Block : Type v} {Query : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (queryOf : Query → ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q)) ↔ ∀ q, ∃ phi, visibleOf phi = queryOf q :=
  supportFullRule_exists_queryDecoder_iff_forall_mem_range
    visibleOf queryOf

/-- Route-coverage anchor: a query family containing one unreachable
exact-visible point cannot be decoded from observed block-output traces. -/
theorem kpolyCoverage_anchor_supportFullRule_no_queryDecoder_of_missed_query
    {Z : Type v} {Block : Type v} {Query : Type v} {k : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (queryOf : Query → ExactVisiblePostSwitchSurface Z k)
    (q₀ : Query) (hmiss : ∀ phi, visibleOf phi ≠ queryOf q₀) :
    ¬ ∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q) :=
  supportFullRule_not_exists_queryDecoder_of_missed_query
    visibleOf queryOf q₀ hmiss


end Mettapedia.Computability.PNP
