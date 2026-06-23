import Mettapedia.Computability.PNP.SameWidthZABObstructionArithmetic
import Mettapedia.Computability.PNP.SameWidthZABObstructionExactERM
import Mettapedia.Computability.PNP.SameWidthZABObstructionActualLocal

/-!
# P vs NP crux: the same-width exact ZAB branch is already impossible

The remaining exact `z+a+b` branch after the collision blockers is the
injective-width side `r ≥ n`.  This file closes the smallest such sub-branch:
if the extractor stays same-width (`r = n`), then the exact/shared local
decision-list budget is still only `n + 2k + 1` bits.  Once the visible width
`n + 2k` is at least `2`, that budget is already smaller than the full exact
visible truth-table size `2^(n + 2k)`.

So even before asking whether a same-width extractor is injective, the current
exact ZAB route cannot be surjective on any nontrivial visible surface.
-/
