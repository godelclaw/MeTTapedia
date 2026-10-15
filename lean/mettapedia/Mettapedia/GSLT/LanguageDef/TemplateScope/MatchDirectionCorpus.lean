import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionCover

/-!
# Template scope: the scope corpus under both sides

Kernel-checked computations on the 80 rows of the scope corpus (each a query
with its equations).

* `rows_direction_blind` — **the corpus does not see the matching direction**:
  under each of the six configurations, on every row, both sides gives the bag
  pattern-only gives.  No row has a `let` that both sides fills and
  pattern-only does not.
* `rows_per_result_bothSides` — under both sides, on every row, the slot model
  and the identity model print the same bag result by result, under rule M and
  under lexical fresh: what a renaming per result predicts.  This is a check of
  80 programs, not the renaming theorem for both sides.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionCorpus

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotExamples

/-- Answers of the slot model under a configuration, with both sides. -/
def ansBoth (c : Config) (cl : Sy → Option A) (t : A) : Option (List T) :=
  answersDirCfg c.bothSides (progOf c cl) 80 t

/-- Answers of the identity model under rule M, with both sides. -/
def ansMIBoth (cl : Sy → Option A) (t : A) : Option (List TI) :=
  answersDir .bothSides .static (progM .u .unit cl) 80 (elabMFormAt [] t)

/-- Answers of the identity model under lexical fresh, with both sides. -/
def ansLFIBoth (cl : Sy → Option A) (t : A) : Option (List TI) :=
  answersDir .bothSides .static (progLF .u .unit cl) 80 (elabLFFormAt [] t)

/-- **The corpus does not see the matching direction.**  On all 80 rows, under
each of the six configurations, the both-sides bag is the pattern-only bag. -/
theorem rows_direction_blind :
    rows.all (fun r => [cfgM, cfgLF, cfgEC, cfgQ, cfgPC, cfgSN].all fun c =>
      decide (ansBoth c r.clauseSet.cl r.src = SpectrumCorpus.ans c r.clauseSet.cl r.src)) =
      true := by
  decide +kernel

/-- **Result by result, the two models print alike on the whole corpus, under
both sides**, under rule M and under lexical fresh. -/
theorem rows_per_result_bothSides :
    rows.all (fun r =>
      decide (perS (ansBoth cfgM r.clauseSet.cl r.src) = perI (ansMIBoth r.clauseSet.cl r.src)) &&
      decide (perS (ansBoth cfgLF r.clauseSet.cl r.src) =
        perI (ansLFIBoth r.clauseSet.cl r.src))) = true := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionCorpus
