import Mettapedia.Logic.HOL.Semantics.HeytingGeneral
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical

/-!
# Kripke-Henkin Bridge Package

Public citation handle for the bridge between the substitutional
Kripke-Henkin presentation and the supported canonical membership interface.

This module re-exports:

- `HeytingSem.ofKripkeHenkin`, the embedding of every substitutional
  `KripkeHenkin` model into the Heyting-valued semantics;
- `KripkeHenkin.SupportedCanonicalFrame.SupportedMembershipConsequence` and
  the `Provable ↔ SupportedMembershipConsequence` interfaces;
- the provider-dispatched successor clauses
  `forces_imp_level_provider`, `forces_not_level_provider`, and
  `forces_all_level_provider`.

What this buys: a presentation bridge, given a `SchedulerProvider` (one exists
for every countable signature, `schedulerProviderOfCountable`), connecting the
supported canonical membership interface to the substitutional Kripke-Henkin
interface and to the Heyting package.

What this does not buy: completeness for the substitutional Kripke-Henkin
class.  Its structures have constant domains and force the constant-domain
sentence, which is not derivable (`KripkeHenkin.not_complete`).  The
hypothesis packages `LocalMembershipClauses`, `LevelLocalMembershipClauses`
and `FullPresentedUpgrade` are empty over every countable signature with a
base type (`KripkeHenkinCanonicalObstruction`), and the conditional
completeness theorems built on them were removed on 2026-10-20 (listed in the
`KripkeHenkinCanonical` docstring).  Kripke completeness holds for varying
domains: `KripkeVarying.Canonical.provable_iff_consequence`.  With constant
domains, forcing disjunction and the existential on covers gives a complete
Beth semantics: `provable_iff_bethConsequence_param_free`.
-/
