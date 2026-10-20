import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.HOLLight.MM0Meaning
import Mettapedia.Languages.Megalodon.HenkinProofSoundness
import Mettapedia.Languages.MM0.Translation.FirstOrderHOLMeaning
import Mettapedia.Logic.HOL.SevenVirtues.UniformSyntax
import Mettapedia.Logic.HOL.DefinitionHistoryProofConservativity

/-!
# Virtue 7: practical extensions of simple type theory, implemented and sound

Farmer's seventh virtue is a claim about practice: extensions of simple type
theory (definitions, polymorphism, choice, type definitions) have effective
implementations. Its formal content in this tree is that several implemented
checkers are sound for the Henkin semantics of `Mettapedia.Logic.HOL`. This
file collects those theorems and checks that they exist and depend only on the
standard axioms; it proves nothing new.

* HOL Light kernel (`Mettapedia.Languages.HOLLight.ProofSystem.checker_models`):
  a proof graph accepted by the axiom-free kernel checker has a translated
  conclusion true, under its translated hypotheses, in every extensional
  Henkin model. Full domains are not required.
* HOL Light kernel with axioms
  (`Mettapedia.Languages.OpenTheory.derives_models`): the same for derivations
  whose axioms are provable from a substitution-closed background theory that
  the model satisfies.
* HOL Light hosted in MM0 (`Mettapedia.Languages.HOLLight.MM0Meaning.accepted_models`):
  the same for certificates accepted by the generated MM0 calculus.
* Megalodon (`...Megalodon.HenkinTermInterpretation.NativeProof.checkProof_sound`):
  an accepted proof in the checked fragment is sound in every Henkin model
  that interprets the checked definitions by their bodies and validates the
  named known facts.
* MM0 propositional theories
  (`Mettapedia.Languages.MM0.Translation.FirstOrderHOLMeaning.accepted_iff_henkin`):
  acceptance is exactly validity in all extensional Henkin models.

The definitional layer of HOL Light is itself correct in every Henkin model,
standard or not: `UniformSyntax.denote_conjunction_general` and the lemmas
after it. Constant definitions are a conservative extension of the
extensional calculus (`DefinitionHistory.old_derivation_conservative`).

Published extensions treated here only as references: Farmer's `Q0^u`
(undefinedness; sound and complete for Henkin-style general models, 2014) and
`CTT_qe` (quotation and evaluation; sound, and complete for formulas without
evaluation, 2018); Kunčar and Popescu's proof that constant and type
definitions are safe and conservative in HOL (POPL 2018); and Candle, a
HOL Light clone verified in HOL4 down to machine code (ITP 2022).
-/

#check @Mettapedia.Languages.HOLLight.ProofSystem.checker_models
#check @Mettapedia.Languages.OpenTheory.derives_models
#check @Mettapedia.Languages.HOLLight.MM0Meaning.accepted_models
#check @Mettapedia.Languages.Megalodon.HenkinTermInterpretation.NativeProof.checkProof_sound
#check @Mettapedia.Languages.MM0.Translation.FirstOrderHOLMeaning.accepted_iff_henkin

#print axioms Mettapedia.Languages.HOLLight.ProofSystem.checker_models
#print axioms Mettapedia.Languages.OpenTheory.derives_models
#print axioms Mettapedia.Languages.HOLLight.MM0Meaning.accepted_models
#print axioms Mettapedia.Languages.Megalodon.HenkinTermInterpretation.NativeProof.checkProof_sound
#print axioms Mettapedia.Languages.MM0.Translation.FirstOrderHOLMeaning.accepted_iff_henkin
#print axioms Mettapedia.Logic.HOL.SevenVirtues.UniformSyntax.denote_conjunction_general
#check @Mettapedia.Logic.HOL.DefinitionHistory.old_derivation_conservative
#print axioms Mettapedia.Logic.HOL.DefinitionHistory.old_derivation_conservative
