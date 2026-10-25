import Mettapedia.Computability.KolmogorovComplexity.Basic
import Mettapedia.UniversalAI.SolomonoffPrior.Basic

/-!
# Prefix-free binary codes and Kraft bounds

This module exports the prefix-free predicate and finite Kraft inequality from
`SolomonoffPrior.Basic`, without importing its prediction or invariance layers.
Machine complexity and output mass are separate consumers of these code bounds.

References: Cover & Thomas, *Elements of Information Theory* (2006), Chapter 5;
Li & Vitányi, *An Introduction to Kolmogorov Complexity* (2019), Chapter 1;
Shen, *Around Kolmogorov Complexity* (arXiv:1504.04955), Section 2.
-/

namespace KolmogorovComplexity

abbrev PrefixFree (S : Set BinString) : Prop :=
  Mettapedia.UniversalAI.SolomonoffPrior.PrefixFree (S := S)

noncomputable abbrev kraftSum (S : Finset BinString) : ℝ :=
  Mettapedia.UniversalAI.SolomonoffPrior.kraftSum (S := S)

theorem kraftSum_nonneg (S : Finset BinString) : 0 ≤ kraftSum S :=
  Mettapedia.UniversalAI.SolomonoffPrior.kraftSum_nonneg S

theorem kraft_inequality (S : Finset BinString) (hpf : PrefixFree (↑S : Set BinString)) :
    kraftSum S ≤ 1 :=
  Mettapedia.UniversalAI.SolomonoffPrior.kraft_inequality S hpf

end KolmogorovComplexity
