import Mettapedia.TypeTheory.HOLFiber.Fiber
import Mettapedia.TypeTheory.HOLFiber.PropositionalDecision
import Mettapedia.TypeTheory.HOLFiber.Universes

/-!
# The HOL fiber of the impredicative code package

* `Fiber`: the region of a HOL reading inside a package's typed judgment,
  carriers and proof types; carriers do not depend on terms; interpreted
  choice gives every sort a closed inhabitant. (Its concrete
  `DeclarationBased.SetProfile` instantiation lives in
  `Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.HOLFiberPeano`.)
* `PropositionalDecision`: the quantifier-free `bool` fragment, decided by
  evaluation at every assignment of its atoms.
* `Universes`: machines of the computational universe, the arithmetic
  classification of their observations, and checkers run as search machines.
-/
