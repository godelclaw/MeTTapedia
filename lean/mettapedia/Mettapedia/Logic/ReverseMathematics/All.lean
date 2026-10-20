import Mettapedia.Logic.ReverseMathematics.RelativeComputability
import Mettapedia.Logic.ReverseMathematics.Syntax
import Mettapedia.Logic.ReverseMathematics.Systems
import Mettapedia.Logic.ReverseMathematics.TuringIdeal
import Mettapedia.Logic.ReverseMathematics.RCA0Models
import Mettapedia.Logic.ReverseMathematics.Halting
import Mettapedia.Logic.ReverseMathematics.WeakKoenig
import Mettapedia.Logic.ReverseMathematics.LeftmostPath
import Mettapedia.Logic.ReverseMathematics.Bubbles
import Mettapedia.Logic.ReverseMathematics.Omniscience

/-!
# Reverse mathematics

* `RelativeComputability`: closure properties of Mathlib's `RecursiveIn`
  (composition, pairing, primitive recursion, unbounded search, oracle
  queries for sets).
* `Syntax`: the two-sorted language of second-order arithmetic over a
  signature of extra function symbols, satisfaction in ω-models, renaming, and
  the classes `Σ⁰ₙ`, `Π⁰ₙ`, bounded and arithmetical formulas.
* `Systems`: the basic axioms, the induction and comprehension schemes, RCA₀
  and ACA₀, and their ω-models as the families closed under `Δ⁰₁` and
  arithmetical definability.
* `TuringIdeal`: Turing reducibility of sets, the join, recursive sets,
  Turing ideals.
* `RCA0Models`: every Turing ideal is an ω-model of RCA₀, the recursive sets
  in particular; every ω-model of RCA₀ is closed under join, complement and
  bounded definability.
* `Halting`: the halting set is `Σ⁰₁`-definable over primitive recursive
  symbols, so the recursive sets are not an ω-model of ACA₀.
* `WeakKoenig`: weak König's lemma in ω-models, König's lemma for the power
  set, the Kleene tree, diagonally noncomputable functions; the recursive
  sets are an ω-model of RCA₀ and not of WKL₀.
* `LeftmostPath`: a Turing ideal that is an ω-model of ACA₀ satisfies weak
  König's lemma, through the extendible nodes and the leftmost path.
* `Bubbles`: least sufficient subsystems as least sufficient bubbles; two
  routes to a DNR function with no least bubble; the least theory once the
  target is a principle; the `WKL`/`RT²₂` shape from published separations.
* `Omniscience`: LPO, WLPO, LLPO and Markov's principle with their
  implications proved without axioms, and their computable reading (MP holds,
  LPO and WLPO fail).
-/
