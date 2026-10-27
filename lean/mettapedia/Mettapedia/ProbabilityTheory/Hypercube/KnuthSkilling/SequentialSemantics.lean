import Mettapedia.ProbabilityTheory.Common.OrderedCombination

/-!
# Sequential interpretation of combination

An execution interpretation of a monoid `M` on states `S` is a monoid
homomorphism `Mᵐᵒᵖ →* Function.End S`. The opposite makes `x * y` execute
`x` first, then `y`. The shared `OrderedCombination.rightRegular` action is
faithful and its commutation criterion retains the noncommutative distinction.
This interface requires a monoid, without an order or a minimum identity.
-/
