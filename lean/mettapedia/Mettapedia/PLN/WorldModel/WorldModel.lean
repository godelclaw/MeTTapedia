import Mettapedia.Logic.WorldModel.Basic
import Mettapedia.Logic.WorldModel.Observation
import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-!
# World-model entry point for PLN

The general interface and its observation maps impose no additive query law.
`AdditiveWorldModel` is the specialized extraction interface for additive
sufficient statistics; binary PLN evidence is a further specialization.
-/
