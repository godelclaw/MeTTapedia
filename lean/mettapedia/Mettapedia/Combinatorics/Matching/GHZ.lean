import Mettapedia.Combinatorics.Matching.GHZ.ColorRestriction
import Mettapedia.Combinatorics.Matching.GHZ.CharacteristicTwo.OfficialBridge
import Mettapedia.Combinatorics.Matching.GHZ.CharacteristicTwo.Descent
import Mettapedia.Combinatorics.Matching.GHZ.CharacteristicTwo.Rigidity
import Mettapedia.Combinatorics.Matching.GHZ.CharacteristicTwo.SixSite
import Mettapedia.Combinatorics.Matching.GHZ.CharacteristicTwo.SixSiteFormula
import Mettapedia.Combinatorics.Matching.GHZ.ColorPerMatching
import Mettapedia.Combinatorics.Matching.GHZ.Conditional
import Mettapedia.Combinatorics.Matching.GHZ.ConditionalThreeRegularity
import Mettapedia.Combinatorics.Matching.GHZ.Configurations
import Mettapedia.Combinatorics.Matching.GHZ.Covectors
import Mettapedia.Combinatorics.Matching.GHZ.CycleCoordinates
import Mettapedia.Combinatorics.Matching.GHZ.Degenerate
import Mettapedia.Combinatorics.Matching.GHZ.Fermionic.Descent
import Mettapedia.Combinatorics.Matching.GHZ.Fermionic.Obstruction
import Mettapedia.Combinatorics.Matching.GHZ.Fermionic.Rigidity
import Mettapedia.Combinatorics.Matching.GHZ.Fermionic.SixSite
import Mettapedia.Combinatorics.Matching.GHZ.FourVertexConstruction
import Mettapedia.Combinatorics.Matching.GHZ.FourVertexRank
import Mettapedia.Combinatorics.Matching.GHZ.Gauge
import Mettapedia.Combinatorics.Matching.GHZ.HardCase
import Mettapedia.Combinatorics.Matching.GHZ.LiveDegree
import Mettapedia.Combinatorics.Matching.GHZ.MatchingSum
import Mettapedia.Combinatorics.Matching.GHZ.MinimalSupport
import Mettapedia.Combinatorics.Matching.GHZ.NoCancellation
import Mettapedia.Combinatorics.Matching.GHZ.OfficialBridge
import Mettapedia.Combinatorics.Matching.GHZ.OfficialDefinitions
import Mettapedia.Combinatorics.Matching.GHZ.Pfaffian
import Mettapedia.Combinatorics.Matching.GHZ.PurePartner
import Mettapedia.Combinatorics.Matching.GHZ.Scenarios
import Mettapedia.Combinatorics.Matching.GHZ.Separation
import Mettapedia.Combinatorics.Matching.GHZ.SingleFlip
import Mettapedia.Combinatorics.Matching.GHZ.SixCycle
import Mettapedia.Combinatorics.Matching.GHZ.StarNormalForm
import Mettapedia.Combinatorics.Matching.GHZ.StarStructure
import Mettapedia.Combinatorics.Matching.GHZ.TightCut
import Mettapedia.Combinatorics.Matching.GHZ.TwoColorCycle
import Mettapedia.Combinatorics.Matching.GHZ.UniformRigidity

/-!
# GHZ weighted perfect-matching equations

Structural consequences, constructions and conditional reductions for the
Krenn–Gu equations, together with characteristic-two and fermionic variants.
The complex-valued conjecture is not asserted here as an unconditional theorem.
-/
