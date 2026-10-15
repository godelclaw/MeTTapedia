import Mettapedia.Logic.WorldModel.Indexed.Doctrine
import Mettapedia.Logic.WorldModel.Indexed.FixedQueryBridge
import Mettapedia.Logic.WorldModel.Indexed.DependentProfiles
import Mettapedia.Logic.WorldModel.Indexed.Survival
import Mettapedia.Logic.WorldModel.Indexed.SourceExample
import Mettapedia.Logic.WorldModel.Indexed.LawBridges
import Mettapedia.Logic.WorldModel.Indexed.BridgesWellbeing
import Mettapedia.Logic.WorldModel.Indexed.Contracts
import Mettapedia.Logic.WorldModel.Indexed.ContractBridges
import Mettapedia.Logic.WorldModel.Indexed.Quantifiers
import Mettapedia.Logic.WorldModel.Indexed.SourceQuantifiers
import Mettapedia.Logic.WorldModel.Indexed.InstitutionBridge
import Mettapedia.Logic.WorldModel.Indexed.HyperdoctrineBridge
import Mettapedia.Logic.WorldModel.Indexed.Modalities
import Mettapedia.Logic.WorldModel.Indexed.PotentialistBase
import Mettapedia.Logic.WorldModel.Indexed.ModalityControls
import Mettapedia.Logic.WorldModel.Indexed.Gluing
import Mettapedia.Logic.WorldModel.Indexed.NonAdditive

/-!
# The indexed world-model doctrine

* `Doctrine`: worlds, profiles, fibres, the total category and its fibration.
* `FixedQueryBridge`: the one-world fibre is the fixed-question calculus.
* `DependentProfiles`: answer types that depend on the question.
* `Survival`, `SourceExample`, `LawBridges`, `BridgesWellbeing`: what survives a
  lossy map, an open-ended base, and the local statements of the law.
* `Contracts`, `ContractBridges`: graded arrows.
* `Quantifiers`, `SourceQuantifiers`, `InstitutionBridge`, `HyperdoctrineBridge`: quantifiers,
  Beck–Chevalley, and the existing institution and hyperdoctrine.
* `Modalities`, `PotentialistBase`, `ModalityControls`: extension necessity.
* `Gluing`: states across worlds and gluing.
* `NonAdditive`: negative controls.
-/
