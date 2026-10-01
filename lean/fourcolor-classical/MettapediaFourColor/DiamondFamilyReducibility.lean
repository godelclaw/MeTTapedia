import MettapediaFourColor.DiamondProfileReducibility
import MettapediaFourColor.TwoDiamondSplitRepair
import FourColor.Reduce.All

/-!
# The complete reducibility range with shared diamond profile repair

The joint-profile certificate supplies configurations 2 and 4. Boundary-split
transfer from configuration 2 supplies configuration 1. The original certificates
for these three configurations are absent. Configuration 3 inherits repair
from configuration 6 through the same split law; 629 original certificates remain.
The range below is rebuilt from individual inputs, so the final proof does
not depend on the original first block or its superseded certificate.

Reference certificate mathematics: Robertson, Sanders, Seymour and Thomas;
Gonthier and Werner; the Lean realization by Chris Emery.
-/

namespace FourColor.DiamondFamilyReducibility

/-- Configuration 1 inherits repair from the shared profile's configuration 2 base. -/
theorem configuration1 : ReducibleInRange 0 1 theConfigs :=
  reducible_range_one (cfs := theConfigs) (i := 0) DiamondProfileReducibility.reducible001

/-- Configuration 2 is supplied by the joint-profile law. -/
theorem configuration2 : ReducibleInRange 1 2 theConfigs :=
  reducible_range_one (cfs := theConfigs) (i := 1) DiamondProfileReducibility.reducible002

/-- The shared-tip double diamond inherits repair through its actual insertion. -/
theorem configuration3 : ReducibleInRange 2 3 theConfigs :=
  reducible_range_one (cfs := theConfigs) (i := 2) TwoDiamondSplitRepair.reducible003

/-- Configuration 4 is supplied by the coupled insertion boundary law. -/
theorem configuration4 : ReducibleInRange 3 4 theConfigs :=
  reducible_range_one (cfs := theConfigs) (i := 3) DiamondProfileReducibility.reducible004

/-- The first forty cases, using transfer in slot one and joint repair in slot four. -/
theorem first_block : ReducibleInRange 0 40 theConfigs :=
  (cat_reducible_range
    (cat_reducible_range
      (cat_reducible_range
        (cat_reducible_range
          (cat_reducible_range
            configuration1
            configuration2)
          (cat_reducible_range
            configuration3
            (cat_reducible_range
              configuration4
              Bulk.Cfg004.reducible)))
        (cat_reducible_range
          (cat_reducible_range
            Bulk.Cfg005.reducible
            Bulk.Cfg006.reducible)
          (cat_reducible_range
            Bulk.Cfg007.reducible
            (cat_reducible_range
              Bulk.Cfg008.reducible
              Bulk.Cfg009.reducible))))
      (cat_reducible_range
        (cat_reducible_range
          (cat_reducible_range
            Bulk.Cfg010.reducible
            Bulk.Cfg011.reducible)
          (cat_reducible_range
            Bulk.Cfg012.reducible
            (cat_reducible_range
              Bulk.Cfg013.reducible
              Bulk.Cfg014.reducible)))
        (cat_reducible_range
          (cat_reducible_range
            Bulk.Cfg015.reducible
            Bulk.Cfg016.reducible)
          (cat_reducible_range
            Bulk.Cfg017.reducible
            (cat_reducible_range
              Bulk.Cfg018.reducible
              Bulk.Cfg019.reducible)))))
    (cat_reducible_range
      (cat_reducible_range
        (cat_reducible_range
          (cat_reducible_range
            Bulk.Cfg020.reducible
            Bulk.Cfg021.reducible)
          (cat_reducible_range
            Bulk.Cfg022.reducible
            (cat_reducible_range
              Bulk.Cfg023.reducible
              Bulk.Cfg024.reducible)))
        (cat_reducible_range
          (cat_reducible_range
            Bulk.Cfg025.reducible
            Bulk.Cfg026.reducible)
          (cat_reducible_range
            Bulk.Cfg027.reducible
            (cat_reducible_range
              Bulk.Cfg028.reducible
              Bulk.Cfg029.reducible))))
      (cat_reducible_range
        (cat_reducible_range
          (cat_reducible_range
            Bulk.Cfg030.reducible
            Bulk.Cfg031.reducible)
          (cat_reducible_range
            Bulk.Cfg032.reducible
            (cat_reducible_range
              Bulk.Hyb033.reducible
              Bulk.Cfg034.reducible)))
        (cat_reducible_range
          (cat_reducible_range
            Bulk.Cfg035.reducible
            Bulk.Cfg036.reducible)
          (cat_reducible_range
            Bulk.Cfg037.reducible
            (cat_reducible_range
              Bulk.Cfg038.reducible
              Bulk.Cfg039.reducible))))))

/-- All configurations, with four original certificate dependencies replaced. -/
theorem reducible_all : ReducibleInRange 0 633 theConfigs :=
  (cat_reducible_range
    (cat_reducible_range
      (cat_reducible_range
        (cat_reducible_range
          first_block
          reducible_block_1)
        (cat_reducible_range
          reducible_block_2
          reducible_block_3))
      (cat_reducible_range
        (cat_reducible_range
          reducible_block_4
          reducible_block_5)
        (cat_reducible_range
          reducible_block_6
          reducible_block_7)))
    (cat_reducible_range
      (cat_reducible_range
        (cat_reducible_range
          reducible_block_8
          reducible_block_9)
        (cat_reducible_range
          reducible_block_10
          reducible_block_11))
      (cat_reducible_range
        (cat_reducible_range
          reducible_block_12
          reducible_block_13)
        (cat_reducible_range
          reducible_block_14
          reducible_block_15))))

end FourColor.DiamondFamilyReducibility
