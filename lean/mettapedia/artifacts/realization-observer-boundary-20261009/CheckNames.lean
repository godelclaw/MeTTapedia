import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Logic.HennessyMilnerTransport
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Ultrainfinite
#check Formula.map_id
#print Mettapedia.GSLT.HennessyMilner.Formula.map_id
example {Atom : Type} (formula : Formula Atom Unit) : Formula.map _root_.id _root_.id formula = formula := by
  exact Mettapedia.GSLT.HennessyMilner.Formula.map_id formula
