import Mettapedia.NARS.Bridges.GSLT.WorldModelReading
import Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus
import Mettapedia.NARS.Bridges.GSLT.ScopedRevisionControls
import Mettapedia.NARS.Bridges.GSLT.InheritanceWitness

/-!
# NARS inference presentations and checked semantics

The scoped-revision presentation keeps source identity and complete belief
paths while distinguishing revision from overlap choice. Its checker soundness
and nested positive and negative controls are included here.

Inheritance witness queries retain four tagged channels and have an exact
finite-to-set interpretation through the shared judgment GSLT.
-/
