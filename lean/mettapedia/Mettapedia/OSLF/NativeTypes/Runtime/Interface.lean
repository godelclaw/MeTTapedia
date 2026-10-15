import Mettapedia.OSLF.NativeTypes.Runtime.Description
import Mettapedia.OSLF.NativeTypes.Decision.Machine.Interface
import Mettapedia.OSLF.NativeTypes.Decision.Machine.Meaning

open Mettapedia.OSLF.Framework

/-!
# Execution attached to a generated native description

An installed description carries the actual suspended operational jobs and
leaf evaluations. Their meanings are compared with the independently defined
native predicates. No work budget is expanded into independent child budgets.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime

open Mettapedia.OSLF.NativeTypes.Runtime.Description
open Mettapedia.OSLF.NativeTypes.Decision.Machine

structure Engine (driver : Driver) where
  cursor : CursorBackend.{0,0} driver.system driver.admitted
  leaves : driver.Leaf → LeafBackend driver.system driver.admitted
  leaf_meaning : ∀ leaf, (leaves leaf).predicate = (driver.tests leaf).predicate

structure Installed where
  native : Driver
  runtime : Engine native

theorem Engine.meaning_at_decoded {driver : Driver} (runtime : Engine driver)
    (formula : driver.Formula) {raw : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (source : driver.Decoded raw) :
    Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation runtime.leaves formula source.val ↔
      Meaning driver formula raw := by
  rw [denotation_comparison runtime.leaves driver.tests runtime.leaf_meaning]
  exact (Mettapedia.OSLF.NativeTypes.Runtime.Description.meaning_at_decoded driver formula raw source).symm

end Mettapedia.OSLF.NativeTypes.Runtime
