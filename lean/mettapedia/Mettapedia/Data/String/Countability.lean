import Mathlib.Data.Set.Countable
import Mathlib.Data.String.Basic

/-!
# Countability of Unicode characters and strings

Characters inject into their Unicode scalar numbers. Strings inject into
their ordered character lists. These elementary constructions are available
independently from any language, evaluator or observation profile.
-/

set_option autoImplicit false

namespace Mettapedia.Data.StringCountability

instance charCountable : Countable Char :=
  Function.Injective.countable (f := Char.toNat) fun _ _ same => Char.toNat_inj.mp same

instance stringCountable : Countable String :=
  Function.Injective.countable (f := String.toList) fun _ _ same => String.toList_injective same

end Mettapedia.Data.StringCountability
