import Mettapedia.GSLT.LanguageDef.LayoutCodes

/-!
# CeTTa's frame-identity layout, as data

The layout CeTTa uses for frame identities: 32 bits, four classes chosen by
the prefixes `0`, `10`, `110` and `1110`, and the reserved prefix `1111`.
This module only states it, so that admissions can compare a declared layout
with it without importing the runtime bridge. `CeTTaFrameLayout` proves that
this layout is the codec `CeTTaFrameWriteback.NativeFrames` restates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameLayoutCode

open Mettapedia.GSLT.LanguageDef.LayoutCodes

def classOneFirst : Nat := 2 ^ 20
def classTwoFirst : Nat := classOneFirst + 2 ^ 24
def classThreeFirst : Nat := classTwoFirst + 2 ^ 26
def handleLimit : Nat := classThreeFirst + 2 ^ 26

/-- A class: the handle in the low `handleBits` bits, stored minus `first`,
valid from `lo`, and the generation in the next `generationBits` bits, valid
from 1 to `max`. -/
def frameClass (handleBits first lo generationBits max : Nat) : Case :=
  ⟨[⟨⟨0, handleBits⟩, first, lo, first + 2 ^ handleBits - 1⟩,
    ⟨⟨handleBits, generationBits⟩, 0, 1, max⟩], false⟩

/-- The reserved region: a handle past the limit, generation zero. -/
def reservedClass : Case :=
  ⟨[⟨⟨0, 28⟩, handleLimit, handleLimit, handleLimit + 2 ^ 28 - 1⟩, ⟨⟨28, 0⟩, 0, 0, 0⟩], true⟩

def frameIdentity : Code :=
  ⟨32, .node (.leaf (frameClass 20 0 1 11 2046))
    (.node (.leaf (frameClass 24 classOneFirst classOneFirst 6 62))
      (.node (.leaf (frameClass 26 classTwoFirst classTwoFirst 3 6))
        (.node (.leaf (frameClass 26 classThreeFirst classThreeFirst 2 2)) (.leaf reservedClass))))⟩

theorem frameIdentity_wellFormed : frameIdentity.wellFormed = true := by decide

example : frameIdentity.encode [5, 3] = some (3 * 2 ^ 20 + 5) := by decide
/-- Generation zero is never issued. -/
example : frameIdentity.encode [5, 0] = none := by decide
/-- The reserved prefix never decodes. -/
example : frameIdentity.decode (15 * 2 ^ 28) = none := by decide

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameLayoutCode
