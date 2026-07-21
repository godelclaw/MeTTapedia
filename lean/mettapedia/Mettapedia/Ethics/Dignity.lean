import Mettapedia.Ethics.Core

set_option autoImplicit false
universe u v

namespace Mettapedia.Ethics.Dignity

abbrev Nature (World : Type u) (a : Type v) : Type (max u v) := a -> Formula World

def goodCondition {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w : World) : Prop :=
  nat x w

def hasDignity {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w : World) : Prop :=
  goodCondition nat x w

theorem dignity_iff_goodCondition {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w : World) :
    hasDignity nat x w <-> goodCondition nat x w := Iff.rfl

def dignityFormula {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) : Formula World :=
  fun w => hasDignity nat x w

def dignityAsValueJudgment {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) : ValueJudgmentSentence World :=
  { tag := .MorallyGood, formula := dignityFormula nat x }

def respectsNature {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w w' : World) : Prop :=
  nat x w -> nat x w'

theorem dignity_preserved_under_respect {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w w' : World)
    (h : hasDignity nat x w) (hresp : respectsNature nat x w w') :
    hasDignity nat x w' := hresp h

def instrumentalUse {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w : World) : Prop :=
  exists (externalEnd : Formula World), externalEnd w ∧ ¬ nat x w

theorem dignity_excludes_mere_instrumental_use {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w : World)
    (h : hasDignity nat x w) : ¬ instrumentalUse nat x w := by
  intro hinst
  obtain ⟨_ext, _hext, hneg⟩ := hinst
  exact hneg h

def hasIntrinsicWorth {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w : World) : Prop :=
  hasDignity nat x w

theorem dignity_implies_intrinsic_worth {World : Type u} {a : Type v}
    (nat : Nature World a) (x : a) (w : World)
    (h : hasDignity nat x w) : hasIntrinsicWorth nat x w := h

end Mettapedia.Ethics.Dignity