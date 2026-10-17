import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Megalodon syntax over ordinary CeTTa data

These codecs preserve every Mathdata type, term and proof constructor.
They are independent of a MeTTa dialect or Prime foundation. Decoding
constructs untrusted syntax; it does not grant proof or import authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeSyntaxWire
open MathdataKernel
abbrev Wire := Mettapedia.GSLT.LanguageDef.CettaWire.Term

def encodeTp : Tp → Wire
  | .var i => .application "Tp.var" [.natural i]
  | .prop => .application "Tp.prop" []
  | .base i => .application "Tp.base" [.natural i]
  | .arr a b => .application "Tp.arr" [encodeTp a, encodeTp b]
  | .all a => .application "Tp.all" [encodeTp a]

def decodeTp : Wire → Option Tp
  | .application "Tp.var" [.natural i] => some (.var i)
  | .application "Tp.prop" [] => some .prop
  | .application "Tp.base" [.natural i] => some (.base i)
  | .application "Tp.arr" [a, b] => return .arr (← decodeTp a) (← decodeTp b)
  | .application "Tp.all" [a] => return .all (← decodeTp a)
  | _ => none

@[simp] theorem decodeTp_encode (type : Tp) : decodeTp (encodeTp type) = some type := by
  induction type <;> simp_all [encodeTp, decodeTp]

def encodeTm : Tm → Wire
  | .db i => .application "Tm.db" [.natural i]
  | .named name => .application "Tm.named" [.string name]
  | .prim i => .application "Tm.prim" [.natural i]
  | .app f a => .application "Tm.app" [encodeTm f, encodeTm a]
  | .lam a body => .application "Tm.lam" [encodeTp a, encodeTm body]
  | .imp a b => .application "Tm.imp" [encodeTm a, encodeTm b]
  | .all a body => .application "Tm.all" [encodeTp a, encodeTm body]
  | .typeApp f a => .application "Tm.typeApp" [encodeTm f, encodeTp a]
  | .typeLam body => .application "Tm.typeLam" [encodeTm body]
  | .typeAll body => .application "Tm.typeAll" [encodeTm body]

def decodeTm : Wire → Option Tm
  | .application "Tm.db" [.natural i] => some (.db i)
  | .application "Tm.named" [.string name] => some (.named name)
  | .application "Tm.prim" [.natural i] => some (.prim i)
  | .application "Tm.app" [f, a] => return .app (← decodeTm f) (← decodeTm a)
  | .application "Tm.lam" [a, body] => return .lam (← decodeTp a) (← decodeTm body)
  | .application "Tm.imp" [a, b] => return .imp (← decodeTm a) (← decodeTm b)
  | .application "Tm.all" [a, body] => return .all (← decodeTp a) (← decodeTm body)
  | .application "Tm.typeApp" [f, a] => return .typeApp (← decodeTm f) (← decodeTp a)
  | .application "Tm.typeLam" [body] => return .typeLam (← decodeTm body)
  | .application "Tm.typeAll" [body] => return .typeAll (← decodeTm body)
  | _ => none

@[simp] theorem decodeTm_encode (term : Tm) : decodeTm (encodeTm term) = some term := by
  induction term <;> simp_all [encodeTm, decodeTm]

def encodePf : Pf → Wire
  | .gpa name => .application "Pf.gpa" [.string name]
  | .hyp i => .application "Pf.hyp" [.natural i]
  | .known name => .application "Pf.known" [.string name]
  | .termApp f a => .application "Pf.termApp" [encodePf f, encodeTm a]
  | .proofApp f a => .application "Pf.proofApp" [encodePf f, encodePf a]
  | .proofLam p body => .application "Pf.proofLam" [encodeTm p, encodePf body]
  | .termLam a body => .application "Pf.termLam" [encodeTp a, encodePf body]
  | .typeApp f a => .application "Pf.typeApp" [encodePf f, encodeTp a]
  | .typeLam body => .application "Pf.typeLam" [encodePf body]

def decodePf : Wire → Option Pf
  | .application "Pf.gpa" [.string name] => some (.gpa name)
  | .application "Pf.hyp" [.natural i] => some (.hyp i)
  | .application "Pf.known" [.string name] => some (.known name)
  | .application "Pf.termApp" [f, a] => return .termApp (← decodePf f) (← decodeTm a)
  | .application "Pf.proofApp" [f, a] => return .proofApp (← decodePf f) (← decodePf a)
  | .application "Pf.proofLam" [p, body] => return .proofLam (← decodeTm p) (← decodePf body)
  | .application "Pf.termLam" [a, body] => return .termLam (← decodeTp a) (← decodePf body)
  | .application "Pf.typeApp" [f, a] => return .typeApp (← decodePf f) (← decodeTp a)
  | .application "Pf.typeLam" [body] => return .typeLam (← decodePf body)
  | _ => none

@[simp] theorem decodePf_encode (proof : Pf) : decodePf (encodePf proof) = some proof := by
  induction proof <;> simp_all [encodePf, decodePf]

theorem encodePf_injective : Function.Injective encodePf := by
  intro first second same
  simpa only [decodePf_encode, Option.some.injEq] using congrArg decodePf same

def decodeList {α : Type} (decode : Wire → Option α) : List Wire → Option (List α)
  | [] => some []
  | first :: rest => return (← decode first) :: (← decodeList decode rest)

theorem decodeList_map {α : Type} (encode : α → Wire) (decode : Wire → Option α)
    (roundTrip : ∀ value, decode (encode value) = some value) (values : List α) :
    decodeList decode (values.map encode) = some values := by
  induction values <;> simp_all [decodeList]

end Mettapedia.Languages.Megalodon.NativeSyntaxWire
