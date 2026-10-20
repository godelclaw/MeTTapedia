import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Recursive Boolean query interpretation

Negation and conjunction act on recursively interpreted queries. Other terms
have an explicitly supplied atomic interpretation. The same syntax can be
interpreted on different world carriers without identifying those carriers.
-/

namespace Mettapedia.GSLT.LanguageDef.BooleanTermSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {W : Type*}

def eval (atom : Pattern → W → Bool) : Pattern → W → Bool
  | .apply "not" [q] => fun world => !eval atom q world
  | .apply "and" [a, b] => fun world => eval atom a world && eval atom b world
  | other => atom other
termination_by pattern => sizeOf pattern

@[simp] theorem eval_not (atom : Pattern → W → Bool) (q : Pattern) :
    eval atom (.apply "not" [q]) = fun world => !eval atom q world := by rw [eval]

@[simp] theorem eval_and (atom : Pattern → W → Bool) (a b : Pattern) :
    eval atom (.apply "and" [a, b]) = fun world => eval atom a world && eval atom b world := by
  rw [eval]

@[simp] theorem eval_atom (atom : Pattern → W → Bool) (name : String) :
    eval atom (.apply name []) = atom (.apply name []) := by rw [eval] <;> simp

end Mettapedia.GSLT.LanguageDef.BooleanTermSemantics
