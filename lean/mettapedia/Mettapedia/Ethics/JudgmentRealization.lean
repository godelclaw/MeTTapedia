import Mathlib.Logic.Function.Basic

/-!
# Exact realization of judgments

A representation may retain more than its judgment. An exact realization chooses
one representative of each judgment; normalization forgets the additional data.
Translations preserve the supplied readout and compose through any intermediate
realization, without asserting equivalence of the original representations.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u v w z

structure JudgmentRealization (Representation : Type u) (Judgment : Type v) where
  readout : Representation → Judgment
  realize : Judgment → Representation
  readout_realize : Function.LeftInverse readout realize

namespace JudgmentRealization

variable {R : Type u} {J : Type v} {S : Type w} {T : Type z}
  (source : JudgmentRealization R J)

def normalize (representation : R) : R := source.realize (source.readout representation)

def translateTo (target : JudgmentRealization S J) (representation : R) : S :=
  target.realize (source.readout representation)

@[simp] theorem readout_normalize (representation : R) :
    source.readout (source.normalize representation) = source.readout representation :=
  source.readout_realize _

@[simp] theorem normalize_idempotent (representation : R) :
    source.normalize (source.normalize representation) = source.normalize representation :=
  congrArg source.realize (source.readout_normalize representation)

theorem normalize_eq_iff (left right : R) :
    source.normalize left = source.normalize right ↔ source.readout left = source.readout right :=
  source.readout_realize.injective.eq_iff

@[simp] theorem readout_translateTo (target : JudgmentRealization S J) (representation : R) :
    target.readout (source.translateTo target representation) = source.readout representation :=
  target.readout_realize _

theorem translateTo_trans (middle : JudgmentRealization S J) (target : JudgmentRealization T J)
    (representation : R) :
    middle.translateTo target (source.translateTo middle representation) =
      source.translateTo target representation :=
  congrArg target.realize (source.readout_translateTo middle representation)

end JudgmentRealization
end Mettapedia.Ethics
