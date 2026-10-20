import Mettapedia.GSLT.LanguageDef.LayoutLowering

/-!
# Layout accessors over `BitVec 64`

`LayoutLowering.eval` gives the accessor expressions C's unsigned 64-bit
meaning on natural numbers. `evalBV` evaluates the same expressions with Lean
core's `BitVec 64` operations, and `eval_toNat` proves the two agree: the
accessors' meaning is the standard fixed-width bitvector semantics, so the
`BitVec` library and its kernel-checked rewriting apply to them directly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LayoutBitVec

open Mettapedia.GSLT.LanguageDef.LayoutLowering

def lift2BV (f : BitVec 64 → BitVec 64 → BitVec 64) : Option (BitVec 64) → Option (BitVec 64) → Option (BitVec 64)
  | some x, some y => some (f x y)
  | _, _ => none

def evalBV (env : List (BitVec 64)) : Expr → Option (BitVec 64)
  | .var i => env[i]?
  | .lit n => if n < top then some (BitVec.ofNat 64 n) else none
  | .band a b => lift2BV (· &&& ·) (evalBV env a) (evalBV env b)
  | .bor a b => lift2BV (· ||| ·) (evalBV env a) (evalBV env b)
  | .bnot a => (evalBV env a).map (~~~ ·)
  | .shl a n => if n < 64 then (evalBV env a).map (fun x : BitVec 64 => x <<< n) else none
  | .shr a n => if n < 64 then (evalBV env a).map (fun x : BitVec 64 => x >>> n) else none
  | .add a b => lift2BV (· + ·) (evalBV env a) (evalBV env b)
  | .sub a b => lift2BV (· - ·) (evalBV env a) (evalBV env b)
  | .eq a b => lift2BV (fun x y => if x = y then 1#64 else 0#64) (evalBV env a) (evalBV env b)
  | .le a b => lift2BV (fun x y => if x ≤ y then 1#64 else 0#64) (evalBV env a) (evalBV env b)
  | .ite c t e => match evalBV env c with
    | some x => if x ≠ 0#64 then evalBV env t else evalBV env e
    | none => none

/-- C defines `~E` on an unsigned type as the type's largest value minus `E`
(C11 6.5.3.3p4); the accessors' complement is that value. -/
theorem complement_eq {x : Nat} (hx : x < 2 ^ 64) : (2 ^ 64 - 1) ^^^ x = 2 ^ 64 - 1 - x := by
  have h := BitVec.toNat_not (x := BitVec.ofNat 64 x)
  rw [BitVec.not_def, BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at h
  exact h

theorem lift2_map {f : BitVec 64 → BitVec 64 → BitVec 64} {g : Nat → Nat → Nat}
    (h : ∀ x y : BitVec 64, (f x y).toNat = g x.toNat y.toNat) (a b : Option (BitVec 64)) :
    lift2 g (a.map BitVec.toNat) (b.map BitVec.toNat) = (lift2BV f a b).map BitVec.toNat := by
  cases a <;> cases b <;> simp [lift2, lift2BV, h]

/-- The accessors' meaning is fixed-width bitvector evaluation. -/
theorem eval_toNat (env : List (BitVec 64)) :
    ∀ e : Expr, eval (env.map BitVec.toNat) e = (evalBV env e).map BitVec.toNat
  | .var i => by simp [eval, evalBV, List.getElem?_map]
  | .lit n => by
      unfold eval evalBV
      split
      · rename_i h
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 from h)]
      · simp
  | .band a b => by
      simp only [eval, evalBV, eval_toNat env a, eval_toNat env b]
      exact lift2_map (fun x y => BitVec.toNat_and x y) _ _
  | .bor a b => by
      simp only [eval, evalBV, eval_toNat env a, eval_toNat env b]
      exact lift2_map (fun x y => BitVec.toNat_or x y) _ _
  | .bnot a => by
      simp only [eval, evalBV, eval_toNat env a, Option.map_map]
      congr 1
  | .shl a n => by
      unfold eval evalBV
      split
      · simp only [eval_toNat env a, Option.map_map]
        congr 1
        funext x
        simp [Function.comp, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, top]
      · rfl
  | .shr a n => by
      unfold eval evalBV
      split
      · simp only [eval_toNat env a, Option.map_map]
        congr 1
        funext x
        simp [Function.comp, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      · rfl
  | .add a b => by
      simp only [eval, evalBV, eval_toNat env a, eval_toNat env b]
      exact lift2_map (fun x y => by simp [BitVec.toNat_add, top]) _ _
  | .sub a b => by
      simp only [eval, evalBV, eval_toNat env a, eval_toNat env b]
      refine lift2_map (fun x y => ?_) _ _
      have := y.isLt
      simp only [BitVec.toNat_sub, top]
      congr 1
      omega
  | .eq a b => by
      simp only [eval, evalBV, eval_toNat env a, eval_toNat env b]
      refine lift2_map (fun x y => ?_) _ _
      by_cases h : x = y
      · simp [h]
      · have : x.toNat ≠ y.toNat := fun e => h (BitVec.toNat_inj.mp e)
        simp [h, this]
  | .le a b => by
      simp only [eval, evalBV, eval_toNat env a, eval_toNat env b]
      refine lift2_map (fun x y => ?_) _ _
      by_cases h : x ≤ y
      · have : x.toNat ≤ y.toNat := BitVec.le_def.mp h
        simp [h, this]
      · have : ¬ x.toNat ≤ y.toNat := fun e => h (BitVec.le_def.mpr e)
        simp [h, this]
  | .ite c t e => by
      simp only [eval, evalBV, eval_toNat env c, eval_toNat env t, eval_toNat env e]
      cases evalBV env c with
      | none => rfl
      | some x =>
          by_cases h : x = 0#64
          · subst h; simp
          · have : x.toNat ≠ 0 := fun e => h (BitVec.toNat_inj.mp (by simp [e]))
            simp [h, this]

end Mettapedia.GSLT.LanguageDef.LayoutBitVec
