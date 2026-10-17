import Mettapedia.Computability.OriginalMachineTraceEncoding
import Mathlib.Computability.PartrecCode
import Mettapedia.Computability.UniversalEffectiveEvidence
import Mathlib.Data.Nat.Size

/-!
# Executable finite codes for original-machine trace data

The constructors below build actual `Nat.Partrec.Code` syntax. Their evaluation
theorems are proved from the code evaluator, without choosing codes from an
existential computability theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.OriginalMachineTraceCode
open Nat.Partrec (Code)
open OriginalMachineTraceEncoding

namespace Programs

theorem eval_zero (value : Nat) : Code.zero.eval value = Part.some 0 := rfl
theorem eval_succ (value : Nat) : Code.succ.eval value = Part.some value.succ := rfl
theorem eval_left (value : Nat) : Code.left.eval value = Part.some value.unpair.1 := rfl
theorem eval_right (value : Nat) : Code.right.eval value = Part.some value.unpair.2 := rfl

theorem eval_comp {outer inner : Code} {f g : Nat → Nat}
    (outside : ∀ value, outer.eval value = Part.some (f value))
    (inside : ∀ value, inner.eval value = Part.some (g value)) (value : Nat) :
    (Code.comp outer inner).eval value = Part.some (f (g value)) := by
  simp only [Code.eval, inside, Part.bind_eq_bind, Part.bind_some, outside]

theorem eval_pair {firstCode secondCode : Code} {f g : Nat → Nat}
    (first : ∀ value, firstCode.eval value = Part.some (f value))
    (second : ∀ value, secondCode.eval value = Part.some (g value)) (value : Nat) :
    (Code.pair firstCode secondCode).eval value = Part.some (Nat.pair (f value) (g value)) := by
  simp [Code.eval, first, second, Seq.seq, Part.map_eq_map]

theorem eval_comp_at {outer inner : Code} {input middle output : Nat}
    (inside : inner.eval input = Part.some middle) (outside : outer.eval middle = Part.some output) :
    (Code.comp outer inner).eval input = Part.some output := by
  rw [Code.eval]
  dsimp only
  rw [inside, Part.bind_eq_bind, Part.bind_some, outside]

theorem eval_pair_at {first second : Code} {input a b : Nat}
    (firstEval : first.eval input = Part.some a) (secondEval : second.eval input = Part.some b) :
    (Code.pair first second).eval input = Part.some (Nat.pair a b) := by
  simp [Code.eval, firstEval, secondEval, Seq.seq, Part.map_eq_map]

private theorem unpair_right_strict (value : Nat) (large : 2 ≤ value) : value.unpair.2 < value := by
  have lower := Nat.max_sq_add_min_le_pair value.unpair.1 value.unpair.2
  rw [Nat.pair_unpair] at lower
  have right := le_max_right value.unpair.1 value.unpair.2
  have upper := Nat.unpair_right_le value
  simp only [Nat.pow_two] at lower
  by_contra failure
  have above : value ≤ value.unpair.2 := Nat.le_of_not_lt failure
  have maximum : value ≤ max value.unpair.1 value.unpair.2 := above.trans right
  have square : value * value ≤ value :=
    (Nat.mul_le_mul maximum maximum).trans ((Nat.le_add_right _ _).trans lower)
  nlinarith

/-- Compact literal syntax by recursive unpairing, with zero and one as leaves. -/
def literal : Nat → Code
  | 0 => .zero
  | 1 => .comp .succ .zero
  | value + 2 => .pair (literal (value + 2).unpair.1) (literal (value + 2).unpair.2)
termination_by value => value
decreasing_by
  · exact Nat.unpair_lt (by omega)
  · exact unpair_right_strict _ (by omega)

theorem eval_literal (value input : Nat) : (literal value).eval input = Part.some value := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
      cases value with
      | zero => simp only [literal, eval_zero]
      | succ value =>
          cases value with
          | zero =>
              change (literal 1).eval input = Part.some 1
              rw [literal]
              exact eval_comp_at (eval_zero input) (eval_succ 0)
          | succ value =>
              rw [literal, eval_pair_at
                (ih _ (Nat.unpair_lt (by omega))) (ih _ (unpair_right_strict _ (by omega)))]
              rw [Nat.pair_unpair]

/-- A search whose only possible answers are zero and one. It avoids primitive
recursion through the numeric value of a serialized packet merely to test zero. -/
def zeroFlag (test : Code) : Code :=
  .comp (.rfind' (.prec Code.id .zero)) (.pair test .zero)

theorem eval_zeroFlag {test : Code} {t : Nat → Nat}
    (tested : ∀ value, test.eval value = Part.some (t value)) (value : Nat) :
    (zeroFlag test).eval value = Part.some (if t value = 0 then 0 else 1) := by
  have base : ∀ number, (Code.prec Code.id .zero).eval (Nat.pair number 0) = Part.some number := by
    intro number
    simp only [Code.eval_prec_zero, Code.eval_id]
  have one : ∀ number, (Code.prec Code.id .zero).eval (Nat.pair number 1) = Part.some 0 := by
    intro number
    rw [Code.eval_prec_succ, base]
    simp only [Part.bind_eq_bind, Part.bind_some, eval_zero]
  have search : ∀ number, (Code.rfind' (.prec Code.id .zero)).eval (Nat.pair number 0) =
      Part.some (if number = 0 then 0 else 1) := by
    intro number
    rw [Code.eval]
    simp only [Nat.unpaired, Nat.unpair_pair, Nat.add_zero]
    have found : Nat.rfind (fun candidate => (fun result => result = 0) <$>
        (Code.prec Code.id .zero).eval (Nat.pair number candidate)) =
        Part.some (if number = 0 then 0 else 1) := by
      apply Part.eq_some_iff.mpr
      rw [Nat.mem_rfind]
      by_cases zero : number = 0
      · simp [zero, base, Part.map_eq_map]
      · simp only [if_neg zero]
        constructor
        · simp [one, Part.map_eq_map]
        · intro candidate bound
          have same : candidate = 0 := by omega
          subst candidate
          simp [base, zero, Part.map_eq_map]
    rw [found]
    simp only [Part.map_some]
  rw [zeroFlag, Code.eval]
  dsimp only
  rw [eval_pair tested eval_zero]
  simp only [Part.bind_eq_bind, Part.bind_some, search]

/-- Branch on a computed natural while retaining the entire original argument. -/
def ifZero (test yes no : Code) : Code :=
  .comp (.prec yes (.comp no .left)) (.pair Code.id (zeroFlag test))

theorem eval_ifZero {test yes no : Code} {t y n : Nat → Nat}
    (tested : ∀ value, test.eval value = Part.some (t value))
    (positive : ∀ value, yes.eval value = Part.some (y value))
    (negative : ∀ value, no.eval value = Part.some (n value)) (value : Nat) :
    (ifZero test yes no).eval value =
      Part.some (if t value = 0 then y value else n value) := by
  have recursion : ∀ count, (Code.prec yes (.comp no .left)).eval (Nat.pair value count) =
      Part.some (if count = 0 then y value else n value) := by
    intro count
    induction count with
    | zero => simp only [Code.eval_prec_zero, positive, ↓reduceIte]
    | succ count ih =>
        rw [Code.eval_prec_succ, ih]
        simp [Code.eval, Part.bind_eq_bind, negative]
  rw [ifZero, Code.eval]
  dsimp only
  rw [eval_pair Code.eval_id (eval_zeroFlag tested)]
  simp only [Part.bind_eq_bind, Part.bind_some]
  rw [recursion]
  by_cases zero : t value = 0 <;> simp [zero]

theorem eval_zeroFlag_at {test : Code} {input output : Nat}
    (tested : test.eval input = Part.some output) :
    (zeroFlag test).eval input = Part.some (if output = 0 then 0 else 1) := by
  have search := eval_zeroFlag Code.eval_id output
  rw [zeroFlag, Code.eval] at search
  dsimp only at search
  rw [eval_pair_at (Code.eval_id output) (eval_zero output)] at search
  simp only [Part.bind_eq_bind, Part.bind_some] at search
  rw [zeroFlag, Code.eval]
  dsimp only
  rw [eval_pair_at tested (eval_zero input)]
  simpa only [Part.bind_eq_bind, Part.bind_some] using search

theorem eval_ifZero_at {test yes no : Code} {input t y n : Nat}
    (tested : test.eval input = Part.some t)
    (positive : yes.eval input = Part.some y) (negative : no.eval input = Part.some n) :
    (ifZero test yes no).eval input = Part.some (if t = 0 then y else n) := by
  have recursion : ∀ count, (Code.prec yes (.comp no .left)).eval (Nat.pair input count) =
      Part.some (if count = 0 then y else n) := by
    intro count
    induction count with
    | zero => simp only [Code.eval_prec_zero, positive, ↓reduceIte]
    | succ count ih =>
        rw [Code.eval_prec_succ, ih]
        simp [Code.eval, Part.bind_eq_bind, negative]
  rw [ifZero, Code.eval]
  dsimp only
  rw [eval_pair_at (Code.eval_id input) (eval_zeroFlag_at tested)]
  simp only [Part.bind_eq_bind, Part.bind_some]
  rw [recursion]
  by_cases zero : t = 0 <;> simp [zero]

theorem eval_ifZero_zero {test yes no : Code} {input output : Nat}
    (tested : test.eval input = Part.some 0) (positive : yes.eval input = Part.some output) :
    (ifZero test yes no).eval input = Part.some output := by
  rw [ifZero, Code.eval]
  dsimp only
  rw [eval_pair_at (Code.eval_id input) (eval_zeroFlag_at tested)]
  simp only [↓reduceIte, Part.bind_eq_bind, Part.bind_some, Code.eval_prec_zero, positive]

def predecessor : Code :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero Code.id)

theorem eval_predecessor (value : Nat) : predecessor.eval value = Part.some value.pred := by
  have recursion : ∀ count, (Code.prec .zero (.comp .left .right)).eval (Nat.pair 0 count) =
      Part.some count.pred := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih =>
        rw [Code.eval_prec_succ, ih]
        simp [Code.eval, Part.bind_eq_bind]
  rw [predecessor, Code.eval]
  dsimp only
  rw [eval_pair (fun _ => rfl) Code.eval_id]
  simpa only [Part.bind_eq_bind, Part.bind_some] using recursion value

def head : Code := ifZero .left .zero (.comp .left .right)
def tail : Code := ifZero .left .zero
  (.pair (.comp predecessor .left) (.comp .right .right))
def cons (first rest : Code) : Code :=
  .pair (.comp .succ (.comp .left rest)) (.pair first (.comp .right rest))

theorem eval_head (value : Nat) : head.eval value =
    Part.some (if value.unpair.1 = 0 then 0 else value.unpair.2.unpair.1) := by
  exact eval_ifZero eval_left eval_zero (eval_comp eval_left eval_right) value

theorem eval_tail (value : Nat) : tail.eval value = Part.some
    (if value.unpair.1 = 0 then 0 else Nat.pair value.unpair.1.pred value.unpair.2.unpair.2) := by
  exact eval_ifZero eval_left eval_zero
    (eval_pair (eval_comp eval_predecessor eval_left) (eval_comp eval_right eval_right)) value

theorem eval_cons {first rest : Code} {f r : Nat → Nat}
    (firstEval : ∀ value, first.eval value = Part.some (f value))
    (restEval : ∀ value, rest.eval value = Part.some (r value)) (value : Nat) :
    (cons first rest).eval value = Part.some
      (Nat.pair (r value).unpair.1.succ (Nat.pair (f value) (r value).unpair.2)) := by
  exact eval_pair (eval_comp eval_succ (eval_comp eval_left restEval))
    (eval_pair firstEval (eval_comp eval_right restEval)) value

theorem eval_cons_at {first rest : Code} {input f r : Nat}
    (firstEval : first.eval input = Part.some f) (restEval : rest.eval input = Part.some r) :
    (cons first rest).eval input = Part.some (Nat.pair r.unpair.1.succ (Nat.pair f r.unpair.2)) := by
  exact eval_pair_at (eval_comp_at (eval_comp_at restEval (eval_left r)) (eval_succ _))
    (eval_pair_at firstEval (eval_comp_at restEval (eval_right r)))

/-- Compile a literal table; out-of-range indices return zero. -/
def lookup : List Nat → Code
  | [] => .zero
  | first :: rest => ifZero Code.id (literal first) (.comp (lookup rest) predecessor)

theorem eval_lookup (values : List Nat) (index : Nat) :
    (lookup values).eval index = Part.some (values.getD index 0) := by
  induction values generalizing index with
  | nil => rfl
  | cons first rest ih =>
      have after : ∀ value, (Code.comp (lookup rest) predecessor).eval value =
          Part.some (rest.getD value.pred 0) := eval_comp ih eval_predecessor
      rw [lookup, eval_ifZero Code.eval_id (eval_literal first) after]
      cases index <;> rfl

theorem head_encodeList (values : List Nat) :
    (if (encodeList values).unpair.1 = 0 then 0 else (encodeList values).unpair.2.unpair.1) = values.getD 0 0 := by
  cases values <;> simp [encodeList, encodePayload, List.getD]

theorem tail_encodeList (values : List Nat) :
    (if (encodeList values).unpair.1 = 0 then 0 else Nat.pair (encodeList values).unpair.1.pred (encodeList values).unpair.2.unpair.2) = encodeList values.tail := by
  cases values with
  | nil => simp [encodeList, encodePayload, Nat.pair]
  | cons head rest => simp [encodeList, encodePayload]

def drop : Code := .prec Code.id (.comp tail (.comp .right .right))

theorem eval_drop (values : List Nat) (count : Nat) :
    drop.eval (Nat.pair (encodeList values) count) = Part.some (encodeList (values.drop count)) := by
  induction count with
  | zero => simp only [drop, Code.eval_prec_zero, Code.eval_id, List.drop_zero]
  | succ count ih =>
      rw [drop, Code.eval_prec_succ]
      change (drop.eval (Nat.pair (encodeList values) count) >>= _) = _
      rw [ih]
      simp only [Part.bind_eq_bind, Part.bind_some]
      rw [eval_comp eval_tail (eval_comp eval_right eval_right)]
      simp only [Nat.unpair_pair, tail_encodeList]
      congr 2
      rw [← List.drop_one, List.drop_drop]

def get : Code := .comp head drop

theorem eval_get (values : List Nat) (index : Nat) :
    get.eval (Nat.pair (encodeList values) index) = Part.some (values.getD index 0) := by
  rw [get, Code.eval]
  dsimp only
  rw [eval_drop]
  simp only [Part.bind_eq_bind, Part.bind_some, eval_head, head_encodeList]
  congr 1
  simp [List.getD]

/-- Authored indices generate finite syntax; the changing list is a runtime field. -/
def setAt : Nat → Code
  | 0 => ifZero .left .zero (cons .right (.comp tail .left))
  | index + 1 => ifZero .left .zero
      (cons (.comp head .left)
        (.comp (setAt index) (.pair (.comp tail .left) .right)))

theorem eval_setAt (index : Nat) (values : List Nat) (value : Nat) :
    (setAt index).eval (Nat.pair (encodeList values) value) =
      Part.some (encodeList (values.set index value)) := by
  induction index generalizing values value with
  | zero =>
      rw [setAt, eval_ifZero_at (eval_left _) (eval_zero _)
        (eval_cons_at (eval_right _)
          (eval_comp_at (eval_left _) (eval_tail _)))]
      simp only [Nat.unpair_pair, encodeList_eq_zero]
      cases values with
      | nil => simp [encodeList, encodePayload, Nat.pair]
      | cons head rest => simp [encodeList, encodePayload]
  | succ index ih =>
      rw [setAt, eval_ifZero_at (eval_left _) (eval_zero _)
        (eval_cons_at (eval_comp_at (eval_left _) (eval_head _))
          (eval_comp_at (eval_pair_at
            (eval_comp_at (eval_left _) (eval_tail _)) (eval_right _))
            (by simpa only [Nat.unpair_pair, tail_encodeList] using ih values.tail value)))]
      simp only [Nat.unpair_pair, encodeList_eq_zero]
      cases values with
      | nil => simp [encodeList, encodePayload, Nat.pair]
      | cons head rest => simp [encodeList, encodePayload]

/-- The diagonal is exactly the end of a pairing shell. -/
theorem successor_pair_left_zero (first second : Nat) :
    (Nat.pair first second).succ.unpair.1 = 0 ↔ first = second := by
  rcases lt_trichotomy first second with smaller | same | larger
  · have position : (Nat.pair first second).succ.unpair.1 = first + 1 := by
      by_cases boundary : first + 1 = second
      · have packet : (Nat.pair first second).succ = Nat.pair second 0 := by
          simp only [Nat.pair, smaller, if_true, Nat.not_lt_zero, if_false]
          omega
        rw [packet, Nat.unpair_pair, ← boundary]
      · have inside : first + 1 < second := by omega
        have packet : (Nat.pair first second).succ = Nat.pair (first + 1) second := by
          simp [Nat.pair, smaller, inside, Nat.add_assoc]
        rw [packet, Nat.unpair_pair]
    rw [position]
    omega
  · subst second
    have packet : (Nat.pair first first).succ = Nat.pair 0 (first + 1) := by
      simp [Nat.pair]
      ring
    rw [packet, Nat.unpair_pair]
    simp
  · have packet : (Nat.pair first second).succ = Nat.pair first (second + 1) := by
      have right : ¬ first < second + 1 := by omega
      simp [Nat.pair, Nat.not_lt.mpr (Nat.le_of_lt larger), right, Nat.add_assoc]
    rw [packet, Nat.unpair_pair]
    omega

/-- Compare full packets using pair/unpair, with no recursion through their value. -/
def equal (first second : Code) : Code :=
  ifZero (.comp .left (.comp .succ (.pair first second))) (literal 1) .zero

theorem eval_equal {first second : Code} {f g : Nat → Nat}
    (firstEval : ∀ value, first.eval value = Part.some (f value))
    (secondEval : ∀ value, second.eval value = Part.some (g value)) (value : Nat) :
    (equal first second).eval value = Part.some (if f value = g value then 1 else 0) := by
  rw [equal, eval_ifZero
    (eval_comp eval_left (eval_comp eval_succ (eval_pair firstEval secondEval)))
    (eval_literal 1) eval_zero]
  simp only [successor_pair_left_zero]

theorem eval_equal_at {first second : Code} {input f g : Nat}
    (firstEval : first.eval input = Part.some f) (secondEval : second.eval input = Part.some g) :
    (equal first second).eval input = Part.some (if f = g then 1 else 0) := by
  rw [equal, eval_ifZero_at
    (eval_comp_at (eval_comp_at (eval_pair_at firstEval secondEval) (eval_succ _)) (eval_left _))
    (eval_literal 1 input) (eval_zero input)]
  simp only [successor_pair_left_zero]

def payloadDrop : Code := .prec Code.id (.comp .right (.comp .right .right))

private theorem dropPayload_next (count payload : Nat) :
    dropPayload (count + 1) payload = (dropPayload count payload).unpair.2 := by
  induction count generalizing payload with
  | zero => rfl
  | succ count ih => simpa only [dropPayload] using ih payload.unpair.2

theorem eval_payloadDrop (payload count : Nat) :
    payloadDrop.eval (Nat.pair payload count) = Part.some (dropPayload count payload) := by
  induction count with
  | zero => simp only [payloadDrop, Code.eval_prec_zero, Code.eval_id, dropPayload]
  | succ count ih =>
      rw [payloadDrop, Code.eval_prec_succ]
      change (payloadDrop.eval (Nat.pair payload count) >>= _) = _
      rw [ih]
      simp only [Part.bind_eq_bind, Part.bind_some]
      rw [eval_comp eval_right (eval_comp eval_right eval_right)]
      simp only [Nat.unpair_pair, dropPayload_next]

def validWord : Code := ifZero (.comp payloadDrop (.pair .right .left)) (literal 1) .zero

theorem eval_validWord (packet : Nat) : validWord.eval packet =
    Part.some (if dropPayload packet.unpair.1 packet.unpair.2 = 0 then 1 else 0) := by
  rw [validWord, eval_ifZero_at
    (eval_comp_at (eval_pair_at (eval_right packet) (eval_left packet))
      (eval_payloadDrop packet.unpair.2 packet.unpair.1)) (eval_literal 1 packet) (eval_zero packet)]

theorem eval_validWord_encoded (values : List Nat) : validWord.eval (encodeList values) = Part.some 1 := by
  simp only [eval_validWord, encodeList, Nat.unpair_pair, dropPayload_encodePayload, ↓reduceIte]

theorem eval_validWord_canonical (packet : Nat) :
    validWord.eval packet = Part.some (canonicalWord packet).toNat := by
  rw [eval_validWord]
  by_cases exhausted : dropPayload packet.unpair.1 packet.unpair.2 = 0
  · simp [exhausted, (canonicalWord_exhausted packet).mpr exhausted]
  · have refused : canonicalWord packet = false := by
      cases result : canonicalWord packet with
      | false => rfl
      | true => exact False.elim (exhausted ((canonicalWord_exhausted packet).mp result))
    simp [exhausted, refused]

def prefixAll (predicate : Code) : Code :=
  .prec (literal 1) (ifZero (.comp .right .right) .zero
    (.comp predicate (.comp get (.pair .left (.comp .left .right)))))

def listAll (predicate : Code) : Code := .comp (prefixAll predicate) (.pair Code.id .left)

theorem eval_prefixAll {predicate : Code} {test : Nat → Bool}
    (tested : ∀ value, predicate.eval value = Part.some (test value).toNat)
    (values : List Nat) (count : Nat) :
    (prefixAll predicate).eval (Nat.pair (encodeList values) count) =
      Part.some ((List.range count).all (fun index => test (values.getD index 0))).toNat := by
  induction count with
  | zero => simp [prefixAll, Code.eval_prec_zero, eval_literal]
  | succ count ih =>
      rw [prefixAll, Code.eval_prec_succ]
      change ((prefixAll predicate).eval (Nat.pair (encodeList values) count) >>= _) = _
      rw [ih]
      simp only [Part.bind_eq_bind, Part.bind_some]
      let input := Nat.pair (encodeList values)
        (Nat.pair count ((List.range count).all (fun index => test (values.getD index 0))).toNat)
      have previous : (Code.comp .right .right).eval input =
          Part.some ((List.range count).all (fun index => test (values.getD index 0))).toNat := by
        simp [input, Code.eval, Part.bind_eq_bind]
      have position : (Code.pair .left (.comp .left .right)).eval input =
          Part.some (Nat.pair (encodeList values) count) := by
        simp [input, Code.eval, Part.bind_eq_bind, Part.map_eq_map, Seq.seq]
      have item := eval_comp_at (eval_comp_at position (eval_get values count)) (tested _)
      change (ifZero _ _ _).eval input = _
      rw [eval_ifZero_at previous (eval_zero input) item]
      simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
      cases (List.range count).all (fun index => test (values.getD index 0)) <;>
        cases test (values.getD count 0) <;> rfl

theorem eval_listAll {predicate : Code} {test : Nat → Bool}
    (tested : ∀ value, predicate.eval value = Part.some (test value).toNat)
    (values : List Nat) :
    (listAll predicate).eval (encodeList values) = Part.some (values.all test).toNat := by
  have argument : (Code.pair Code.id .left).eval (encodeList values) =
      Part.some (Nat.pair (encodeList values) values.length) := by
    simp [Code.eval, Code.eval_id, encodeList, Part.map_eq_map, Seq.seq]
  rw [listAll, eval_comp_at argument (eval_prefixAll tested values values.length)]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range]
  rw [List.forall_mem_iff_forall_getElem]
  constructor
  · intro all index bound
    simpa [List.getD, bound] using all index bound
  · intro all index bound
    simpa [List.getD, bound] using all index bound

def both (first second : Code) : Code := ifZero first .zero second

theorem eval_both_at {first second : Code} {packet : Nat} {a b : Bool}
    (firstEval : first.eval packet = Part.some a.toNat)
    (secondEval : second.eval packet = Part.some b.toNat) :
    (both first second).eval packet = Part.some (a && b).toNat := by
  rw [both, eval_ifZero_at firstEval (eval_zero _) secondEval]
  cases a <;> cases b <;> rfl

def validList (predicate : Code) : Code := ifZero validWord .zero (listAll predicate)

theorem eval_validList {predicate : Code} {test : Nat → Bool}
    (tested : ∀ value, predicate.eval value = Part.some (test value).toNat) (packet : Nat) :
    (validList predicate).eval packet =
      Part.some (canonicalWord packet && (decodeList packet).all test).toNat := by
  have valid := eval_validWord_canonical packet
  by_cases outer : canonicalWord packet = true
  · have encoded : encodeList (decodeList packet) = packet := of_decide_eq_true outer
    have checked : (listAll predicate).eval packet = Part.some ((decodeList packet).all test).toNat := by
      calc
        (listAll predicate).eval packet = (listAll predicate).eval (encodeList (decodeList packet)) :=
          congrArg (listAll predicate).eval encoded.symm
        _ = _ := eval_listAll tested (decodeList packet)
    rw [validList, eval_ifZero_at valid (eval_zero _) checked]
    simp only [outer, Bool.toNat_true, Nat.one_ne_zero, ↓reduceIte, Bool.true_and]
  · have refused : canonicalWord packet = false := by
      cases result : canonicalWord packet with
      | false => rfl
      | true => exact False.elim (outer result)
    rw [validList, eval_ifZero_zero (by simpa [refused] using valid) (eval_zero _)]
    simp [refused]

def validConfiguration : Code := .comp (validList validWord) (.comp .right .right)

theorem eval_validConfiguration (packet : Nat) :
    validConfiguration.eval packet = Part.some (Configuration.canonical packet).toNat := by
  let words := packet.unpair.2.unpair.2
  have projected : (Code.comp .right .right).eval packet = Part.some words := by
    simp [words, Code.eval, Part.bind_eq_bind]
  rw [validConfiguration, eval_comp_at projected
    (eval_validList (test := canonicalWord) eval_validWord_canonical words)]
  have flags : (canonicalWord words && (decodeList words).all canonicalWord) = Configuration.canonical packet := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Configuration.canonical_columns, words]
  exact congrArg (fun value : Bool => Part.some value.toNat) flags

def contains : List Nat → Code
  | [] => .zero
  | value :: rest => ifZero (equal Code.id (literal value)) (contains rest) (literal 1)

theorem eval_contains (values : List Nat) (packet : Nat) :
    (contains values).eval packet = Part.some (decide (packet ∈ values)).toNat := by
  induction values with
  | nil => simp [contains, eval_zero]
  | cons value rest ih =>
      rw [contains, eval_ifZero_at (eval_equal_at (Code.eval_id packet) (eval_literal value packet))
        ih (eval_literal 1 packet)]
      by_cases same : packet = value
      · simp [same]
      · simp [same]

def ordinal (capacity : Nat) : Code := contains (List.range capacity)

theorem eval_ordinal (capacity packet : Nat) :
    (ordinal capacity).eval packet = Part.some (decide (packet < capacity)).toNat := by
  simp only [ordinal, eval_contains, List.mem_range]

end Programs

namespace Instructions
open Programs

def state : Code := .comp .left .right
def columns : Code := .comp .right .right
def make (label register words : Code) : Code := .pair label (.pair register words)
def word (stack : Nat) : Code := .comp get (.pair columns (literal stack))
def changeWord (stack : Nat) (value : Code) : Code := .comp (setAt stack) (.pair columns value)

theorem eval_state (configuration : Configuration) :
    state.eval configuration.encode = Part.some configuration.state := by
  simp [state, Code.eval, Configuration.encode, Part.bind_eq_bind]

theorem eval_columns (configuration : Configuration) :
    columns.eval configuration.encode = Part.some (encodeList (configuration.columns.map encodeList)) := by
  simp [columns, Code.eval, Configuration.encode, Part.bind_eq_bind]

theorem eval_label (configuration : Configuration) :
    Code.left.eval configuration.encode = Part.some (configuration.label.map Nat.succ |>.getD 0) := by
  simp [Code.eval, Configuration.encode]

private theorem mapWord_lookup (values : List (List Nat)) (index : Nat) :
    (values.map encodeList).getD index 0 = encodeList (values.getD index []) := by
  simp only [List.getD, List.getElem?_map]
  cases values[index]? <;> rfl

theorem eval_word (stack : Nat) (configuration : Configuration) :
    (word stack).eval configuration.encode = Part.some (encodeList (configuration.columns.getD stack [])) := by
  have result := eval_comp_at (eval_pair_at (eval_columns configuration) (eval_literal stack configuration.encode))
    (eval_get (configuration.columns.map encodeList) stack)
  simpa only [word, mapWord_lookup] using result

theorem eval_make {label register words : Code} {l r w : Configuration → Nat}
    (labelEval : ∀ configuration, label.eval configuration.encode = Part.some (l configuration))
    (registerEval : ∀ configuration, register.eval configuration.encode = Part.some (r configuration))
    (wordsEval : ∀ configuration, words.eval configuration.encode = Part.some (w configuration))
    (configuration : Configuration) :
    (make label register words).eval configuration.encode =
      Part.some (Nat.pair (l configuration) (Nat.pair (r configuration) (w configuration))) :=
  eval_pair_at (labelEval configuration) (eval_pair_at (registerEval configuration) (wordsEval configuration))

theorem eval_changeWord {value : Code} {v : Configuration → List Nat}
    (valueEval : ∀ configuration, value.eval configuration.encode = Part.some (encodeList (v configuration)))
    (stack : Nat) (configuration : Configuration) :
    (changeWord stack value).eval configuration.encode =
      Part.some (encodeList ((configuration.columns.set stack (v configuration)).map encodeList)) := by
  have result := eval_comp_at (eval_pair_at (eval_columns configuration) (valueEval configuration))
    (eval_setAt stack (configuration.columns.map encodeList) (encodeList (v configuration)))
  simpa only [changeWord, List.map_set] using result

def table (values : List Nat) : Code := .comp (lookup values) state

theorem eval_table (values : List Nat) (configuration : Configuration) :
    (table values).eval configuration.encode = Part.some (values.getD configuration.state 0) :=
  eval_comp_at (eval_state configuration) (eval_lookup values configuration.state)

def symbol (stack : Nat) : Code := ifZero (word stack) .zero (.comp .succ (.comp head (word stack)))

theorem eval_symbol (stack : Nat) (configuration : Configuration) :
    (symbol stack).eval configuration.encode = Part.some
      (((configuration.columns.getD stack []).head?.map Nat.succ).getD 0) := by
  rw [symbol, eval_ifZero_at (eval_word stack configuration) (eval_zero _)
    (eval_comp_at (eval_comp_at (eval_word stack configuration) (eval_head _)) (eval_succ _))]
  simp only [head_encodeList, encodeList_eq_zero]
  cases configuration.columns.getD stack [] <;> rfl

def table2 (stack : Nat) (values : List (List Nat)) : Code :=
  .comp get (.pair (table (values.map encodeList)) (symbol stack))

theorem eval_table2 (stack : Nat) (values : List (List Nat)) (configuration : Configuration) :
    (table2 stack values).eval configuration.encode = Part.some
      ((values.getD configuration.state []).getD
        (((configuration.columns.getD stack []).head?.map Nat.succ).getD 0) 0) := by
  have tableEval : (table (values.map encodeList)).eval configuration.encode =
      Part.some (encodeList (values.getD configuration.state [])) := by
    simpa only [mapWord_lookup] using eval_table (values.map encodeList) configuration
  exact eval_comp_at (eval_pair_at tableEval (eval_symbol stack configuration)) (eval_get _ _)

theorem compose_configuration {outer inner : Code}
    {function : Configuration → Nat} {transform : Configuration → Configuration}
    (outside : ∀ configuration, outer.eval configuration.encode = Part.some (function configuration))
    (inside : ∀ configuration, inner.eval configuration.encode = Part.some (transform configuration).encode)
    (configuration : Configuration) :
    (Code.comp outer inner).eval configuration.encode = Part.some (function (transform configuration)) :=
  eval_comp_at (inside configuration) (outside (transform configuration))

def pushValue (stack : Nat) (values : List Nat) : Code := cons (table values) (word stack)
def tailWord (stack : Nat) : Code := .comp tail (word stack)

theorem eval_pushValue (stack : Nat) (values : List Nat) (configuration : Configuration) :
    (pushValue stack values).eval configuration.encode = Part.some
      (encodeList (values.getD configuration.state 0 :: configuration.columns.getD stack [])) := by
  rw [pushValue, eval_cons_at (eval_table values configuration) (eval_word stack configuration)]
  simp only [encodeList, Nat.unpair_pair, List.length_cons, encodePayload]

theorem eval_tailWord (stack : Nat) (configuration : Configuration) :
    (tailWord stack).eval configuration.encode = Part.some (encodeList (configuration.columns.getD stack []).tail) := by
  have result := eval_comp_at (eval_word stack configuration) (eval_tail _)
  simpa only [tailWord, tail_encodeList] using result

/-- Structural compilation of all original statement forms into finite code. -/
def compile : Statement → Code
  | .push stack values next => .comp (compile next)
      (make .left state (changeWord stack (pushValue stack values)))
  | .peek stack values next => .comp (compile next)
      (make .left (table2 stack values) columns)
  | .pop stack values next => .comp (compile next)
      (make .left (table2 stack values) (changeWord stack (tailWord stack)))
  | .load values next => .comp (compile next) (make .left (table values) columns)
  | .branch values yes no => ifZero
      (table (values.map (fun value => if value then 1 else 0))) (compile no) (compile yes)
  | .goto values => make (.comp .succ (table values)) state columns
  | .halt => make .zero state columns

theorem eval_compile (statement : Statement) (configuration : Configuration) :
    (compile statement).eval configuration.encode =
      Part.some (statement.run configuration.state configuration.columns).encode := by
  induction statement generalizing configuration with
  | push stack values next ih =>
      have changed : ∀ configuration : Configuration, (make .left state (changeWord stack (pushValue stack values))).eval
          configuration.encode = Part.some
            (Configuration.mk configuration.label configuration.state
              (configuration.columns.set stack
                (values.getD configuration.state 0 :: configuration.columns.getD stack []))).encode := by
        intro configuration
        exact eval_make eval_label eval_state (eval_changeWord (eval_pushValue stack values) stack) configuration
      exact compose_configuration ih changed configuration
  | peek stack values next ih =>
      have changed : ∀ configuration : Configuration, (make .left (table2 stack values) columns).eval configuration.encode =
          Part.some (Configuration.mk configuration.label
            ((values.getD configuration.state []).getD
              (((configuration.columns.getD stack []).head?.map Nat.succ).getD 0) 0)
            configuration.columns).encode := by
        intro configuration
        exact eval_make eval_label (eval_table2 stack values) eval_columns configuration
      exact compose_configuration ih changed configuration
  | pop stack values next ih =>
      have changed : ∀ configuration : Configuration, (make .left (table2 stack values) (changeWord stack (tailWord stack))).eval
          configuration.encode = Part.some (Configuration.mk configuration.label
            ((values.getD configuration.state []).getD
              (((configuration.columns.getD stack []).head?.map Nat.succ).getD 0) 0)
            (configuration.columns.set stack (configuration.columns.getD stack []).tail)).encode := by
        intro configuration
        exact eval_make eval_label (eval_table2 stack values)
          (eval_changeWord (eval_tailWord stack) stack) configuration
      exact compose_configuration ih changed configuration
  | load values next ih =>
      have changed : ∀ configuration : Configuration, (make .left (table values) columns).eval configuration.encode =
          Part.some (Configuration.mk configuration.label (values.getD configuration.state 0)
            configuration.columns).encode := by
        intro configuration
        exact eval_make eval_label (eval_table values) eval_columns configuration
      exact compose_configuration ih changed configuration
  | branch values yes no iy ino =>
      rw [compile, eval_ifZero_at (eval_table _ configuration) (ino configuration) (iy configuration)]
      have tableValue : (values.map (fun value => if value then 1 else 0)).getD configuration.state 0 =
          if values.getD configuration.state false then 1 else 0 := by
        simp only [List.getD, List.getElem?_map]
        have default : ∀ choice : Option Bool,
            (choice.map (fun value => if value then 1 else 0)).getD 0 =
              if choice.getD false then 1 else 0 := by
          intro choice
          cases choice with
          | none => rfl
          | some value => cases value <;> rfl
        exact default _
      rw [tableValue]
      simp only [Statement.run]
      cases values.getD configuration.state false <;> rfl
  | goto values =>
      have labelEval : ∀ configuration : Configuration,
          (Code.comp .succ (table values)).eval configuration.encode =
            Part.some ((values.getD configuration.state 0).succ) := by
        intro configuration
        exact eval_comp_at (eval_table values configuration) (eval_succ _)
      exact eval_make labelEval eval_state eval_columns configuration
  | halt => exact eval_make (fun _ => eval_zero _) eval_state eval_columns configuration

end Instructions

namespace Machines
open Programs Instructions

def encodeOption (configuration : Option Configuration) : Nat :=
  (configuration.map (fun value => value.encode.succ)).getD 0

theorem encodeOption_injective : Function.Injective encodeOption := by
  intro first second same
  cases first with
  | none => cases second <;> simp [encodeOption] at same ⊢
  | some first =>
      cases second with
      | none => simp [encodeOption] at same
      | some second =>
          simp only [encodeOption, Option.map_some, Option.getD_some, Nat.succ_inj] at same
          exact congrArg some (Configuration.encode_injective same)

/-- Label dispatch is compiled from the literal finite program list. -/
def dispatch : List Statement → Code
  | [] => .zero
  | statement :: rest => ifZero .right
      (.comp .succ (.comp (Instructions.compile statement) .left))
      (.comp (dispatch rest) (.pair .left (.comp predecessor .right)))

theorem eval_dispatch (program : List Statement) (configuration : Configuration) (index : Nat) :
    (dispatch program).eval (Nat.pair configuration.encode index) = Part.some (encodeOption
      (program[index]?.map (fun statement => statement.run configuration.state configuration.columns))) := by
  induction program generalizing index with
  | nil => rfl
  | cons statement rest ih =>
      have first : Code.left.eval (Nat.pair configuration.encode index) = Part.some configuration.encode := by
        simpa only [Nat.unpair_pair] using eval_left (Nat.pair configuration.encode index)
      have second : Code.right.eval (Nat.pair configuration.encode index) = Part.some index := by
        simpa only [Nat.unpair_pair] using eval_right (Nat.pair configuration.encode index)
      rw [dispatch, eval_ifZero_at second
        (eval_comp_at (eval_comp_at first (eval_compile statement configuration)) (eval_succ _))
        (eval_comp_at (eval_pair_at first (eval_comp_at second (eval_predecessor index))) (ih index.pred))]
      cases index <;> simp [encodeOption]

def step (descriptor : Descriptor) : Code :=
  ifZero .left .zero (.comp (dispatch descriptor.program)
    (.pair Code.id (.comp predecessor .left)))

theorem eval_step (descriptor : Descriptor) (configuration : Configuration) :
    (step descriptor).eval configuration.encode = Part.some (encodeOption (descriptor.step configuration)) := by
  have first := Instructions.eval_label configuration
  have changed := eval_pair_at (Code.eval_id configuration.encode)
    (eval_comp_at first (eval_predecessor _))
  rw [step, eval_ifZero_at first (eval_zero _) (eval_comp_at changed (eval_dispatch descriptor.program configuration _))]
  cases configuration with
  | mk label register words => cases label <;> simp [Descriptor.step, encodeOption]

/-- The generated code checks the actual original step on every complete configuration. -/
theorem original_step {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (configuration : machine.Cfg) :
    (step profile.descriptor).eval (profile.encodeConfiguration configuration).encode =
      Part.some (encodeOption ((machine.step configuration).map profile.encodeConfiguration)) := by
  rw [eval_step, profile.descriptor_step]

end Machines

namespace Traces
open Programs

def current : Code := .comp .left .right
def remaining : Code := .comp .right .right
def cursor (value rest : Code) : Code := .pair (literal 1) (.pair value rest)

theorem eval_current (configuration : Configuration) (trace : List Configuration) :
    current.eval (TraceCursor.encode (some (configuration, trace))) = Part.some configuration.encode := by
  simp [current, TraceCursor.encode, Code.eval, Part.bind_eq_bind]

theorem eval_remaining (configuration : Configuration) (trace : List Configuration) :
    remaining.eval (TraceCursor.encode (some (configuration, trace))) =
      Part.some (encodeList (trace.map Configuration.encode)) := by
  simp [remaining, TraceCursor.encode, Code.eval, Part.bind_eq_bind]

private theorem encode_cursor_nonzero (configuration : Configuration) (trace : List Configuration) :
    TraceCursor.encode (some (configuration, trace)) ≠ 0 := by
  intro zero
  have lower := Nat.left_le_pair 1 (Nat.pair configuration.encode (encodeList (trace.map Configuration.encode)))
  rw [← TraceCursor.encode, zero] at lower
  omega

def advance (descriptor : Descriptor) : Code :=
  ifZero Code.id .zero
    (ifZero remaining .zero
      (ifZero (equal (.comp (Machines.step descriptor) current) (.comp .succ (.comp head remaining)))
        .zero (cursor (.comp head remaining) (.comp tail remaining))))

theorem eval_advance (descriptor : Descriptor) (position : TraceCursor.Cursor) :
    (advance descriptor).eval (TraceCursor.encode position) =
      Part.some (TraceCursor.encode (TraceCursor.advance descriptor position)) := by
  cases position with
  | none => exact eval_ifZero_zero (Code.eval_id 0) (eval_zero 0)
  | some pair =>
      rcases pair with ⟨configuration, trace⟩
      let packet := TraceCursor.encode (some (configuration, trace))
      have body : (ifZero remaining .zero
          (ifZero (equal (.comp (Machines.step descriptor) current) (.comp .succ (.comp head remaining)))
            .zero (cursor (.comp head remaining) (.comp tail remaining)))).eval packet =
          Part.some (TraceCursor.encode (TraceCursor.advance descriptor (some (configuration, trace)))) := by
        cases trace with
        | nil =>
            apply eval_ifZero_zero
            · simpa [encodeList, encodePayload, Nat.pair] using eval_remaining configuration []
            · exact eval_zero packet
        | cons next rest =>
            have nextEval : (Code.comp head remaining).eval packet = Part.some next.encode := by
              simpa only [head_encodeList, List.map_cons, List.getD_cons_zero] using
                eval_comp_at (eval_remaining configuration (next :: rest)) (eval_head _)
            have restEval : (Code.comp tail remaining).eval packet =
                Part.some (encodeList (rest.map Configuration.encode)) := by
              simpa only [tail_encodeList, List.map_cons, List.tail_cons] using
                eval_comp_at (eval_remaining configuration (next :: rest)) (eval_tail _)
            have expected := eval_comp_at (eval_current configuration (next :: rest))
              (Machines.eval_step descriptor configuration)
            have computed := eval_equal_at expected (eval_comp_at nextEval (eval_succ _))
            have rebuilt : (cursor (Code.comp head remaining) (Code.comp tail remaining)).eval packet =
                Part.some (TraceCursor.encode (some (next, rest))) :=
              eval_pair_at (eval_literal 1 packet) (eval_pair_at nextEval restEval)
            have edge : Machines.encodeOption (descriptor.step configuration) = next.encode.succ ↔
                descriptor.step configuration = some next :=
              Machines.encodeOption_injective.eq_iff (a := descriptor.step configuration) (b := some next)
            rw [eval_ifZero_at (eval_remaining configuration (next :: rest)) (eval_zero packet)
              (eval_ifZero_at computed (eval_zero packet) rebuilt)]
            simp only [edge, encodeList_eq_zero, List.map_cons, List.cons_ne_nil, ↓reduceIte]
            by_cases valid : descriptor.step configuration = some next
            · simp [TraceCursor.advance, valid, TraceCursor.encode]
            · simp [TraceCursor.advance, valid, TraceCursor.encode]
      rw [advance, eval_ifZero_at (Code.eval_id packet) (eval_zero packet) body]
      simp only [packet, encode_cursor_nonzero, ↓reduceIte]

def canonical (descriptor : Descriptor) (label : Option Nat) (stack : Nat) (word : Code) : Code :=
  Instructions.make (literal (label.map Nat.succ |>.getD 0)) (literal descriptor.initialState)
    (.comp (setAt stack) (.pair (literal (encodeList (List.replicate descriptor.stackCount 0))) word))

theorem eval_canonical {word : Code} (words : List Nat) (packet : Nat)
    (wordEval : word.eval packet = Part.some (encodeList words))
    (descriptor : Descriptor) (label : Option Nat) (stack : Nat) :
    (canonical descriptor label stack word).eval packet = Part.some
      (Configuration.mk label descriptor.initialState ((List.replicate descriptor.stackCount []).set stack words)).encode := by
  have columns := eval_comp_at
    (eval_pair_at (eval_literal (encodeList (List.replicate descriptor.stackCount 0)) packet) wordEval)
    (eval_setAt stack (List.replicate descriptor.stackCount 0) (encodeList words))
  rw [canonical, Instructions.make, eval_pair_at (eval_literal _ packet)
    (eval_pair_at (eval_literal _ packet) columns)]
  have empty : encodeList ([] : List Nat) = 0 := rfl
  simp only [Configuration.encode, List.map_set, List.map_replicate, empty]

def initial (descriptor : Descriptor) : Code :=
  cursor (canonical descriptor (some descriptor.main) descriptor.inputStack .left) (.comp .right .right)

theorem eval_initial (descriptor : Descriptor) (request : Request) :
    (initial descriptor).eval request.payload = Part.some
      (TraceCursor.encode (some (descriptor.initial request.input, request.trace))) := by
  have wordEval : Code.left.eval request.payload = Part.some (encodeList request.input) := by
    simp [Code.eval, Request.payload]
  have traceEval : (Code.comp .right .right).eval request.payload =
      Part.some (encodeList (request.trace.map Configuration.encode)) := by
    simp [Code.eval, Request.payload, Part.bind_eq_bind]
  exact eval_pair_at (eval_literal 1 request.payload)
    (eval_pair_at (eval_canonical request.input request.payload wordEval descriptor _ _) traceEval)

def fold (descriptor : Descriptor) : Code :=
  .prec (initial descriptor) (.comp (advance descriptor) (.comp .right .right))

theorem eval_fold (descriptor : Descriptor) (request : Request) (count : Nat) :
    (fold descriptor).eval (Nat.pair request.payload count) = Part.some
      (TraceCursor.encode (TraceCursor.run descriptor count (some (descriptor.initial request.input, request.trace)))) := by
  induction count with
  | zero => simpa only [fold, Code.eval_prec_zero, TraceCursor.run,
      Function.iterate_zero, id_eq] using eval_initial descriptor request
  | succ count ih =>
      rw [fold, Code.eval_prec_succ]
      change ((fold descriptor).eval (Nat.pair request.payload count) >>= _) = _
      rw [ih]
      simp only [Part.bind_eq_bind, Part.bind_some]
      have previous : (Code.comp .right .right).eval
          (Nat.pair request.payload (Nat.pair count (TraceCursor.encode (TraceCursor.run descriptor count
            (some (descriptor.initial request.input, request.trace)))))) =
          Part.some (TraceCursor.encode (TraceCursor.run descriptor count
            (some (descriptor.initial request.input, request.trace)))) := by
        simp [Code.eval, Part.bind_eq_bind]
      rw [eval_comp_at previous (eval_advance descriptor _)]
      simp only [TraceCursor.run, Function.iterate_succ_apply']

def finish (descriptor : Descriptor) : Code :=
  ifZero .right .zero
    (ifZero (.comp remaining .right)
      (equal (.comp current .right)
        (canonical descriptor none descriptor.outputStack (.comp .left (.comp .right .left)))) .zero)

theorem eval_finish (descriptor : Descriptor) (request : Request) (position : TraceCursor.Cursor) :
    (finish descriptor).eval (Nat.pair request.payload (TraceCursor.encode position)) =
      Part.some (if position = some (descriptor.terminal request.output, []) then 1 else 0) := by
  cases position with
  | none =>
      have test : Code.right.eval (Nat.pair request.payload (TraceCursor.encode none)) = Part.some 0 := by
        simp [Code.eval, TraceCursor.encode]
      exact eval_ifZero_zero test (eval_zero _)
  | some pair =>
      rcases pair with ⟨configuration, rest⟩
      let packet := Nat.pair request.payload (TraceCursor.encode (some (configuration, rest)))
      have currentPosition : Code.right.eval packet = Part.some (TraceCursor.encode (some (configuration, rest))) := by
        simp [packet, Code.eval]
      have words : (Code.comp .left (.comp .right .left)).eval packet = Part.some (encodeList request.output) := by
        simp [packet, Code.eval, Request.payload, Part.bind_eq_bind]
      have expected := eval_canonical request.output packet words descriptor none descriptor.outputStack
      have computed := eval_equal_at
        (eval_comp_at currentPosition (eval_current configuration rest)) expected
      have body := eval_ifZero_at (eval_comp_at currentPosition (eval_remaining configuration rest))
        computed (eval_zero packet)
      rw [finish, eval_ifZero_at currentPosition (eval_zero packet) body]
      simp only [encode_cursor_nonzero, encodeList_eq_zero, ↓reduceIte]
      cases rest with
      | nil => simp [Descriptor.terminal, Configuration.encode_injective.eq_iff]
      | cons next rest => simp

def coreChecker (descriptor : Descriptor) : Code :=
  .comp (finish descriptor) (.pair .left (fold descriptor))

theorem eval_coreChecker (descriptor : Descriptor) (request : Request) :
    (coreChecker descriptor).eval request.encode = Part.some (if request.check descriptor then 1 else 0) := by
  have first : Code.left.eval request.encode = Part.some request.payload := by simp [Code.eval, Request.encode]
  have computed := eval_pair_at first (eval_fold descriptor request request.count)
  have final := eval_comp_at computed (eval_finish descriptor request _)
  simpa only [coreChecker, Request.check, TraceCursor.accepts, decide_eq_true_eq] using final

def inputWord : Code := .comp .left .left
def outputWord : Code := .comp .left (.comp .right .left)
def traceWord : Code := .comp .right (.comp .right .left)
def matchingCount : Code := equal (.comp .left traceWord) .right

def validRequest : Code :=
  both (.comp validWord inputWord)
    (both (.comp validWord outputWord) (.comp (validList validConfiguration) traceWord))

theorem eval_validRequest (packet : Nat) :
    validRequest.eval packet = Part.some (Request.canonical packet).toNat := by
  have inputEval : inputWord.eval packet = Part.some packet.unpair.1.unpair.1 := by
    simp [inputWord, Code.eval, Part.bind_eq_bind]
  have outputEval : outputWord.eval packet = Part.some packet.unpair.1.unpair.2.unpair.1 := by
    simp [outputWord, Code.eval, Part.bind_eq_bind]
  have traceEval : traceWord.eval packet = Part.some packet.unpair.1.unpair.2.unpair.2 := by
    simp [traceWord, Code.eval, Part.bind_eq_bind]
  rw [validRequest, eval_both_at (eval_comp_at inputEval (eval_validWord_canonical _))
    (eval_both_at (eval_comp_at outputEval (eval_validWord_canonical _))
      (eval_comp_at traceEval
        (eval_validList (test := Configuration.canonical) eval_validConfiguration _)))]
  have flags : (canonicalWord packet.unpair.1.unpair.1 &&
      (canonicalWord packet.unpair.1.unpair.2.unpair.1 &&
        (canonicalWord packet.unpair.1.unpair.2.unpair.2 &&
          (decodeList packet.unpair.1.unpair.2.unpair.2).all Configuration.canonical))) =
      Request.canonical packet := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Request.canonical_fields]
  exact congrArg (fun value : Bool => Part.some value.toNat) flags

/-- Exhaust input/output payloads and reject an incorrect transition count before replay. -/
def replayChecker (descriptor : Descriptor) : Code :=
  ifZero (.comp validWord inputWord) .zero
    (ifZero (.comp validWord outputWord) .zero
      (ifZero matchingCount .zero (coreChecker descriptor)))

theorem eval_replayChecker (descriptor : Descriptor) (request : Request) :
    (replayChecker descriptor).eval request.encode = Part.some (if request.check descriptor then 1 else 0) := by
  have inputEval : inputWord.eval request.encode = Part.some (encodeList request.input) := by
    simp [inputWord, Code.eval, Request.encode, Request.payload, Part.bind_eq_bind]
  have outputEval : outputWord.eval request.encode = Part.some (encodeList request.output) := by
    simp [outputWord, Code.eval, Request.encode, Request.payload, Part.bind_eq_bind]
  have lengthEval : (Code.comp .left traceWord).eval request.encode = Part.some request.trace.length := by
    simp [traceWord, Code.eval, Request.encode, Request.payload, encodeList, Part.bind_eq_bind]
  have countEval : Code.right.eval request.encode = Part.some request.count := by
    simp [Code.eval, Request.encode]
  rw [replayChecker, matchingCount, eval_ifZero_at (eval_comp_at inputEval (eval_validWord_encoded request.input))
    (eval_zero _) (eval_ifZero_at (eval_comp_at outputEval (eval_validWord_encoded request.output))
      (eval_zero _) (eval_ifZero_at (eval_equal_at lengthEval countEval)
        (eval_zero _) (eval_coreChecker descriptor request)))]
  simp only [Nat.one_ne_zero, ↓reduceIte]
  by_cases same : request.trace.length = request.count
  · simp [same]
  · have refused : request.check descriptor = false := by
      cases result : request.check descriptor with
      | false => rfl
      | true => exact False.elim (same ((TraceCursor.accepts_iff descriptor _ _ _ _).mp result).1)
    simp [same, refused]

/-- Validate every serialized configuration before checking its actual transition. -/
def checker (descriptor : Descriptor) : Code := ifZero validRequest .zero (replayChecker descriptor)

theorem eval_checker (descriptor : Descriptor) (request : Request) :
    (checker descriptor).eval request.encode = Part.some (if request.check descriptor then 1 else 0) := by
  have valid : validRequest.eval request.encode = Part.some 1 := by
    rw [eval_validRequest]
    simp [Request.canonical, Request.decode_encode]
  rw [checker, eval_ifZero_at valid (eval_zero _) (eval_replayChecker descriptor request)]
  simp only [Nat.one_ne_zero, ↓reduceIte]

theorem eval_checker_packet (descriptor : Descriptor) (packet : Nat) :
    (checker descriptor).eval packet = Part.some
      (if Request.canonical packet then
        if (Request.decode packet).check descriptor then 1 else 0 else 0) := by
  cases result : Request.canonical packet with
  | false =>
      have refused : validRequest.eval packet = Part.some 0 := by
        simp only [eval_validRequest, result, Bool.toNat_false]
      rw [checker, eval_ifZero_zero refused (eval_zero _)]
      simp
  | true =>
      have encoded : (Request.decode packet).encode = packet := of_decide_eq_true result
      have exactEval := (congrArg (checker descriptor).eval encoded).symm.trans
        (eval_checker descriptor (Request.decode packet))
      simpa only [result, ↓reduceIte] using exactEval

theorem accepted_raw_iff (descriptor : Descriptor) (packet : Nat) :
    (checker descriptor).eval packet = Part.some 1 ↔
      Request.canonical packet = true ∧ (Request.decode packet).check descriptor = true := by
  rw [eval_checker_packet]
  cases Request.canonical packet <;> cases (Request.decode packet).check descriptor <;> simp

theorem malformed_refused (descriptor : Descriptor) (packet : Nat)
    (malformed : Request.read packet = none) : (checker descriptor).eval packet = Part.some 0 := by
  have invalid : Request.canonical packet = false := by
    cases result : Request.canonical packet with
    | false => rfl
    | true =>
        have canonical : (Request.decode packet).encode = packet := of_decide_eq_true result
        simp only [Request.read, canonical, ↓reduceIte] at malformed
        cases malformed
  simp only [eval_checker_packet, invalid, Bool.false_eq_true, if_false]

theorem accepted_iff (descriptor : Descriptor) (request : Request) :
    (checker descriptor).eval request.encode = Part.some 1 ↔ request.check descriptor = true := by
  rw [eval_checker]
  cases request.check descriptor <;> simp

theorem eval_checker_read (descriptor : Descriptor) {packet : Nat} {request : Request}
    (decoded : Request.read packet = some request) :
    (checker descriptor).eval packet = Part.some (if request.check descriptor then 1 else 0) := by
  rw [← Request.read_canonical decoded]
  exact eval_checker descriptor request

theorem accepted_packet_iff (descriptor : Descriptor) {packet : Nat} {request : Request}
    (decoded : Request.read packet = some request) :
    (checker descriptor).eval packet = Part.some 1 ↔ request.check descriptor = true := by
  rw [← Request.read_canonical decoded]
  exact accepted_iff descriptor request

theorem refused (descriptor : Descriptor) (request : Request) (rejected : request.check descriptor = false) :
    (checker descriptor).eval request.encode = Part.some 0 := by
  simp only [eval_checker, rejected, Bool.false_eq_true, if_false]

theorem bounded_iff (descriptor : Descriptor) (request : Request) :
    (∃ fuel, UniversalEffectiveEvidence.check (checker descriptor) request.encode 1 fuel = true) ↔
      request.check descriptor = true := by
  rw [← UniversalEffectiveEvidence.graph_iff_evidence, ← Part.eq_some_iff, accepted_iff]

/-- Original alphabet ranges are finite authored data, not totalized table defaults. -/
def originalChecker (descriptor : Descriptor) (inputCapacity outputCapacity : Nat) : Code :=
  ifZero (checker descriptor) .zero
    (both (.comp (listAll (ordinal inputCapacity)) inputWord)
      (.comp (listAll (ordinal outputCapacity)) outputWord))

def originalAccepted (descriptor : Descriptor) (inputCapacity outputCapacity packet : Nat) : Bool :=
  Request.canonical packet && (Request.decode packet).check descriptor &&
    (Request.decode packet).input.all (fun value => decide (value < inputCapacity)) &&
      (Request.decode packet).output.all (fun value => decide (value < outputCapacity))

theorem eval_originalChecker_request (descriptor : Descriptor) (inputCapacity outputCapacity : Nat)
    (request : Request) :
    (originalChecker descriptor inputCapacity outputCapacity).eval request.encode =
      Part.some (if request.check descriptor then
        (request.input.all (fun value => decide (value < inputCapacity)) &&
          request.output.all (fun value => decide (value < outputCapacity))).toNat else 0) := by
  have inputEval : inputWord.eval request.encode = Part.some (encodeList request.input) := by
    simp [inputWord, Code.eval, Request.encode, Request.payload, Part.bind_eq_bind]
  have outputEval : outputWord.eval request.encode = Part.some (encodeList request.output) := by
    simp [outputWord, Code.eval, Request.encode, Request.payload, Part.bind_eq_bind]
  have words := eval_both_at
    (eval_comp_at inputEval (eval_listAll (test := fun value => decide (value < inputCapacity))
      (eval_ordinal inputCapacity) request.input))
    (eval_comp_at outputEval (eval_listAll (test := fun value => decide (value < outputCapacity))
      (eval_ordinal outputCapacity) request.output))
  rw [originalChecker, eval_ifZero_at (eval_checker descriptor request) (eval_zero _) words]
  cases request.check descriptor <;> simp

theorem eval_originalChecker (descriptor : Descriptor) (inputCapacity outputCapacity packet : Nat) :
    (originalChecker descriptor inputCapacity outputCapacity).eval packet =
      Part.some (originalAccepted descriptor inputCapacity outputCapacity packet).toNat := by
  cases canonical : Request.canonical packet with
  | false =>
      have rejected : (checker descriptor).eval packet = Part.some 0 := by
        simp only [eval_checker_packet, canonical, Bool.false_eq_true, if_false]
      rw [originalChecker, eval_ifZero_zero rejected (eval_zero _)]
      simp only [originalAccepted, canonical, Bool.false_and, Bool.toNat_false]
  | true =>
      have encoded : (Request.decode packet).encode = packet := of_decide_eq_true canonical
      have computed := (congrArg (originalChecker descriptor inputCapacity outputCapacity).eval encoded).symm.trans
        (eval_originalChecker_request descriptor inputCapacity outputCapacity (Request.decode packet))
      rw [computed]
      simp only [originalAccepted, canonical, Bool.true_and]
      cases (Request.decode packet).check descriptor <;>
        cases (Request.decode packet).input.all (fun value => decide (value < inputCapacity)) <;>
        cases (Request.decode packet).output.all (fun value => decide (value < outputCapacity)) <;>
        rfl

theorem originalAccepted_iff (descriptor : Descriptor) (inputCapacity outputCapacity packet : Nat) :
    (originalChecker descriptor inputCapacity outputCapacity).eval packet = Part.some 1 ↔
      Request.canonical packet = true ∧ (Request.decode packet).check descriptor = true ∧
        (Request.decode packet).input.all (fun value => decide (value < inputCapacity)) = true ∧
          (Request.decode packet).output.all (fun value => decide (value < outputCapacity)) = true := by
  rw [eval_originalChecker]
  have toNat : ∀ value : Bool, Part.some value.toNat = Part.some 1 ↔ value = true := by
    intro value
    cases value <;> simp
  rw [toNat]
  simp only [originalAccepted, Bool.and_eq_true, and_assoc]

theorem eval_originalChecker_typed {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁)) (request : Request)
    (inputEncoded : profile.encodeWord machine.k₀ input = request.input)
    (outputEncoded : profile.encodeWord machine.k₁ output = request.output) :
    (originalChecker profile.descriptor (profile.symbols machine.k₀) (profile.symbols machine.k₁)).eval
      request.encode = Part.some (if request.check profile.descriptor then 1 else 0) := by
  have inputWithin : request.input.all (fun value => decide (value < profile.symbols machine.k₀)) = true := by
    rw [← inputEncoded]
    exact profile.wordWithin_encodeWord machine.k₀ input
  have outputWithin : request.output.all (fun value => decide (value < profile.symbols machine.k₁)) = true := by
    rw [← outputEncoded]
    exact profile.wordWithin_encodeWord machine.k₁ output
  simp only [eval_originalChecker_request, inputWithin, outputWithin, Bool.and_self, Bool.toNat_true]

/-- Decode the actual serialized transition data before generating finite syntax. -/
def generate (packet : Nat) : Option Code := (Descriptor.decode packet).map checker

theorem generate_encoded (descriptor : Descriptor) : generate descriptor.encode = some (checker descriptor) := by
  simp only [generate, Descriptor.decode_encode, Option.map_some]

theorem generate_refused (packet : Nat) (malformed : Descriptor.decode packet = none) :
    generate packet = none := by simp only [generate, malformed, Option.map_none]

/-- Structural wire decoding is the practical descriptor input interface. -/
def generateBytes (word : List Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet) : Option Code :=
  (Bytes.decodeDescriptor word).map checker

theorem generateBytes_encoded (descriptor : Descriptor) :
    generateBytes (Bytes.encodeDescriptor descriptor) = some (checker descriptor) := by
  simp only [generateBytes, Bytes.descriptor_roundtrip, Option.map_some]

theorem generateBytes_refused (word : List Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet)
    (malformed : Bytes.decodeDescriptor word = none) : generateBytes word = none := by
  simp only [generateBytes, malformed, Option.map_none]

def generateOriginalBytes (word : List Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet) : Option Code :=
  (Bytes.decodeOriginalDescriptor word).map (fun descriptor =>
    originalChecker descriptor.program descriptor.inputCapacity descriptor.outputCapacity)

theorem generateOriginalBytes_encoded (descriptor : OriginalDescriptor) :
    generateOriginalBytes (Bytes.encodeOriginalDescriptor descriptor) =
      some (originalChecker descriptor.program descriptor.inputCapacity descriptor.outputCapacity) := by
  simp only [generateOriginalBytes, Bytes.originalDescriptor_roundtrip, Option.map_some]

def originalOfAlignedCheck {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁))
    (request : Request)
    (inputEncoded : profile.encodeWord machine.k₀ input = request.input)
    (outputEncoded : profile.encodeWord machine.k₁ output = request.output)
    (checked : request.check profile.descriptor = true) :
    Turing.TM2OutputsInTime machine input (some output) request.count := by
  have complete := (TraceCursor.accepts_iff profile.descriptor request.input request.output
    request.count request.trace).mp checked
  have aligned : profile.descriptor.accepts (profile.encodeWord machine.k₀ input)
      (profile.encodeWord machine.k₁ output) request.trace = true := by
    rw [inputEncoded, outputEncoded]
    exact complete.2
  have execution := profile.accepts_reflects input output request.trace aligned
  simpa only [complete.1] using execution

/-- Both typed words are decoded by the finite profile; no word-alignment or
checker-soundness premise is supplied by the caller. -/
structure OriginalExecution {machine : Turing.FinTM2} (profile : FiniteProfile machine) (packet : Nat) where
  input : List (machine.Γ machine.k₀)
  output : List (machine.Γ machine.k₁)
  canonical : Request.canonical packet = true
  inputEncoding : profile.encodeWord machine.k₀ input = (Request.decode packet).input
  outputEncoding : profile.encodeWord machine.k₁ output = (Request.decode packet).output
  execution : Turing.TM2OutputsInTime machine input (some output) (Request.decode packet).count

def originalExecutionFromCode {machine : Turing.FinTM2} (profile : FiniteProfile machine) (packet : Nat)
    (accepted : (originalChecker profile.descriptor (profile.symbols machine.k₀)
      (profile.symbols machine.k₁)).eval packet = Part.some 1) : OriginalExecution profile packet := by
  have evidence := (originalAccepted_iff profile.descriptor (profile.symbols machine.k₀)
    (profile.symbols machine.k₁) packet).mp accepted
  let input := profile.checkedWord machine.k₀ (Request.decode packet).input evidence.2.2.1
  let output := profile.checkedWord machine.k₁ (Request.decode packet).output evidence.2.2.2
  have inputEncoded := profile.encode_checkedWord machine.k₀ (Request.decode packet).input evidence.2.2.1
  have outputEncoded := profile.encode_checkedWord machine.k₁ (Request.decode packet).output evidence.2.2.2
  exact ⟨input, output, evidence.1, inputEncoded, outputEncoded,
    originalOfAlignedCheck profile input output (Request.decode packet)
      inputEncoded outputEncoded evidence.2.1⟩

theorem originalChecker_complete {machine : Turing.FinTM2} (profile : FiniteProfile machine) :
    (∃ packet, (originalChecker profile.descriptor (profile.symbols machine.k₀)
      (profile.symbols machine.k₁)).eval packet = Part.some 1) ↔
      ∃ input output, Nonempty (Turing.TM2Outputs machine input (some output)) := by
  constructor
  · rintro ⟨packet, accepted⟩
    let execution := originalExecutionFromCode profile packet accepted
    exact ⟨execution.input, execution.output, ⟨execution.execution.toEvalsTo⟩⟩
  · rintro ⟨input, output, execution⟩
    obtain ⟨trace, accepted⟩ := (profile.accepts_iff_original input output).mpr execution
    let request : Request := ⟨profile.encodeWord machine.k₀ input,
      profile.encodeWord machine.k₁ output, trace, trace.length⟩
    have checked : request.check profile.descriptor = true :=
      (TraceCursor.accepts_iff profile.descriptor _ _ _ _).mpr ⟨rfl, accepted⟩
    exact ⟨request.encode, by
      rw [eval_originalChecker_typed profile input output request rfl rfl, checked]
      rfl⟩

def originalExecution {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁))
    (trace : List Configuration) (count fuel : Nat)
    (accepted : UniversalEffectiveEvidence.check (checker profile.descriptor)
      (Request.mk (profile.encodeWord machine.k₀ input) (profile.encodeWord machine.k₁ output)
        trace count).encode 1 fuel = true) :
    Turing.TM2OutputsInTime machine input (some output) count := by
  have checked := (bounded_iff profile.descriptor _).mp ⟨fuel, accepted⟩
  have complete := (TraceCursor.accepts_iff profile.descriptor _ _ count trace).mp checked
  have execution := profile.accepts_reflects input output trace complete.2
  simpa only [complete.1] using execution

theorem original_iff {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁)) :
    (∃ trace count fuel, UniversalEffectiveEvidence.check (checker profile.descriptor)
      (Request.mk (profile.encodeWord machine.k₀ input) (profile.encodeWord machine.k₁ output)
        trace count).encode 1 fuel = true) ↔
      Nonempty (Turing.TM2Outputs machine input (some output)) := by
  constructor
  · rintro ⟨trace, count, fuel, accepted⟩
    exact ⟨(originalExecution profile input output trace count fuel accepted).toEvalsTo⟩
  · intro execution
    obtain ⟨trace, accepted⟩ := (profile.accepts_iff_original input output).mpr execution
    have check : (Request.mk (profile.encodeWord machine.k₀ input) (profile.encodeWord machine.k₁ output)
        trace trace.length).check profile.descriptor = true := by
      exact (TraceCursor.accepts_iff profile.descriptor _ _ _ _).mpr ⟨rfl, accepted⟩
    obtain ⟨fuel, bounded⟩ := (bounded_iff profile.descriptor _).mpr check
    exact ⟨trace, trace.length, fuel, bounded⟩

def codeNodes : Code → Nat
  | .zero | .succ | .left | .right => 1
  | .pair first second | .comp first second | .prec first second =>
      1 + codeNodes first + codeNodes second
  | .rfind' next => 1 + codeNodes next

private theorem pair_size_bound (first second : Nat) :
    (Nat.pair first second).size ≤ 2 * max first.size second.size := by
  apply Nat.size_le.mpr
  have firstBound : first < 2 ^ max first.size second.size := Nat.size_le.mp (le_max_left _ _)
  have secondBound : second < 2 ^ max first.size second.size := Nat.size_le.mp (le_max_right _ _)
  have maximum : max first second + 1 ≤ 2 ^ max first.size second.size := by omega
  calc
    Nat.pair first second < (max first second + 1) ^ 2 := Nat.pair_lt_max_add_one_sq _ _
    _ ≤ (2 ^ max first.size second.size) ^ 2 := Nat.pow_le_pow_left maximum 2
    _ = 2 ^ (2 * max first.size second.size) := by rw [← pow_mul, Nat.mul_comm]

private theorem radix_size_bound (value tag : Nat) (small : tag ≤ 7) :
    (4 * value + tag).size ≤ value.size + 3 := by
  apply Nat.size_le.mpr
  have bound : value < 2 ^ value.size := Nat.lt_size_self value
  rw [pow_add]
  norm_num
  omega

/-- A bit upper bound computed from syntax, without materializing the possibly
enormous numeric code encoding. Its exponential growth remains visible. -/
def codeNumericBitBound : Code → Nat
  | .zero | .succ | .left | .right => 2
  | .pair first second | .comp first second | .prec first second =>
      2 * max (codeNumericBitBound first) (codeNumericBitBound second) + 3
  | .rfind' next => codeNumericBitBound next + 3

private theorem radix_pair_size_bound (first second tag firstBound secondBound : Nat)
    (small : tag ≤ 7) (firstSize : first.size ≤ firstBound) (secondSize : second.size ≤ secondBound) :
    (4 * Nat.pair first second + tag).size ≤ 2 * max firstBound secondBound + 3 :=
  ((radix_size_bound _ _ small).trans (Nat.add_le_add_right (pair_size_bound _ _) 3)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (max_le_max firstSize secondSize)) 3)

theorem code_numeric_bits_bound (code : Code) :
    (Code.encodeCode code).size ≤ codeNumericBitBound code := by
  induction code with
  | zero | succ | left | right => decide
  | pair first second ihFirst ihSecond =>
      have same : Code.encodeCode (Code.pair first second) =
          4 * Nat.pair (Code.encodeCode first) (Code.encodeCode second) + 4 := by
        simp [Code.encodeCode]; ring
      rw [same]
      exact radix_pair_size_bound _ _ 4 _ _ (by decide) ihFirst ihSecond
  | comp first second ihFirst ihSecond =>
      have same : Code.encodeCode (Code.comp first second) =
          4 * Nat.pair (Code.encodeCode first) (Code.encodeCode second) + 6 := by
        simp [Code.encodeCode]; ring
      rw [same]
      exact radix_pair_size_bound _ _ 6 _ _ (by decide) ihFirst ihSecond
  | prec first second ihFirst ihSecond =>
      have same : Code.encodeCode (Code.prec first second) =
          4 * Nat.pair (Code.encodeCode first) (Code.encodeCode second) + 5 := by
        simp [Code.encodeCode]; ring
      rw [same]
      exact radix_pair_size_bound _ _ 5 _ _ (by decide) ihFirst ihSecond
  | rfind' next ih =>
      have same : Code.encodeCode (Code.rfind' next) = 4 * Code.encodeCode next + 7 := by
        simp [Code.encodeCode]; ring
      rw [same]
      exact (radix_size_bound (Code.encodeCode next) 7 (by decide)).trans (Nat.add_le_add_right ih 3)

/-- Distinct measured artifacts. Nested pairing and unary source arithmetic may
inflate these values; no polynomial preservation in original trace bytes follows. -/
structure SizeAccount where
  descriptorSymbols : Nat
  codeNodes : Nat
  codeNumericBitsBound : Nat
  inputSymbols : Nat
  outputSymbols : Nat
  suppliedConfigurations : Nat
  claimedTransitions : Nat
  configurationBits : List Nat
  requestBits : Nat
  fuelValue : Nat
  fuelBits : Nat
  deriving DecidableEq, Repr

/-- The same bit length as `Nat.size`, using the runtime logarithm. -/
def bitWidth (value : Nat) : Nat := if value = 0 then 0 else value.log2 + 1

theorem bitWidth_eq_size (value : Nat) : bitWidth value = value.size := by
  by_cases zero : value = 0
  · simp [bitWidth, zero]
  · simp only [bitWidth, if_neg zero]
    apply Nat.le_antisymm
    · exact (Nat.lt_size.mpr ((Nat.le_log2 zero).mp (Nat.le_refl _)))
    · exact Nat.size_le.mpr (Nat.lt_log2_self)

def sizeAccount (descriptor : Descriptor) (request : Request) (fuel : Nat) : SizeAccount where
  descriptorSymbols := (Bytes.encodeDescriptor descriptor).length
  codeNodes := codeNodes (checker descriptor)
  codeNumericBitsBound := codeNumericBitBound (checker descriptor)
  inputSymbols := request.input.length
  outputSymbols := request.output.length
  suppliedConfigurations := request.trace.length
  claimedTransitions := request.count
  configurationBits := request.trace.map (fun configuration => bitWidth configuration.encode)
  requestBits := bitWidth request.encode
  fuelValue := fuel
  fuelBits := bitWidth fuel

def originalSizeAccount (descriptor : OriginalDescriptor) (request : Request) (fuel : Nat) : SizeAccount :=
  { sizeAccount descriptor.program request fuel with
    descriptorSymbols := (Bytes.encodeOriginalDescriptor descriptor).length
    codeNodes := codeNodes (originalChecker descriptor.program descriptor.inputCapacity descriptor.outputCapacity)
    codeNumericBitsBound := codeNumericBitBound
      (originalChecker descriptor.program descriptor.inputCapacity descriptor.outputCapacity) }

theorem accepted_count (descriptor : Descriptor) (request : Request)
    (accepted : request.check descriptor = true) : request.trace.length = request.count :=
  ((TraceCursor.accepts_iff descriptor _ _ _ _).mp accepted).1

end Traces

end Mettapedia.Computability.OriginalMachineTraceCode
