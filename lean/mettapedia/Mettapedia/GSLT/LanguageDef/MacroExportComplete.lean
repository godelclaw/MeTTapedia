import Mettapedia.GSLT.LanguageDef.MacroExportHeader

/-!
# Every use of a rule in the declared forms is lowered and admitted

`export_correct` covers the blocks `lower` produces. This file shows that it
produces one for every use of a rule in the declared lowering forms, so the
check is not limited to recorded fixtures. A rule is in those forms
(`lowerable`) when it is a gnu11 rule, every evaluated argument is evaluated
once and has a C type, and an expression's result has a C type. The decoder
supplies the rest: every slot a template, argument type or result names is one
of the rule's arguments (`decodeRule_scoped`).

`lower_complete`: for such a rule and arguments of the right number, every
supply of at least `2 * arguments + locals + 2` names has a prefix that `lower`
uses exactly, and the block it gives fills in the written arguments.
`admitUse_complete`: the record of that lowering, with distinct names, is
admitted, and `export_complete` adds that the block behaves as the use.
`checkHeader_function_complete` and `checkHeader_macro_complete` do the same
for header definitions: a function whose parameter declarators each have one
slot and whose expression result is a plain C type, and a macro without
locals whose template is a nonempty expression, are admitted for any distinct
names.

Each lowering step uses a prefix of the names it is given and gives the same
result from that prefix followed by anything; prefixes compose, so the whole
lowering needs only the names it took.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportComplete

open Mettapedia.GSLT.LanguageDef.MacroExportPlan
open Mettapedia.GSLT.LanguageDef.MacroExportStateful
open Mettapedia.GSLT.LanguageDef.MacroExportCorrect
open Mettapedia.GSLT.LanguageDef.MacroExportTheorem
open Mettapedia.GSLT.LanguageDef.MacroExportHeader

set_option autoImplicit false

/-! ## The declared forms -/

mutual
  /-- Every slot a source term names is below `n`, and none of the lowering's
  own leaves occurs: the terms the decoder produces. -/
  def inScope (n : Nat) : Marked → Bool
    | .symbol _ => true
    | .text _ => true
    | .list items => inScopeMany n items
    | .arg i => decide (i < n)
    | .typeArg i => decide (i < n)
    | .localRef _ => true
    | .name _ => false
    | .operand _ => false
    | .inner _ => false
  def inScopeMany (n : Nat) : List Marked → Bool
    | [] => true
    | m :: rest => inScope n m && inScopeMany n rest
end

def inScopeRule (rule : Rule) : Bool :=
  inScope rule.arguments.length rule.body && inScope rule.arguments.length rule.result &&
    rule.arguments.all fun a => inScope rule.arguments.length a.ctype

/-- A C type as `cesta check-macros` writes one. -/
def cTypeForm : Marked → Bool
  | .list [.symbol "CType", _] => true
  | .list [.symbol "CType", _, _] => true
  | _ => false

/-- The forms the readable export lowers. -/
def lowerable (rule : Rule) : Bool :=
  rule.gnu &&
    (rule.arguments.all fun a => a.category == .syntax || (a.once && cTypeForm a.ctype)) &&
    (!rule.expression || cTypeForm rule.result)

/-! ## Filling -/

/-- A lowered term fills in the written arguments. -/
def Fills (w : List Atom) (m : Marked) : Prop := (fill w m).isSome = true

theorem fillMany_isSome (w : List Atom) :
    ∀ (items : List Marked), (fillMany w items).isSome = true ↔ ∀ m ∈ items, Fills w m
  | [] => by simp [fillMany]
  | m :: rest => by
      have ih := fillMany_isSome w rest
      constructor
      · intro h
        cases hm : fill w m with
        | none => simp [fillMany, hm, bind, Option.bind] at h
        | some a =>
            cases hr : fillMany w rest with
            | none => simp [fillMany, hm, hr, bind, Option.bind] at h
            | some as =>
                intro x hx
                rcases List.mem_cons.mp hx with rfl | hx
                · simp [Fills, hm]
                · exact ih.mp (by simp [hr]) x hx
      · intro h
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h m List.mem_cons_self)
        obtain ⟨as, has⟩ := Option.isSome_iff_exists.mp (ih.mpr fun x hx => h x (List.mem_cons_of_mem _ hx))
        simp [fillMany, ha, has, bind, Option.bind, pure]

theorem fills_list (w : List Atom) (items : List Marked) :
    Fills w (.list items) ↔ ∀ m ∈ items, Fills w m := by
  rw [← fillMany_isSome]
  simp [Fills, fill]

@[simp] theorem fills_symbol (w : List Atom) (s : String) : Fills w (.symbol s) := by simp [Fills, fill]
@[simp] theorem fills_text (w : List Atom) (s : String) : Fills w (.text s) := by simp [Fills, fill]
@[simp] theorem fills_name (w : List Atom) (s : String) : Fills w (.name s) := by simp [Fills, fill]

theorem fills_operand {w : List Atom} {i : Nat} (h : i < w.length) : Fills w (.operand i) := by
  simp [Fills, fill, h]

theorem fills_blockOf (w : List Atom) (items : List Marked) :
    Fills w (blockOf items) ↔ ∀ m ∈ items, Fills w m := by
  unfold blockOf
  rw [fills_list]
  simp

mutual
  theorem fills_instantiate (w : List Atom) (slots : Nat → Marked) (L : Nat → String) (n : Nat)
      (hs : ∀ k < n, Fills w (slots k)) : ∀ (m : Marked), inScope n m = true → Fills w (instantiate slots L m)
    | .symbol _, _ => by simp [instantiate]
    | .text _, _ => by simp [instantiate]
    | .list items, h => by
        simp only [inScope] at h
        simp only [instantiate]
        exact (fills_list w _).mpr (fills_instantiateMany w slots L n hs items h)
    | .arg i, h => by
        simp only [inScope, decide_eq_true_eq] at h
        simpa [instantiate] using hs i h
    | .typeArg i, h => by
        simp only [inScope, decide_eq_true_eq] at h
        simpa [instantiate] using hs i h
    | .localRef _, _ => by simp [instantiate]
    | .name _, h => by simp [inScope] at h
    | .operand _, h => by simp [inScope] at h
    | .inner _, h => by simp [inScope] at h
  theorem fills_instantiateMany (w : List Atom) (slots : Nat → Marked) (L : Nat → String) (n : Nat)
      (hs : ∀ k < n, Fills w (slots k)) :
      ∀ (items : List Marked), inScopeMany n items = true → ∀ m ∈ instantiateMany slots L items, Fills w m
    | [], _ => by simp [instantiateMany]
    | m :: rest, h => by
        simp only [inScopeMany, Bool.and_eq_true] at h
        intro x hx
        simp only [instantiateMany, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact fills_instantiate w slots L n hs m h.1
        · exact fills_instantiateMany w slots L n hs rest h.2 x hx
end

theorem fills_addressOfObjectNode (w : List Atom) (m : Marked) (h : Fills w m) :
    Fills w (addressOfObjectNode m) := by
  unfold addressOfObjectNode
  split
  · rename_i x
    have h1 := (fills_list w _).mp h (.list [.symbol "*", x]) (by simp)
    exact (fills_list w _).mp h1 x (by simp)
  · exact h

mutual
  theorem fills_addressOfObject (w : List Atom) : ∀ (m : Marked), Fills w m → Fills w (addressOfObject m)
    | .list items, h => by
        simp only [addressOfObject]
        exact fills_addressOfObjectNode w _
          ((fills_list w _).mpr (fills_addressOfObjectMany w items ((fills_list w items).mp h)))
    | .symbol _, _ => by simp [addressOfObject]
    | .text _, _ => by simp [addressOfObject]
    | .arg _, h => by simpa [addressOfObject] using h
    | .typeArg _, h => by simpa [addressOfObject] using h
    | .localRef _, h => by simpa [addressOfObject] using h
    | .name _, _ => by simp [addressOfObject]
    | .operand _, h => by simpa [addressOfObject] using h
    | .inner _, h => by simpa [addressOfObject] using h
  theorem fills_addressOfObjectMany (w : List Atom) :
      ∀ (items : List Marked), (∀ m ∈ items, Fills w m) → ∀ m ∈ addressOfObjectMany items, Fills w m
    | [], _ => by simp [addressOfObjectMany]
    | m :: rest, h => by
        intro x hx
        simp only [addressOfObjectMany, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact fills_addressOfObject w m (h m List.mem_cons_self)
        · exact fills_addressOfObjectMany w rest (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx
end

mutual
  theorem fills_withDeclarator (w : List Atom) (al : String) :
      ∀ (m : Marked), Fills w m → Fills w (withDeclarator al m)
    | .list items, h => by
        simp only [withDeclarator]
        exact (fills_list w _).mpr (fills_withDeclaratorMany w al items ((fills_list w items).mp h))
    | .symbol s, h => by
        by_cases hs : s = "TypeSlot"
        · subst hs; simp [withDeclarator]
        · have : withDeclarator al (.symbol s) = .symbol s := by
            unfold withDeclarator; split <;> simp_all
          rw [this]; exact h
    | .text _, _ => by simp [withDeclarator]
    | .arg _, h => by simpa [withDeclarator] using h
    | .typeArg _, h => by simpa [withDeclarator] using h
    | .localRef _, h => by simpa [withDeclarator] using h
    | .name _, _ => by simp [withDeclarator]
    | .operand _, h => by simpa [withDeclarator] using h
    | .inner _, h => by simpa [withDeclarator] using h
  theorem fills_withDeclaratorMany (w : List Atom) (al : String) :
      ∀ (items : List Marked), (∀ m ∈ items, Fills w m) → ∀ m ∈ withDeclaratorMany al items, Fills w m
    | [], _ => by simp [withDeclaratorMany]
    | m :: rest, h => by
        intro x hx
        simp only [withDeclaratorMany, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact fills_withDeclarator w al m (h m List.mem_cons_self)
        · exact fills_withDeclaratorMany w al rest (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx
end

theorem fills_admission {w : List Atom} {subject type : Marked} (message : String)
    (hs : Fills w subject) (ht : Fills w type) : Fills w (admission subject type message) := by
  unfold admission
  simp [fills_list, hs, ht]

/-! ## Using a prefix of the names -/

theorem cTypeForm_instantiate (slots : Nat → Marked) (L : Nat → String) {t : Marked} (h : cTypeForm t = true) :
    cTypeForm (instantiate slots L t) = true := by
  unfold cTypeForm at h
  split at h
  · simp [instantiate, instantiateMany, cTypeForm]
  · simp [instantiate, instantiateMany, cTypeForm]
  · cases h

/-- A C type is admitted whenever a name is left for its typedef. -/
theorem admittedType_total (t : Marked) (place : Bool) (al : String) (s : List String)
    (ht : cTypeForm t = true) : (admittedType t place (al :: s)).isSome = true := by
  unfold cTypeForm at ht
  split at ht
  · simp [admittedType]
  · simp only [admittedType]
    split_ifs <;> simp
  · cases ht

/-- Admitting a type uses at most one name, and from those names followed by
anything gives the same result. -/
theorem admittedType_uses {t : Marked} {place : Bool} {s : List String} {ty : Marked} {item : Option Marked}
    {r : List String} (h : admittedType t place s = some (ty, item, r)) :
    ∃ c, c.length ≤ 1 ∧ s = c ++ r ∧ ∀ t', admittedType t place (c ++ t') = some (ty, item, t') := by
  cases place <;>
  · unfold admittedType at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, rfl, fun t' => by simp [admittedType]⟩
    · simp only [Bool.false_eq_true, if_false, if_true] at h
      split_ifs at h with hd
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[], by simp, rfl, fun t' => by simp_all [admittedType]⟩
      · split at h
        · rename_i al rest
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨[al], by simp, rfl, fun t' => by simp_all [admittedType]⟩
        · cases h
    · cases h

theorem fills_admittedType {w : List Atom} {t : Marked} {place : Bool} {s : List String} {ty : Marked}
    {item : Option Marked} {r : List String} (h : admittedType t place s = some (ty, item, r)) (ht : Fills w t) :
    Fills w ty ∧ ∀ x ∈ item.toList, Fills w x := by
  cases place <;>
  · unfold admittedType at h
    split at h
    · rename_i specs
      have hsp := (fills_list w _).mp ht specs (by simp)
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      simp_all [fills_list]
    · rename_i specs decl
      have hsp := (fills_list w _).mp ht specs (by simp)
      have hdc := (fills_list w _).mp ht decl (by simp)
      simp only [Bool.false_eq_true, if_false, if_true] at h
      split_ifs at h with hd
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        simp_all [fills_list]
      · split at h
        · rename_i al rest
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          simp_all [fills_list, fills_withDeclarator w al decl hdc]
        · cases h
    · cases h

/-! ## The acquisition -/

/-- What an argument needs to be acquired. -/
def acquirable (a : Argument) : Bool := a.category == .syntax || (a.once && cTypeForm a.ctype)

/-- Acquisition uses at most two names per argument, and from those names
followed by anything gives the same result. -/
theorem acquire_uses (rule : Rule) (written : List Atom) :
    ∀ (args : List (Nat × Argument)) (s : List String) (items : List Marked) (slots : List (Nat × Marked))
      (r : List String), acquire rule written args s = some (items, slots, r) →
      ∃ c, c.length ≤ 2 * args.length ∧ s = c ++ r ∧
        ∀ t, acquire rule written args (c ++ t) = some (items, slots, t)
  | [], s, items, slots, r, h => by
      simp only [acquire, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, rfl, fun t => by simp [acquire]⟩
  | (i, a) :: rest, s, items, slots, r, h => by
      by_cases hc : a.category = .syntax
      · obtain ⟨slots', h1, rfl⟩ := acquire_syntax h hc
        obtain ⟨c, hcl, rfl, hu⟩ := acquire_uses rule written rest s items slots' r h1
        refine ⟨c, by simp only [List.length_cons]; omega, rfl, fun t => ?_⟩
        simp [acquire, hc, hu t, bind, Option.bind, pure]
      · simp only [acquire, if_neg hc] at h
        by_cases ho : a.once = true
        · simp only [ho, Bool.not_true, Bool.false_eq_true, if_false] at h
          cases s with
          | nil => simp [bind, Option.bind] at h
          | cons n s1 =>
              simp only [bind, Option.bind_eq_some_iff, pure] at h
              obtain ⟨⟨n', s'⟩, hn, ⟨ty, item, s2⟩, h1, ⟨itemsRest, slotsRest, s3⟩, h2, h3⟩ := h
              simp only [Option.some.injEq, Prod.mk.injEq] at hn
              obtain ⟨rfl, rfl⟩ := hn
              simp only [Option.some.injEq, Prod.mk.injEq] at h3
              obtain ⟨rfl, rfl, rfl⟩ := h3
              obtain ⟨k, hkl, rfl, hk⟩ := admittedType_uses h1
              obtain ⟨c, hcl, rfl, hu⟩ := acquire_uses rule written rest _ itemsRest slotsRest s3 h2
              refine ⟨n :: (k ++ c), by simp only [List.length_cons, List.length_append]; omega, by simp,
                fun t => ?_⟩
              simp only [acquire, hc, if_false, ho, Bool.not_true, Bool.false_eq_true, List.cons_append,
                List.append_assoc, bind, Option.bind, hk (c ++ t), hu t, pure]
        · simp [ho, bind, Option.bind] at h

theorem acquire_total (rule : Rule) (written : List Atom) :
    ∀ (args : List (Nat × Argument)), (∀ p ∈ args, acquirable p.2 = true) →
      ∀ (s : List String), 2 * args.length ≤ s.length → (acquire rule written args s).isSome = true
  | [], _, s, _ => by simp [acquire]
  | (i, a) :: rest, hargs, s, hs => by
      have ha := hargs (i, a) List.mem_cons_self
      have hrest : ∀ p ∈ rest, acquirable p.2 = true := fun p hp => hargs p (List.mem_cons_of_mem _ hp)
      simp only [List.length_cons] at hs
      by_cases hc : a.category = .syntax
      · obtain ⟨⟨items, slots, r⟩, h⟩ := Option.isSome_iff_exists.mp (acquire_total rule written rest hrest s (by omega))
        simp [acquire, hc, h, bind, Option.bind, pure]
      · have hform : a.once = true ∧ cTypeForm a.ctype = true := by
          simpa [acquirable, hc] using ha
        obtain ⟨n, al, s1, rfl⟩ : ∃ n al s1, s = n :: al :: s1 := by
          rcases s with _ | ⟨n, _ | ⟨al, s1⟩⟩
          · simp at hs
          · simp at hs; omega
          · exact ⟨n, al, s1, rfl⟩
        simp only [List.length_cons] at hs
        obtain ⟨⟨ty, item, s2⟩, h1⟩ := Option.isSome_iff_exists.mp (admittedType_total
          (instantiate (fun k => .operand k) (fun _ => "") a.ctype) (decide (a.category ≠ .value)) al s1
          (cTypeForm_instantiate _ _ hform.2))
        obtain ⟨k, hkl, hk, -⟩ := admittedType_uses h1
        have hs2 : 2 * rest.length ≤ s2.length := by
          have := congrArg List.length hk
          simp only [List.length_cons, List.length_append] at this
          omega
        obtain ⟨⟨items, slots, r⟩, h2⟩ := Option.isSome_iff_exists.mp (acquire_total rule written rest hrest s2 hs2)
        simp only [acquire, hc, if_false, hform.1, Bool.not_true, Bool.false_eq_true, bind, Option.bind, h1, h2,
          pure, Option.isSome_some]

theorem acquire_fills (rule : Rule) (written : List Atom) :
    ∀ (args : List (Nat × Argument)) (s : List String) (items : List Marked) (slots : List (Nat × Marked))
      (r : List String),
      acquire rule written args s = some (items, slots, r) →
      (∀ p ∈ args, p.1 < written.length ∧ inScope written.length p.2.ctype = true) →
      (∀ x ∈ items, Fills written x) ∧ ∀ e ∈ slots, Fills written e.2
  | [], s, items, slots, r, h, _ => by
      simp only [acquire, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      simp
  | (i, a) :: rest, s, items, slots, r, h, hargs => by
      have ⟨hi, hct⟩ := hargs (i, a) List.mem_cons_self
      have hrest := fun p hp => hargs p (List.mem_cons_of_mem _ hp)
      by_cases hc : a.category = .syntax
      · obtain ⟨slots', h1, rfl⟩ := acquire_syntax h hc
        obtain ⟨hitems, hslots⟩ := acquire_fills rule written rest s items slots' r h1 hrest
        refine ⟨hitems, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact fills_operand hi
        · exact hslots e he
      · simp only [acquire, if_neg hc] at h
        by_cases ho : a.once = true
        · simp only [ho, Bool.not_true, Bool.false_eq_true, if_false] at h
          cases s with
          | nil => simp [bind, Option.bind] at h
          | cons n s1 =>
              simp only [bind, Option.bind_eq_some_iff, pure] at h
              obtain ⟨⟨n', s'⟩, hn, ⟨ty, item, s2⟩, h1, ⟨itemsRest, slotsRest, s3⟩, h2, h3⟩ := h
              simp only [Option.some.injEq, Prod.mk.injEq] at hn
              obtain ⟨rfl, rfl⟩ := hn
              simp only [Option.some.injEq, Prod.mk.injEq] at h3
              obtain ⟨rfl, rfl, rfl⟩ := h3
              have htyped : Fills written (instantiate (fun k => .operand k) (fun _ => "") a.ctype) :=
                fills_instantiate written _ _ written.length (fun k hk => fills_operand hk) a.ctype hct
              obtain ⟨hty, hitem⟩ := fills_admittedType h1 htyped
              obtain ⟨hitems, hslots⟩ := acquire_fills rule written rest s2 itemsRest slotsRest s3 h2 hrest
              refine ⟨?_, ?_⟩
              · intro x hx
                simp only [List.append_assoc, List.cons_append, List.mem_cons,
                  List.mem_append, List.not_mem_nil, false_or] at hx
                rcases hx with rfl | hx | rfl | hx
                · refine (fills_list written _).mpr ?_
                  intro m hm
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
                  rcases hm with rfl | rfl | rfl | rfl
                  · exact fills_symbol written _
                  · exact fills_symbol written _
                  · exact fills_name written _
                  · split
                    · split
                      · rename_i x hx
                        simp [Fills, fill, hx]
                      · exact (fills_list written _).mpr (by simp [fills_operand hi])
                    · exact fills_operand hi
                · exact hitem x hx
                · exact fills_admission _ (fills_name written _) hty
                · exact hitems x hx
              · intro e he
                rcases List.mem_cons.mp he with rfl | he
                · split
                  · exact (fills_list written _).mpr (by simp)
                  · exact fills_name written _
                · exact hslots e he
        · simp [ho, bind, Option.bind] at h

/-! ## The body items -/

/-- The body items use at most two names, and from those names followed by
anything give the same result. -/
theorem bodyItems_uses (rule : Rule) (written : List Atom) (declared : Marked) (all : List Marked) :
    ∀ (items : List Marked) (s : List String) (out : List Marked) (r : List String),
      bodyItems rule written declared all items s = some (out, r) →
      ∃ c, s = c ++ r ∧ ∀ t, bodyItems rule written declared all items (c ++ t) = some (out, t)
  | [], s, out, r, h => by
      simp only [bodyItems, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, fun t => by simp [bodyItems]⟩
  | [last], s, out, r, h => by
      by_cases he : rule.expression = true
      · by_cases hr : declaresResult written declared last all.dropLast = true
        · simp only [bodyItems, he, hr, if_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], rfl, fun t => by simp [bodyItems, he, hr]⟩
        · by_cases ht : (spelling? last == none && !effectFree last) = true
          · cases s with
            | nil =>
                simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind] at h
                simp at h
            | cons rn s1 =>
                simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind,
                  Option.bind_some] at h
                simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨⟨ty, item, s2⟩, h2, rfl, rfl⟩ := h
                obtain ⟨k, -, rfl, hk⟩ := admittedType_uses h2
                exact ⟨rn :: k, by simp, fun t => by
                  simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, List.cons_append,
                    bind, Option.bind_some, hk t, pure]⟩
          · simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind,
              Option.bind_some] at h
            simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨ty, item, s2⟩, h2, rfl, rfl⟩ := h
            obtain ⟨k, -, rfl, hk⟩ := admittedType_uses h2
            exact ⟨k, rfl, fun t => by
              simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind, Option.bind_some,
                hk t, pure]⟩
      · simp only [bodyItems, he, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, fun t => by simp [bodyItems, he]⟩
  | item :: next :: rest, s, out, r, h => by
      simp only [bodyItems, bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨⟨out', s'⟩, h1, h2⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨c, rfl, hu⟩ := bodyItems_uses rule written declared all (next :: rest) s out' _ h1
      exact ⟨c, rfl, fun t => by simp [bodyItems, hu t, bind, Option.bind, pure]⟩

theorem bodyItems_total (rule : Rule) (written : List Atom) (declared : Marked) (all : List Marked)
    (hd : rule.expression = true → cTypeForm declared = true) :
    ∀ (items : List Marked) (s : List String), 2 ≤ s.length →
      (bodyItems rule written declared all items s).isSome = true
  | [], s, _ => by simp [bodyItems]
  | [last], s, hs => by
      obtain ⟨n, al, s1, rfl⟩ : ∃ n al s1, s = n :: al :: s1 := by
        rcases s with _ | ⟨n, _ | ⟨al, s1⟩⟩
        · simp at hs
        · simp at hs
        · exact ⟨n, al, s1, rfl⟩
      by_cases he : rule.expression = true
      · by_cases hr : declaresResult written declared last all.dropLast = true
        · simp [bodyItems, he, hr]
        · by_cases ht : (spelling? last == none && !effectFree last) = true
          · obtain ⟨⟨ty, item, s2⟩, h2⟩ := Option.isSome_iff_exists.mp (admittedType_total declared false al s1 (hd he))
            simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind, Option.bind_some, h2,
              pure, Option.isSome_some]
          · obtain ⟨⟨ty, item, s2⟩, h2⟩ :=
              Option.isSome_iff_exists.mp (admittedType_total declared false n (al :: s1) (hd he))
            simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind, Option.bind_some, h2,
              pure, Option.isSome_some]
      · simp [bodyItems, he]
  | item :: next :: rest, s, hs => by
      obtain ⟨⟨out, r⟩, h⟩ := Option.isSome_iff_exists.mp (bodyItems_total rule written declared all hd (next :: rest) s hs)
      simp [bodyItems, h, bind, Option.bind, pure]

theorem bodyItems_fills (rule : Rule) (written : List Atom) (declared : Marked) (all : List Marked)
    (hd : Fills written declared) :
    ∀ (items : List Marked) (s : List String) (out : List Marked) (r : List String),
      bodyItems rule written declared all items s = some (out, r) →
      (∀ x ∈ items, Fills written x) → ∀ x ∈ out, Fills written x
  | [], s, out, r, h, _ => by
      simp only [bodyItems, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp
  | [last], s, out, r, h, hitems => by
      have hl := hitems last List.mem_cons_self
      by_cases he : rule.expression = true
      · by_cases hr : declaresResult written declared last all.dropLast = true
        · simp only [bodyItems, he, hr, if_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simpa using hl
        · have key : ∃ value temporary ty item s2, Fills written value ∧ (∀ x ∈ temporary, Fills written x) ∧
              (∃ s1, admittedType declared false s1 = some (ty, item, s2)) ∧
              out = temporary ++ item.toList ++
                [admission value ty (rule.head ++ " result has its declared type"), value] := by
            by_cases ht : (spelling? last == none && !effectFree last) = true
            · cases s with
              | nil =>
                  simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind] at h
                  simp at h
              | cons rn s1 =>
                  simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind,
                    Option.bind_some] at h
                  simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨⟨ty, item, s2⟩, h2, rfl, -⟩ := h
                  exact ⟨_, _, ty, item, s2, fills_name written rn, by simp [fills_list, hl], ⟨s1, h2⟩, rfl⟩
            · simp only [bodyItems, he, hr, ht, if_true, if_false, Bool.false_eq_true, bind,
                Option.bind_some] at h
              simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨⟨ty, item, s2⟩, h2, rfl, -⟩ := h
              exact ⟨last, [], ty, item, s2, hl, by simp, ⟨s, h2⟩, by simp⟩
          obtain ⟨value, temporary, ty, item, s2, hvalue, htemp, ⟨s1, h2⟩, rfl⟩ := key
          obtain ⟨hty, hitem⟩ := fills_admittedType h2 hd
          intro x hx
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with (hx | hx) | rfl | rfl
          · exact htemp x hx
          · exact hitem x hx
          · exact fills_admission _ hvalue hty
          · exact hvalue
      · simp only [bodyItems, he, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simpa using hl
  | item :: next :: rest, s, out, r, h, hitems => by
      simp only [bodyItems, bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨⟨out', s'⟩, h1, h2⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      have ih := bodyItems_fills rule written declared all hd (next :: rest) s out' s' h1
        (fun x hx => hitems x (List.mem_cons_of_mem _ hx))
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hitems x List.mem_cons_self
      · exact ih x hx

/-! ## The whole lowering -/

theorem lookup_mem {α β : Type} [BEq α] : ∀ (l : List (α × β)) (k : α) (x : β), l.lookup k = some x → ∃ k', (k', x) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (a, b) :: rest, k, x, h => by
      simp only [List.lookup] at h
      split at h
      · cases h; exact ⟨a, List.mem_cons_self⟩
      · obtain ⟨k', hk⟩ := lookup_mem rest k x h
        exact ⟨k', List.mem_cons_of_mem _ hk⟩

theorem fills_assemble {w : List Atom} {acquired template : List Marked} (b : Bool)
    (ha : ∀ x ∈ acquired, Fills w x) (ht : ∀ x ∈ template, Fills w x) :
    Fills w (assemble acquired template b) := by
  have hall : ∀ x ∈ acquired ++ template, Fills w x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ha x hx
    · exact ht x hx
  have hb : Fills w (blockOf template) := (fills_blockOf w _).mpr ht
  unfold assemble
  dsimp only
  split_ifs <;> first
    | exact (fills_blockOf w _).mpr hall
    | exact (fills_blockOf w _).mpr (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ha x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hb)

theorem fills_bodyView {w : List Atom} {body : Marked} (h : Fills w body) :
    ∀ x ∈ (bodyView body).2, Fills w x := by
  unfold bodyView
  split
  · rename_i xs
    intro x hx
    exact (fills_list w _).mp h x (List.mem_cons_of_mem _ hx)
  · simpa using h

/-! ## The decoder's terms are in scope -/

theorem indexOf_lt {names : List String} {x : String} {i : Nat} (h : indexOf names x = some i) :
    i < names.length :=
  (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1

mutual
  theorem mark_inScope (args : List String) (locals : List (String × String)) (ports : List (String × String)) :
      ∀ (a : Atom) (m : Marked), mark args locals ports a = some m → inScope args.length m = true
    | .symbol s, m, h => by simp only [mark, Option.some.injEq] at h; subst h; rfl
    | .text s, m, h => by simp only [mark, Option.some.injEq] at h; subst h; rfl
    | .list items, m, h => by
        have ih := markMany_inScope args locals ports items
        unfold mark at h
        split at h
        all_goals rename_i heq
        all_goals cases heq
        all_goals first
          | (simp only [Option.map_eq_some_iff] at h
             obtain ⟨i, hi, rfl⟩ := h
             simp [inScope, indexOf_lt hi])
          | (simp only [Option.map_eq_some_iff] at h
             obtain ⟨i, hi, rfl⟩ := h
             rfl)
          | (simp only [Option.map_eq_some_iff] at h
             obtain ⟨ms, hms, rfl⟩ := h
             exact ih ms hms)
          | cases h
  theorem markMany_inScope (args : List String) (locals : List (String × String)) (ports : List (String × String)) :
      ∀ (as : List Atom) (ms : List Marked), markMany args locals ports as = some ms → inScopeMany args.length ms = true
    | [], ms, h => by simp only [markMany, Option.some.injEq] at h; subst h; rfl
    | a :: rest, ms, h => by
        simp only [markMany, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
        obtain ⟨m, hm, ms', hms', rfl⟩ := h
        simp [inScopeMany, mark_inScope args locals ports a m hm, markMany_inScope args locals ports rest ms' hms']
end

theorem mapM_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → l'.length = l.length ∧ ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; simp
  | a :: rest, l', h => by
      simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      obtain ⟨hlen, hmem⟩ := mapM_some f rest bs hbs
      refine ⟨by simp [hlen], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨a, List.mem_cons_self, hb⟩
      · obtain ⟨y, hy, hfy⟩ := hmem x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

theorem argument_inScope {args : List String} {ports : List (String × String)} {atom : Atom} {a : Argument}
    (h : argument args ports atom = some a) : inScope args.length a.ctype = true := by
  unfold argument at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c, -, t, ht, rfl⟩ := h
    exact mark_inScope args [] ports _ t ht
  · cases h

/-- Every slot a decoded rule names is one of its arguments. -/
theorem decodeRule_inScope {a : Atom} {rule : Rule} (h : decodeRule a = some rule) : inScopeRule rule = true := by
  unfold decodeRule at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨profile, -, h⟩ := h
    split at h
    rotate_left 2
    · simp at h
    all_goals
      simp only [Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨argAtoms, -, args, hargs, arguments, harguments, result, -, h⟩ := h
      have hlen : arguments.length = args.length := by
        rw [(mapM_some _ _ _ harguments).1, (mapM_some _ _ _ hargs).1]
      have hargsIn : ∀ x ∈ arguments, inScope args.length x.ctype = true := by
        intro x hx
        obtain ⟨atom, -, hx⟩ := (mapM_some _ _ _ harguments).2 x hx
        exact argument_inScope hx
      split at h
      rotate_left 2
      · simp at h
      all_goals
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨⟨resultType, expression⟩, ⟨t, ht, hte⟩, localAtoms, -, locals, -, template, -, h⟩ := h
        simp only [Prod.mk.injEq] at hte
        obtain ⟨rfl, -⟩ := hte
        split at h
        · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
          obtain ⟨body, hbody, rfl⟩ := h
          simp only [inScopeRule, hlen, Bool.and_eq_true, List.all_eq_true]
          exact ⟨⟨mark_inScope _ _ _ _ body hbody, mark_inScope _ _ _ _ t ht⟩, hargsIn⟩
        · simp at h
  · cases h

/-- `lower` from its steps. -/
theorem lower_eq {rule : Rule} {written : List Atom} {supply : List String} {acquired : List Marked}
    {slotList : List (Nat × Marked)} {s1 : List String} {template : List Marked}
    (hg : rule.gnu = true) (hlen : written.length = rule.arguments.length)
    (hacq : acquire rule written (List.zip (List.range rule.arguments.length) rule.arguments) supply =
      some (acquired, slotList, s1))
    (hk : rule.locals.length ≤ s1.length)
    (hb : bodyItems rule written
      (instantiate (fun k => (slotList.lookup k).getD (.operand k))
        (fun j => (s1.take rule.locals.length).getD j "") rule.result)
      (bodyView (addressOfObject (instantiate (fun k => (slotList.lookup k).getD (.operand k))
        (fun j => (s1.take rule.locals.length).getD j "") rule.body))).2
      (bodyView (addressOfObject (instantiate (fun k => (slotList.lookup k).getD (.operand k))
        (fun j => (s1.take rule.locals.length).getD j "") rule.body))).2
      (s1.drop rule.locals.length) = some (template, [])) :
    lower rule written supply =
      some (assemble acquired template (bodyView (addressOfObject (instantiate (fun k => (slotList.lookup k).getD (.operand k))
        (fun j => (s1.take rule.locals.length).getD j "") rule.body))).1) := by
  unfold lower
  simp only [hg, hlen, Bool.not_true, Bool.false_eq_true, if_false, ne_eq, not_true_eq_false, bind,
    Option.bind, hacq, hk, if_true]
  rw [hb]
  rfl

/-- Every use of a rule in the declared forms is lowered: some prefix of any
long enough supply is exactly the names the lowering uses, and the lowered
block fills in the written arguments. -/
theorem lower_complete (rule : Rule) (written : List Atom) (hl : lowerable rule = true)
    (hsc : inScopeRule rule = true) (hlen : written.length = rule.arguments.length) (supply : List String)
    (hs : 2 * rule.arguments.length + rule.locals.length + 2 ≤ supply.length) :
    ∃ picked rest block atom, supply = picked ++ rest ∧ lower rule written picked = some block ∧
      fill written block = some atom := by
  simp only [lowerable, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hl
  obtain ⟨⟨hgnu, hargs⟩, hres⟩ := hl
  simp only [inScopeRule, Bool.and_eq_true, List.all_eq_true] at hsc
  obtain ⟨⟨hbody, hresult⟩, hctypes⟩ := hsc
  have hargs' : ∀ p ∈ List.zip (List.range rule.arguments.length) rule.arguments, acquirable p.2 = true := by
    rintro ⟨i, a⟩ hp
    have := hargs a (List.of_mem_zip hp).2
    simpa [acquirable] using this
  have hargsF : ∀ p ∈ List.zip (List.range rule.arguments.length) rule.arguments,
      p.1 < written.length ∧ inScope written.length p.2.ctype = true := by
    rintro ⟨i, a⟩ hp
    have h1 := (List.of_mem_zip hp).1
    have h2 := (List.of_mem_zip hp).2
    simp only [List.mem_range] at h1
    exact ⟨by omega, by rw [hlen]; exact hctypes a h2⟩
  obtain ⟨⟨items, slotList, r1⟩, hacq0⟩ := Option.isSome_iff_exists.mp
    (acquire_total rule written _ hargs' supply (by simp; omega))
  obtain ⟨c1, hc1, rfl, hu1⟩ := acquire_uses rule written _ supply items slotList r1 hacq0
  simp only [List.length_append, List.length_zip, List.length_range, Nat.min_self] at hs hc1
  obtain ⟨L, hL⟩ : ∃ L, r1.take rule.locals.length = L := ⟨_, rfl⟩
  have hLlen : L.length = rule.locals.length := by rw [← hL]; simp; omega
  have hd : rule.expression = true → cTypeForm (instantiate (fun k => (slotList.lookup k).getD (.operand k))
      (fun j => L.getD j "") rule.result) = true := fun he =>
    cTypeForm_instantiate _ _ (by cases hres with | inl h => simp [h] at he | inr h => exact h)
  obtain ⟨⟨template, r3⟩, hb0⟩ := Option.isSome_iff_exists.mp
    (bodyItems_total rule written _ _ hd _ (r1.drop rule.locals.length) (by simp; omega))
  obtain ⟨c3, hr3, hu3⟩ := bodyItems_uses rule written _ _ _ _ template r3 hb0
  have htake : (L ++ c3).take rule.locals.length = L := by simp [← hLlen]
  have hdrop : (L ++ c3).drop rule.locals.length = c3 := by simp [← hLlen]
  have hlow := lower_eq (supply := c1 ++ (L ++ c3)) (template := template) hgnu hlen (hu1 (L ++ c3))
    (by simp [hLlen]) (by rw [htake, hdrop]; simpa using hu3 [])
  rw [htake] at hlow
  have hslots : ∀ k < written.length, Fills written ((slotList.lookup k).getD (.operand k)) := by
    intro k hk
    cases hlk : slotList.lookup k with
    | none => exact fills_operand hk
    | some x =>
        obtain ⟨k', hk'⟩ := lookup_mem slotList k x hlk
        exact (acquire_fills rule written _ _ items slotList r1 (hu1 r1) hargsF).2 (k', x) hk'
  have hbodyF := fills_addressOfObject written _ (fills_instantiate written _ (fun j => L.getD j "")
    written.length hslots rule.body (by rw [hlen]; exact hbody))
  have hdeclF := fills_instantiate written _ (fun j => L.getD j "") written.length hslots rule.result
    (by rw [hlen]; exact hresult)
  have htemplate := bodyItems_fills rule written _ _ hdeclF _ _ template r3 hb0 (fills_bodyView hbodyF)
  obtain ⟨atom, hatom⟩ := Option.isSome_iff_exists.mp
    (fills_assemble _ (acquire_fills rule written _ _ items slotList r1 (hu1 r1) hargsF).1 htemplate)
  refine ⟨c1 ++ (L ++ c3), r3, _, atom, ?_, hlow, hatom⟩
  have : r1 = L ++ r1.drop rule.locals.length := by rw [← hL]; exact (List.take_append_drop _ _).symm
  rw [this, hr3]
  simp

/-! ## The record of every such lowering is admitted -/

/-- A use record as `cesta export-c --plan` writes it. -/
def useRecord (path theory label : String) (written acquired locals : List Atom) (picked : List String)
    (expression : Bool) (target : Atom) : Atom :=
  .list [.symbol "use", .symbol "cesta-export-plan/2", .list [.symbol "rule", .text path, .text theory, .text label],
    .list (.symbol "arguments" :: written), .list (.symbol "acquired" :: acquired),
    .list (.symbol "locals" :: locals), .list (.symbol "picked" :: picked.map .text),
    .list [.symbol "position", .symbol (if expression then "expression" else "statement")],
    .list [.symbol "target", target]]

theorem mapM_texts (g : Atom → Option String) (hg : ∀ s, g (.text s) = some s) :
    ∀ (names : List String), names.mapM (g ∘ Atom.text) = some names
  | [] => rfl
  | n :: rest => by simp [List.mapM_cons, hg, mapM_texts g hg rest, bind, pure]

theorem decodeUse_record (path theory label : String) (written acquired locals : List Atom) (picked : List String)
    (expression : Bool) (target : Atom) :
    decodeUse (useRecord path theory label written acquired locals picked expression target) =
      some { label, written, picked, expression, target } := by
  cases expression <;>
  · simp only [decodeUse, useRecord, List.mapM_map, bind, pure, Bool.false_eq_true, if_true, if_false]
    rw [mapM_texts _ (fun _ => rfl)]
    rfl

/-- Every use of a decoded, admitted rule in the declared forms is lowered by
a prefix of any long enough supply of names, and the record of that lowering
is admitted. -/
theorem admitUse_complete (ruleAtom : Atom) (rule : Rule) (hr : decodeRule ruleAtom = some rule)
    (hadm : admittedRule rule = true) (hl : lowerable rule = true) (written : List Atom)
    (hlen : written.length = rule.arguments.length) (supply : List String) (hnd : supply.Nodup)
    (hs : 2 * rule.arguments.length + rule.locals.length + 2 ≤ supply.length) :
    ∃ picked rest block target, supply = picked ++ rest ∧ lower rule written picked = some block ∧
      fill written block = some target ∧
      ∀ path theory acquired locals,
        admitUse ruleAtom (useRecord path theory rule.label written acquired locals picked rule.expression target) =
          true := by
  obtain ⟨picked, rest, block, target, rfl, hlow, hfill⟩ :=
    lower_complete rule written hl (decodeRule_inScope hr) hlen supply hs
  refine ⟨picked, rest, block, target, rfl, hlow, hfill, fun path theory acquired locals => ?_⟩
  have hpicked : picked.Nodup := hnd.sublist (List.sublist_append_left _ _)
  simp [admitUse, checkUse, hr, decodeUse_record, hlow, hfill, hadm, hpicked]

/-- The checker is complete for the declared forms, and what it admits is
correct: every use of a decoded, admitted rule in those forms has a readable
export, from a prefix of any long enough supply of distinct names, that behaves
as the source use. -/
theorem export_complete (ruleAtom : Atom) (rule : Rule) (hr : decodeRule ruleAtom = some rule)
    (hadm : admittedRule rule = true) (hl : lowerable rule = true) (written : List Atom)
    (hlen : written.length = rule.arguments.length) (supply : List String) (hnd : supply.Nodup)
    (hs : 2 * rule.arguments.length + rule.locals.length + 2 ≤ supply.length) :
    ∃ picked rest block target, supply = picked ++ rest ∧ lower rule written picked = some block ∧
      fill written block = some target ∧
      ∀ (profile : Profile) (operands : Nat → Operand) (st : State),
        runBlock profile written operands rule.expression block st =
          invoke profile written operands rule (chosenLocals rule written picked) st := by
  obtain ⟨picked, rest, block, target, rfl, hlow, hfill, -⟩ :=
    admitUse_complete ruleAtom rule hr hadm hl written hlen supply hnd hs
  exact ⟨picked, rest, block, target, rfl, hlow, hfill, fun profile operands st =>
    export_correct profile written operands rule picked block st hlow
      (hnd.sublist (List.sublist_append_left _ _)) hadm⟩

/-! ## Header definitions -/

mutual
  /-- How many slots a declarator has does not depend on the name put there. -/
  theorem withParameter_count (x y : Marked) (p : Bool) :
      ∀ (m : Marked), (withParameter x p m).2 = (withParameter y p m).2
    | .list items => by
        have ih := withParameterMany_count x y p items
        unfold withParameter
        split <;> (try split) <;> simp_all
    | .symbol s => by unfold withParameter; split <;> (try split) <;> simp_all
    | .text _ => by simp [withParameter]
    | .arg _ => by simp [withParameter]
    | .typeArg _ => by simp [withParameter]
    | .localRef _ => by simp [withParameter]
    | .name _ => by simp [withParameter]
    | .operand _ => by simp [withParameter]
    | .inner _ => by simp [withParameter]
  theorem withParameterMany_count (x y : Marked) (p : Bool) :
      ∀ (ms : List Marked), (withParameterMany x p ms).2 = (withParameterMany y p ms).2
    | [] => rfl
    | m :: rest => by
        have h1 := withParameter_count x y p m
        have h2 := withParameterMany_count x y p rest
        show (withParameter x p m).2 + (withParameterMany x p rest).2 =
          (withParameter y p m).2 + (withParameterMany y p rest).2
        rw [h1, h2]
end

mutual
  theorem fills_withParameter (w : List Atom) (x : Marked) (p : Bool) (hx : Fills w x) :
      ∀ (m : Marked), Fills w m → Fills w (withParameter x p m).1
    | .list items, h => by
        have ih := fills_withParameterMany w x p hx items ((fills_list w items).mp h)
        unfold withParameter
        split
        all_goals first
          | (split <;> simp_all [fills_list])
          | simp_all [fills_list]
    | .symbol s, h => by
        unfold withParameter
        split
        all_goals first
          | (split <;> simp_all [fills_list])
          | simp_all
    | .text _, _ => by simp [withParameter]
    | .arg _, h => by simpa [withParameter] using h
    | .typeArg _, h => by simpa [withParameter] using h
    | .localRef _, h => by simpa [withParameter] using h
    | .name _, _ => by simp [withParameter]
    | .operand _, h => by simpa [withParameter] using h
    | .inner _, h => by simpa [withParameter] using h
  theorem fills_withParameterMany (w : List Atom) (x : Marked) (p : Bool) (hx : Fills w x) :
      ∀ (ms : List Marked), (∀ m ∈ ms, Fills w m) → ∀ m ∈ (withParameterMany x p ms).1, Fills w m
    | [], _ => by simp [withParameterMany]
    | m :: rest, h => by
        intro y hy
        change y ∈ (withParameter x p m).1 :: (withParameterMany x p rest).1 at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact fills_withParameter w x p hx m (h m List.mem_cons_self)
        · exact fills_withParameterMany w x p hx rest (fun z hz => h z (List.mem_cons_of_mem _ hz)) y hy
end

/-- Whether an argument's parameter is declared does not depend on its name. -/
theorem parameter_isSome (a : Argument) (n n' : String) :
    (parameter a n).isSome = (parameter a n').isSome := by
  unfold parameter
  split
  · rfl
  · rename_i specs decl _
    show (if (withParameter (.name n) (a.category != .value) decl).2 = 1 then
        some (Marked.list [specs, (withParameter (.name n) (a.category != .value) decl).1]) else none).isSome =
      (if (withParameter (.name n') (a.category != .value) decl).2 = 1 then
        some (Marked.list [specs, (withParameter (.name n') (a.category != .value) decl).1]) else none).isSome
    rw [withParameter_count (.name n) (.name n')]
    split <;> rfl
  · rfl

theorem fills_parameter {w : List Atom} {a : Argument} {n : String} {x : Marked} (h : parameter a n = some x)
    (ht : Fills w (instantiate (fun k => .operand k) (fun _ => "") a.ctype)) : Fills w x := by
  unfold parameter at h
  split at h
  · rename_i specs heq
    rw [heq] at ht
    have hs := (fills_list w _).mp ht specs (by simp)
    simp only [Option.some.injEq] at h
    subst h
    refine (fills_list w _).mpr ?_
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hs
    · split
      · exact (fills_list w _).mpr (by simp)
      · simp
  · rename_i specs decl heq
    rw [heq] at ht
    have hs := (fills_list w _).mp ht specs (by simp)
    have hd := (fills_list w _).mp ht decl (by simp)
    change (if (withParameter (.name n) (a.category != .value) decl).2 = 1 then
        some (Marked.list [specs, (withParameter (.name n) (a.category != .value) decl).1]) else none) = some x at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact (fills_list w _).mpr (by simp [hs, fills_withParameter w _ _ (fills_name w n) decl hd])
    · cases h
  · cases h

/-- The header function forms: every parameter has a declarator with one
slot, and an expression's result is a plain C type. -/
def functionForm (rule : Rule) : Bool :=
  (evaluated rule).all (fun s => (parameter s.2 "").isSome) &&
    (!rule.expression || match rule.result with
      | .list [.symbol "CType", _] => true
      | _ => false)

theorem mapM_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome = true) → (l.mapM f).isSome = true
  | [], _ => by simp
  | x :: rest, h => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
      obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
        (mapM_isSome f rest fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp [List.mapM_cons, hb, hbs, bind, pure]

/-- A function-form rule is lowered for any names of the right number. -/
theorem lowerFunctionParts_complete (rule : Rule) (hf : functionForm rule = true) (names : List String)
    (hlen : names.length = (evaluated rule).length + rule.locals.length) :
    ∃ parts, lowerFunctionParts rule names = some parts ∧
      (∀ x ∈ parts.params, ∃ s ∈ (evaluated rule).zip (names.take (evaluated rule).length),
        parameter s.1.2 s.2 = some x) ∧
      parts.items = (bodyView (addressOfObject (instantiate (functionSlots rule (names.take (evaluated rule).length))
        (fun j => (names.drop (evaluated rule).length).getD j "") rule.body))).2 ∧
      (parts.result = .symbol "void" ∨ ∃ t, rule.result = .list [.symbol "CType", t] ∧
        parts.result = instantiate (functionSlots rule (names.take (evaluated rule).length))
          (fun j => (names.drop (evaluated rule).length).getD j "") t) := by
  simp only [functionForm, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨hps, hres⟩ := hf
  obtain ⟨params, hp⟩ := Option.isSome_iff_exists.mp
    (mapM_isSome (fun s : (Nat × Argument) × String => parameter s.1.2 s.2)
      ((evaluated rule).zip (names.take (evaluated rule).length)) (by
        rintro ⟨s, n⟩ hs
        rw [parameter_isSome s.2 n ""]
        exact hps s (List.of_mem_zip hs).1))
  have hmem := (mapM_some _ _ _ hp).2
  unfold lowerFunctionParts
  simp only [hlen, ne_eq, not_true_eq_false, if_false, bind, Option.bind, hp]
  cases he : rule.expression
  · exact ⟨_, rfl, hmem, rfl, .inl rfl⟩
  · have : ∃ t, rule.result = .list [.symbol "CType", t] := by
      rcases hres with h | h
      · simp [he] at h
      · split at h
        · rename_i t heq; exact ⟨t, heq⟩
        · cases h
    obtain ⟨t, ht⟩ := this
    simp only [if_true, ht, instantiate, instantiateMany]
    exact ⟨_, rfl, hmem, rfl, .inr ⟨t, rfl, rfl⟩⟩

theorem headerWritten_length (rule : Rule) (use : HeaderUse) :
    (headerWritten rule use).length = rule.arguments.length := by
  unfold headerWritten
  generalize use.picked = names
  induction rule.arguments generalizing names with
  | nil => simp [headerWritten.go]
  | cons a rest ih =>
      simp only [headerWritten.go]
      split
      · simp [ih]
      · split
        · simp [ih]
        · split <;> simp [ih]

theorem fills_functionAtom {w : List Atom} (fname : String) (expression : Bool) (p : FunctionParts)
    (hr : Fills w p.result) (hp : ∀ x ∈ p.params, Fills w x) (hi : ∀ x ∈ p.items, Fills w x) :
    Fills w (functionAtom fname expression p) := by
  unfold functionAtom
  dsimp only
  refine (fills_list w _).mpr ?_
  intro m hm
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | hm
  · simp
  · refine (fills_list w _).mpr ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro m (rfl | rfl)
    · simp
    · exact (fills_list w _).mpr (by simp [hr])
  · simp
  · refine (fills_list w _).mpr ?_
    split
    · simp
    · exact hp
  · split at hm
    · split at hm
      · rename_i last earlier heq
        have hmem : ∀ y, y ∈ earlier.reverse ∨ y = last → y ∈ p.items := by
          intro y hy
          have : p.items = earlier.reverse ++ [last] := by
            rw [← List.reverse_reverse p.items, heq]; simp
          rw [this]; simpa using hy
        simp only [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact hi m (hmem m (.inl hm))
        · exact (fills_list w _).mpr (by simp [hi last (hmem last (.inr rfl))])
      · simp at hm
    · exact hi m hm

theorem typePair_mapM : ∀ (types : List (String × Atom)),
    types.mapM (typePair ∘ fun kt => Atom.list [.symbol kt.1, kt.2]) = some types
  | [] => rfl
  | kt :: rest => by simp [List.mapM_cons, typePair, typePair_mapM rest, bind, pure]

/-- What a header definition's arguments are written as depends only on its
type parameters, its kind and its names. -/
theorem headerWritten_congr (rule : Rule) (u v : HeaderUse) (ht : u.types = v.types) (hf : u.function = v.function)
    (hp : u.picked = v.picked) : headerWritten rule u = headerWritten rule v := by
  unfold headerWritten
  rw [hp]
  generalize v.picked = names
  induction rule.arguments generalizing names with
  | nil => rfl
  | cons a rest ih => simp only [headerWritten.go, ht, hf, ih]

/-- A header plan record as `cesta export-header --plan` writes it. -/
def headerRecord (path theory label : String) (function : Bool) (name : String) (types : List (String × Atom))
    (picked : List String) (emitted : Atom) : Atom :=
  .list [.symbol "header", .symbol "cesta-header-plan/1", .list [.symbol "rule", .text path, .text theory, .text label],
    .list [.symbol (if function then "function" else "macro"), .symbol name],
    .list (.symbol "types" :: types.map fun kt => .list [.symbol kt.1, kt.2]),
    .list (.symbol "picked" :: picked.map .text),
    .list [.symbol (if function then "definition" else "expression"), emitted]]

theorem decodeHeader_record (path theory label : String) (function : Bool) (name : String)
    (types : List (String × Atom)) (picked : List String) (emitted : Atom) :
    decodeHeader (headerRecord path theory label function name types picked emitted) =
      some { label, function, name, types, picked, emitted } := by
  cases function <;>
  · simp only [decodeHeader, headerRecord, List.mapM_map, bind, pure, Bool.false_eq_true, if_true, if_false,
      Option.bind_some]
    rw [typePair_mapM, mapM_texts _ (fun _ => rfl)]
    rfl

/-- Every header function of a decoded, admitted rule in the function forms,
with any distinct names of the right number, is admitted by `checkHeader`. -/
theorem checkHeader_function_complete (ruleAtom : Atom) (rule : Rule) (hr : decodeRule ruleAtom = some rule)
    (hadm : admittedRule rule = true) (hf : functionForm rule = true) (fname : String)
    (types : List (String × Atom)) (names : List String) (hnd : names.Nodup)
    (hlen : names.length = (evaluated rule).length + rule.locals.length) :
    ∃ parts target, lowerFunctionParts rule names = some parts ∧
      ∀ path theory, checkHeader ruleAtom (headerRecord path theory rule.label true fname types names target) = true := by
  obtain ⟨parts, hlow, hparams, hitems, hresult⟩ := lowerFunctionParts_complete rule hf names hlen
  have hsc := decodeRule_inScope hr
  simp only [inScopeRule, Bool.and_eq_true, List.all_eq_true] at hsc
  obtain ⟨⟨hbody, hres⟩, hctypes⟩ := hsc
  let written := headerWritten rule ⟨rule.label, true, fname, types, names, .symbol ""⟩
  have hwl : written.length = rule.arguments.length := headerWritten_length _ _
  have hslots : ∀ k < written.length,
      Fills written (functionSlots rule (names.take (evaluated rule).length) k) := by
    intro k hk
    unfold functionSlots
    split
    · split
      · split
        · simp
        · exact (fills_list written _).mpr (by simp)
      · exact fills_operand hk
    · exact fills_operand hk
  have hfills : Fills written (functionAtom fname rule.expression parts) := by
    refine fills_functionAtom fname rule.expression parts ?_ ?_ ?_
    · rcases hresult with h | ⟨t, ht, h⟩
      · rw [h]; simp
      · rw [h]
        rw [ht] at hres
        simp only [inScope, inScopeMany, Bool.and_eq_true] at hres
        exact fills_instantiate written _ _ written.length hslots t (by rw [hwl]; exact hres.2.1)
    · intro x hx
      obtain ⟨⟨⟨k, a⟩, n⟩, hs, hpx⟩ := hparams x hx
      have ha : a ∈ rule.arguments := by
        have := (evaluated_mem.mp (List.of_mem_zip hs).1).1
        exact (List.of_mem_zip this).2
      exact fills_parameter hpx (fills_instantiate written _ _ written.length (fun k hk => fills_operand hk)
        a.ctype (by rw [hwl]; exact hctypes a ha))
    · rw [hitems]
      exact fills_bodyView (fills_addressOfObject written _ (fills_instantiate written _ _ written.length hslots
        rule.body (by rw [hwl]; exact hbody)))
  obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp hfills
  refine ⟨parts, target, hlow, fun path theory => ?_⟩
  unfold checkHeader
  rw [hr, decodeHeader_record]
  have hw : headerWritten rule ⟨rule.label, true, fname, types, names, target⟩ = written :=
    headerWritten_congr rule _ _ rfl rfl rfl
  simp [hadm, hnd, hlow, hw, htarget]

theorem instantiateMany_map (σ : Nat → Marked) (L : Nat → String) :
    ∀ (xs : List Marked), instantiateMany σ L xs = xs.map (instantiate σ L)
  | [] => rfl
  | x :: xs => by simp [instantiateMany, instantiateMany_map σ L xs]

/-- Instantiating slots that are neither lists nor the symbol `block` keeps a
template's block structure. -/
theorem bodyView_instantiate (σ : Nat → Marked) (L : Nat → String)
    (hσ : ∀ k, σ k ≠ .symbol "block" ∧ ∀ xs, σ k ≠ .list xs) (body : Marked) :
    bodyView (instantiate σ L body) = ((bodyView body).1, (bodyView body).2.map (instantiate σ L)) := by
  have plain : ∀ (b : Marked), (∀ xs, b ≠ .list (.symbol "block" :: xs)) →
      (∀ xs, instantiate σ L b ≠ .list (.symbol "block" :: xs)) →
      bodyView (instantiate σ L b) = ((bodyView b).1, (bodyView b).2.map (instantiate σ L)) := by
    intro b hb hib
    have h1 : bodyView b = (false, [b]) := by
      unfold bodyView; split
      · rename_i xs; exact absurd rfl (hb xs)
      · rfl
    have h2 : bodyView (instantiate σ L b) = (false, [instantiate σ L b]) := by
      unfold bodyView; split
      · rename_i xs heq; exact absurd heq (hib xs)
      · rfl
    rw [h1, h2]; rfl
  cases body with
  | list items =>
      rcases items with _ | ⟨hd, rest⟩
      · apply plain <;> simp [instantiate, instantiateMany]
      · by_cases hs : hd = .symbol "block"
        · subst hs
          simp [instantiate, instantiateMany, bodyView, instantiateMany_map]
        · apply plain
          · intro xs h; simp at h; exact hs h.1
          · intro xs h
            simp only [instantiate, instantiateMany, Marked.list.injEq, List.cons.injEq] at h
            cases hd with
            | arg i => exact (hσ i).1 (by simpa [instantiate] using h.1)
            | typeArg i => exact (hσ i).1 (by simpa [instantiate] using h.1)
            | symbol s => simp [instantiate] at h; exact hs (by rw [h.1])
            | _ => simp [instantiate] at h
  | arg i => exact plain _ (by simp) (fun xs => by simpa [instantiate] using (hσ i).2 _)
  | typeArg i => exact plain _ (by simp) (fun xs => by simpa [instantiate] using (hσ i).2 _)
  | _ => apply plain <;> simp [instantiate]

/-- The header macro forms: syntax parameters only, no locals, an expression's
template is not a block, and the template is not empty. -/
def macroForm (rule : Rule) : Bool :=
  rule.arguments.all (fun a => a.category == .syntax) &&
    rule.locals.isEmpty && !(rule.expression && (bodyView rule.body).1) && !(bodyView rule.body).2.isEmpty

theorem fills_foldl_comma {w : List Atom} :
    ∀ (rest : List Marked) (acc : Marked), Fills w acc → (∀ q ∈ rest, Fills w q) →
      Fills w (rest.foldl (fun acc q => .list [.symbol ",", acc, q]) acc)
  | [], acc, h, _ => h
  | q :: rest, acc, h, hq =>
      fills_foldl_comma rest _ ((fills_list w _).mpr (by simp [h, hq q List.mem_cons_self]))
        (fun x hx => hq x (List.mem_cons_of_mem _ hx))

theorem fills_staticCheckPart {w : List Atom} (fname : String) {item : Marked} (h : Fills w item) :
    Fills w (staticCheckPart fname item) := by
  unfold staticCheckPart
  simp [fills_list, h]

/-- A macro-form rule is lowered, under any name: its template's items,
static checks as expressions, joined by the comma operator. -/
theorem lowerMacro_complete (rule : Rule) (hm : macroForm rule = true) (fname : String) :
    ∃ first rest, (bodyView (instantiate (fun i => .operand i) (fun _ => "") rule.body)).2.map
        (fun item => if isStaticCheck item then staticCheckPart fname item else item) = first :: rest ∧
      lowerMacro rule fname = some (rest.foldl (fun acc q => .list [.symbol ",", acc, q]) first) := by
  simp only [macroForm, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hm
  obtain ⟨⟨⟨hargs, hloc⟩, hexpr⟩, hne⟩ := hm
  have hv := bodyView_instantiate (fun i => .operand i) (fun _ => "") (fun _ => by simp) rule.body
  obtain ⟨first, rest, hfr⟩ : ∃ first rest, (bodyView (instantiate (fun i => .operand i) (fun _ => "") rule.body)).2.map
      (fun item => if isStaticCheck item then staticCheckPart fname item else item) = first :: rest := by
    rw [hv]
    cases h : (bodyView rule.body).2 with
    | nil => exact absurd h (by simpa using hne)
    | cons x xs => exact ⟨_, _, rfl⟩
  refine ⟨first, rest, hfr, ?_⟩
  unfold lowerMacro
  simp only [hargs, hloc, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
  have hblock : (rule.expression && (bodyView (instantiate (fun i => .operand i) (fun _ => "") rule.body)).1) =
      false := by rw [hv]; simpa using hexpr
  show (if (rule.expression && (bodyView (instantiate (fun i => .operand i) (fun _ => "") rule.body)).1) = true then
      none else commaJoin ((bodyView (instantiate (fun i => .operand i) (fun _ => "") rule.body)).2.map
        (fun item => if isStaticCheck item then staticCheckPart fname item else item))) = _
  rw [hblock, hfr]
  rfl

/-- Every header macro of a decoded, admitted rule in the macro forms, with any
distinct parameter names, is admitted by `checkHeader`. -/
theorem checkHeader_macro_complete (ruleAtom : Atom) (rule : Rule) (hr : decodeRule ruleAtom = some rule)
    (hadm : admittedRule rule = true) (hm : macroForm rule = true) (fname : String)
    (types : List (String × Atom)) (names : List String) (hnd : names.Nodup) :
    ∃ m target, lowerMacro rule fname = some m ∧
      ∀ path theory, checkHeader ruleAtom (headerRecord path theory rule.label false fname types names target) =
        true := by
  obtain ⟨first, rest, hfr, hlow⟩ := lowerMacro_complete rule hm fname
  have hsc := decodeRule_inScope hr
  simp only [inScopeRule, Bool.and_eq_true, List.all_eq_true] at hsc
  let written := headerWritten rule ⟨rule.label, false, fname, types, names, .symbol ""⟩
  have hwl : written.length = rule.arguments.length := headerWritten_length _ _
  have hbody : Fills written (instantiate (fun i => .operand i) (fun _ => "") rule.body) :=
    fills_instantiate written _ _ written.length (fun k hk => fills_operand hk) rule.body
      (by rw [hwl]; exact hsc.1.1)
  have hparts : ∀ x ∈ first :: rest, Fills written x := by
    rw [← hfr]
    intro x hx
    obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hx
    have hi := fills_bodyView hbody item hitem
    split
    · exact fills_staticCheckPart fname hi
    · exact hi
  have hfills : Fills written (rest.foldl (fun acc q => .list [.symbol ",", acc, q]) first) :=
    fills_foldl_comma rest first (hparts first List.mem_cons_self) (fun q hq => hparts q (List.mem_cons_of_mem _ hq))
  obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp hfills
  refine ⟨_, target, hlow, fun path theory => ?_⟩
  unfold checkHeader
  rw [hr, decodeHeader_record]
  have hw : headerWritten rule ⟨rule.label, false, fname, types, names, target⟩ = written :=
    headerWritten_congr rule _ _ rfl rfl rfl
  simp [hadm, hnd, hlow, hw, htarget]

/-! ## Examples -/

/-- A small expression rule: `inc(x)` adds one to a modifiable `int`. -/
def incRule : Rule where
  label := "Inc"
  head := "inc"
  expression := true
  gnu := true
  arguments := [⟨"x", .modifiable, true, .list [.symbol "CType", .symbol "int"]⟩]
  result := .list [.symbol "CType", .symbol "int"]
  locals := []
  body := .list [.symbol "+=", .arg 0, .symbol "1"]

example : lowerable incRule = true ∧ inScopeRule incRule = true ∧ admittedRule incRule = true := by decide

/-- Textual macro substitution cannot capture a modifiable argument once. -/
theorem inc_not_macro_form : macroForm incRule = false := by decide

theorem inc_macro_refused (name : String) : lowerMacro incRule name = none := by
  simp [lowerMacro, incRule]

/-- Lowered from exactly the names it needs: the argument's local and the
result's temporary. -/
example : (lower incRule [.symbol "n"] ["x_1", "r_1"]).isSome = true := by decide

/-- One name short, the lowering is refused; `lower_complete` asks for enough. -/
example : (lower incRule [.symbol "n"] ["x_1"]).isSome = false := by decide

/-- A name left over is refused too: the record must list exactly the names used. -/
example : (lower incRule [.symbol "n"] ["x_1", "r_1", "spare"]).isSome = false := by decide

/-- An argument evaluated more than once is outside the declared forms, and no
supply lowers it. -/
def repeatedRule : Rule := { incRule with arguments := [⟨"x", .modifiable, false, .list [.symbol "CType", .symbol "int"]⟩] }

example : lowerable repeatedRule = false := by decide

theorem repeated_not_lowered (written : List Atom) (supply : List String) :
    lower repeatedRule written supply = none := by
  unfold lower
  by_cases h : written.length = 1
  · simp [repeatedRule, incRule, h, acquire, bind, Option.bind]
  · simp [repeatedRule, incRule, h]

/-- A c11 rule is outside the readable export's forms. -/
def c11Rule : Rule := { incRule with gnu := false }

example : lowerable c11Rule = false := by decide

theorem c11_not_lowered (written : List Atom) (supply : List String) : lower c11Rule written supply = none := by
  simp [lower, c11Rule, incRule]

/-- A template naming a slot past the arguments is not in scope, and its
lowering does not fill: the decoder never produces it. -/
def strayRule : Rule := { incRule with body := .list [.symbol "+=", .arg 1, .symbol "1"] }

example : inScopeRule strayRule = false := by decide

example : ((lower strayRule [.symbol "n"] ["x_1", "r_1"]).bind (fill [.symbol "n"])).isSome = false := by decide

end Mettapedia.GSLT.LanguageDef.MacroExportComplete
