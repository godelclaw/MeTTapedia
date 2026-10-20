import Mettapedia.GSLT.LanguageDef.LayoutLowering

/-!
# Migrating words between layout versions

When a layout changes, words written under the old version must be rewritten
under the new one. `migrate` reads a word with the old layout's checked
reading and writes the value with the new layout's encoder: `encode₂ ∘ decode₁`.

`embeds k₁ k₂` is a decidable sufficient condition for every value the old
layout writes to be writable in the new one: each admitting case of the old
layout lies, field by field, inside one admitting case of the new layout.
When it holds:
- `migrate_decode`: a migrated word reads back, under the new layout, as the
  value the old word read as;
- `migrate_some_iff`: a word migrates exactly when the old layout decodes it,
  so the refused words are exactly the old layout's invalid ones;
- `migrate_injective`: distinct old words never migrate to the same new word.

The C migration is one expression: the old validity test guarding the new
encoder with the old field readings substituted for its parameters
(`migrateExpr`); `eval_migrate` proves it computes `migrate`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LayoutMigration

open Mettapedia.GSLT.LanguageDef.LayoutCodes
open Mettapedia.GSLT.LanguageDef.LayoutLowering

/-! ## The migration and its laws -/

def migrate (k₁ k₂ : Code) (w : Nat) : Option Nat := (k₁.decode w).bind k₂.encode

/-- An admitting case lies inside another, field by field. -/
def boxIn (a b : Case) : Bool :=
  !a.reserved && !b.reserved && a.places.length == b.places.length &&
    (a.places.zip b.places).all fun pq => decide (pq.2.lo ≤ pq.1.lo ∧ pq.1.hi ≤ pq.2.hi)

/-- Every admitting case of `k₁` lies inside an admitting case of `k₂`. -/
def embeds (k₁ k₂ : Code) : Bool :=
  k₁.trie.leaves.all fun l => l.1.reserved || k₂.trie.leaves.any fun m => boxIn l.1 m.1

theorem within_of_boxIn : ∀ (ps qs : List Place) (v : List Nat), ps.length = qs.length →
    (ps.zip qs).all (fun pq => decide (pq.2.lo ≤ pq.1.lo ∧ pq.1.hi ≤ pq.2.hi)) = true →
    within ps v = true → within qs v = true
  | [], [], _, _, _, h => h
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, h => by simp [within] at h
  | p :: ps, q :: qs, x :: v, hl, hb, hw => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [within, Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
      exact ⟨⟨by omega, by omega⟩, within_of_boxIn ps qs v hl hb.2 hw.2⟩

theorem admits_of_boxIn {a b : Case} (h : boxIn a b = true) {v : List Nat} (hv : a.admits v = true) :
    b.admits v = true := by
  unfold boxIn at h
  unfold Case.admits at hv ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h hv ⊢
  exact ⟨h.1.1.2, within_of_boxIn _ _ v h.1.2 h.2 hv.2⟩

/-- Under an embedding, the new layout writes every value the old one admits. -/
theorem encode_isSome_of_embeds {k₁ k₂ : Code} (he : embeds k₁ k₂ = true) {l : Case × Nat × Nat}
    (hl : l ∈ k₁.trie.leaves) {v : List Nat} (hv : l.1.admits v = true) : (k₂.encode v).isSome = true := by
  unfold embeds at he
  rw [List.all_eq_true] at he
  have h := he l hl
  have hr : l.1.reserved = false := by
    unfold Case.admits at hv; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hv; exact hv.1
  rw [hr, Bool.false_or, List.any_eq_true] at h
  obtain ⟨m, hm, hb⟩ := h
  have hmv := admits_of_boxIn hb hv
  unfold Code.encode Code.choose
  cases hf : k₂.trie.leaves.find? (fun l => l.1.admits v) with
  | some _ => rfl
  | none => exact absurd hmv (by have := List.find?_eq_none.mp hf m hm; simpa using this)

/-- The value an old word decodes to is admitted by the old word's case. -/
theorem admits_of_decode {k : Code} {w : Nat} {v : List Nat} (hk : k.Facts) (h : k.decode w = some v) :
    ∃ l ∈ k.trie.leaves, l.1.admits v = true := by
  have hw := Code.encode_decode hk h
  unfold Code.encode at hw
  cases hc : k.choose v with
  | none => rw [hc] at hw; simp at hw
  | some l => exact ⟨l, (Code.choose_spec hc).1, (Code.choose_spec hc).2⟩

theorem migrate_some_iff {k₁ k₂ : Code} (h₁ : k₁.Facts) (he : embeds k₁ k₂ = true) (w : Nat) :
    (migrate k₁ k₂ w).isSome = (k₁.decode w).isSome := by
  unfold migrate
  cases hd : k₁.decode w with
  | none => rfl
  | some v =>
      obtain ⟨l, hl, hv⟩ := admits_of_decode h₁ hd
      simpa using encode_isSome_of_embeds he hl hv

/-- A migrated word reads back as the value the old word read as. -/
theorem migrate_decode {k₁ k₂ : Code} (h₁ : k₁.Facts) (h₂ : k₂.Facts) (he : embeds k₁ k₂ = true)
    {w : Nat} {v : List Nat} (hd : k₁.decode w = some v) :
    ∃ w', migrate k₁ k₂ w = some w' ∧ k₂.decode w' = some v := by
  obtain ⟨l, hl, hv⟩ := admits_of_decode h₁ hd
  have hs := encode_isSome_of_embeds he hl hv
  cases he2 : k₂.encode v with
  | none => rw [he2] at hs; simp at hs
  | some w' =>
      refine ⟨w', ?_, Code.decode_encode h₂ he2⟩
      simp [migrate, hd, he2]

/-- Distinct old words never migrate to the same new word. -/
theorem migrate_injective {k₁ k₂ : Code} (h₁ : k₁.Facts) (h₂ : k₂.Facts) {w₁ w₂ x : Nat}
    (m₁ : migrate k₁ k₂ w₁ = some x) (m₂ : migrate k₁ k₂ w₂ = some x) : w₁ = w₂ := by
  unfold migrate at m₁ m₂
  cases hd₁ : k₁.decode w₁ with
  | none => rw [hd₁] at m₁; simp at m₁
  | some v₁ =>
      cases hd₂ : k₁.decode w₂ with
      | none => rw [hd₂] at m₂; simp at m₂
      | some v₂ =>
          rw [hd₁] at m₁; rw [hd₂] at m₂
          simp only [Option.bind_some] at m₁ m₂
          have r₁ := Code.decode_encode h₂ m₁
          have r₂ := Code.decode_encode h₂ m₂
          rw [r₁] at r₂
          cases r₂
          have e₁ := Code.encode_decode h₁ hd₁
          have e₂ := Code.encode_decode h₁ hd₂
          rw [e₁] at e₂
          exact Option.some.inj e₂

/-! ## The C migration -/

/-- Replace each parameter `i` by `σ i`. -/
def subst (σ : Nat → Expr) : Expr → Expr
  | .var i => σ i
  | .lit n => .lit n
  | .band a b => .band (subst σ a) (subst σ b)
  | .bor a b => .bor (subst σ a) (subst σ b)
  | .bnot a => .bnot (subst σ a)
  | .shl a n => .shl (subst σ a) n
  | .shr a n => .shr (subst σ a) n
  | .add a b => .add (subst σ a) (subst σ b)
  | .sub a b => .sub (subst σ a) (subst σ b)
  | .eq a b => .eq (subst σ a) (subst σ b)
  | .le a b => .le (subst σ a) (subst σ b)
  | .ite c a b => .ite (subst σ c) (subst σ a) (subst σ b)

theorem eval_subst (σ : Nat → Expr) (env env' : List Nat) (h : ∀ i, eval env (σ i) = env'[i]?) :
    ∀ e : Expr, eval env (subst σ e) = eval env' e
  | .var i => by simp only [subst, eval, h i]
  | .lit n => rfl
  | .band a b => by simp only [subst, eval, eval_subst σ env env' h a, eval_subst σ env env' h b]
  | .bor a b => by simp only [subst, eval, eval_subst σ env env' h a, eval_subst σ env env' h b]
  | .bnot a => by simp only [subst, eval, eval_subst σ env env' h a]
  | .shl a n => by simp only [subst, eval, eval_subst σ env env' h a]
  | .shr a n => by simp only [subst, eval, eval_subst σ env env' h a]
  | .add a b => by simp only [subst, eval, eval_subst σ env env' h a, eval_subst σ env env' h b]
  | .sub a b => by simp only [subst, eval, eval_subst σ env env' h a, eval_subst σ env env' h b]
  | .eq a b => by simp only [subst, eval, eval_subst σ env env' h a, eval_subst σ env env' h b]
  | .le a b => by simp only [subst, eval, eval_subst σ env env' h a, eval_subst σ env env' h b]
  | .ite c a b => by
      simp only [subst, eval, eval_subst σ env env' h c, eval_subst σ env env' h a, eval_subst σ env env' h b]

/-- The old layout's reading of field `i`, for each field; past them, a
parameter that does not exist. -/
def readings (k₁ : Code) (n : Nat) (i : Nat) : Expr :=
  if i < n then partExpr k₁.width i k₁.trie 0 else .var (i + 1)

def migrateExpr (k₁ k₂ : Code) (n : Nat) : Expr :=
  .ite (validExpr k₁.width k₁.trie 0) (subst (readings k₁ n) (encodeExpr k₂.width k₂.trie.leaves)) (.lit 0)

/-- Every case of a layout places `n` fields. -/
def arity (k : Code) (n : Nat) : Bool := k.trie.leaves.all fun l => l.1.places.length == n

theorem parts_length {k : Code} {n : Nat} (ha : arity k n = true) (w : Nat) (hw : w < 2 ^ k.width)
    (hk : k.Facts) : (k.parts w).length = n := by
  obtain ⟨hl, _, _⟩ := Trie.locate_spec k.trie k.width w hk.depth hw
  unfold arity at ha
  rw [List.all_eq_true] at ha
  have := ha _ hl
  simp only [beq_iff_eq] at this
  simp [Code.parts, length_readPlaces, this]

theorem parts_lt_top {k : Code} (hk : k.Facts) (hf : allFit64 k = true) {w : Nat} (hw : w < 2 ^ k.width) :
    ∀ x ∈ k.parts w, x < top := by
  intro x hx
  obtain ⟨hl, _, _⟩ := Trie.locate_spec k.trie k.width w hk.depth hw
  unfold Code.parts readPlaces at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have hfit := (placed_of_facts hk hf _ hl p hp).1
  unfold fits64 at hfit
  simp only [decide_eq_true_eq] at hfit
  have := LayoutAlgebra.get_lt (w % 2 ^ (k.width - (k.trie.locate k.width w).2.2)) p.slot.shift p.slot.width
  omega

/-- The generated migration computes `migrate`, writing 0 for a word the old
layout does not decode. -/
theorem eval_migrate {k₁ k₂ : Code} {n : Nat} (h₁ : k₁.Facts) (h₂ : k₂.Facts) (f₁ : allFit64 k₁ = true)
    (f₂ : allFit64 k₂ = true) (a₁ : arity k₁ n = true) (a₂ : arity k₂ n = true) {w : Nat}
    (hw : w < 2 ^ k₁.width) : eval [w] (migrateExpr k₁ k₂ n) = some ((migrate k₁ k₂ w).getD 0) := by
  have hlen := parts_length a₁ w hw h₁
  have hσ : ∀ i, eval [w] (readings k₁ n i) = (k₁.parts w)[i]? := by
    intro i
    unfold readings
    split
    · rename_i hi
      rw [eval_parts h₁ f₁ i hw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    · rename_i hi
      rw [List.getElem?_eq_none (by omega)]
      simp [eval]
  have hlens : ∀ l ∈ k₂.trie.leaves, l.1.places.length = (k₁.parts w).length := by
    intro l hl
    unfold arity at a₂
    rw [List.all_eq_true] at a₂
    have := a₂ l hl
    simp only [beq_iff_eq] at this
    rw [this, hlen]
  obtain ⟨henc, _⟩ := eval_encode h₂ f₂ (parts_lt_top h₁ f₁ hw) hlens
  unfold migrateExpr
  simp only [eval, eval_valid_code h₁ f₁ hw, eval_subst _ [w] (k₁.parts w) hσ, henc, choose_some]
  unfold migrate
  cases hd : k₁.decode w with
  | none => simp [top]
  | some v =>
      have hv : k₁.parts w = v := Code.decode_parts hd
      simp [hv]

/-! ## Recorded migrations -/

open Mettapedia.GSLT.LanguageDef.LayoutDeclarations (Declaration decodeLayout admitted facts_of_admitted)
open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)

def lowerMigration (old new : Declaration) : Function :=
  ⟨new.name ++ "_from_" ++ old.name, ["old"], "word", migrateExpr old.code new.code old.fields.length⟩

/-- `(cesta-layout-migration/1 OLD NEW (Function …))`, as `cesta layout functions` prints it. -/
def decodeMigration : Atom → Option (String × String × Function)
  | .list [.symbol "cesta-layout-migration/1", .symbol old, .symbol new, f] => do
      pure (old, new, ← decodeFunction f)
  | _ => none

/-- A recorded migration is admitted when both versions are, the new version
reads the same fields and embeds the old one, and the recorded function is
the lowering of `encode₂ ∘ decode₁`. -/
def migrationAdmitted (oldAtom newAtom migrationAtom : Atom) : Bool :=
  match decodeLayout oldAtom, decodeLayout newAtom, decodeMigration migrationAtom with
  | some o, some n, some (on, nn, f) =>
      admitted oldAtom && admitted newAtom && allFit64 o.code && allFit64 n.code && on == o.name &&
        nn == n.name && o.fields.map (·.name) == n.fields.map (·.name) &&
        arity o.code o.fields.length && arity n.code o.fields.length && embeds o.code n.code &&
        f == lowerMigration o n
  | _, _, _ => false

/-- What an admitted migration computes: for every old word, the new word of
the value it decodes to, which the new version reads back as that value; 0
on refusal. A successful migration can also encode as 0, so callers must use
the old layout's validity predicate to distinguish refusal. -/
theorem migration_of_admitted {oa na ma : Atom} (h : migrationAdmitted oa na ma = true) :
    ∃ o n f, decodeLayout oa = some o ∧ decodeLayout na = some n ∧ f = lowerMigration o n ∧
      (∀ w, w < 2 ^ o.code.width → eval [w] f.body = some ((migrate o.code n.code w).getD 0)) ∧
      (∀ w v, o.code.decode w = some v → ∃ w', migrate o.code n.code w = some w' ∧ n.code.decode w' = some v) ∧
      (∀ w, (migrate o.code n.code w).isSome = (o.code.decode w).isSome) := by
  unfold migrationAdmitted at h
  cases ho : decodeLayout oa with
  | none => rw [ho] at h; simp at h
  | some o =>
      cases hn : decodeLayout na with
      | none => rw [ho, hn] at h; simp at h
      | some n =>
          cases hm : decodeMigration ma with
          | none => rw [ho, hn, hm] at h; simp at h
          | some r =>
              obtain ⟨on, nn, f⟩ := r
              rw [ho, hn, hm] at h
              simp only [Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hoa, hna⟩, fo⟩, fn⟩, _⟩, _⟩, _⟩, ao⟩, an⟩, he⟩, hf⟩ := h
              obtain ⟨o', ho', facto⟩ := facts_of_admitted hoa
              obtain ⟨n', hn', factn⟩ := facts_of_admitted hna
              rw [ho] at ho'; cases ho'
              rw [hn] at hn'; cases hn'
              refine ⟨o, n, f, rfl, rfl, hf, ?_, ?_, ?_⟩
              · intro w hw
                rw [hf]
                exact eval_migrate facto factn fo fn ao an hw
              · intro w v hd
                exact migrate_decode facto factn he hd
              · intro w
                exact migrate_some_iff facto he w

/-- The C sentinel loses the distinction that `Option` retains: both words
fit the byte, but only the first is admitted, and both C results are zero. -/
theorem zero_sentinel_ambiguous :
    let k : Code := ⟨8, .leaf ⟨[⟨⟨0, 8⟩, 0, 0, 127⟩], false⟩⟩
    migrate k k 0 = some 0 ∧ migrate k k 128 = none ∧
      eval [0] (migrateExpr k k 1) = some 0 ∧ eval [128] (migrateExpr k k 1) = some 0 := by
  decide

end Mettapedia.GSLT.LanguageDef.LayoutMigration
