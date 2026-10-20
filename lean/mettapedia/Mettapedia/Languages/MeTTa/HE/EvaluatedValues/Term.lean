import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Marked runtime terms

A runtime term of Hyperon Experimental carries, on every expression node, one
bit saying whether that node is the result of an evaluation. The bit belongs to
the node, not to the subtree: `(quote (fr a))` returned by a call whose
parameter is `Atom` is a value, while the `(fr a)` inside it is still code.
Observation never sees the bit: `erase` forgets it, and two terms are the same
observable atom exactly when their erasures are equal.

## Main definitions

* `MAtom` — atoms whose expression nodes carry an `evaluated` bit.
* `MAtom.erase` / `code` — forget the bits / read plain syntax as unmarked code.
* `MAtom.mark` — mark the root node as evaluated; `MAtom.isValue` — a symbol,
  variable, grounded atom, or an expression whose root node is marked.
* `MAtom.marks` — the erasures of all marked nodes of a term.
* `Subst`, `MAtom.subst` — substitution: inserted terms keep their bits, and an
  expression node whose subtree had a variable replaced loses its bit.
* `matchAtom` — one-way matching of a plain pattern against a runtime term,
  binding pattern variables to runtime subterms (bits preserved); repeated
  pattern variables compare erasures.
* `dedupErase` — keep the first occurrence of each erasure.

## Examples

* `(code (fr a)).isValue = false`: written code is unmarked.
* `(mark (code (quote (fr a))))` is a value; its child `(fr a)` is not.
* Substituting a marked `(fr a)` for `$x` in `(wrap $x)` yields an unmarked
  `wrap` node over the still-marked `(fr a)`.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Runtime atoms: the four HE atom forms, with an `evaluated` bit on every
expression node. -/
inductive MAtom where
  | symbol : String → MAtom
  | var : String → MAtom
  | grounded : GroundedValue → MAtom
  | expr : (evaluated : Bool) → (children : List MAtom) → MAtom
  deriving Repr, Inhabited

namespace MAtom

/-- Induction over runtime terms with the hypothesis for every child. -/
@[elab_as_elim]
theorem induction {motive : MAtom → Prop}
    (symbol : ∀ s, motive (.symbol s)) (var : ∀ x, motive (.var x))
    (grounded : ∀ g, motive (.grounded g))
    (expr : ∀ m cs, (∀ c ∈ cs, motive c) → motive (.expr m cs)) :
    ∀ t, motive t := by
  intro t
  refine MAtom.rec (motive_1 := motive) (motive_2 := fun cs => ∀ c ∈ cs, motive c)
    symbol var grounded (fun m cs ih => expr m cs ih) ?_ ?_ t
  · intro c h
    cases h
  · intro c cs hc hcs d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd

mutual
/-- Forget every `evaluated` bit. -/
def erase : MAtom → Atom
  | symbol s => .symbol s
  | var x => .var x
  | grounded g => .grounded g
  | expr _ cs => .expression (eraseList cs)

/-- `erase` on a list of children. -/
def eraseList : List MAtom → List Atom
  | [] => []
  | c :: cs => erase c :: eraseList cs
end

@[simp] theorem eraseList_eq (cs : List MAtom) : eraseList cs = cs.map erase := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [eraseList, ih]

@[simp] theorem erase_symbol (s : String) : (symbol s).erase = .symbol s := rfl
@[simp] theorem erase_var (x : String) : (var x).erase = .var x := rfl
@[simp] theorem erase_grounded (g : GroundedValue) : (grounded g).erase = .grounded g := rfl
@[simp] theorem erase_expr (m : Bool) (cs : List MAtom) :
    (expr m cs).erase = .expression (cs.map erase) := by
  simp [erase]

/-- Mark the root node as the result of an evaluation. Non-expressions carry
no bit and are unchanged. -/
def mark : MAtom → MAtom
  | expr _ cs => expr true cs
  | t => t

/-- Values: atoms without an expression root, and expressions whose root node
is marked. Children are not consulted. -/
def isValue : MAtom → Bool
  | expr m _ => m
  | _ => true

@[simp] theorem erase_mark (t : MAtom) : t.mark.erase = t.erase := by
  cases t <;> simp [mark]

@[simp] theorem isValue_mark (t : MAtom) : t.mark.isValue = true := by
  cases t <;> rfl

@[simp] theorem mark_mark (t : MAtom) : t.mark.mark = t.mark := by
  cases t <;> rfl

theorem mark_of_isValue {t : MAtom} (h : t.isValue = true) : t.mark = t := by
  cases t with
  | expr m cs => simp only [isValue] at h; subst h; rfl
  | _ => rfl

/-- Mark `r` exactly when it is, up to marks, the atom `a` that was evaluated:
an evaluation that returns its own term returns a value. Any other answer
keeps the bits it already has. -/
def markIf (a : Atom) (r : MAtom) : MAtom := if r.erase = a then r.mark else r

@[simp] theorem erase_markIf (a : Atom) (r : MAtom) : (r.markIf a).erase = r.erase := by
  unfold markIf; split <;> simp

theorem markIf_of_isValue {r : MAtom} (a : Atom) (h : r.isValue = true) : r.markIf a = r := by
  unfold markIf; split
  · exact mark_of_isValue h
  · rfl

theorem isValue_markIf_of_erase {r : MAtom} {a : Atom} (h : r.erase = a) :
    (r.markIf a).isValue = true := by
  simp [markIf, h]

theorem isValue_markIf_iff (a : Atom) (r : MAtom) :
    (r.markIf a).isValue = true ↔ r.erase = a ∨ r.isValue = true := by
  unfold markIf
  split
  · rename_i h; simp [h]
  · rename_i h; simp [h]

@[simp] theorem markIf_markIf (a : Atom) (r : MAtom) : (r.markIf a).markIf a = r.markIf a := by
  unfold markIf
  split
  · rename_i h; simp [h]
  · rename_i h; simp

mutual
/-- The erasures of all marked nodes, root first. -/
def marks : MAtom → List Atom
  | expr m cs => (if m then [(expr m cs).erase] else []) ++ marksList cs
  | _ => []

/-- `marks` on a list of children. -/
def marksList : List MAtom → List Atom
  | [] => []
  | c :: cs => marks c ++ marksList cs
end

@[simp] theorem marksList_eq (cs : List MAtom) : marksList cs = cs.flatMap marks := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [marksList, ih]

@[simp] theorem marks_symbol (s : String) : (symbol s).marks = [] := by simp [marks]
@[simp] theorem marks_var (x : String) : (var x).marks = [] := by simp [marks]
@[simp] theorem marks_grounded (g : GroundedValue) : (grounded g).marks = [] := by simp [marks]
@[simp] theorem marks_expr (m : Bool) (cs : List MAtom) :
    (expr m cs).marks =
      (if m then [Atom.expression (cs.map erase)] else []) ++ cs.flatMap marks := by
  simp [marks]

/-- The marks strictly below the root. -/
def childMarks : MAtom → List Atom
  | expr _ cs => cs.flatMap marks
  | _ => []

theorem marks_sub (t : MAtom) : ∀ a ∈ t.marks, a = t.erase ∨ a ∈ t.childMarks := by
  intro a ha
  cases t with
  | expr m cs =>
    simp only [marks_expr, List.mem_append] at ha
    rcases ha with ha | ha
    · split at ha
      · simp at ha; exact Or.inl (by simp [ha])
      · simp at ha
    · exact Or.inr (by simpa [childMarks] using ha)
  | _ => simp at ha

theorem childMarks_mark (t : MAtom) : t.mark.childMarks = t.childMarks := by
  cases t <;> rfl

theorem childMarks_markIf (a : Atom) (t : MAtom) : (t.markIf a).childMarks = t.childMarks := by
  unfold markIf; split
  · exact childMarks_mark t
  · rfl

theorem childMarks_sub_marks (t : MAtom) : ∀ a ∈ t.childMarks, a ∈ t.marks := by
  intro a ha
  cases t with
  | expr m cs => simp only [childMarks] at ha; simp [ha]
  | _ => simp [childMarks] at ha

end MAtom

open MAtom

mutual
/-- Plain syntax read as code: every expression node unmarked. -/
def code : Atom → MAtom
  | .symbol s => .symbol s
  | .var x => .var x
  | .grounded g => .grounded g
  | .expression as => .expr false (codeList as)

/-- `code` on a list. -/
def codeList : List Atom → List MAtom
  | [] => []
  | a :: as => code a :: codeList as
end

/-- Induction over plain atoms with the hypothesis for every child. -/
@[elab_as_elim]
theorem atomInduction {motive : Atom → Prop}
    (symbol : ∀ s, motive (.symbol s)) (var : ∀ x, motive (.var x))
    (grounded : ∀ g, motive (.grounded g))
    (expression : ∀ as, (∀ a ∈ as, motive a) → motive (.expression as)) :
    ∀ a, motive a := by
  intro a
  refine Atom.rec (motive_1 := motive) (motive_2 := fun as => ∀ a ∈ as, motive a)
    symbol var grounded (fun as ih => expression as ih) ?_ ?_ a
  · intro c h
    cases h
  · intro c cs hc hcs d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd

@[simp] theorem codeList_eq (as : List Atom) : codeList as = as.map code := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [codeList, ih]

@[simp] theorem code_symbol (s : String) : code (.symbol s) = .symbol s := by simp [code]
@[simp] theorem code_var (x : String) : code (.var x) = .var x := by simp [code]
@[simp] theorem code_grounded (g : GroundedValue) : code (.grounded g) = .grounded g := by
  simp [code]
@[simp] theorem code_expression (as : List Atom) :
    code (.expression as) = .expr false (as.map code) := by simp [code]

@[simp] theorem erase_code (a : Atom) : (code a).erase = a := by
  induction a using atomInduction with
  | expression as ih =>
    simp only [code_expression, erase_expr, List.map_map]
    congr 1
    conv => rhs; rw [← List.map_id as]
    exact List.map_congr_left fun a ha => by simpa using ih a ha
  | _ => rfl

@[simp] theorem marks_code (a : Atom) : (code a).marks = [] := by
  induction a using atomInduction with
  | expression as ih =>
    simp only [code_expression, marks_expr, Bool.false_eq_true, ↓reduceIte, List.nil_append,
      List.flatMap_map, List.flatMap_eq_nil_iff]
    exact ih
  | _ => simp

/-! ## Substitution -/

/-- A finite substitution; the first binding of a name wins. -/
abbrev Subst := List (String × MAtom)

/-- The binding of a name. -/
def Subst.lookup : Subst → String → Option MAtom
  | [], _ => none
  | (y, u) :: σ, x => if x = y then some u else Subst.lookup σ x

@[simp] theorem Subst.lookup_nil (x : String) : Subst.lookup [] x = none := rfl

theorem Subst.lookup_cons (y x : String) (u : MAtom) (σ : Subst) :
    Subst.lookup ((y, u) :: σ) x = if x = y then some u else σ.lookup x := rfl

theorem Subst.lookup_mem {σ : Subst} {x : String} {u : MAtom}
    (h : σ.lookup x = some u) : (x, u) ∈ σ := by
  induction σ with
  | nil => simp at h
  | cons p σ ih =>
    obtain ⟨y, v⟩ := p
    rw [Subst.lookup_cons] at h
    split at h
    · cases h; subst x; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

namespace MAtom

mutual
/-- Whether a substitution replaces some variable of the term. -/
def touched (σ : Subst) : MAtom → Bool
  | var x => (σ.lookup x).isSome
  | expr _ cs => touchedList σ cs
  | _ => false

/-- `touched` on a list. -/
def touchedList (σ : Subst) : List MAtom → Bool
  | [] => false
  | c :: cs => touched σ c || touchedList σ cs
end

@[simp] theorem touchedList_eq (σ : Subst) (cs : List MAtom) :
    touchedList σ cs = cs.any (touched σ) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [touchedList, ih]

mutual
/-- Substitution. Inserted terms keep their bits; an expression node whose
subtree had a variable replaced is unmarked; untouched nodes are unchanged. -/
def subst (σ : Subst) : MAtom → MAtom
  | var x => (σ.lookup x).getD (var x)
  | expr m cs => expr (m && !touchedList σ cs) (substList σ cs)
  | t => t

/-- `subst` on a list. -/
def substList (σ : Subst) : List MAtom → List MAtom
  | [] => []
  | c :: cs => subst σ c :: substList σ cs
end

@[simp] theorem substList_eq (σ : Subst) (cs : List MAtom) :
    substList σ cs = cs.map (subst σ) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [substList, ih]

@[simp] theorem subst_var (σ : Subst) (x : String) :
    (var x).subst σ = (σ.lookup x).getD (var x) := by simp [subst]
@[simp] theorem subst_symbol (σ : Subst) (s : String) : (symbol s).subst σ = symbol s := by
  simp [subst]
@[simp] theorem subst_grounded (σ : Subst) (g : GroundedValue) :
    (grounded g).subst σ = grounded g := by simp [subst]
@[simp] theorem subst_expr (σ : Subst) (m : Bool) (cs : List MAtom) :
    (expr m cs).subst σ = expr (m && !cs.any (touched σ)) (cs.map (subst σ)) := by
  simp [subst]

@[simp] theorem touched_var (σ : Subst) (x : String) :
    (var x).touched σ = (σ.lookup x).isSome := by simp [touched]
@[simp] theorem touched_expr (σ : Subst) (m : Bool) (cs : List MAtom) :
    (expr m cs).touched σ = cs.any (touched σ) := by simp [touched]
@[simp] theorem touched_symbol (σ : Subst) (s : String) : (symbol s).touched σ = false := by
  simp [touched]
@[simp] theorem touched_grounded (σ : Subst) (g : GroundedValue) :
    (grounded g).touched σ = false := by simp [touched]

/-- An untouched term is left exactly as it was, bits included. -/
theorem subst_of_not_touched (σ : Subst) :
    ∀ t : MAtom, t.touched σ = false → t.subst σ = t := by
  intro t
  induction t using MAtom.induction with
  | var x =>
    intro h
    simp only [touched_var, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    simp [h]
  | expr m cs ih =>
    intro h
    simp only [touched_expr, List.any_eq_false, Bool.not_eq_true] at h
    have hany : cs.any (touched σ) = false := by simpa using h
    simp only [subst_expr, hany, Bool.not_false, Bool.and_true]
    congr 1
    conv => rhs; rw [← List.map_id cs]
    exact List.map_congr_left fun c hc => ih c hc (h c hc)
  | _ => intro _; simp

end MAtom

/-! ## Matching -/

open MAtom in
mutual
/-- One-way matching of a plain pattern against a runtime term. Pattern
variables bind runtime subterms with their bits; a repeated variable must meet
an equal erasure. Runtime variables are matched only by pattern variables. -/
def matchAtom : Atom → MAtom → Subst → Option Subst
  | .var x, t, σ =>
    match σ.lookup x with
    | some u => if u.erase = t.erase then some σ else none
    | none => some ((x, t) :: σ)
  | .symbol s, .symbol s', σ => if s = s' then some σ else none
  | .grounded g, .grounded g', σ => if g = g' then some σ else none
  | .expression ps, .expr _ ts, σ => matchList ps ts σ
  | _, _, _ => none

/-- Matching of children, left to right. -/
def matchList : List Atom → List MAtom → Subst → Option Subst
  | [], [], σ => some σ
  | p :: ps, t :: ts, σ =>
    match matchAtom p t σ with
    | some σ' => matchList ps ts σ'
    | none => none
  | _, _, _ => none
end

/-! ## Duplicates up to erasure -/

/-- Keep the first occurrence of every erasure not already seen. -/
def dedupAux : List Atom → List MAtom → List MAtom
  | _, [] => []
  | seen, r :: rs =>
    if r.erase ∈ seen then dedupAux seen rs else r :: dedupAux (r.erase :: seen) rs

/-- Keep the first occurrence of every erasure. -/
def dedupErase (rs : List MAtom) : List MAtom := dedupAux [] rs

theorem dedupAux_spec : ∀ (seen : List Atom) (rs : List MAtom),
    ((dedupAux seen rs).map MAtom.erase).Nodup ∧
    (∀ a ∈ (dedupAux seen rs).map MAtom.erase, a ∉ seen) ∧
    (∀ a, a ∈ (dedupAux seen rs).map MAtom.erase ∨ a ∈ seen ↔
      a ∈ rs.map MAtom.erase ∨ a ∈ seen) ∧
    (dedupAux seen rs).Sublist rs := by
  intro seen rs
  induction rs generalizing seen with
  | nil => simp [dedupAux]
  | cons r rs ih =>
    by_cases h : r.erase ∈ seen
    · obtain ⟨h1, h2, h3, h4⟩ := ih seen
      simp only [dedupAux, h, ↓reduceIte]
      refine ⟨h1, h2, fun a => ?_, h4.cons r⟩
      rw [h3]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((rfl | h') | h')
        · exact Or.inr h
        · exact Or.inl h'
        · exact Or.inr h'
    · obtain ⟨h1, h2, h3, h4⟩ := ih (r.erase :: seen)
      simp only [dedupAux, h, ↓reduceIte, List.map_cons, List.nodup_cons]
      refine ⟨⟨fun hm => h2 _ hm (List.mem_cons_self), h1⟩, ?_, fun a => ?_, h4.cons_cons r⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact h
        · exact fun hs => h2 a ha (List.mem_cons_of_mem _ hs)
      · have := h3 a
        simp only [List.mem_cons] at this ⊢
        constructor
        · rintro ((rfl | h') | h')
          · exact Or.inl (Or.inl rfl)
          · rcases this.mp (Or.inl h') with h'' | h'' | h''
            · exact Or.inl (Or.inr h'')
            · exact Or.inl (Or.inl h'')
            · exact Or.inr h''
          · exact Or.inr h'
        · rintro ((rfl | h') | h')
          · exact Or.inl (Or.inl rfl)
          · rcases this.mpr (Or.inl h') with h'' | h'' | h''
            · exact Or.inl (Or.inr h'')
            · exact Or.inl (Or.inl h'')
            · exact Or.inr h''
          · exact Or.inr h'

/-- No erasure occurs twice in `dedupErase rs`. -/
theorem dedupErase_nodup (rs : List MAtom) : ((dedupErase rs).map MAtom.erase).Nodup :=
  (dedupAux_spec [] rs).1

/-- `dedupErase rs` has the same erasures as `rs`. -/
theorem mem_dedupErase_iff (rs : List MAtom) (a : Atom) :
    a ∈ (dedupErase rs).map MAtom.erase ↔ a ∈ rs.map MAtom.erase := by
  have := (dedupAux_spec [] rs).2.2.1 a
  simpa [dedupErase] using this

/-- `dedupErase rs` keeps a subsequence of `rs`. -/
theorem dedupErase_sublist (rs : List MAtom) : (dedupErase rs).Sublist rs :=
  (dedupAux_spec [] rs).2.2.2

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues
