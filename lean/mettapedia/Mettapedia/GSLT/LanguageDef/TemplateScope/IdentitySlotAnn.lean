import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRelation
import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFresh
import Mettapedia.GSLT.LanguageDef.TemplateScope.QuotePatternEmbed

/-!
# Template scope: the slot model and the identity model, statically related

Rule M and lexical fresh each have two elaborations: the slot model's
(`elabMS`, `elabLF`: names are slots `(owner, spelling)`, a `let` that
introduces names and a `new` block are activations) and the identity model's
(`elabMId`, `elabLFId`: names are binder identities, every binder is allocated
in its frame).  Both elaborations of one profile take the same decisions: which
names a lambda owns, which names a `let` introduces, which names a `new` block
declares.  `Ann` records those decisions (an annotated text); `Ann.slotOf` and
`Ann.idOf` are the two elaborations of an annotated text.

The main result, `rel_ann`, relates `slotOf` and `idOf` by `IdSlot.Rel` in the
setting `SC` (sealed code related through `codeOf` and `codeI`), on every
well-formed annotated text: the identity of every name a lambda owns is apart
from every frame-allocated name of its body that is live, and the reserved
names of pending activations are distinct.

## The conditions

* A pattern quotation is code. A hole is an outer name, so the free-name claim
  is the same claim as for any pattern. A binder of the code, and a free
  parameter of the code, is named inside the code and related by `CodeRel`.
* No `new` block with names on the matched spine of a pattern.
* The identity of every name a lambda owns is its frame's head, a `new` at the
  frame's body, or a pattern that is not an activation (`KeyOK`).
* The resolution environment and the owners a scope writes are scope owners:
  not a binder of code, and not a free parameter of code.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace IdSlot

variable {S : Type u} {X : Type v}

/-! ## Annotated text -/

/-- Authored text with an elaboration's decisions recorded: the names each
lambda owns with their identities, the names each `let` introduces (`letA`,
nonempty), the names each `new` block declares. -/
inductive Ann (S : Type u) (X : Type v) where
  | sym (s : S)
  | fn (F : S)
  | sv (y : X)
  | par (z : X)
  | lam (z : X) (own : List X) (key : X → SlotId X) (body : Ann S X)
  | app (f a : Ann S X)
  | quote (c : Src S X)
  | pquote (c : Src S X)
  | letP (p w b : Ann S X)
  | letA (y₀ : X) (ys : List X) (p w b : Ann S X)
  | alt (t₁ t₂ : Ann S X)
  | new (ys : List X) (body : Ann S X)

namespace Ann

/-- The spellings written, outside sealed code. -/
def names : Ann S X → List X
  | .sv y => [y]
  | .lam _ _ _ b => names b
  | .app f a => names f ++ names a
  | .pquote c => Src.names c
  | .letP p w b => names p ++ names w ++ names b
  | .letA _ _ p w b => names p ++ names w ++ names b
  | .alt t₁ t₂ => names t₁ ++ names t₂
  | .new _ b => names b
  | _ => []

/-- The `new` blocks with names are off the matched spine. -/
def NewFree : Ann S X → Prop
  | .app f a => NewFree f ∧ NewFree a
  | .pquote _ => True
  | .letP p _ _ => NewFree p
  | .letA _ _ p _ _ => NewFree p
  | .new [] b => NewFree b
  | .new (_ :: _) _ => False
  | _ => True

/-- A `let` that introduces names sits at the relative position (a `new` block
is not a position of its own). -/
def LetAAt : Ann S X → Owner → Prop
  | .new _ b, P => LetAAt b P
  | .letA _ _ _ _ _, [] => True
  | .app f _, 0 :: P => LetAAt f P
  | .app _ a, 1 :: P => LetAAt a P
  | .letP p _ _, 0 :: P => LetAAt p P
  | .letP _ w _, 1 :: P => LetAAt w P
  | .letP _ _ b, 2 :: P => LetAAt b P
  | .letA _ _ p _ _, 0 :: P => LetAAt p P
  | .letA _ _ _ w _, 1 :: P => LetAAt w P
  | .letA _ _ _ _ b, 2 :: P => LetAAt b P
  | .alt t _, 0 :: P => LetAAt t P
  | .alt _ u, 1 :: P => LetAAt u P
  | _, _ => False

end Ann

/-- **An admissible identity for a name a frame owns**, the frame's body being
`b` at `F`: the frame's head, a `new` at the frame's body, or a pattern of the
body that is not an activation. -/
def KeyOK (F : Owner) (b : Ann S X) (k : SlotId X) : Prop :=
  k.intro = .head ∨ (k.intro = .new ∧ k.site = F) ∨
    (k.intro = .pat ∧ ∃ P, k.site = F ++ P ∧ ¬ b.LetAAt P)

namespace Ann

variable [DecidableEq X]

/-- **Well-formed annotated text** at the identity position `pos`: patterns
without `new` blocks on their spine, admissible identities for every lambda's
own names, and, for a pattern quotation, one `CodeRel` between the two
elaborations, in a form rooted at any scope owner. A hole is a free name of that
code. A binder of the code and a free parameter of the code are named inside
it, so the relation's one map sends both, and neither is a free name of the
sealed quotation. -/
def WF : Owner → Ann S X → Prop
  | pos, .lam _ own key b =>
      (∀ y ∈ own, (key y).spell = y ∧ (key y).frame = pos ++ [0] ∧ KeyOK (pos ++ [0]) b (key y)) ∧
        WF (pos ++ [0]) b
  | pos, .app f a => WF (pos ++ [0]) f ∧ WF (pos ++ [1]) a
  | _, .pquote c =>
      ∀ (R : Owner) (env : REnv X) (envI : IEnv X), scopeOwner R →
        (∀ y, codeBound (env y) = false) → (∀ y, env y ≠ codeFreeParam) →
        CodeRel (R₁ := fun (_ : Slot X) => True) (R₂ := fun (_ : BId X) => True)
          codeQ (fun _ => True) (codeMapHoles env envI)
          (sealParams (codeAt R (some env) [] [] [] c))
          (sealParams (codeIAt R (some envI) [] [] [] c))
  | pos, .letP p w b => p.NewFree ∧ WF (pos ++ [0]) p ∧ WF (pos ++ [1]) w ∧ WF (pos ++ [2]) b
  | pos, .letA _ _ p w b => p.NewFree ∧ WF (pos ++ [0]) p ∧ WF (pos ++ [1]) w ∧ WF (pos ++ [2]) b
  | pos, .alt t₁ t₂ => WF (pos ++ [0]) t₁ ∧ WF (pos ++ [1]) t₂
  | pos, .new _ b => WF pos b
  | _, _ => True

/-- Annotated text whose holes are outer names. A pattern quotation is open
when every free name of its sealed elaboration is the surrounding scope's
slot of a spelling written in the code. Code binders are not free names. -/
def Open : Ann S X → Prop
  | .lam _ _ _ b => Open b
  | .app f a => Open f ∧ Open a
  | .pquote c =>
      ∀ (R : Owner) (env : REnv X) (n : Nm (Slot X)),
        n ∈ freeNames (sealParams (codeAt R (some env) [] [] [] c)) →
        ∃ y ∈ Src.names c, n = .src (env y, y)
  | .letP p w b => Open p ∧ Open w ∧ Open b
  | .letA _ _ p w b => Open p ∧ Open w ∧ Open b
  | .alt t₁ t₂ => Open t₁ ∧ Open t₂
  | .new _ b => Open b
  | _ => True

theorem Open.of_WF {pos : Owner} {t : Ann S X} (h : t.WF pos) : t.Open := by
  induction t generalizing pos with
  | pquote c =>
      intro R env n hn
      rw [freeNames_sealParams] at hn
      exact mem_freeNames_codeAt R env [] [] [] c n hn
  | lam _ _ _ _ ih =>
      simp only [WF] at h
      exact ih h.2
  | app _ _ ihf iha =>
      simp only [WF] at h
      exact ⟨ihf h.1, iha h.2⟩
  | letP _ _ _ ihp ihw ihb =>
      simp only [WF] at h
      exact ⟨ihp h.2.1, ihw h.2.2.1, ihb h.2.2.2⟩
  | letA _ _ _ _ _ ihp ihw ihb =>
      simp only [WF] at h
      exact ⟨ihp h.2.1, ihw h.2.2.1, ihb h.2.2.2⟩
  | alt _ _ ih₁ ih₂ =>
      simp only [WF] at h
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | new _ _ ih =>
      simp only [WF] at h
      exact ih h
  | sym _ => trivial
  | fn _ => trivial
  | sv _ => trivial
  | par _ => trivial
  | quote _ => trivial

/-- Parameters of authored text not bound by one of its lambdas. -/
def srcFreePars : Src S X → List X
  | .par z => [z]
  | .lam z _ b => (srcFreePars b).filter fun z' => decide (z' ≠ z)
  | .form z b => (srcFreePars b).filter fun z' => decide (z' ≠ z)
  | .app f a => srcFreePars f ++ srcFreePars a
  | .pquote c => srcFreePars c
  | .letS p w b _ => srcFreePars p ++ srcFreePars w ++ srcFreePars b
  | .unify p w b => srcFreePars p ++ srcFreePars w ++ srcFreePars b
  | .alt t₁ t₂ => srcFreePars t₁ ++ srcFreePars t₂
  | .new _ b => srcFreePars b
  | _ => []

/-- Parameters not bound in the text, outside sealed code. -/
def freePars : Ann S X → List X
  | .par z => [z]
  | .lam z _ _ b => (freePars b).filter fun z' => decide (z' ≠ z)
  | .app f a => freePars f ++ freePars a
  | .pquote c => srcFreePars c
  | .letP p w b => freePars p ++ freePars w ++ freePars b
  | .letA _ _ p w b => freePars p ++ freePars w ++ freePars b
  | .alt t₁ t₂ => freePars t₁ ++ freePars t₂
  | .new _ b => freePars b
  | _ => []

/-! ## The two elaborations of annotated text -/

/- The root of the form being elaborated: the holes of its quotations are the
root's head slots. -/
variable (R : Owner)

/-- **The slot model**: names are slots; a lambda owns its names as slots of its
body's position; a `let` that introduces names and a `new` block are
activations. -/
def slotOf (env : REnv X) (pos : Owner) : Ann S X → Tm S (Slot X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => slotVar env y
  | .par z => .pvar (parName z)
  | .lam z own _ b =>
      .lam (parName z) (own.map fun y => (pos ++ [0], y))
        (slotOf (env.update own (pos ++ [0])) (pos ++ [0]) b)
  | .app f a => .app (slotOf env (pos ++ [0]) f) (slotOf env (pos ++ [1]) a)
  | .quote c => .quote (codeOf R c)
  | .pquote c => .pquote (sealParams (codeAt R (some env) [] [] [] c))
  | .letP p w b =>
      .letP (slotOf env (pos ++ [0]) p) (slotOf env (pos ++ [1]) w) (slotOf env (pos ++ [2]) b)
  | .letA y₀ ys p w b =>
      .app
        (.lam (letParam (pos ++ [2]) y₀) ((y₀ :: ys).map fun y => (pos ++ [2], y))
          (.letP (slotOf (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [0]) p)
            (.pvar (letParam (pos ++ [2]) y₀))
            (slotOf (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [2]) b)))
        (slotOf env (pos ++ [1]) w)
  | .alt t₁ t₂ => .alt (slotOf env (pos ++ [0]) t₁) (slotOf env (pos ++ [1]) t₂)
  | .new [] b => slotOf env (pos ++ [0]) b
  | .new (y₀ :: ys) b =>
      newBlock pos y₀ ys (slotOf (env.update (y₀ :: ys) (pos ++ [0])) (pos ++ [0]) b)

/-- **The identity model**: names are binder identities; every binder is
allocated in its frame (`fr`), and a lambda's own list is its frame's slots
that occur in its body. -/
def idOf (env : IEnv X) (pv : X → Owner) (fr pos : Owner) : Ann S X → Tm S (BId X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => iVar (env y)
  | .par z => .pvar (.src (.par z (pv z)))
  | .lam z own key b =>
      .lam (.src (.par z pos))
        (frameSlots (pos ++ [0]) (idOf (env.set own key) (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b))
        (idOf (env.set own key) (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b)
  | .app f a => .app (idOf env pv fr (pos ++ [0]) f) (idOf env pv fr (pos ++ [1]) a)
  | .quote c => .quote (codeI R c)
  | .pquote c => .pquote (sealParams (codeIAt R (some env) [] [] [] c))
  | .letP p w b =>
      .letP (idOf env pv fr (pos ++ [0]) p) (idOf env pv fr (pos ++ [1]) w)
        (idOf env pv fr (pos ++ [2]) b)
  | .letA y₀ ys p w b =>
      .letP (idOf (env.set (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩) pv fr (pos ++ [0]) p)
        (idOf env pv fr (pos ++ [1]) w)
        (idOf (env.set (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩) pv fr (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (idOf env pv fr (pos ++ [0]) t₁) (idOf env pv fr (pos ++ [1]) t₂)
  | .new ys b => idOf (env.set ys fun y => ⟨y, fr, pos, .new⟩) pv fr pos b

end Ann

/-! ## The setting -/

/-- A free parameter of code, on the slot side. -/
def codeFreeS : Nm (Slot X) → Bool
  | .src (o, _) => decide (o = codeFreeParam)
  | .inst _ n => codeFreeS n

/-- A free parameter of code, on the identity side. -/
def codeFreeI : Nm (BId X) → Bool
  | .src (.code _ o) => decide (o = codeFreeParam)
  | .inst _ n => codeFreeI n
  | _ => false

/-- The owner written on a slot name. -/
def ownerS : Nm (Slot X) → Owner
  | .src (o, _) => o
  | .inst _ n => ownerS n

/-- The owner written on a name of code. A slot or a scope parameter has none. -/
def ownerI : Nm (BId X) → Owner
  | .src (.code _ o) => o
  | .inst _ n => ownerI n
  | _ => []

/-- The spelling of a slot name. -/
def spellS : Nm (Slot X) → X
  | .src (_, y) => y
  | .inst _ n => spellS n

/-- The spelling of an identity. -/
def spellI : Nm (BId X) → X
  | .src (.slot k) => k.spell
  | .src (.par z _) => z
  | .src (.code y _) => y
  | .inst _ n => spellI n

/-- A name of the code: a binder, or a free parameter. An activation copy is not. -/
def codeParamS : Nm (Slot X) → Prop
  | .src (o, _) => codeBound o = true ∨ o = codeFreeParam
  | .inst _ _ => False

/-- The same on the identity side. A slot or a scope parameter is not. -/
def codeParamI : Nm (BId X) → Prop
  | .src (.code _ o) => codeBound o = true ∨ o = codeFreeParam
  | _ => False

/-- Holes that `matchCode` treats alike. Two free parameters of code agree by
spelling. Two scope holes agree without a spelling. A free parameter of code
and a scope hole do not. -/
def holeMatch (n₁ : Nm (Slot X)) (n₂ : Nm (BId X)) : Prop :=
  (codeFreeS n₁ = true ∧ codeFreeI n₂ = true ∧ spellS n₁ = spellI n₂) ∨
    (codeFreeS n₁ = false ∧ codeFreeI n₂ = false)

/-- Whether a slot name is a hole, copying the code-identity equation on
constructors and recurring under an activation. `CodeId.hole` recurses the
same way, so an activation copy of a binder stays a binder. -/
def holeRecS : Nm (Slot X) → Bool
  | .src (o, _) => !codeBound o
  | .inst _ n => holeRecS n

/-- The same for an identity. A slot and a scope parameter are holes. -/
def holeRecI : Nm (BId X) → Bool
  | .src (.code _ o) => !codeBound o
  | .src _ => true
  | .inst _ n => holeRecI n

/-- `CodeId.hole` on a slot is the hole bit `holeRecS` uses. -/
theorem slotHole_eq_holeRecS : ∀ n : Nm (Slot X), slotHole n = holeRecS n
  | .src _ => rfl
  | .inst _ n => slotHole_eq_holeRecS n

/-- `CodeId.hole` on an identity is the hole bit `holeRecI` uses. -/
theorem bIdHole_eq_holeRecI : ∀ n : Nm (BId X), bIdHole n = holeRecI n
  | .src (.code _ _) => rfl
  | .src (.slot _) => rfl
  | .src (.par _ _) => rfl
  | .inst _ n => bIdHole_eq_holeRecI n

theorem hole_eq_holeRecS [DecidableEq X] (n : Nm (Slot X)) :
    CodeId.hole n = holeRecS n :=
  slotHole_eq_holeRecS n

theorem hole_eq_holeRecI [DecidableEq X] (n : Nm (BId X)) :
    CodeId.hole n = holeRecI n :=
  bIdHole_eq_holeRecI n

/-- An activation copy keeps the hole bit, on both models. -/
theorem hole_instL [DecidableEq X] (ρ : Path) (n : Nm (Slot X)) :
    CodeId.hole (.inst ρ n) = CodeId.hole n := rfl

theorem hole_instI [DecidableEq X] (ρ : Path) (n : Nm (BId X)) :
    CodeId.hole (.inst ρ n) = CodeId.hole n := rfl

/-- Store names are holes together, or binders of code together. -/
def scVarHole (n₁ : Nm (Slot X)) (n₂ : Nm (BId X)) : Prop :=
  holeRecS n₁ = holeRecI n₂

/-- Parameters of code share an owner. Parameters of the scope are neither. -/
def scParOK (x₁ : Nm (Slot X)) (x₂ : Nm (BId X)) : Prop :=
  (codeParamS x₁ ∧ codeParamI x₂ ∧ ownerS x₁ = ownerI x₂) ∨
    (¬ codeParamS x₁ ∧ ¬ codeParamI x₂)

/-- Written as a source name, rather than as an activation copy.
`CodeId.same` does not look through a copy, so two binders `matchCode` may
enter are both originals or both copies. -/
def actSrcS : Nm (Slot X) → Bool
  | .src _ => true
  | .inst _ _ => false

/-- The same on the identity side. -/
def actSrcI : Nm (BId X) → Bool
  | .src _ => true
  | .inst _ _ => false

/-- A scope binder is a hole at any own lists. A free parameter of code is a
hole that owns nothing and agrees by spelling. A binder of code is not a hole,
owns nothing, and shares an owner. The two names are both originals or both
activation copies. -/
def scBare (x₁ : Nm (Slot X)) (own₁ : List (Slot X)) (x₂ : Nm (BId X))
    (own₂ : List (BId X)) : Prop :=
  (holeRecS x₁ = true ∧ holeRecI x₂ = true ∧ holeMatch x₁ x₂ ∧
      ((codeFreeS x₁ = true ∧ codeFreeI x₂ = true) → own₁ = [] ∧ own₂ = []) ∧
      actSrcS x₁ = actSrcI x₂) ∨
    (holeRecS x₁ = false ∧ holeRecI x₂ = false ∧ own₁ = [] ∧ own₂ = [] ∧
      ownerS x₁ = ownerI x₂ ∧ actSrcS x₁ = actSrcI x₂)

/-- `matchCode` enters a lambda when both binders are binders of code, and when
both are free parameters of code with one spelling. A scope hole is not entered. -/
def scEnter (x₁ : Nm (Slot X)) (x₂ : Nm (BId X)) : Prop :=
  (holeRecS x₁ = false ∧ holeRecI x₂ = false) ∨
    (codeFreeS x₁ = true ∧ codeFreeI x₂ = true ∧ spellS x₁ = spellI x₂)

/-- A free parameter of code is a hole: its owner is not a binder. -/
theorem holeRecS_of_codeFree {n : Nm (Slot X)} (h : codeFreeS n = true) :
    holeRecS n = true := by
  induction n with
  | src s =>
      obtain ⟨o, _⟩ := s
      rw [codeFreeS] at h
      rw [holeRecS, of_decide_eq_true h]
      rfl
  | inst _ n ih =>
      rw [codeFreeS] at h
      rw [holeRecS]
      exact ih h

/-- Second-side names that are holes together, or binders of code together. -/
def scPreserve (a b : Nm (BId X)) : Prop :=
  holeRecI a = holeRecI b

/-- An own list excluded by `True` is empty. -/
theorem list_eq_nil_of_not_true {α : Type*} {l : List α} (h : ∀ s ∈ l, ¬ True) : l = [] := by
  cases l with
  | nil => rfl
  | cons s _ => exact absurd trivial (h s List.mem_cons_self)

theorem scEnter_nil {x₁ : Nm (Slot X)} {own₁ : List (Slot X)} {x₂ : Nm (BId X)}
    {own₂ : List (BId X)} (hb : scBare x₁ own₁ x₂ own₂) (he : scEnter x₁ x₂) :
    own₁ = [] ∧ own₂ = [] := by
  rcases he with ⟨hL, _⟩ | ⟨hf₁, hf₂, _⟩
  · rcases hb with ⟨hl, _, _, _, _⟩ | ⟨_, _, e₁, e₂, _, _⟩
    · rw [hL] at hl
      exact absurd hl Bool.false_ne_true
    · exact ⟨e₁, e₂⟩
  · rcases hb with ⟨_, _, hm, hown, _⟩ | ⟨hlS, _, _, _, _, _⟩
    · rcases hm with ⟨_, _, _⟩ | ⟨hc, _⟩
      · exact hown ⟨hf₁, hf₂⟩
      · rw [hf₁] at hc
        exact absurd hc Bool.false_ne_true.symm
    · rw [holeRecS_of_codeFree hf₁] at hlS
      exact absurd hlS Bool.false_ne_true.symm

theorem sc_varHole_instL {n : Nm (Slot X)} {m : Nm (BId X)} (ρ : Path)
    (h : scVarHole n m) : scVarHole (.inst ρ n) m := h

theorem sc_varHole_rename {n : Nm (Slot X)} {m m' : Nm (BId X)}
    (h : scVarHole n m) (p : scPreserve m m') : scVarHole n m' := h.trans p

/-- `codeMapHoles` preserves the hole bit. -/
theorem scVarHole_map [DecidableEq X] (env : REnv X) (envI : IEnv X) :
    ∀ n, scVarHole n (codeMapHoles env envI n)
  | .inst _ n => scVarHole_map env envI n
  | .src (o, y) => by
      by_cases hb : codeBound o = true ∨ o = codeFreeParam
      · rw [codeMapHoles_owned hb, scVarHole, holeRecS, holeRecI]
      · by_cases he : o = env y
        · have hB : codeBound o = false := by
            cases hco : codeBound o
            · rfl
            · exact absurd (Or.inl hco) hb
          simp only [codeMapHoles, if_neg hb, if_pos he, scVarHole, holeRecS, holeRecI]
          rw [hB]
          rfl
        · simp only [codeMapHoles, if_neg hb, if_neg he, scVarHole, holeRecS, holeRecI]

/-- `codeMapHoles` sends parameters of code to parameters of the same owner,
and every other name to a name that is not a parameter of code. -/
theorem scParOK_map [DecidableEq X] (env : REnv X) (envI : IEnv X) :
    ∀ x, scParOK x (codeMapHoles env envI x)
  | .inst _ _ => Or.inr ⟨fun h => h.elim, fun h => h.elim⟩
  | .src (o, y) => by
      by_cases hb : codeBound o = true ∨ o = codeFreeParam
      · rw [codeMapHoles_owned hb]
        exact Or.inl ⟨hb, hb, rfl⟩
      · by_cases he : o = env y
        · simp only [codeMapHoles, if_neg hb, if_pos he]
          exact Or.inr ⟨fun h => hb h, fun h => h.elim⟩
        · simp only [codeMapHoles, if_neg hb, if_neg he]
          exact Or.inr ⟨fun h => hb h, fun h => hb h⟩

/-- An activation copy of a related binder pair stays related. Both sides gain
one copy, so `CodeId.same` still refuses both or accepts both. -/
theorem scBare_inst {ρ : Path} {x : Nm (Slot X)} {m : Nm (BId X)}
    {own₁ : List (Slot X)} {own₂ : List (BId X)} (h : scBare x own₁ m own₂) :
    scBare (.inst ρ x) own₁ (.inst ρ m) own₂ := by
  rcases h with ⟨hS, hI, hm, hown, _⟩ | ⟨hS, hI, e₁, e₂, ho, _⟩
  · refine Or.inl ⟨?_, ?_, ?_, ?_, rfl⟩
    · rw [holeRecS]; exact hS
    · rw [holeRecI]; exact hI
    · rcases hm with ⟨a, b, c⟩ | ⟨a, b⟩
      · exact Or.inl ⟨by rw [codeFreeS]; exact a, by rw [codeFreeI]; exact b,
          by rw [spellS, spellI]; exact c⟩
      · exact Or.inr ⟨by rw [codeFreeS]; exact a, by rw [codeFreeI]; exact b⟩
    · intro hcf
      rw [codeFreeS, codeFreeI] at hcf
      exact hown hcf
  · refine Or.inr ⟨?_, ?_, e₁, e₂, ?_, rfl⟩
    · rw [holeRecS]; exact hS
    · rw [holeRecI]; exact hI
    · rw [ownerS, ownerI]; exact ho

/-- Own lists that `True` excludes are empty, and `codeMapHoles` sends a binder
to a binder `scBare` accepts. -/
theorem scBare_map [DecidableEq X] (env : REnv X) (envI : IEnv X) {x : Nm (Slot X)}
    {own₁ : List (Slot X)} {own₂ : List (BId X)} (h₁ : ∀ s ∈ own₁, ¬ True)
    (h₂ : ∀ s ∈ own₂, ¬ True) : scBare x own₁ (codeMapHoles env envI x) own₂ := by
  have e₁ : own₁ = [] := list_eq_nil_of_not_true h₁
  have e₂ : own₂ = [] := list_eq_nil_of_not_true h₂
  induction x with
  | inst ρ n ih =>
      simpa [codeMapHoles] using scBare_inst (ρ := ρ) ih
  | src s =>
      obtain ⟨o, y⟩ := s
      by_cases hb : codeBound o = true ∨ o = codeFreeParam
      · rw [codeMapHoles_owned hb]
        rcases hb with hb | hf
        · exact Or.inr ⟨by rw [holeRecS, hb]; rfl, by rw [holeRecI, hb]; rfl, e₁, e₂, rfl, rfl⟩
        · refine Or.inl ⟨?_, ?_, Or.inl ⟨?_, ?_, rfl⟩, fun _ => ⟨e₁, e₂⟩, rfl⟩
          · rw [holeRecS, hf]; rfl
          · rw [holeRecI, hf]; rfl
          · rw [codeFreeS, hf]; rfl
          · rw [codeFreeI, hf]; rfl
      · have hB : codeBound o = false := by
          cases hco : codeBound o
          · rfl
          · exact absurd (Or.inl hco) hb
        have hF : o ≠ codeFreeParam := fun h => hb (Or.inr h)
        by_cases he : o = env y
        · simp only [codeMapHoles, if_neg hb, if_pos he]
          refine Or.inl ⟨?_, rfl, Or.inr ⟨?_, rfl⟩, fun hcf => ?_, rfl⟩
          · rw [holeRecS, hB]; rfl
          · rw [codeFreeS]; exact decide_eq_false hF
          · rw [codeFreeS] at hcf
            exact absurd ((decide_eq_false hF).symm.trans hcf.1) Bool.false_ne_true
        · simp only [codeMapHoles, if_neg hb, if_neg he]
          refine Or.inl ⟨?_, ?_, Or.inr ⟨?_, ?_⟩, fun hcf => ?_, rfl⟩
          · rw [holeRecS, hB]; rfl
          · rw [holeRecI, hB]; rfl
          · rw [codeFreeS]; exact decide_eq_false hF
          · rw [codeFreeI]; exact decide_eq_false hF
          · rw [codeFreeS] at hcf
            exact absurd ((decide_eq_false hF).symm.trans hcf.1) Bool.false_ne_true

/-- A scope parameter is a hole on both sides, so the lambda may carry any own
lists and `matchCode` does not enter it. -/
theorem scBare_scope {z : X} {pos : Owner} {own₁ : List (Slot X)} {own₂ : List (BId X)} :
    scBare (parName z) own₁ (.src (.par z pos)) own₂ := by
  refine Or.inl ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩, fun h => ?_, rfl⟩
  have hc : codeFreeS (parName z) = false := rfl
  exact absurd (hc.symm.trans h.1) Bool.false_ne_true

theorem scParOK_scope {z : X} {pos : Owner} :
    scParOK (parName z) (.src (.par z pos)) := by
  refine Or.inr ⟨?_, fun h => h.elim⟩
  intro h
  rcases h with h | h
  · simp [codeBound] at h
  · simp [codeFreeParam] at h

/-- The slot model's code names in the identity model. A binder of code and a
free parameter of code keep their owner, as a code name. A slot of any other
owner is a hole: the head slot of that owner, `⟨y, o, o, .head⟩`. The hole of a
quotation written in a form rooted at `R` is `(R, y)`, so it is sent to the
form's head slot: for the query, sealed code and the body's `$` share that one
cell; for an equation, it is a slot of the equation's frame. The map is
injective. -/
def codeFwd : Nm (Slot X) → Nm (BId X)
  | .src (o, y) =>
      if codeBound o = true ∨ o = codeFreeParam then .src (.code y o)
      else .src (.slot ⟨y, o, o, .head⟩)
  | .inst ρ n => .inst ρ (codeFwd n)

/-- The identity model's code names in the slot model. A slot is read back at
its frame. -/
def codeBack : Nm (BId X) → Nm (Slot X)
  | .src (.code y o) => .src (o, y)
  | .src (.slot k) => .src (k.frame, k.spell)
  | .src (.par z _) => .src ([], z)
  | .inst ρ n => .inst ρ (codeBack n)

/-- A name of code keeps its owner. -/
theorem codeFwd_code {o : Owner} {y : X} (h : codeBound o = true ∨ o = codeFreeParam) :
    codeFwd (.src (o, y)) = .src (.code y o) := by
  simp only [codeFwd, if_pos h]

/-- A slot of a scope owner is that owner's head slot. -/
theorem codeFwd_scope {o : Owner} {y : X} (h : scopeOwner o) :
    codeFwd (.src (o, y)) = .src (.slot ⟨y, o, o, .head⟩) := by
  simp only [codeFwd, if_neg (not_code_of_scopeOwner h)]

theorem codeBack_codeFwd : ∀ n : Nm (Slot X), codeBack (codeFwd n) = n
  | .src (o, y) => by
      by_cases h : codeBound o = true ∨ o = codeFreeParam
      · rw [codeFwd_code h]
        rfl
      · simp only [codeFwd, if_neg h]
        rfl
  | .inst _ n => by simp only [codeFwd, codeBack, codeBack_codeFwd n]

theorem codeFwd_injective : Function.Injective (codeFwd : Nm (Slot X) → Nm (BId X)) :=
  Function.LeftInverse.injective codeBack_codeFwd

theorem codeFwd_root (y : X) :
    codeFwd (.src ([], y)) = .src (.slot ⟨y, [], [], .head⟩) :=
  codeFwd_scope ⟨rfl, by decide⟩

theorem codeBinder_ne_nil (pos : Owner) : codeBinder pos ≠ [] :=
  List.cons_ne_nil 9 (1 :: pos)

theorem codeFreeParam_ne_nil : (codeFreeParam : Owner) ≠ [] :=
  List.cons_ne_nil 9 []

theorem owner_code_ne_nil {o : Owner}
    (h : codeBound o = true ∨ o = codeFreeParam) : o ≠ [] := by
  rcases h with hb | rfl
  · intro e
    subst e
    simp [codeBound] at hb
  · exact codeFreeParam_ne_nil

/-- **The root of a form**: `[]` for the query, `[5]` for an equation.  A hole of
sealed code written in a form is a slot of the form's root. -/
def formRoot (o : Owner) : Prop := o = [] ∨ o = [5]

theorem formRoot.scopeOwner {o : Owner} (h : formRoot o) : scopeOwner o := by
  rcases h with rfl | rfl
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩

/-- No owner written below a position other than `5` is a form root. -/
theorem not_formRoot_append (pos : Owner) {i : ℕ} (hi : i ≠ 5) : ¬ formRoot (pos ++ [i]) := by
  rintro (h | h)
  · simp at h
  · cases pos with
    | nil =>
        simp only [List.nil_append, List.cons.injEq, and_true] at h
        exact hi h
    | cons a l => simp at h

theorem codeFwd_src : ∀ s : Slot X, ∃ s', codeFwd (.src s : Nm (Slot X)) = .src s'
  | (o, y) => by
      by_cases h : codeBound o = true ∨ o = codeFreeParam
      · exact ⟨_, codeFwd_code h⟩
      · exact ⟨_, codeFwd_scope ⟨by
          rcases Bool.eq_false_or_eq_true (codeBound o) with hb | hb
          · exact absurd (Or.inl hb) h
          · exact hb, fun e => h (Or.inr e)⟩⟩

/-- **The setting of the two models**: sealed code is related through the two
code maps, written in a form rooted at a scope owner (`codeQ`); the query's own
slots (owner `[]`) and identities (frame `[]`) are the names no binder owns.
Holes agree by recurring under an activation. A binder of code, and a free
parameter of code, owns nothing; those are the names `matchCode` may enter. A
scope hole is not entered, at any own lists.  A hole of sealed code is a slot of
a form root. -/
def SC [DecidableEq X] : Setting S (Slot X) (BId X) where
  Q := codeQ
  root₁ s := s.1 = []
  root₂ b := ∃ k : SlotId X, b = .slot k ∧ k.frame = []
  varHole := scVarHole
  parOK := scParOK
  bareLam := scBare
  enterLam := scEnter
  enter_nil := scEnter_nil
  preserve := scPreserve
  preserve_refl _ := rfl
  preserve_inst _ _ := rfl
  varHole_instL := sc_varHole_instL
  varHole_rename := sc_varHole_rename
  codeMap := codeFwd
  codeMap_inj := codeFwd_injective
  codeMap_src := codeFwd_src
  codeMap_root s hs := by
    obtain ⟨o, y⟩ := s
    change o = [] at hs
    subst hs
    exact ⟨_, codeFwd_root y, _, rfl, rfl⟩
  hole s := formRoot s.1

variable [DecidableEq X]

/-- Whether matching code can enter this text. A lambda's own result is stable.
A `let` that introduces names, and a `new` block that declares names, are
pending activations. -/
def annOK : Ann S X → Bool
  | .app f a => annOK f && annOK a
  | .letP p w b => annOK p && annOK w && annOK b
  | .letA _ _ _ _ _ => false
  | .alt t u => annOK t && annOK u
  | .new [] b => annOK b
  | .new (_ :: _) _ => false
  | .lam _ _ _ _ => true
  | _ => true

/-- The name map inside a binder at owner `o` declaring `ys` with identities
`k`. -/
def bindν (ν : Nm (Slot X) → Nm (BId X)) (o : Owner) (ys : List X) (k : X → SlotId X) :
    Nm (Slot X) → Nm (BId X)
  | .src (o', y) => if o' = o ∧ y ∈ ys then .src (.slot (k y)) else ν (.src (o', y))
  | .inst ρ n => ν (.inst ρ n)

theorem ownKey_map_src {o o' : Owner} {ys : List X} {y : X} :
    ownKey (ys.map fun y => (o, y)) (.src (o', y) : Nm (Slot X)) = decide (o' = o ∧ y ∈ ys) := by
  simp only [ownKey, List.contains_eq_mem, List.mem_map, Prod.mk.injEq]
  by_cases h : o' = o ∧ y ∈ ys
  · rw [decide_eq_true h]
    exact decide_eq_true ⟨y, h.2, h.1.symm, rfl⟩
  · rw [decide_eq_false h]
    apply decide_eq_false
    rintro ⟨y', hy', ho, rfl⟩
    exact h ⟨ho.symm, hy'⟩

theorem bindν_off {ν : Nm (Slot X) → Nm (BId X)} {o : Owner} {ys : List X} {k : X → SlotId X}
    {n : Nm (Slot X)} (h : ownKey (ys.map fun y => (o, y)) n = false) : bindν ν o ys k n = ν n := by
  cases n with
  | src s =>
      obtain ⟨o', y⟩ := s
      rw [ownKey_map_src, decide_eq_false_iff_not] at h
      simp only [bindν, if_neg h]
  | inst ρ n => rfl

theorem bindν_on {ν : Nm (Slot X) → Nm (BId X)} {o : Owner} {ys : List X} {k : X → SlotId X}
    {y : X} (h : y ∈ ys) : bindν ν o ys k (.src (o, y)) = .src (.slot (k y)) := by
  simp [bindν, h]

theorem bindν_not_mem {ν : Nm (Slot X) → Nm (BId X)} {o o' : Owner} {ys : List X}
    {k : X → SlotId X} {y : X} (h : y ∉ ys) : bindν ν o ys k (.src (o', y)) = ν (.src (o', y)) := by
  simp only [bindν]
  rw [if_neg (fun h' => h h'.2)]

/-! ## Free names and parameters of the slot model -/

namespace Ann

theorem update_of_mem {env : REnv X} {ys : List X} {o : Owner} {y : X} (h : y ∈ ys) :
    env.update ys o y = o := by
  simp [REnv.update, h]

theorem update_of_not_mem {env : REnv X} {ys : List X} {o : Owner} {y : X} (h : y ∉ ys) :
    env.update ys o y = env y := by
  simp [REnv.update, h]

/- The root of the form being elaborated. -/
variable (R : Owner)

/-- **Free names of the slot model**: occurrences of the environment's slots
of spellings written in open text.  A pattern quotation is sealed, so the
claim is stated for open text. -/
theorem freeNames_slotOf : ∀ (t : Ann S X) (env : REnv X) (pos : Owner) (n : Nm (Slot X)),
    t.Open → n ∈ freeNames (t.slotOf R env pos) → ∃ y ∈ t.names, n = .src (env y, y)
  | .sym _, _, _, _, _, h => by simp [slotOf, freeNames] at h
  | .fn _, _, _, _, _, h => by simp [slotOf, freeNames] at h
  | .sv y, env, _, n, _, h => by
      simp only [slotOf, slotVar, freeNames, List.mem_singleton] at h
      exact ⟨y, by simp [names], h⟩
  | .par _, _, _, _, _, h => by simp [slotOf, freeNames] at h
  | .lam _ own _ b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen h.1
      by_cases hyo : y ∈ own
      · rw [update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at h
        exact absurd ⟨rfl, hyo⟩ h.2
      · exact ⟨y, hy, by rw [update_of_not_mem hyo]⟩
  | .app f a, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf f _ _ n hopen.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf a _ _ n hopen.2 h
        exact ⟨y, by simp [names, hy], rfl⟩
  | .quote _, _, _, _, _, h => by simp [slotOf, freeNames] at h
  | .pquote c, env, _, n, hopen, h => by
      simp only [slotOf, freeNames] at h
      obtain ⟨y, hy, rfl⟩ := hopen R env n h
      exact ⟨y, by simpa [names] using hy, rfl⟩
  | .letP p w b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf p _ _ n hopen.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf w _ _ n hopen.2.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen.2.2 h
        exact ⟨y, by simp [names, hy], rfl⟩
  | .letA y₀ ys p w b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil, or_false] at h
      rcases h with ⟨h | h, ho⟩ | h
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf p _ _ n hopen.1 h
        by_cases hyo : y ∈ y₀ :: ys
        · rw [update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at ho
          exact absurd ⟨rfl, hyo⟩ ho
        · exact ⟨y, by simp [names, hy], by rw [update_of_not_mem hyo]⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen.2.2 h
        by_cases hyo : y ∈ y₀ :: ys
        · rw [update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at ho
          exact absurd ⟨rfl, hyo⟩ ho
        · exact ⟨y, by simp [names, hy], by rw [update_of_not_mem hyo]⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf w _ _ n hopen.2.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
  | .alt t₁ t₂, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeNames, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf t₁ _ _ n hopen.1 h
        exact ⟨y, by simp [names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := freeNames_slotOf t₂ _ _ n hopen.2 h
        exact ⟨y, by simp [names, hy], rfl⟩
  | .new [] b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf] at h
      obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen h
      exact ⟨y, by simp [names, hy], rfl⟩
  | .new (y₀ :: ys) b, env, _, n, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, newBlock, freeNames, List.mem_append, List.mem_filter,
        Bool.not_eq_eq_eq_not, Bool.not_true, List.not_mem_nil] at h
      obtain ⟨h, ho⟩ | ⟨⟨⟩, _⟩ := h
      obtain ⟨y, hy, rfl⟩ := freeNames_slotOf b _ _ n hopen h
      by_cases hyo : y ∈ y₀ :: ys
      · rw [update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at ho
        exact absurd ⟨rfl, hyo⟩ ho
      · exact ⟨y, by simp [names, hy], by rw [update_of_not_mem hyo]⟩

/-- **Free parameters of the slot model** are written parameters, by spelling. -/
theorem freeParams_slotOf : ∀ (t : Ann S X) (env : REnv X) (pos : Owner) (x : Nm (Slot X)),
    t.Open → x ∈ freeParams (t.slotOf R env pos) → ∃ z ∈ t.freePars, x = .src ([], z)
  | .sym _, _, _, _, _, h => by simp [slotOf, freeParams] at h
  | .fn _, _, _, _, _, h => by simp [slotOf, freeParams] at h
  | .sv _, _, _, _, _, h => by simp [slotOf, slotVar, freeParams] at h
  | .par z, _, _, x, _, h => by
      simp only [slotOf, freeParams, List.mem_singleton] at h
      exact ⟨z, by simp [freePars], h⟩
  | .lam _ _ _ b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_filter, decide_eq_true_eq] at h
      obtain ⟨z', hz', rfl⟩ := freeParams_slotOf b _ _ x hopen h.1
      refine ⟨z', ?_, rfl⟩
      simp only [freePars, List.mem_filter, decide_eq_true_eq]
      exact ⟨hz', fun e => h.2 (by rw [e]; rfl)⟩
  | .app f a, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf f _ _ x hopen.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf a _ _ x hopen.2 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
  | .quote _, _, _, _, _, h => by simp [slotOf, freeParams] at h
  | .pquote _, _, _, _, _, h => by
      simp only [slotOf, freeParams] at h
      rw [freeParams_sealParams] at h
      simp at h
  | .letP p w b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf p _ _ x hopen.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf w _ _ x hopen.2.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf b _ _ x hopen.2.2 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
  | .letA _ _ p w b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at h
      rcases h with ⟨(h | h) | h, hne⟩ | h
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf p _ _ x hopen.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · exact absurd h hne
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf b _ _ x hopen.2.2 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf w _ _ x hopen.2.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
  | .alt t₁ t₂, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, freeParams, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf t₁ _ _ x hopen.1 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf t₂ _ _ x hopen.2 h
        exact ⟨z, by simp [freePars, hz], rfl⟩
  | .new [] b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf] at h
      obtain ⟨z, hz, rfl⟩ := freeParams_slotOf b _ _ x hopen h
      exact ⟨z, by simp [freePars, hz], rfl⟩
  | .new (_ :: _) b, _, _, x, hopen, h => by
      simp only [Open] at hopen
      simp only [slotOf, newBlock, freeParams, List.mem_append, List.mem_filter,
        decide_eq_true_eq, List.mem_singleton] at h
      rcases h with ⟨h, _⟩ | ⟨h, hne⟩
      · obtain ⟨z, hz, rfl⟩ := freeParams_slotOf b _ _ x hopen h
        exact ⟨z, by simp [freePars, hz], rfl⟩
      · exact absurd h hne

end Ann

/-! ## Frame slots -/

omit [DecidableEq X] in
theorem mem_vars_of_mem_freeNames {Y : Type v} [DecidableEq Y] {n : Nm Y} :
    ∀ {t : Tm S Y}, n ∈ freeNames t → n ∈ Tm.vars t
  | .sym _, h => by simp [freeNames] at h
  | .fn _, h => by simp [freeNames] at h
  | .var _, h => by simpa [freeNames, Tm.vars] using h
  | .pvar _, h => by simp [freeNames] at h
  | .lam _ _ b, h => by
      simp only [freeNames, List.mem_filter] at h
      exact mem_vars_of_mem_freeNames (t := b) h.1
  | .app f a, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      rcases h with h | h
      · exact Or.inl (mem_vars_of_mem_freeNames h)
      · exact Or.inr (mem_vars_of_mem_freeNames h)
  | .quote _, h => by simp [freeNames] at h
  | .pquote c, h => by
      simp only [freeNames] at h
      exact mem_vars_of_mem_freeNames (t := c) h
  | .letP p w b, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (mem_vars_of_mem_freeNames h))
      · exact Or.inl (Or.inr (mem_vars_of_mem_freeNames h))
      · exact Or.inr (mem_vars_of_mem_freeNames h)
  | .alt t₁ t₂, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      rcases h with h | h
      · exact Or.inl (mem_vars_of_mem_freeNames h)
      · exact Or.inr (mem_vars_of_mem_freeNames h)

theorem slot_mem_frameSlots {F : Owner} {b : Tm S (BId X)} {k : SlotId X}
    (h : (.src (.slot k) : Nm (BId X)) ∈ Tm.vars b) (hk : k.frame = F) :
    BId.slot k ∈ frameSlots F b := by
  unfold frameSlots
  rw [List.mem_eraseDups]
  exact List.mem_filterMap.2 ⟨_, h, by simp [frameSlotOf, hk]⟩

theorem frame_of_mem_frameSlots {F : Owner} {b : Tm S (BId X)} {x : BId X}
    (h : x ∈ frameSlots F b) : ∃ k : SlotId X, x = .slot k ∧ k.frame = F := by
  unfold frameSlots at h
  rw [List.mem_eraseDups] at h
  obtain ⟨n, _, hn⟩ := List.mem_filterMap.1 h
  cases n with
  | src b =>
      cases b with
      | slot k =>
          by_cases hk : k.frame = F
          · simp only [frameSlotOf, if_pos hk, Option.some.injEq] at hn
            exact ⟨k, hn.symm, hk⟩
          · simp [frameSlotOf, hk] at hn
      | par _ _ => simp [frameSlotOf] at hn
      | code _ => simp [frameSlotOf] at hn
  | inst _ _ => simp [frameSlotOf] at hn

theorem ownKey_frameSlots {F : Owner} {b : Tm S (BId X)} {k : SlotId X}
    (h : (.src (.slot k) : Nm (BId X)) ∈ freeNames b) (hk : k.frame = F) :
    ownKey (frameSlots F b) (.src (.slot k) : Nm (BId X)) = true := by
  simp only [ownKey, List.contains_eq_mem, decide_eq_true_eq]
  exact slot_mem_frameSlots (mem_vars_of_mem_freeNames h) hk

theorem ownKey_frameSlots_false {F : Owner} {b : Tm S (BId X)} {k : SlotId X}
    (hk : k.frame ≠ F) : ownKey (frameSlots F b) (.src (.slot k) : Nm (BId X)) = false := by
  simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
  intro hm
  obtain ⟨k', hk', hF⟩ := frame_of_mem_frameSlots hm
  cases hk'
  exact hk hF

theorem ownKey_map_true {o : Owner} {ys : List X} {n : Nm (Slot X)}
    (h : ownKey (ys.map fun y => (o, y)) n = true) : ∃ y ∈ ys, n = .src (o, y) := by
  cases n with
  | src s =>
      obtain ⟨o', y⟩ := s
      rw [ownKey_map_src, decide_eq_true_iff] at h
      obtain ⟨rfl, hy⟩ := h
      exact ⟨y, hy, rfl⟩
  | inst _ _ => simp [ownKey] at h

/-! ## Reserved names -/

/-- **The reserved names of a related pair**, at the frame `fr` and the identity
position `pos` of the text `t`: distinct, each a slot of the frame made inside
`t` by an activation (a `let` that introduces names, at a position where `t`
has one, or a `new` block), each free on the identity side; one made by a `new`
at `pos` itself is spelled unlike every free name of the slot side. -/
structure ResOK (fr pos : Owner) (t : Ann S X) (t₁ : Tm S (Slot X)) (t₂ : Tm S (BId X))
    (Res : List (Nm (BId X))) : Prop where
  nodup : Res.Nodup
  shape : ∀ m ∈ Res, ∃ k : SlotId X, m = .src (.slot k) ∧ k.frame = fr ∧ k.intro ≠ .head ∧
    ∃ q, k.site = pos ++ q ∧ (k.intro = .pat → t.LetAAt q)
  free : ∀ m ∈ Res, m ∈ freeNames t₂
  news : ∀ k : SlotId X, (.src (.slot k) : Nm (BId X)) ∈ Res → k.intro = .new → k.site = pos →
    ∀ n ∈ freeNames t₁, spellS n ≠ k.spell

theorem ResOK.nil {fr pos : Owner} {t : Ann S X} {t₁ : Tm S (Slot X)} {t₂ : Tm S (BId X)} :
    ResOK fr pos t t₁ t₂ [] :=
  ⟨List.nodup_nil, (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩

omit [DecidableEq X] in
theorem site_child_ne {pos q q' : Owner} {i j : ℕ} (hij : i ≠ j) :
    pos ++ [i] ++ q ≠ pos ++ [j] ++ q' := by
  intro h
  rw [List.append_assoc, List.append_assoc] at h
  have := List.append_cancel_left h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at this
  exact hij this.1

omit [DecidableEq X] in
theorem site_child_ne_self {pos q : Owner} {i : ℕ} : pos ++ [i] ++ q ≠ pos := by
  intro h
  have := congrArg List.length h
  simp at this

/-- The site of a reserved name of a child. -/
theorem ResOK.site {fr pos : Owner} {i : ℕ} {t : Ann S X} {t₁ : Tm S (Slot X)}
    {t₂ : Tm S (BId X)} {R : List (Nm (BId X))} (h : ResOK fr (pos ++ [i]) t t₁ t₂ R) :
    ∀ m ∈ R, ∃ k : SlotId X, m = .src (.slot k) ∧ ∃ q, k.site = pos ++ [i] ++ q := by
  intro m hm
  obtain ⟨k, hk, -, -, q, hq, -⟩ := h.shape m hm
  exact ⟨k, hk, q, hq⟩

/-- Reserved names of two different children are apart. -/
theorem ResOK.apart {fr pos : Owner} {i j : ℕ} (hij : i ≠ j) {t u : Ann S X}
    {t₁ u₁ : Tm S (Slot X)} {t₂ u₂ : Tm S (BId X)} {R R' : List (Nm (BId X))}
    (h : ResOK fr (pos ++ [i]) t t₁ t₂ R) (h' : ResOK fr (pos ++ [j]) u u₁ u₂ R') :
    ∀ m ∈ R, m ∉ R' := by
  intro m hm hm'
  obtain ⟨k, rfl, q, hq⟩ := h.site m hm
  obtain ⟨k', hk', q', hq'⟩ := h'.site _ hm'
  injection hk' with hk'
  injection hk' with hk'
  subst hk'
  exact site_child_ne hij (hq.symm.trans hq')

/-- The shape of a child's reserved name, seen from the parent. -/
theorem ResOK.lift {fr pos : Owner} {i : ℕ} {t c : Ann S X} {t₁ : Tm S (Slot X)}
    {t₂ : Tm S (BId X)} {R : List (Nm (BId X))} (h : ResOK fr (pos ++ [i]) c t₁ t₂ R)
    (hlet : ∀ q, c.LetAAt q → t.LetAAt (i :: q)) :
    ∀ m ∈ R, ∃ k : SlotId X, m = .src (.slot k) ∧ k.frame = fr ∧ k.intro ≠ .head ∧
      ∃ q, k.site = pos ++ q ∧ (k.intro = .pat → t.LetAAt q) := by
  intro m hm
  obtain ⟨k, hk, hf, hh, q, hq, hp⟩ := h.shape m hm
  exact ⟨k, hk, hf, hh, i :: q, by rw [hq]; simp, fun e => hlet q (hp e)⟩

/-- A child's reserved names are not at the parent's position. -/
theorem ResOK.news_child {fr pos : Owner} {i : ℕ} {c : Ann S X} {t₁ : Tm S (Slot X)}
    {t₂ : Tm S (BId X)} {R : List (Nm (BId X))} (h : ResOK fr (pos ++ [i]) c t₁ t₂ R)
    {k : SlotId X} (hk : (.src (.slot k) : Nm (BId X)) ∈ R) : k.site ≠ pos := by
  obtain ⟨k', hk', q, hq⟩ := h.site _ hk
  injection hk' with hk'
  injection hk' with hk'
  subst hk'
  rw [hq]
  exact site_child_ne_self

/-! ## The conditions of a frame -/

/-- **The conditions of a frame**: the body of a lambda (or of a clause), with
the frame's own names at owner `O` on the slot side and at frame `F` on the
identity side, satisfies the side conditions of `Rel.lam`. -/
theorem frame_conds {R : Owner} {own : List X} {O F : Owner} {key : X → SlotId X}
    {νb μb : Nm (Slot X) → Nm (BId X)} {b : Ann S X} {env' : REnv X} {b₂ : Tm S (BId X)}
    {Rb : List (Nm (BId X))} {ok : Bool}
    (hrel : Rel SC νb μb .code Rb ok (b.slotOf R env' O) b₂)
    (hres : ResOK F F b (b.slotOf R env' O) b₂ Rb)
    (hO : ∀ y ∈ b.names, y ∈ own → env' y = O)
    (hνown : ∀ y ∈ own, νb (.src (O, y)) = .src (.slot (key y)))
    (hout : ∀ y ∈ b.names, y ∉ own →
      ∃ k : SlotId X, νb (.src (env' y, y)) = .src (.slot k) ∧ k.frame ≠ F)
    (hkey : ∀ y ∈ own, (key y).spell = y ∧ (key y).frame = F ∧ KeyOK F b (key y))
    (hopen : b.Open) :
    (∀ n ∈ freeNames (b.slotOf R env' O),
      ownKey (frameSlots F b₂) (νb n) = ownKey (own.map fun y => (O, y)) n) ∧
    (∀ m ∈ Rb, ownKey (frameSlots F b₂) m = true) ∧
    (∀ n ∈ freeNames (b.slotOf R env' O), ∀ n' ∈ freeNames (b.slotOf R env' O),
      ownKey (own.map fun y => (O, y)) n = true → ownKey (own.map fun y => (O, y)) n' = true →
        νb n = νb n' → n = n') ∧
    (∀ n ∈ freeNames (b.slotOf R env' O), ownKey (own.map fun y => (O, y)) n = true → νb n ∉ Rb) := by
  have hown_iff : ∀ y ∈ b.names,
      ownKey (own.map fun y => (O, y)) (.src (env' y, y)) = decide (y ∈ own) := by
    intro y hy
    rw [ownKey_map_src]
    by_cases h : y ∈ own
    · rw [hO y hy h]; simp [h]
    · simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨y, hy, rfl⟩ := Ann.freeNames_slotOf R b env' O n hopen hn
    rw [hown_iff y hy]
    by_cases h : y ∈ own
    · have hm := hrel.mem_freeNames hn
      rw [hO y hy h, hνown y h] at hm ⊢
      rw [decide_eq_true h]
      exact ownKey_frameSlots hm (hkey y h).2.1
    · obtain ⟨k, hk, hkF⟩ := hout y hy h
      rw [hk, decide_eq_false h]
      exact ownKey_frameSlots_false hkF
  · intro m hm
    obtain ⟨k, rfl, hkF, -, -⟩ := hres.shape m hm
    exact ownKey_frameSlots (hres.free _ hm) hkF
  · intro n hn n' hn' ho ho' he
    obtain ⟨y, hy, rfl⟩ := Ann.freeNames_slotOf R b env' O n hopen hn
    obtain ⟨y', hy', rfl⟩ := Ann.freeNames_slotOf R b env' O n' hopen hn'
    rw [hown_iff y hy, decide_eq_true_iff] at ho
    rw [hown_iff y' hy', decide_eq_true_iff] at ho'
    rw [hO y hy ho, hO y' hy' ho', hνown y ho, hνown y' ho'] at he
    rw [hO y hy ho, hO y' hy' ho']
    have hkk : key y = key y' := by
      injection he with he
      injection he
    have hyy : y = y' := by rw [← (hkey y ho).1, ← (hkey y' ho').1, hkk]
    rw [hyy]
  · intro n hn ho hmem
    obtain ⟨y, hy, rfl⟩ := Ann.freeNames_slotOf R b env' O n hopen hn
    rw [hown_iff y hy, decide_eq_true_iff] at ho
    have hmem' : (.src (.slot (key y)) : Nm (BId X)) ∈ Rb := by
      rw [hO y hy ho, hνown y ho] at hmem
      exact hmem
    obtain ⟨k, hk, -, hkh, q, hq, hpat⟩ := hres.shape _ hmem'
    have hkk : key y = k := by
      injection hk with hk
      injection hk
    subst hkk
    rcases (hkey y ho).2.2 with hh | ⟨hn', hs⟩ | ⟨hp, P, hP, hnot⟩
    · exact hkh hh
    · exact hres.news (key y) hmem' hn' hs _ hn (by simp [spellS, (hkey y ho).1])
    · rw [hP] at hq
      have hPq : P = q := List.append_cancel_left hq
      subst hPq
      exact hnot (hpat hp)

/-! ## Combining reserved names -/

omit [DecidableEq X] in
theorem nodup_append_of {α : Type*} {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ a ∈ l₁, a ∉ l₂) : (l₁ ++ l₂).Nodup :=
  List.nodup_append.2 ⟨h₁, h₂, fun a ha _ hb e => hd a ha (e ▸ hb)⟩

/-- Two children. -/
theorem ResOK.two {fr pos : Owner} {i j : ℕ} (hij : i ≠ j) {t c d : Ann S X}
    {t₁ c₁ d₁ : Tm S (Slot X)} {t₂ c₂ d₂ : Tm S (BId X)} {R R' : List (Nm (BId X))}
    (hc : ResOK fr (pos ++ [i]) c c₁ c₂ R) (hd : ResOK fr (pos ++ [j]) d d₁ d₂ R')
    (hlc : ∀ q, c.LetAAt q → t.LetAAt (i :: q)) (hld : ∀ q, d.LetAAt q → t.LetAAt (j :: q))
    (hfc : ∀ m ∈ freeNames c₂, m ∈ freeNames t₂) (hfd : ∀ m ∈ freeNames d₂, m ∈ freeNames t₂) :
    ResOK fr pos t t₁ t₂ (R ++ R') where
  nodup := nodup_append_of hc.nodup hd.nodup (hc.apart hij hd)
  shape m hm := by
    rcases List.mem_append.1 hm with h | h
    · exact hc.lift hlc m h
    · exact hd.lift hld m h
  free m hm := by
    rcases List.mem_append.1 hm with h | h
    · exact hfc m (hc.free m h)
    · exact hfd m (hd.free m h)
  news k hk _ hs := by
    rcases List.mem_append.1 hk with h | h
    · exact absurd hs (hc.news_child h)
    · exact absurd hs (hd.news_child h)

/-- Three children. -/
theorem ResOK.three {fr pos : Owner} {t c d e : Ann S X}
    {t₁ c₁ d₁ e₁ : Tm S (Slot X)} {t₂ c₂ d₂ e₂ : Tm S (BId X)} {R R' R'' : List (Nm (BId X))}
    (hc : ResOK fr (pos ++ [0]) c c₁ c₂ R) (hd : ResOK fr (pos ++ [1]) d d₁ d₂ R')
    (he : ResOK fr (pos ++ [2]) e e₁ e₂ R'')
    (hlc : ∀ q, c.LetAAt q → t.LetAAt (0 :: q)) (hld : ∀ q, d.LetAAt q → t.LetAAt (1 :: q))
    (hle : ∀ q, e.LetAAt q → t.LetAAt (2 :: q))
    (hfc : ∀ m ∈ freeNames c₂, m ∈ freeNames t₂) (hfd : ∀ m ∈ freeNames d₂, m ∈ freeNames t₂)
    (hfe : ∀ m ∈ freeNames e₂, m ∈ freeNames t₂) :
    ResOK fr pos t t₁ t₂ (R ++ R' ++ R'') where
  nodup := nodup_append_of (nodup_append_of hc.nodup hd.nodup (hc.apart (by decide) hd)) he.nodup
    (fun m hm => by
      rcases List.mem_append.1 hm with h | h
      · exact hc.apart (by decide) he m h
      · exact hd.apart (by decide) he m h)
  shape m hm := by
    rcases List.mem_append.1 hm with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hc.lift hlc m h
      · exact hd.lift hld m h
    · exact he.lift hle m h
  free m hm := by
    rcases List.mem_append.1 hm with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hfc m (hc.free m h)
      · exact hfd m (hd.free m h)
    · exact hfe m (he.free m h)
  news k hk _ hs := by
    rcases List.mem_append.1 hk with h | h
    · rcases List.mem_append.1 h with h | h
      · exact absurd hs (hc.news_child h)
      · exact absurd hs (hd.news_child h)
    · exact absurd hs (he.news_child h)

/-! ## Activations -/

/-- **A `let` that introduces names**: an activation on the slot side, a plain
`let` on the identity side, whose introduced identities are reserved until the
activation runs. -/
theorem rel_letA_of {k : Kd} (hk : k ≠ .val) {ν μ : Nm (Slot X) → Nm (BId X)} {O : Owner}
    (hO : ¬ formRoot O) {y₀ : X} {ys : List X} {fr pos : Owner} {ℓ : Nm (Slot X)}
    {t p w b : Ann S X} {t₁ p₁ w₁ b₁ : Tm S (Slot X)} {p₂ w₂ b₂ : Tm S (BId X)}
    {Rp Rw Rb : List (Nm (BId X))} {ow op ob : Bool}
    (hℓp : ℓ ∉ freeParams p₁) (hℓb : ℓ ∉ freeParams b₁)
    (hw : Rel SC ν μ .code Rw ow w₁ w₂)
    (hp : Rel SC (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩) μ .pat Rp op p₁ p₂)
    (hb : Rel SC (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩) μ .code Rb ob b₁ b₂)
    (hrp : ResOK fr (pos ++ [0]) p p₁ p₂ Rp) (hrw : ResOK fr (pos ++ [1]) w w₁ w₂ Rw)
    (hrb : ResOK fr (pos ++ [2]) b b₁ b₂ Rb)
    (hl : t.LetAAt []) (hl0 : ∀ q, p.LetAAt q → t.LetAAt (0 :: q))
    (hl1 : ∀ q, w.LetAAt q → t.LetAAt (1 :: q)) (hl2 : ∀ q, b.LetAAt q → t.LetAAt (2 :: q)) :
    ∃ Res, Rel SC ν μ k Res false
        (.app (.lam ℓ ((y₀ :: ys).map fun y => (O, y)) (.letP p₁ (.pvar ℓ) b₁)) w₁)
        (.letP p₂ w₂ b₂) ∧
      ResOK fr pos t t₁ (.letP p₂ w₂ b₂) Res := by
  have hRh : ∀ m ∈ ((((freeNames p₁ ++ freeNames b₁).filter
      fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
        (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩)).dedup),
      ∃ n ∈ freeNames p₁ ++ freeNames b₁, ∃ y ∈ y₀ :: ys,
        n = .src (O, y) ∧ m = .src (.slot ⟨y, fr, pos, .pat⟩) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hm)
    obtain ⟨hn, ho⟩ := List.mem_filter.1 hn
    obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
    exact ⟨_, hn, y, hy, rfl, bindν_on hy⟩
  refine ⟨((((freeNames p₁ ++ freeNames b₁).filter
      fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
        (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩)).dedup) ++ Rw ++ Rp ++ Rb, ?_, ?_⟩
  · refine .letAct hk (fun n hn => bindν_off hn) ?_ hℓp hℓb hw hp hb ?_ ?_
    · intro s hs
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hs
      exact ⟨fun h => hO (Or.inl h), hO⟩
    · intro n hn ho
      exact List.mem_dedup.2 (List.mem_map.2 ⟨n, List.mem_filter.2 ⟨hn, ho⟩, rfl⟩)
    · intro n _ n' _ ho ho' he
      obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
      obtain ⟨y', hy', rfl⟩ := ownKey_map_true ho'
      rw [bindν_on hy, bindν_on hy'] at he
      injection he with he
      injection he with he
      injection he with he
      rw [he]
  · have hsite : ∀ m ∈ ((((freeNames p₁ ++ freeNames b₁).filter
        fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
          (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .pat⟩)).dedup),
        ∀ i (R : List (Nm (BId X))) (c : Ann S X) (c₁ : Tm S (Slot X)) (c₂ : Tm S (BId X)),
          ResOK fr (pos ++ [i]) c c₁ c₂ R → m ∉ R := by
      intro m hm i R c c₁ c₂ hR hmR
      obtain ⟨_, _, y, _, _, rfl⟩ := hRh m hm
      obtain ⟨k', hk', q, hq⟩ := hR.site _ hmR
      injection hk' with hk'
      injection hk' with hk'
      subst hk'
      exact site_child_ne_self hq.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine nodup_append_of (nodup_append_of (nodup_append_of (List.nodup_dedup _) hrw.nodup
        (fun m hm => hsite m hm 1 _ _ _ _ hrw)) hrp.nodup ?_) hrb.nodup ?_
      · intro m hm
        rcases List.mem_append.1 hm with h | h
        · exact hsite m h 0 _ _ _ _ hrp
        · exact hrw.apart (by decide) hrp m h
      · intro m hm
        rcases List.mem_append.1 hm with h | h
        · rcases List.mem_append.1 h with h | h
          · exact hsite m h 2 _ _ _ _ hrb
          · exact hrw.apart (by decide) hrb m h
        · exact hrp.apart (by decide) hrb m h
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨_, _, y, _, _, rfl⟩ := hRh m h
            exact ⟨_, rfl, rfl, by simp, [], by simp, fun _ => hl⟩
          · exact hrw.lift hl1 m h
        · exact hrp.lift hl0 m h
      · exact hrb.lift hl2 m h
    · intro m hm
      simp only [freeNames, List.mem_append]
      rcases List.mem_append.1 hm with h | h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨n, hn, y, hy, rfl, rfl⟩ := hRh m h
            rcases List.mem_append.1 hn with hn | hn
            · have := hp.mem_freeNames hn
              rw [bindν_on hy] at this
              exact Or.inl (Or.inl this)
            · have := hb.mem_freeNames hn
              rw [bindν_on hy] at this
              exact Or.inr this
          · exact Or.inl (Or.inr (hrw.free m h))
        · exact Or.inl (Or.inl (hrp.free m h))
      · exact Or.inr (hrb.free m h)
    · intro k hk hn hs
      rcases List.mem_append.1 hk with h | h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨_, _, y, _, _, he⟩ := hRh _ h
            injection he with he
            injection he with he
            subst he
            cases hn
          · exact absurd hs (hrw.news_child h)
        · exact absurd hs (hrp.news_child h)
      · exact absurd hs (hrb.news_child h)

/-- **A `new` block**: an activation on the slot side, nothing on the identity
side, whose declared identities are reserved until the activation runs. -/
theorem rel_new_of {ν μ : Nm (Slot X) → Nm (BId X)} {O : Owner} (hO : ¬ formRoot O) {y₀ : X}
    {ys : List X} {fr pos : Owner} {ℓ : Nm (Slot X)} {t b : Ann S X} {b₁ : Tm S (Slot X)}
    {b₂ : Tm S (BId X)} {Rb : List (Nm (BId X))} {ob : Bool}
    (hℓ : ℓ ∉ freeParams b₁)
    (hb : Rel SC (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .new⟩) μ .code Rb ob b₁ b₂)
    (hrb : ResOK fr pos b b₁ b₂ Rb) (hl : ∀ q, b.LetAAt q → t.LetAAt q)
    (hfree : ∀ n ∈ freeNames b₁, ownKey ((y₀ :: ys).map fun y => (O, y)) n = false →
      spellS n ∉ y₀ :: ys) :
    ∃ Res, Rel SC ν μ .code Res false
        (.app (.lam ℓ ((y₀ :: ys).map fun y => (O, y)) b₁) (.lam ℓ [] (.pvar ℓ))) b₂ ∧
      ResOK fr pos t (.app (.lam ℓ ((y₀ :: ys).map fun y => (O, y)) b₁) (.lam ℓ [] (.pvar ℓ)))
        b₂ Res := by
  have hRh : ∀ m ∈ (((freeNames b₁).filter
      fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
        (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .new⟩)).dedup,
      ∃ n ∈ freeNames b₁, ∃ y ∈ y₀ :: ys,
        n = .src (O, y) ∧ m = .src (.slot ⟨y, fr, pos, .new⟩) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hm)
    obtain ⟨hn, ho⟩ := List.mem_filter.1 hn
    obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
    exact ⟨_, hn, y, hy, rfl, bindν_on hy⟩
  refine ⟨(((freeNames b₁).filter
      fun n => ownKey ((y₀ :: ys).map fun y => (O, y)) n).map
        (bindν ν O (y₀ :: ys) fun y => ⟨y, fr, pos, .new⟩)).dedup ++ Rb, ?_, ?_⟩
  · refine .newAct (fun n hn => bindν_off hn) ?_ hℓ hb ?_ ?_
    · intro s hs
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hs
      exact ⟨fun h => hO (Or.inl h), hO⟩
    · intro n hn ho
      exact List.mem_dedup.2 (List.mem_map.2 ⟨n, List.mem_filter.2 ⟨hn, ho⟩, rfl⟩)
    · intro n _ n' _ ho ho' he
      obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
      obtain ⟨y', hy', rfl⟩ := ownKey_map_true ho'
      rw [bindν_on hy, bindν_on hy'] at he
      injection he with he
      injection he with he
      injection he with he
      rw [he]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · refine nodup_append_of (List.nodup_dedup _) hrb.nodup ?_
      intro m hm hmb
      obtain ⟨n, hn, y, _, rfl, rfl⟩ := hRh m hm
      exact hrb.news _ hmb rfl rfl _ hn rfl
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · obtain ⟨_, _, y, _, _, rfl⟩ := hRh m h
        exact ⟨_, rfl, rfl, by simp, [], by simp, fun h => by cases h⟩
      · obtain ⟨k, hk, hf, hh, q, hq, hp⟩ := hrb.shape m h
        exact ⟨k, hk, hf, hh, q, hq, fun e => hl q (hp e)⟩
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · obtain ⟨n, hn, y, hy, rfl, rfl⟩ := hRh m h
        have := hb.mem_freeNames hn
        rwa [bindν_on hy] at this
      · exact hrb.free m h
    · intro k hk hi hs n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil] at hn
      obtain ⟨hn, ho⟩ | ⟨⟨⟩, _⟩ := hn
      rcases List.mem_append.1 hk with h | h
      · obtain ⟨_, _, y, hy, _, he⟩ := hRh _ h
        injection he with he
        injection he with he
        subst he
        intro e
        exact hfree n hn ho (e ▸ hy)
      · exact hrb.news k h hi hs n hn

omit [DecidableEq X] in
theorem ne_of_prefix {a b : Owner} (h : a <+: b) (i : ℕ) : a ≠ b ++ [i] := by
  intro e
  have := h.length_le
  rw [e] at this
  simp at this
  omega

/-! ## Scope owners -/

/-- Every extension of `o` is a scope owner. -/
def headSafe (o : Owner) : Prop :=
  ∀ xs, scopeOwner (o ++ xs)

/-- The three owners written under a scope position. -/
def PosSafe (pos : Owner) : Prop :=
  headSafe (pos ++ [0]) ∧ headSafe (pos ++ [1]) ∧ headSafe (pos ++ [2])

omit [DecidableEq X] in
theorem codeBound_of_head {a : ℕ} (ha : a ≠ 9) (xs : List ℕ) : codeBound (a :: xs) = false := by
  unfold codeBound
  split
  · next h =>
      injection h with ha'
      exact absurd ha' ha
  · rfl

omit [DecidableEq X] in
theorem headSafe_cons {a : ℕ} (ha : a ≠ 9) (o : Owner) : headSafe (a :: o) := by
  intro xs
  refine ⟨codeBound_of_head ha (o ++ xs), ?_⟩
  intro h
  simp only [codeFreeParam] at h
  injection h with ha'
  exact ha ha'

omit [DecidableEq X] in
theorem headSafe.append {o xs : Owner} (h : headSafe o) : headSafe (o ++ xs) := by
  intro ys
  simpa [List.append_assoc] using h (xs ++ ys)

omit [DecidableEq X] in
theorem headSafe.owner {o : Owner} (h : headSafe o) : scopeOwner o := by
  simpa [List.append_nil] using h []

theorem scopeOwner_update {env : REnv X} {ys : List X} {o : Owner}
    (h : ∀ y, scopeOwner (env y)) (ho : scopeOwner o) :
    ∀ y, scopeOwner (REnv.update env ys o y) := by
  intro y
  simp only [REnv.update]
  split
  · exact ho
  · exact h y

omit [DecidableEq X] in
theorem PosSafe.zero {pos : Owner} (h : PosSafe pos) : PosSafe (pos ++ [0]) :=
  ⟨headSafe.append (xs := [0]) h.1, headSafe.append (xs := [1]) h.1,
    headSafe.append (xs := [2]) h.1⟩

omit [DecidableEq X] in
theorem PosSafe.one {pos : Owner} (h : PosSafe pos) : PosSafe (pos ++ [1]) :=
  ⟨headSafe.append (xs := [0]) h.2.1, headSafe.append (xs := [1]) h.2.1,
    headSafe.append (xs := [2]) h.2.1⟩

omit [DecidableEq X] in
theorem PosSafe.two {pos : Owner} (h : PosSafe pos) : PosSafe (pos ++ [2]) :=
  ⟨headSafe.append (xs := [0]) h.2.2, headSafe.append (xs := [1]) h.2.2,
    headSafe.append (xs := [2]) h.2.2⟩

/-- The query root is a scope owner. -/
theorem scopeOwner_nil : scopeOwner ([] : Owner) := ⟨rfl, by decide⟩

/-- The root of an equation is a scope owner. -/
theorem scopeOwner_five : scopeOwner ([5] : Owner) := ⟨rfl, by decide⟩

omit [DecidableEq X] in
theorem scopeOwners_nil : ∀ _ : X, scopeOwner ([] : Owner) :=
  fun _ => scopeOwner_nil

omit [DecidableEq X] in
theorem scopeOwners_five : ∀ _ : X, scopeOwner ([5] : Owner) :=
  fun _ => scopeOwner_five

omit [DecidableEq X] in
theorem PosSafe.root : PosSafe ([] : Owner) :=
  ⟨headSafe_cons (by decide) [], headSafe_cons (by decide) [], headSafe_cons (by decide) []⟩

omit [DecidableEq X] in
theorem PosSafe.clause : PosSafe ([5] : Owner) :=
  ⟨headSafe_cons (by decide) [0], headSafe_cons (by decide) [1], headSafe_cons (by decide) [2]⟩

/-! ## Sealed code -/

theorem ownNil_fold {Y : Type v} (ps : List (Nm Y)) {t : Tm S Y} (h : ownNil t) :
    ownNil (ps.foldr (fun p acc => .lam p [] acc) t) := by
  induction ps with
  | nil => exact h
  | cons _ _ ih => exact ⟨rfl, ih⟩

theorem ownNil_seal {Y : Type v} [DecidableEq Y] {t : Tm S Y} (h : ownNil t) :
    ownNil (sealParams t) := by
  unfold sealParams
  exact ownNil_fold _ h

theorem ownNil_codeAt (R : Owner) (holes : Option (X → Owner)) (penv senv : List (X × Owner))
    (pos : Owner) (s : Src S X) : ownNil (codeAt R holes penv senv pos s) := by
  induction s generalizing holes penv senv pos with
  | sym _ => simp [codeAt, ownNil]
  | fn _ => simp [codeAt, ownNil]
  | sv y =>
      simp only [codeAt]
      cases codeLookup senv y with
      | some _ => simp [ownNil]
      | none => cases holes <;> simp [ownNil]
  | par _ =>
      simp only [codeAt]
      split <;> simp [ownNil]
  | lam z _ _ ih =>
      unfold codeAt
      exact ⟨rfl, ih _ _ _ _⟩
  | form z _ ih =>
      unfold codeAt
      exact ⟨rfl, ih _ _ _ _⟩
  | app _ _ ihf iha =>
      simp only [codeAt, ownNil]
      exact ⟨ihf _ _ _ _, iha _ _ _ _⟩
  | quote _ ih =>
      simp only [codeAt, ownNil]
      exact ownNil_seal (ih none [] [] [])
  | pquote _ ih =>
      simp only [codeAt, ownNil]
      exact ih _ _ _ _
  | letS _ _ _ _ ihp ihw ihb =>
      simp only [codeAt, ownNil]
      exact ⟨ihp _ _ _ _, ihw _ _ _ _, ihb _ _ _ _⟩
  | unify _ _ _ ihp ihw ihb =>
      simp only [codeAt, ownNil]
      exact ⟨ihp _ _ _ _, ihw _ _ _ _, ihb _ _ _ _⟩
  | alt _ _ iht ihu =>
      simp only [codeAt, ownNil]
      exact ⟨iht _ _ _ _, ihu _ _ _ _⟩
  | new _ _ ih =>
      simpa [codeAt] using ih holes penv senv (pos ++ [0])

omit [DecidableEq X] in
theorem mapCode_back_fwd {t : Tm S (Slot X)} (h : ownNil t) :
    mapCode codeBack (mapCode codeFwd t) = t := by
  induction t with
  | sym _ => rfl
  | fn _ => rfl
  | var n => simp [mapCode, codeBack_codeFwd]
  | pvar n => simp [mapCode, codeBack_codeFwd]
  | lam x own b ih =>
      simp only [ownNil] at h
      rcases h with ⟨rfl, hb⟩
      simp only [mapCode, codeBack_codeFwd, ih hb]
  | app _ _ ihf iha =>
      simp only [ownNil] at h
      simp only [mapCode, ihf h.1, iha h.2]
  | quote _ ih =>
      simp only [ownNil] at h
      simp only [mapCode, ih h]
  | ctx ks c ih =>
      simp only [ownNil] at h
      have hb := ih h
      simp only [mapCode, hb, List.map_map]
      congr
      induction ks with
      | nil => rfl
      | cons n ns ihk => simp [List.map_cons, codeBack_codeFwd, ihk]
  | pquote _ ih =>
      simp only [ownNil] at h
      simp only [mapCode, ih h]
  | letP _ _ _ ihp ihw ihb =>
      simp only [ownNil] at h
      simp only [mapCode, ihp h.1, ihw h.2.1, ihb h.2.2]
  | alt _ _ ih₁ ih₂ =>
      simp only [ownNil] at h
      simp only [mapCode, ih₁ h.1, ih₂ h.2]

omit [DecidableEq X] in
private theorem map_filter_binder {α β : Type v} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (x : α) (l : List α) :
    ((l.filter fun y => decide (y ≠ x)).map f) =
      ((l.map f).filter fun z => decide (z ≠ f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : a = x
      · have hd : decide (a ≠ x) = false := decide_eq_false (fun h => h ha)
        have hdf : decide (f a ≠ f x) = false :=
          decide_eq_false (fun h => h (congrArg f ha))
        rw [List.filter_cons_of_neg (p := fun y => decide (y ≠ x))
            (by rw [hd]; exact Bool.false_ne_true),
          List.map_cons,
          List.filter_cons_of_neg (p := fun z => decide (z ≠ f x))
            (by rw [hdf]; exact Bool.false_ne_true),
          ih]
      · have hk : decide (a ≠ x) = true := decide_eq_true ha
        have hkf : decide (f a ≠ f x) = true := decide_eq_true (hf.ne ha)
        rw [List.filter_cons_of_pos (p := fun y => decide (y ≠ x)) hk,
          List.map_cons, List.map_cons,
          List.filter_cons_of_pos (p := fun z => decide (z ≠ f x)) hkf, ih]

private theorem paramOcc_mapCode {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    {f : Nm Y → Nm Z} (hf : Function.Injective f) :
    ∀ t : Tm S Y, paramOcc (mapCode f t) = (paramOcc t).map f
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam x _ b => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf b, map_filter_binder hf x]
  | .app a b => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf a, paramOcc_mapCode hf b, List.map_append]
  | .quote _ => rfl
  | .ctx _ _ => rfl
  | .pquote c => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf c]
  | .letP p w b => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf p, paramOcc_mapCode hf w,
        paramOcc_mapCode hf b, List.map_append]
  | .alt t₁ t₂ => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf t₁, paramOcc_mapCode hf t₂, List.map_append]

private theorem mapCode_fold {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    (f : Nm Y → Nm Z) (ps : List (Nm Y)) (t : Tm S Y) :
    mapCode f (ps.foldr (fun p acc => .lam p [] acc) t) =
      (ps.map f).foldr (fun p acc => .lam p [] acc) (mapCode f t) := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldr, List.map, mapCode, ih]

theorem mapCode_seal {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    {f : Nm Y → Nm Z} (hf : Function.Injective f) (t : Tm S Y) :
    mapCode f (sealParams t) = sealParams (mapCode f t) := by
  unfold sealParams
  rw [mapCode_fold, paramOcc_mapCode hf]

omit [DecidableEq X] in
private theorem nil_bound : ∀ p ∈ ([] : List (X × Owner)), codeBound p.2 = true := by
  intro _ h
  simp at h

omit [DecidableEq X] in
private theorem cons_bound {z : X} {o : Owner} {l : List (X × Owner)}
    (ho : codeBound o = true) (hl : ∀ p ∈ l, codeBound p.2 = true) :
    ∀ p ∈ (z, o) :: l, codeBound p.2 = true := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ho
  · exact hl p hp

omit [DecidableEq X] in
private theorem append_bound {l₁ l₂ : List (X × Owner)}
    (h₁ : ∀ p ∈ l₁, codeBound p.2 = true) (h₂ : ∀ p ∈ l₂, codeBound p.2 = true) :
    ∀ p ∈ l₁ ++ l₂, codeBound p.2 = true := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

theorem codeLookup_bound (l : List (X × Owner)) {z : X} {o : Owner}
    (hb : ∀ p ∈ l, codeBound p.2 = true) (hl : codeLookup l z = some o) :
    codeBound o = true := by
  induction l generalizing z o with
  | nil => simp [codeLookup] at hl
  | cons p rest ih =>
      obtain ⟨y, o'⟩ := p
      simp only [codeLookup] at hl
      by_cases hy : y = z
      · simp only [hy] at hl
        cases hl
        exact hb (y, o) List.mem_cons_self
      · simp only [hy] at hl
        exact ih (fun q hq => hb q (List.mem_cons_of_mem _ hq)) hl

omit [DecidableEq X] in
theorem svBinds_bound (pos : Owner) (s : Src S X) :
    ∀ p ∈ svBinds pos s, codeBound p.2 = true := by
  induction s generalizing pos with
  | sv _ =>
      intro p hp
      simp only [svBinds, List.mem_singleton] at hp
      subst hp
      exact codeBound_binder _
  | app _ _ ihf iha =>
      intro p hp
      simp only [svBinds, List.mem_append] at hp
      rcases hp with hp | hp
      · exact ihf _ p hp
      · exact iha _ p hp
  | alt _ _ iht ihu =>
      intro p hp
      simp only [svBinds, List.mem_append] at hp
      rcases hp with hp | hp
      · exact iht _ p hp
      · exact ihu _ p hp
  | sym _ | fn _ | par _ | lam _ _ _ | quote _ | pquote _ | letS _ _ _ _ | unify _ _ _ | new _ _ | form _ _ =>
      intro p hp
      simp [svBinds] at hp

/-- Sealed code in the slot model is sealed code in the identity model, for
code written in a form rooted at the scope owner `R`.  The environments are the
binders of this quotation, most recent first, all binders of code; a hole is the
root's head slot on both sides. -/
theorem mapCode_codeAt (R : Owner) (hR : scopeOwner R) (penv senv : List (X × Owner)) (pos : Owner)
    (hpenv : ∀ p ∈ penv, codeBound p.2 = true) (hsenv : ∀ p ∈ senv, codeBound p.2 = true) :
    ∀ s : Src S X,
      mapCode codeFwd (codeAt R none penv senv pos s) = codeIAt R none penv senv pos s
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv y => by
      simp only [codeAt, codeIAt]
      cases h : codeLookup senv y with
      | none =>
          simp only [mapCode, iVar]
          rw [codeFwd_scope hR]
      | some p =>
          simp only [mapCode]
          rw [codeFwd_code (Or.inl (codeLookup_bound senv hsenv h))]
  | .par z => by
      simp only [codeAt, codeIAt]
      cases h : codeLookup penv z with
      | none =>
          simp only [mapCode]
          rw [codeFwd_code (Or.inr rfl)]
      | some p =>
          simp only [mapCode]
          rw [codeFwd_code (Or.inl (codeLookup_bound penv hpenv h))]
  | .lam z _ b => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt R hR ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (cons_bound (codeBound_binder pos) hpenv) hsenv b]
      rw [codeFwd_code (Or.inl (codeBound_binder pos))]
  | .form z b => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt R hR ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (cons_bound (codeBound_binder pos) hpenv) hsenv b]
      rw [codeFwd_code (Or.inl (codeBound_binder pos))]
  | .app f a => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt R hR penv senv (pos ++ [0]) hpenv hsenv f,
        mapCode_codeAt R hR penv senv (pos ++ [1]) hpenv hsenv a]
  | .quote c => by
      simp only [codeAt, codeIAt, mapCode]
      rw [mapCode_seal codeFwd_injective]
      exact congrArg Tm.quote (congrArg sealParams
        (mapCode_codeAt R hR [] [] [] nil_bound nil_bound c))
  | .pquote c => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt R hR [] [] [] nil_bound nil_bound c]
  | .letS p w b _ => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv
          (append_bound (svBinds_bound (pos ++ [0]) p) hsenv) p,
        mapCode_codeAt R hR penv senv (pos ++ [1]) hpenv hsenv w,
        mapCode_codeAt R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv
          (append_bound (svBinds_bound (pos ++ [0]) p) hsenv) b]
  | .unify p w b => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv
          (append_bound (svBinds_bound (pos ++ [0]) p) hsenv) p,
        mapCode_codeAt R hR penv senv (pos ++ [1]) hpenv hsenv w,
        mapCode_codeAt R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv
          (append_bound (svBinds_bound (pos ++ [0]) p) hsenv) b]
  | .alt t₁ t₂ => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt R hR penv senv (pos ++ [0]) hpenv hsenv t₁,
        mapCode_codeAt R hR penv senv (pos ++ [1]) hpenv hsenv t₂]
  | .new _ b => by
      simp only [codeAt, codeIAt,
        mapCode_codeAt R hR penv senv (pos ++ [0]) hpenv hsenv b]

/-- Sealed code in the identity model is sealed code in the slot model. -/
theorem mapCode_codeIAt (R : Owner) (hR : scopeOwner R) (penv senv : List (X × Owner))
    (pos : Owner) :
    ∀ s : Src S X,
      mapCode codeBack (codeIAt R none penv senv pos s) = codeAt R none penv senv pos s
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv y => by
      simp only [codeAt, codeIAt]
      cases codeLookup senv y <;> rfl
  | .par z => by
      simp only [codeAt, codeIAt]
      cases codeLookup penv z <;> rfl
  | .lam z _ b => by
      simp only [codeAt, codeIAt, mapCode, codeBack,
        mapCode_codeIAt R hR ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b]
  | .form z b => by
      simp only [codeAt, codeIAt, mapCode, codeBack,
        mapCode_codeIAt R hR ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b]
  | .app f a => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeIAt R hR penv senv (pos ++ [0]) f, mapCode_codeIAt R hR penv senv (pos ++ [1]) a]
  | .quote c => by
      simp only [codeAt, codeIAt, mapCode]
      have hfwd : mapCode codeFwd (codeAt R none [] [] [] c) = codeIAt R none [] [] [] c :=
        mapCode_codeAt R hR [] [] [] nil_bound nil_bound c
      rw [← hfwd, ← mapCode_seal codeFwd_injective]
      exact congrArg Tm.quote
        (mapCode_back_fwd (ownNil_seal (ownNil_codeAt R none [] [] [] c)))
  | .pquote c => by
      simp only [codeAt, codeIAt, mapCode, mapCode_codeIAt R hR [] [] [] c]
  | .letS p w b _ => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeIAt R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p,
        mapCode_codeIAt R hR penv senv (pos ++ [1]) w,
        mapCode_codeIAt R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b]
  | .unify p w b => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeIAt R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p,
        mapCode_codeIAt R hR penv senv (pos ++ [1]) w,
        mapCode_codeIAt R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b]
  | .alt t₁ t₂ => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeIAt R hR penv senv (pos ++ [0]) t₁, mapCode_codeIAt R hR penv senv (pos ++ [1]) t₂]
  | .new _ b => by
      simp only [codeAt, codeIAt, mapCode_codeIAt R hR penv senv (pos ++ [0]) b]

theorem mapCode_codeOf {R : Owner} (hR : scopeOwner R) (s : Src S X) :
    mapCode codeFwd (codeOf R s) = codeI R s := by
  simp only [codeOf, codeI]
  rw [mapCode_seal codeFwd_injective]
  exact congrArg sealParams (mapCode_codeAt R hR [] [] [] nil_bound nil_bound s)

theorem mapCode_codeI {R : Owner} (hR : scopeOwner R) (s : Src S X) :
    mapCode codeBack (codeI R s) = codeOf R s := by
  rw [← mapCode_codeOf hR]
  exact mapCode_back_fwd (ownNil_seal (ownNil_codeAt R none [] [] [] s))

/-! ## Sealed code in the setting -/

omit [DecidableEq X] in
theorem codeVars_fold {Y : Type v} (ps : List (Nm Y)) (t : Tm S Y) :
    codeVars (ps.foldr (fun p acc => .lam p [] acc) t) = codeVars t := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldr_cons, codeVars, ih]

omit [DecidableEq X] in
theorem codeVars_sealParams {Y : Type v} [DecidableEq Y] (t : Tm S Y) :
    codeVars (sealParams t) = codeVars t := by
  unfold sealParams
  exact codeVars_fold _ t

theorem sealedFree_fold {Y : Type v} [DecidableEq Y] (ps : List (Nm Y)) (t : Tm S Y) :
    sealedFree (ps.foldr (fun p acc => .lam p [] acc) t) = sealedFree t := by
  induction ps with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.foldr_cons, sealedFree, ih]
      exact List.filter_eq_self.2 fun n _ => by cases n <;> simp [ownKey]

theorem sealedFree_sealParams {Y : Type v} [DecidableEq Y] (t : Tm S Y) :
    sealedFree (sealParams t) = sealedFree t := by
  unfold sealParams
  exact sealedFree_fold _ t

omit [DecidableEq X] in
/-- A parameter occurring in a term is a name of its code. -/
theorem mem_codeNames_of_paramOcc {Y : Type v} [DecidableEq Y] :
    ∀ (t : Tm S Y) {n : Nm Y}, n ∈ paramOcc t → n ∈ codeNames t
  | .pvar x, n, h => by simpa [paramOcc, codeNames] using h
  | .lam x _ b, n, h => by
      simp only [paramOcc, List.mem_filter] at h
      exact List.mem_cons_of_mem _ (mem_codeNames_of_paramOcc b h.1)
  | .app f a, n, h => by
      simp only [paramOcc, List.mem_append] at h
      simp only [codeNames, List.mem_append]
      exact h.imp (mem_codeNames_of_paramOcc f) (mem_codeNames_of_paramOcc a)
  | .pquote c, n, h => by
      simp only [paramOcc] at h
      exact mem_codeNames_of_paramOcc c h
  | .letP p w b, n, h => by
      simp only [paramOcc, List.mem_append] at h
      simp only [codeNames, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (mem_codeNames_of_paramOcc p h))
      · exact Or.inl (Or.inr (mem_codeNames_of_paramOcc w h))
      · exact Or.inr (mem_codeNames_of_paramOcc b h)
  | .alt t u, n, h => by
      simp only [paramOcc, List.mem_append] at h
      simp only [codeNames, List.mem_append]
      exact h.imp (mem_codeNames_of_paramOcc t) (mem_codeNames_of_paramOcc u)
  | .sym _, _, h | .fn _, _, h | .var _, _, h | .quote _, _, h | .ctx _ _, _, h => by
      simp [paramOcc] at h

omit [DecidableEq X] in
/-- Sealing the parameters of code adds no name: the binders it adds are the
code's parameters. -/
theorem codeNames_sealParams {Y : Type v} [DecidableEq Y] (t : Tm S Y) {n : Nm Y}
    (h : n ∈ codeNames (sealParams t)) : n ∈ codeNames t := by
  unfold sealParams at h
  have key : ∀ (ps : List (Nm Y)), (∀ p ∈ ps, p ∈ codeNames t) →
      n ∈ codeNames (ps.foldr (fun p acc => .lam p [] acc) t) → n ∈ codeNames t := by
    intro ps hps
    induction ps with
    | nil => exact id
    | cons p ps ih =>
        intro h
        simp only [List.foldr_cons, codeNames, List.mem_cons] at h
        rcases h with rfl | h
        · exact hps _ (by simp)
        · exact ih (fun q hq => hps q (by simp [hq])) h
  exact key _ (fun p hp => mem_codeNames_of_paramOcc t hp) h

/-- **The names of sealed code written by `codeAt` are names as written**, and
its holes, when it seals them, are the root's slots. -/
theorem codeNames_codeAt (R : Owner) :
    ∀ (holes : Option (X → Owner)) (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X),
      ∀ n ∈ codeNames (codeAt R holes penv senv pos s), ∃ s', n = .src s'
  | _, _, _, _, .sym _, n, h | _, _, _, _, .fn _, n, h => by simp [codeAt, codeNames] at h
  | _, penv, _, _, .par z, n, h => by
      simp only [codeAt] at h
      split at h <;> simp only [codeNames, List.mem_singleton] at h <;> exact ⟨_, h⟩
  | holes, _, senv, _, .sv y, n, h => by
      simp only [codeAt] at h
      split at h
      · simp only [codeNames, List.mem_singleton] at h
        exact ⟨_, h⟩
      · split at h <;> simp only [codeNames, List.mem_singleton] at h <;> exact ⟨_, h⟩
  | holes, penv, senv, pos, .lam z _ b, n, h => by
      simp only [codeAt, codeNames, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, rfl⟩
      · exact codeNames_codeAt R holes _ senv _ b n h
  | holes, penv, senv, pos, .form z b, n, h => by
      simp only [codeAt, codeNames, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, rfl⟩
      · exact codeNames_codeAt R holes _ senv _ b n h
  | holes, penv, senv, pos, .app f a, n, h => by
      simp only [codeAt, codeNames, List.mem_append] at h
      rcases h with h | h
      · exact codeNames_codeAt R holes penv senv _ f n h
      · exact codeNames_codeAt R holes penv senv _ a n h
  | _, _, _, _, .quote c, n, h => by
      simp only [codeAt, codeNames] at h
      exact codeNames_codeAt R none [] [] [] c n (codeNames_sealParams _ h)
  | holes, _, _, _, .pquote c, n, h => by
      simp only [codeAt, codeNames] at h
      exact codeNames_codeAt R holes [] [] [] c n h
  | holes, penv, senv, pos, .letS p w b _, n, h => by
      simp only [codeAt, codeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · exact codeNames_codeAt R holes _ _ _ p n h
      · exact codeNames_codeAt R holes _ _ _ w n h
      · exact codeNames_codeAt R holes _ _ _ b n h
  | holes, penv, senv, pos, .unify p w b, n, h => by
      simp only [codeAt, codeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · exact codeNames_codeAt R holes _ _ _ p n h
      · exact codeNames_codeAt R holes _ _ _ w n h
      · exact codeNames_codeAt R holes _ _ _ b n h
  | holes, penv, senv, pos, .alt t u, n, h => by
      simp only [codeAt, codeNames, List.mem_append] at h
      rcases h with h | h
      · exact codeNames_codeAt R holes _ _ _ t n h
      · exact codeNames_codeAt R holes _ _ _ u n h
  | holes, penv, senv, pos, .new _ b, n, h => by
      simp only [codeAt] at h
      exact codeNames_codeAt R holes _ _ _ b n h

/-- **The holes of sealed code written in a form rooted at `R` are `R`'s slots.** -/
theorem codeVars_codeAt_none (R : Owner) :
    ∀ (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X),
      ∀ n ∈ codeVars (codeAt R none penv senv pos s), ∃ y, n = .src (R, y)
  | _, _, _, .sym _, n, h | _, _, _, .fn _, n, h => by simp [codeAt, codeVars] at h
  | penv, _, _, .par z, n, h => by
      simp only [codeAt] at h
      split at h <;> simp [codeVars] at h
  | _, senv, _, .sv y, n, h => by
      simp only [codeAt] at h
      split at h
      · simp [codeVars] at h
      · simp only [codeVars, List.mem_singleton] at h
        exact ⟨y, h⟩
  | penv, senv, pos, .lam z _ b, n, h => by
      simp only [codeAt, codeVars] at h
      exact codeVars_codeAt_none R _ senv _ b n h
  | penv, senv, pos, .form z b, n, h => by
      simp only [codeAt, codeVars] at h
      exact codeVars_codeAt_none R _ senv _ b n h
  | penv, senv, pos, .app f a, n, h => by
      simp only [codeAt, codeVars, List.mem_append] at h
      rcases h with h | h
      · exact codeVars_codeAt_none R penv senv _ f n h
      · exact codeVars_codeAt_none R penv senv _ a n h
  | _, _, _, .quote c, n, h => by
      simp only [codeAt, codeVars, codeVars_sealParams] at h
      exact codeVars_codeAt_none R [] [] [] c n h
  | _, _, _, .pquote c, n, h => by
      simp only [codeAt, codeVars] at h
      exact codeVars_codeAt_none R [] [] [] c n h
  | penv, senv, pos, .letS p w b _, n, h => by
      simp only [codeAt, codeVars, List.mem_append] at h
      rcases h with (h | h) | h
      · exact codeVars_codeAt_none R _ _ _ p n h
      · exact codeVars_codeAt_none R _ _ _ w n h
      · exact codeVars_codeAt_none R _ _ _ b n h
  | penv, senv, pos, .unify p w b, n, h => by
      simp only [codeAt, codeVars, List.mem_append] at h
      rcases h with (h | h) | h
      · exact codeVars_codeAt_none R _ _ _ p n h
      · exact codeVars_codeAt_none R _ _ _ w n h
      · exact codeVars_codeAt_none R _ _ _ b n h
  | penv, senv, pos, .alt t u, n, h => by
      simp only [codeAt, codeVars, List.mem_append] at h
      rcases h with h | h
      · exact codeVars_codeAt_none R _ _ _ t n h
      · exact codeVars_codeAt_none R _ _ _ u n h
  | penv, senv, pos, .new _ b, n, h => by
      simp only [codeAt] at h
      exact codeVars_codeAt_none R _ _ _ b n h

theorem codeVars_codeOf (R : Owner) (c : Src S X) :
    ∀ n ∈ codeVars (codeOf R c), ∃ y, n = .src (R, y) := by
  intro n hn
  simp only [codeOf, codeVars_sealParams] at hn
  exact codeVars_codeAt_none R [] [] [] c n hn

/-- **The free names of sealed code in pattern code written in a form rooted at
`R` are `R`'s slots.** -/
theorem sealedFree_codeAt (R : Owner) :
    ∀ (holes : Option (X → Owner)) (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X),
      ∀ n ∈ sealedFree (codeAt R holes penv senv pos s), ∃ y, n = .src (R, y)
  | _, _, _, _, .sym _, n, h | _, _, _, _, .fn _, n, h => by simp [codeAt, sealedFree] at h
  | _, penv, _, _, .par z, n, h => by
      simp only [codeAt] at h
      split at h <;> simp [sealedFree] at h
  | holes, _, senv, _, .sv y, n, h => by
      simp only [codeAt] at h
      split at h
      · simp [sealedFree] at h
      · split at h <;> simp [sealedFree] at h
  | holes, penv, senv, pos, .lam z _ b, n, h => by
      simp only [codeAt, sealedFree, List.mem_filter] at h
      exact sealedFree_codeAt R holes _ senv _ b n h.1
  | holes, penv, senv, pos, .form z b, n, h => by
      simp only [codeAt, sealedFree, List.mem_filter] at h
      exact sealedFree_codeAt R holes _ senv _ b n h.1
  | holes, penv, senv, pos, .app f a, n, h => by
      simp only [codeAt, sealedFree, List.mem_append] at h
      rcases h with h | h
      · exact sealedFree_codeAt R holes penv senv _ f n h
      · exact sealedFree_codeAt R holes penv senv _ a n h
  | _, _, _, _, .quote c, n, h => by
      simp only [codeAt, sealedFree, codeVars_sealParams] at h
      exact codeVars_codeAt_none R [] [] [] c n h
  | holes, _, _, _, .pquote c, n, h => by
      simp only [codeAt, sealedFree] at h
      exact sealedFree_codeAt R holes [] [] [] c n h
  | holes, penv, senv, pos, .letS p w b _, n, h => by
      simp only [codeAt, sealedFree, List.mem_append] at h
      rcases h with (h | h) | h
      · exact sealedFree_codeAt R holes _ _ _ p n h
      · exact sealedFree_codeAt R holes _ _ _ w n h
      · exact sealedFree_codeAt R holes _ _ _ b n h
  | holes, penv, senv, pos, .unify p w b, n, h => by
      simp only [codeAt, sealedFree, List.mem_append] at h
      rcases h with (h | h) | h
      · exact sealedFree_codeAt R holes _ _ _ p n h
      · exact sealedFree_codeAt R holes _ _ _ w n h
      · exact sealedFree_codeAt R holes _ _ _ b n h
  | holes, penv, senv, pos, .alt t u, n, h => by
      simp only [codeAt, sealedFree, List.mem_append] at h
      rcases h with h | h
      · exact sealedFree_codeAt R holes _ _ _ t n h
      · exact sealedFree_codeAt R holes _ _ _ u n h
  | holes, penv, senv, pos, .new _ b, n, h => by
      simp only [codeAt] at h
      exact sealedFree_codeAt R holes _ _ _ b n h

omit [DecidableEq X] in
/-- Reading a name as written strips no tag. -/
theorem mapCode_nmBase_self {Y : Type v} :
    ∀ (t : Tm S Y), ownNil t → (∀ n ∈ codeNames t, ∃ s, n = .src s) → mapCode nmBase t = t
  | .sym _, _, _ => rfl
  | .fn _, _, _ => rfl
  | .var n, _, h => by
      obtain ⟨s, rfl⟩ := h n (by simp [codeNames])
      rfl
  | .pvar n, _, h => by
      obtain ⟨s, rfl⟩ := h n (by simp [codeNames])
      rfl
  | .lam x o b, ho, h => by
      obtain ⟨rfl, hb⟩ := ho
      obtain ⟨s, rfl⟩ := h x (by simp [codeNames])
      simp only [mapCode, nmBase,
        mapCode_nmBase_self b hb fun n hn => h n (by simp [codeNames, hn])]
  | .app f a, ho, h => by
      simp only [mapCode, mapCode_nmBase_self f ho.1 fun n hn => h n (by simp [codeNames, hn]),
        mapCode_nmBase_self a ho.2 fun n hn => h n (by simp [codeNames, hn])]
  | .quote c, ho, h => by
      simp only [mapCode, mapCode_nmBase_self c ho fun n hn => h n (by simpa [codeNames] using hn)]
  | .ctx ks c, ho, h => by
      have hks : ∀ (l : List (Nm Y)), (∀ n ∈ l, ∃ s, n = .src s) → l.map nmBase = l := by
        intro l hl
        induction l with
        | nil => rfl
        | cons a l ih =>
            obtain ⟨s, rfl⟩ := hl a (by simp)
            simp only [List.map_cons, nmBase, ih (fun n hn => hl n (by simp [hn]))]
      simp only [mapCode, mapCode_nmBase_self c ho fun n hn => h n (by simp [codeNames, hn]),
        hks ks fun n hn => h n (by simp [codeNames, hn])]
  | .pquote c, ho, h => by
      simp only [mapCode, mapCode_nmBase_self c ho fun n hn => h n (by simpa [codeNames] using hn)]
  | .letP p w b, ho, h => by
      simp only [mapCode, mapCode_nmBase_self p ho.1 fun n hn => h n (by simp [codeNames, hn]),
        mapCode_nmBase_self w ho.2.1 fun n hn => h n (by simp [codeNames, hn]),
        mapCode_nmBase_self b ho.2.2 fun n hn => h n (by simp [codeNames, hn])]
  | .alt t u, ho, h => by
      simp only [mapCode, mapCode_nmBase_self t ho.1 fun n hn => h n (by simp [codeNames, hn]),
        mapCode_nmBase_self u ho.2 fun n hn => h n (by simp [codeNames, hn])]

omit [DecidableEq X] in
theorem codeNames_mapCode {Y Z : Type v} (f : Nm Y → Nm Z) :
    ∀ (t : Tm S Y) {m : Nm Z}, m ∈ codeNames (mapCode f t) → ∃ n ∈ codeNames t, m = f n
  | .sym _, _, h | .fn _, _, h => by simp [mapCode, codeNames] at h
  | .var n, m, h => by simp only [mapCode, codeNames, List.mem_singleton] at h; exact ⟨n, by simp [codeNames], h⟩
  | .pvar n, m, h => by simp only [mapCode, codeNames, List.mem_singleton] at h; exact ⟨n, by simp [codeNames], h⟩
  | .lam x o b, m, h => by
      simp only [mapCode, codeNames, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨x, by simp [codeNames], rfl⟩
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f b h
        exact ⟨n, by simp [codeNames, hn], rfl⟩
  | .app a b, m, h => by
      simp only [mapCode, codeNames, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f a h
        exact ⟨n, by simp [codeNames, hn], rfl⟩
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f b h
        exact ⟨n, by simp [codeNames, hn], rfl⟩
  | .quote c, m, h => by
      simp only [mapCode, codeNames] at h
      obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f c h
      exact ⟨n, by simpa [codeNames] using hn, rfl⟩
  | .ctx ks c, m, h => by
      simp only [mapCode, codeNames, List.mem_append, List.mem_map] at h
      rcases h with ⟨n, hn, rfl⟩ | h
      · exact ⟨n, by simp [codeNames, hn], rfl⟩
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f c h
        exact ⟨n, by simp [codeNames, hn], rfl⟩
  | .pquote c, m, h => by
      simp only [mapCode, codeNames] at h
      obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f c h
      exact ⟨n, by simpa [codeNames] using hn, rfl⟩
  | .letP p w b, m, h => by
      simp only [mapCode, codeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f p h
        exact ⟨n, by simp [codeNames, hn], rfl⟩
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f w h
        exact ⟨n, by simp [codeNames, hn], rfl⟩
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f b h
        exact ⟨n, by simp [codeNames, hn], rfl⟩
  | .alt t u, m, h => by
      simp only [mapCode, codeNames, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f t h
        exact ⟨n, by simp [codeNames, hn], rfl⟩
      · obtain ⟨n, hn, rfl⟩ := codeNames_mapCode f u h
        exact ⟨n, by simp [codeNames, hn], rfl⟩

omit [DecidableEq X] in
theorem ownNil_mapCode {Y Z : Type v} (f : Nm Y → Nm Z) : ∀ t : Tm S Y, ownNil (mapCode f t)
  | .sym _ => trivial
  | .fn _ => trivial
  | .var _ => trivial
  | .pvar _ => trivial
  | .lam _ _ b => ⟨rfl, ownNil_mapCode f b⟩
  | .app a b => ⟨ownNil_mapCode f a, ownNil_mapCode f b⟩
  | .quote c => ownNil_mapCode f c
  | .ctx _ c => ownNil_mapCode f c
  | .pquote c => ownNil_mapCode f c
  | .letP p w b => ⟨ownNil_mapCode f p, ownNil_mapCode f w, ownNil_mapCode f b⟩
  | .alt t u => ⟨ownNil_mapCode f t, ownNil_mapCode f u⟩

/-- **Sealed code written in a form root is related sealed code**, under any name
map: its names are names as written, read by `codeFwd`, and its holes are the
root's slots. -/
theorem QR_codeOf {R : Owner} (hR : formRoot R) (c : Src S X) (ν : Nm (Slot X) → Nm (BId X)) :
    QR SC ν (codeOf R c) (codeI R c) := by
  have hsrc : ∀ n ∈ codeNames (codeOf R c), ∃ s, n = .src s := fun n hn =>
    codeNames_codeAt R none [] [] [] c n (codeNames_sealParams _ hn)
  have hown : ownNil (codeOf R c) := ownNil_seal (ownNil_codeAt R none [] [] [] c)
  have hI : codeI R c = mapCode codeFwd (codeOf R c) := (mapCode_codeOf hR.scopeOwner c).symm
  have hsrcI : ∀ n ∈ codeNames (codeI R c), ∃ s, n = .src s := by
    intro n hn
    rw [hI] at hn
    obtain ⟨m, hm, rfl⟩ := codeNames_mapCode codeFwd _ hn
    obtain ⟨s, rfl⟩ := hsrc m hm
    exact codeFwd_src s
  refine ⟨?_, ⟨hown, ?_, ?_⟩, ?_⟩
  · show codeQ (stripCode (codeOf R c)) (stripCode (codeI R c))
    rw [stripCode, stripCode, mapCode_nmBase_self _ hown hsrc,
      mapCode_nmBase_self _ (by rw [hI]; exact ownNil_mapCode _ _) hsrcI]
    exact ⟨R, c, hR.scopeOwner, rfl, rfl⟩
  · intro n hn
    obtain ⟨y, rfl⟩ := codeVars_codeOf R c n hn
    exact hR
  · intro n hn
    exact hsrc n ((mem_codeNames _).2 (Or.inr hn))
  · rw [hI]
    exact mapCode_congr _ fun n hn => by
      obtain ⟨s, rfl⟩ := hsrc n hn
      rfl

/-- **The free names of sealed code of an elaborated form rooted at `R` are `R`'s
slots.** -/
theorem Ann.sealedFree_slotOf (R : Owner) :
    ∀ (t : Ann S X) (env : REnv X) (pos : Owner),
      ∀ n ∈ sealedFree (t.slotOf R env pos), ∃ y, n = .src (R, y)
  | .sym _, _, _, n, h | .fn _, _, _, n, h | .sv _, _, _, n, h | .par _, _, _, n, h => by
      simp [Ann.slotOf, slotVar, sealedFree] at h
  | .lam z own _ b, env, pos, n, h => by
      simp only [Ann.slotOf, sealedFree, List.mem_filter] at h
      exact Ann.sealedFree_slotOf R b _ _ n h.1
  | .app f a, env, pos, n, h => by
      simp only [Ann.slotOf, sealedFree, List.mem_append] at h
      rcases h with h | h
      · exact Ann.sealedFree_slotOf R f _ _ n h
      · exact Ann.sealedFree_slotOf R a _ _ n h
  | .quote c, _, _, n, h => by
      simp only [Ann.slotOf, sealedFree] at h
      exact codeVars_codeOf R c n h
  | .pquote c, env, _, n, h => by
      simp only [Ann.slotOf, sealedFree, sealedFree_sealParams] at h
      exact sealedFree_codeAt R (some env) [] [] [] c n h
  | .letP p w b, env, pos, n, h => by
      simp only [Ann.slotOf, sealedFree, List.mem_append] at h
      rcases h with (h | h) | h
      · exact Ann.sealedFree_slotOf R p _ _ n h
      · exact Ann.sealedFree_slotOf R w _ _ n h
      · exact Ann.sealedFree_slotOf R b _ _ n h
  | .letA y₀ ys p w b, env, pos, n, h => by
      simp only [Ann.slotOf, sealedFree, List.mem_append, List.mem_filter] at h
      rcases h with ⟨(h | h) | h, -⟩ | h
      · exact Ann.sealedFree_slotOf R p _ _ n h
      · simp at h
      · exact Ann.sealedFree_slotOf R b _ _ n h
      · exact Ann.sealedFree_slotOf R w _ _ n h
  | .alt t u, env, pos, n, h => by
      simp only [Ann.slotOf, sealedFree, List.mem_append] at h
      rcases h with h | h
      · exact Ann.sealedFree_slotOf R t _ _ n h
      · exact Ann.sealedFree_slotOf R u _ _ n h
  | .new [] b, env, pos, n, h => by
      simp only [Ann.slotOf] at h
      exact Ann.sealedFree_slotOf R b _ _ n h
  | .new (y₀ :: ys) b, env, pos, n, h => by
      simp only [Ann.slotOf, newBlock, sealedFree, List.mem_append, List.mem_filter] at h
      rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · exact Ann.sealedFree_slotOf R b _ _ n h
      · simp at h

/-! ## Holes are variables of elaborated text -/

omit [DecidableEq X] in
/-- In a term without contextual code, a name of code is one of its variables. -/
theorem mem_vars_of_mem_codeVars {Y : Type v} {n : Nm Y} :
    ∀ {t : Tm S Y}, ctxFree t → n ∈ codeVars t → n ∈ Tm.vars t
  | .var _, _, h => by simpa [codeVars, Tm.vars] using h
  | .lam _ _ b, hc, h => by
      simp only [codeVars, Tm.vars] at h ⊢
      exact mem_vars_of_mem_codeVars (t := b) hc h
  | .app f a, hc, h => by
      simp only [codeVars, Tm.vars, List.mem_append] at h ⊢
      exact h.imp (mem_vars_of_mem_codeVars hc.1) (mem_vars_of_mem_codeVars hc.2)
  | .quote c, hc, h => by
      simp only [codeVars, Tm.vars] at h ⊢
      exact mem_vars_of_mem_codeVars (t := c) hc h
  | .pquote c, hc, h => by
      simp only [codeVars, Tm.vars] at h ⊢
      exact mem_vars_of_mem_codeVars (t := c) hc h
  | .letP p w b, hc, h => by
      simp only [codeVars, Tm.vars, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (mem_vars_of_mem_codeVars hc.1 h))
      · exact Or.inl (Or.inr (mem_vars_of_mem_codeVars hc.2.1 h))
      · exact Or.inr (mem_vars_of_mem_codeVars hc.2.2 h)
  | .alt t u, hc, h => by
      simp only [codeVars, Tm.vars, List.mem_append] at h ⊢
      exact h.imp (mem_vars_of_mem_codeVars hc.1) (mem_vars_of_mem_codeVars hc.2)
  | .ctx _ _, hc, _ => hc.elim
  | .sym _, _, h | .fn _, _, h | .pvar _, _, h => by simp [codeVars] at h

omit [DecidableEq X] in
/-- In a term without contextual code, a free name of sealed code is one of its
variables. -/
theorem mem_vars_of_mem_sealedFree {Y : Type v} [DecidableEq Y] {n : Nm Y} :
    ∀ {t : Tm S Y}, ctxFree t → n ∈ sealedFree t → n ∈ Tm.vars t
  | .quote c, hc, h => by
      simp only [sealedFree, Tm.vars] at h ⊢
      exact mem_vars_of_mem_codeVars (t := c) hc h
  | .lam _ _ b, hc, h => by
      simp only [sealedFree, List.mem_filter, Tm.vars] at h ⊢
      exact mem_vars_of_mem_sealedFree (t := b) hc h.1
  | .app f a, hc, h => by
      simp only [sealedFree, Tm.vars, List.mem_append] at h ⊢
      exact h.imp (mem_vars_of_mem_sealedFree hc.1) (mem_vars_of_mem_sealedFree hc.2)
  | .pquote c, hc, h => by
      simp only [sealedFree, Tm.vars] at h ⊢
      exact mem_vars_of_mem_sealedFree (t := c) hc h
  | .letP p w b, hc, h => by
      simp only [sealedFree, Tm.vars, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (mem_vars_of_mem_sealedFree hc.1 h))
      · exact Or.inl (Or.inr (mem_vars_of_mem_sealedFree hc.2.1 h))
      · exact Or.inr (mem_vars_of_mem_sealedFree hc.2.2 h)
  | .alt t u, hc, h => by
      simp only [sealedFree, Tm.vars, List.mem_append] at h ⊢
      exact h.imp (mem_vars_of_mem_sealedFree hc.1) (mem_vars_of_mem_sealedFree hc.2)
  | .ctx _ _, hc, _ => hc.elim
  | .sym _, _, h | .fn _, _, h | .var _, _, h | .pvar _, _, h => by simp [sealedFree] at h

omit [DecidableEq X] in
theorem ctxFree_sealParams {Y : Type v} [DecidableEq Y] {t : Tm S Y} (h : ctxFree t) :
    ctxFree (sealParams t) := by
  unfold sealParams
  induction paramOcc t with
  | nil => exact h
  | cons _ _ ih => simpa only [List.foldr_cons, ctxFree] using ih

/-- Sealed code holds no contextual code. -/
theorem ctxFree_codeAt (R : Owner) :
    ∀ (holes : Option (X → Owner)) (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X),
      ctxFree (codeAt R holes penv senv pos s)
  | _, _, _, _, .sym _ | _, _, _, _, .fn _ => trivial
  | _, penv, _, _, .par z => by
      simp only [codeAt]
      split <;> trivial
  | holes, _, senv, _, .sv y => by
      simp only [codeAt]
      split
      · trivial
      · split <;> trivial
  | holes, penv, senv, pos, .lam z _ b => by
      simpa only [codeAt, ctxFree] using ctxFree_codeAt R holes _ senv _ b
  | holes, penv, senv, pos, .form z b => by
      simpa only [codeAt, ctxFree] using ctxFree_codeAt R holes _ senv _ b
  | holes, penv, senv, pos, .app f a =>
      ⟨ctxFree_codeAt R holes penv senv _ f, ctxFree_codeAt R holes penv senv _ a⟩
  | _, _, _, _, .quote c => ctxFree_sealParams (ctxFree_codeAt R none [] [] [] c)
  | holes, _, _, _, .pquote c => ctxFree_codeAt R holes [] [] [] c
  | holes, penv, senv, pos, .letS p w b _ =>
      ⟨ctxFree_codeAt R holes _ _ _ p, ctxFree_codeAt R holes _ _ _ w,
        ctxFree_codeAt R holes _ _ _ b⟩
  | holes, penv, senv, pos, .unify p w b =>
      ⟨ctxFree_codeAt R holes _ _ _ p, ctxFree_codeAt R holes _ _ _ w,
        ctxFree_codeAt R holes _ _ _ b⟩
  | holes, penv, senv, pos, .alt t u =>
      ⟨ctxFree_codeAt R holes _ _ _ t, ctxFree_codeAt R holes _ _ _ u⟩
  | holes, penv, senv, pos, .new _ b => by
      simpa only [codeAt] using ctxFree_codeAt R holes penv senv _ b

/-- **Elaborated text holds no contextual code.** -/
theorem Ann.ctxFree_slotOf (R : Owner) :
    ∀ (t : Ann S X) (env : REnv X) (pos : Owner), ctxFree (t.slotOf R env pos)
  | .sym _, _, _ | .fn _, _, _ | .sv _, _, _ | .par _, _, _ => trivial
  | .lam _ _ _ b, _, _ => Ann.ctxFree_slotOf R b _ _
  | .app f a, _, _ => ⟨Ann.ctxFree_slotOf R f _ _, Ann.ctxFree_slotOf R a _ _⟩
  | .quote c, _, _ => ctxFree_sealParams (ctxFree_codeAt R none [] [] [] c)
  | .pquote c, _, _ => ctxFree_sealParams (ctxFree_codeAt R _ [] [] [] c)
  | .letP p w b, _, _ =>
      ⟨Ann.ctxFree_slotOf R p _ _, Ann.ctxFree_slotOf R w _ _, Ann.ctxFree_slotOf R b _ _⟩
  | .letA _ _ p w b, _, _ =>
      ⟨⟨Ann.ctxFree_slotOf R p _ _, trivial, Ann.ctxFree_slotOf R b _ _⟩,
        Ann.ctxFree_slotOf R w _ _⟩
  | .alt t u, _, _ => ⟨Ann.ctxFree_slotOf R t _ _, Ann.ctxFree_slotOf R u _ _⟩
  | .new [] b, _, _ => Ann.ctxFree_slotOf R b _ _
  | .new (_ :: _) b, _, _ => ⟨Ann.ctxFree_slotOf R b _ _, trivial⟩

/-- **The identity model's frame collects the holes of its form**: a hole of
sealed code written in a form rooted at `R` is, on the identity side, the head
slot of `R`'s frame, and it is among the frame's slots. -/
theorem Ann.hole_mem_frameSlots {R : Owner} (hR : formRoot R) {t : Ann S X} {env : REnv X}
    {pos : Owner} {ν μ : Nm (Slot X) → Nm (BId X)} {k : Kd} {Res : List (Nm (BId X))}
    {ok : Bool} {t₂ : Tm S (BId X)} (hrel : Rel SC ν μ k Res ok (t.slotOf R env pos) t₂) {y : X}
    (hy : (.src (R, y) : Nm (Slot X)) ∈ sealedFree (t.slotOf R env pos)) :
    BId.slot ⟨y, R, R, .head⟩ ∈ frameSlots R t₂ := by
  have h := hrel.holeRead_mem_sealedFree hy
  change codeFwd (.src (R, y)) ∈ sealedFree t₂ at h
  rw [codeFwd_scope hR.scopeOwner] at h
  exact slot_mem_frameSlots
    (mem_vars_of_mem_sealedFree (hrel.ctxFree (Ann.ctxFree_slotOf R t env pos)) h) rfl

/-! ## The static relation -/

/-- **The two elaborations of well-formed annotated text are related.**  When
each spelling's slot is sent to its identity, the identities belong to the
enclosing frames, and each free parameter is sent to its binder, the slot
model's term and the identity model's term are related by `Rel`, as a pattern
(`k = .pat`, for text without `new` blocks on its spine) or as code, with
reserved names satisfying `ResOK`. A pattern quotation is related as code:
its holes are the outer slots, and its binders travel by `CodeRel`. The
resolution environment and the owners written at `posS` are scope owners. -/
theorem rel_ann {R : Owner} (hR : formRoot R) (t : Ann S X) :
    ∀ {k : Kd} {env : REnv X} {posS : Owner} {envI : IEnv X}
    {pv : X → Owner} {fr posI : Owner} {ν μ : Nm (Slot X) → Nm (BId X)},
    t.WF posI → k ≠ .val → (k = .pat → t.NewFree) →
    (∀ y ∈ t.names, ν (.src (env y, y)) = .src (.slot (envI y))) →
    (∀ y ∈ t.names, (envI y).spell = y ∧ (envI y).frame <+: fr) → fr <+: posI →
    (∀ z ∈ t.freePars, μ (.src ([], z)) = .src (.par z (pv z))) →
    (∀ y, scopeOwner (env y)) → PosSafe posS →
    ∃ Res, Rel SC ν μ k Res (annOK t) (t.slotOf R env posS) (t.idOf R envI pv fr posI) ∧
      ResOK fr posI t (t.slotOf R env posS) (t.idOf R envI pv fr posI) Res := by
  induction t with
  | sym s =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨[], .sym s, .nil⟩
  | fn F =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      exact ⟨[], .fn F, .nil⟩
  | sv y =>
      intro k env posS envI pv fr posI ν μ _ _ _ hν _ _ _ hE _
      refine ⟨[], ?_, .nil⟩
      show Rel SC ν μ k [] true (.var (.src (env y, y))) (.var (.src (.slot (envI y))))
      rw [← hν y (by simp [Ann.names])]
      exact .var (.src (env y, y)) <| by
        rw [hν y (by simp [Ann.names])]
        simp only [SC, scVarHole, holeRecS, holeRecI, (hE y).1]
        decide
  | par z =>
      intro k env posS envI pv fr posI ν μ _ _ _ _ _ _ hμ _ _
      refine ⟨[], ?_, .nil⟩
      show Rel SC ν μ k [] true (.pvar (.src ([], z))) (.pvar (.src (.par z (pv z))))
      rw [← hμ z (by simp [Ann.freePars])]
      exact .pvar (.src ([], z)) <| by
        rw [hμ z (by simp [Ann.freePars])]
        exact scParOK_scope
  | quote c =>
      intro _ _ _ _ _ _ _ ν _ _ _ _ _ _ _ _ _ _
      exact ⟨[], .quote (QR_codeOf hR c ν), .nil⟩
  | pquote c =>
      intro _ env _ envI _ _ _ ν μ _ _ _ hν _ _ _ hE _
      simp only [Ann.slotOf, Ann.idOf]
      have hB : ∀ y, codeBound (env y) = false := fun y => (hE y).1
      have hF : ∀ y, env y ≠ codeFreeParam := fun y => (hE y).2
      have hbody : Rel SC (codeMapHoles env envI) (codeMapHoles env envI) .code [] true
          (sealParams (codeAt R (some env) [] [] [] c))
          (sealParams (codeIAt R (some envI) [] [] [] c)) :=
        Rel.code_pattern (C := SC) R hR.scopeOwner env envI (fun s => QR_codeOf hR s _)
          (scVarHole_map env envI) (scParOK_map env envI)
          (fun {_ _ _} h₁ h₂ => scBare_map env envI h₁ h₂) hB hF c .code (by decide)
      have hbody' : Rel SC ν μ .code [] true
          (sealParams (codeAt R (some env) [] [] [] c))
          (sealParams (codeIAt R (some envI) [] [] [] c)) := by
        refine hbody.congr ?_ ?_ ?_
        · intro n hn
          rw [freeNames_sealParams] at hn
          obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt R env [] [] [] c n hn
          rw [codeMapHoles_hole (hB y) (hF y), hν y (by simpa [Ann.names] using hy)]
        · intro n hn
          rw [sealedFree_sealParams] at hn
          obtain ⟨y, rfl⟩ := sealedFree_codeAt R (some env) [] [] [] c n hn
          exact Or.inl ⟨_, rfl⟩
        · intro x hx
          rw [freeParams_sealParams] at hx
          cases hx
      exact ⟨[], .pquote hbody' (hbody'.shape_of rfl) rfl, ResOK.nil⟩
  | lam z own key b ih =>
      intro _ env posS envI pv fr posI ν μ hwf _ _ hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hkeys, hwfb⟩ := hwf
      have hνb : ∀ y ∈ b.names, bindν ν (posS ++ [0]) own key
          (.src (env.update own (posS ++ [0]) y, y)) = .src (.slot (envI.set own key y)) := by
        intro y hy
        by_cases hyo : y ∈ own
        · rw [Ann.update_of_mem hyo, bindν_on hyo, IEnv.set_of_mem hyo]
        · rw [Ann.update_of_not_mem hyo, bindν_not_mem hyo, IEnv.set_of_not_mem hyo]
          exact hν y hy
      have hIb : ∀ y ∈ b.names, (envI.set own key y).spell = y ∧
          (envI.set own key y).frame <+: posI ++ [0] := by
        intro y hy
        by_cases hyo : y ∈ own
        · rw [IEnv.set_of_mem hyo, (hkeys y hyo).2.1]
          exact ⟨(hkeys y hyo).1, List.prefix_refl _⟩
        · rw [IEnv.set_of_not_mem hyo]
          exact ⟨(hI y hy).1, ((hI y hy).2.trans hfr).trans (List.prefix_append _ _)⟩
      have hμb : ∀ z' ∈ b.freePars, Function.update μ (parName z) (.src (.par z posI))
          (.src ([], z')) = .src (.par z' (pvSet pv z posI z')) := by
        intro z' hz'
        by_cases hzz : z' = z
        · subst hzz
          simp [pvSet, parName]
        · have hne : (.src ([], z') : Nm (Slot X)) ≠ parName z := by
            simp [parName, hzz]
          rw [Function.update_of_ne hne]
          simp only [pvSet, if_neg hzz]
          exact hμ z' (by simp [Ann.freePars, hz', hzz])
      obtain ⟨Rb, hrel, hres⟩ := ih (k := .code) (env := env.update own (posS ++ [0]))
        (posS := posS ++ [0]) (envI := envI.set own key) (pv := pvSet pv z posI)
        (fr := posI ++ [0]) (posI := posI ++ [0]) (ν := bindν ν (posS ++ [0]) own key)
        (μ := Function.update μ (parName z) (.src (.par z posI))) hwfb (by decide)
        (fun h => by cases h) hνb hIb (List.prefix_refl _) hμb
        (scopeOwner_update hE (headSafe.owner hP.1)) hP.zero
      obtain ⟨hown, hresb, hinj, hdisj⟩ := frame_conds (key := key) hrel hres
        (fun y _ hy => Ann.update_of_mem hy) (fun y hy => bindν_on hy)
        (fun y hy hyo => ⟨envI y, by rw [Ann.update_of_not_mem hyo, bindν_not_mem hyo]; exact hν y hy,
          ne_of_prefix ((hI y hy).2.trans hfr) 0⟩) hkeys (Ann.Open.of_WF hwfb)
      have hnotown : ∀ n ∈ sealedFree (b.slotOf R (env.update own (posS ++ [0])) (posS ++ [0])),
          ownKey (own.map fun y => (posS ++ [0], y)) n = false := by
        intro n hn
        obtain ⟨y, rfl⟩ := Ann.sealedFree_slotOf R b _ _ n hn
        rw [ownKey_map_src, decide_eq_false_iff_not]
        rintro ⟨hRo, -⟩
        exact not_formRoot_append posS (by decide) (hRo ▸ hR)
      have hfreeOwn : ∀ n ∈ freeNames (b.slotOf R (env.update own (posS ++ [0])) (posS ++ [0])) ++
          sealedFree (b.slotOf R (env.update own (posS ++ [0])) (posS ++ [0])),
          ownKey (own.map fun y => (posS ++ [0], y)) n = true →
          n ∈ freeNames (b.slotOf R (env.update own (posS ++ [0])) (posS ++ [0])) := by
        intro n hn ho
        rcases List.mem_append.1 hn with h | h
        · exact h
        · rw [hnotown n h] at ho
          cases ho
      refine ⟨[], ?_, .nil⟩
      simp only [Ann.slotOf, Ann.idOf]
      refine .lam (νb := bindν ν (posS ++ [0]) own key)
        (μb := Function.update μ (parName z) (.src (.par z posI)))
        (fun n hn => bindν_off hn) (fun x hx => Function.update_of_ne hx _ _)
        (Function.update_self _ _ _) ?_ ?_ hrel hown hresb
        (fun n hn n' hn' ho ho' he => hinj n (hfreeOwn n hn ho) n' (hfreeOwn n' hn' ho') ho ho' he)
        (fun n hn ho => hdisj n (hfreeOwn n hn ho) ho) hres.nodup ?_
        scBare_scope
        (by
          intro hent
          simp only [SC, scEnter, holeRecS, holeRecI, codeFreeS, codeFreeI, parName,
            codeBound, codeFreeParam] at hent
          rcases hent with hent | hent
          · exact absurd hent.1 Bool.false_ne_true.symm
          · exact absurd hent.1 Bool.false_ne_true) ?_ ?_
      · intro s hs h
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 hs
        exact (by simp : posS ++ [0] ≠ []) h
      · intro s hs h
        obtain ⟨k', rfl, hkF⟩ := frame_of_mem_frameSlots hs
        obtain ⟨k'', hk'', hk0⟩ := h
        injection hk'' with hk''
        subst hk''
        rw [hkF] at hk0
        simp at hk0
      · intro x hx hne
        obtain ⟨z', hz', rfl⟩ := Ann.freeParams_slotOf R b _ _ x (Ann.Open.of_WF hwfb) hx
        have hzz : z' ≠ z := fun e => hne (by rw [e]; rfl)
        rw [hμ z' (by simp [Ann.freePars, hz', hzz])]
        intro e
        injection e with e
        injection e with e
        exact hzz e
      · intro s hs
        rw [hnotown _ hs]
        obtain ⟨y, hy⟩ := Ann.sealedFree_slotOf R b _ _ _ hs
        cases hy
        change ownKey _ (codeFwd (.src (R, y))) = false
        rw [codeFwd_scope hR.scopeOwner]
        cases hk : ownKey (frameSlots (posI ++ [0])
            (b.idOf R (envI.set own key) (pvSet pv z posI) (posI ++ [0]) (posI ++ [0])))
            (.src (.slot ⟨y, R, R, .head⟩))
        · rfl
        · exfalso
          simp only [ownKey, List.contains_eq_mem, decide_eq_true_eq] at hk
          obtain ⟨k', hk', hkF⟩ := frame_of_mem_frameSlots hk
          injection hk' with hk'
          subst hk'
          have hRe : R = posI ++ [0] := hkF
          exact not_formRoot_append posI (i := 0) (by decide) (hRe ▸ hR)
      · intro n hn ho
        rw [hnotown n hn] at ho
        cases ho
  | app f a ihf iha =>
      intro k env posS envI pv fr posI ν μ hwf hk hpat hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hwf₁, hwf₂⟩ := hwf
      obtain ⟨R₁, h₁, hr₁⟩ := ihf (posS := posS ++ [0]) hwf₁ hk
        (fun e => by have := hpat e; simp only [Ann.NewFree] at this; exact this.1)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hfr.trans (List.prefix_append _ _)) (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        hE hP.zero
      obtain ⟨R₂, h₂, hr₂⟩ := iha (posS := posS ++ [1]) hwf₂ hk
        (fun e => by have := hpat e; simp only [Ann.NewFree] at this; exact this.2)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hfr.trans (List.prefix_append _ _)) (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        hE hP.one
      simp only [Ann.slotOf, Ann.idOf]
      exact ⟨R₁ ++ R₂, .app h₁ h₂, ResOK.two (by decide) hr₁ hr₂ (fun _ h => h) (fun _ h => h)
        (fun m hm => by simp [freeNames, hm]) (fun m hm => by simp [freeNames, hm])⟩
  | letP p w b ihp ihw ihb =>
      intro k env posS envI pv fr posI ν μ hwf hk _ hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hnf, hwp, hww, hwb⟩ := hwf
      have hpre : ∀ i, fr <+: posI ++ [i] := fun i => hfr.trans (List.prefix_append _ _)
      obtain ⟨Rp, hp, hrp⟩ := ihp (k := .pat) (posS := posS ++ [0]) hwp (by decide) (fun _ => hnf)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hpre 0) (fun z hz => hμ z (by simp [Ann.freePars, hz])) hE hP.zero
      obtain ⟨Rw, hw, hrw⟩ := ihw (k := .code) (posS := posS ++ [1]) hww (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hpre 1) (fun z hz => hμ z (by simp [Ann.freePars, hz])) hE hP.one
      obtain ⟨Rb, hb, hrb⟩ := ihb (k := .code) (posS := posS ++ [2]) hwb (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hpre 2) (fun z hz => hμ z (by simp [Ann.freePars, hz])) hE hP.two
      simp only [Ann.slotOf, Ann.idOf]
      exact ⟨Rp ++ Rw ++ Rb, .letP hk hp hw hb, ResOK.three hrp hrw hrb (fun _ h => h)
        (fun _ h => h) (fun _ h => h) (fun m hm => by simp [freeNames, hm])
        (fun m hm => by simp [freeNames, hm]) (fun m hm => by simp [freeNames, hm])⟩
  | letA y₀ ys p w b ihp ihw ihb =>
      intro k env posS envI pv fr posI ν μ hwf hk _ hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hnf, hwp, hww, hwb⟩ := hwf
      have hpre : ∀ i, fr <+: posI ++ [i] := fun i => hfr.trans (List.prefix_append _ _)
      have hν' : ∀ y ∈ p.names ++ b.names,
          bindν ν (posS ++ [2]) (y₀ :: ys) (fun y => ⟨y, fr, posI, .pat⟩)
            (.src (env.update (y₀ :: ys) (posS ++ [2]) y, y)) =
          .src (.slot (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .pat⟩) y)) := by
        intro y hy
        by_cases hyo : y ∈ y₀ :: ys
        · rw [Ann.update_of_mem hyo, bindν_on hyo, IEnv.set_of_mem hyo]
        · rw [Ann.update_of_not_mem hyo, bindν_not_mem hyo, IEnv.set_of_not_mem hyo]
          exact hν y (by simp only [List.mem_append] at hy; simp [Ann.names]; tauto)
      have hI' : ∀ y ∈ p.names ++ b.names,
          (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .pat⟩) y).spell = y ∧
          (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .pat⟩) y).frame <+: fr := by
        intro y hy
        by_cases hyo : y ∈ y₀ :: ys
        · rw [IEnv.set_of_mem hyo]
          exact ⟨rfl, List.prefix_refl _⟩
        · rw [IEnv.set_of_not_mem hyo]
          exact hI y (by simp only [List.mem_append] at hy; simp [Ann.names]; tauto)
      obtain ⟨Rp, hp, hrp⟩ := ihp (k := .pat) (posS := posS ++ [0])
        (env := env.update (y₀ :: ys) (posS ++ [2]))
        (envI := envI.set (y₀ :: ys) fun y => ⟨y, fr, posI, .pat⟩) (pv := pv) (fr := fr)
        (posI := posI ++ [0]) (ν := bindν ν (posS ++ [2]) (y₀ :: ys) fun y => ⟨y, fr, posI, .pat⟩)
        (μ := μ) hwp (by decide) (fun _ => hnf) (fun y hy => hν' y (List.mem_append_left _ hy))
        (fun y hy => hI' y (List.mem_append_left _ hy)) (hpre 0)
        (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        (scopeOwner_update hE (headSafe.owner hP.2.2)) hP.zero
      obtain ⟨Rw, hw, hrw⟩ := ihw (k := .code) (posS := posS ++ [1]) (env := env) (envI := envI)
        (pv := pv) (fr := fr) (posI := posI ++ [1]) (ν := ν) (μ := μ) hww (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hpre 1) (fun z hz => hμ z (by simp [Ann.freePars, hz])) hE hP.one
      obtain ⟨Rb, hb, hrb⟩ := ihb (k := .code) (posS := posS ++ [2])
        (env := env.update (y₀ :: ys) (posS ++ [2]))
        (envI := envI.set (y₀ :: ys) fun y => ⟨y, fr, posI, .pat⟩) (pv := pv) (fr := fr)
        (posI := posI ++ [2]) (ν := bindν ν (posS ++ [2]) (y₀ :: ys) fun y => ⟨y, fr, posI, .pat⟩)
        (μ := μ) hwb (by decide) (fun h => by cases h)
        (fun y hy => hν' y (List.mem_append_right _ hy))
        (fun y hy => hI' y (List.mem_append_right _ hy)) (hpre 2)
        (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        (scopeOwner_update hE (headSafe.owner hP.2.2)) hP.two
      simp only [Ann.slotOf, Ann.idOf]
      exact rel_letA_of hk (not_formRoot_append posS (by decide))
        (fun h => by
          obtain ⟨z, _, hz⟩ := Ann.freeParams_slotOf R p _ _ _ (Ann.Open.of_WF hwp) h
          simp [letParam] at hz)
        (fun h => by
          obtain ⟨z, _, hz⟩ := Ann.freeParams_slotOf R b _ _ _ (Ann.Open.of_WF hwb) h
          simp [letParam] at hz)
        hw hp hb hrp hrw hrb trivial (fun _ h => h) (fun _ h => h) (fun _ h => h)
  | alt t₁ t₂ ih₁ ih₂ =>
      intro k env posS envI pv fr posI ν μ hwf hk _ hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      obtain ⟨hw₁, hw₂⟩ := hwf
      obtain ⟨R₁, h₁, hr₁⟩ := ih₁ (k := .code) (posS := posS ++ [0]) hw₁ (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hfr.trans (List.prefix_append _ _)) (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        hE hP.zero
      obtain ⟨R₂, h₂, hr₂⟩ := ih₂ (k := .code) (posS := posS ++ [1]) hw₂ (by decide)
        (fun h => by cases h)
        (fun y hy => hν y (by simp [Ann.names, hy])) (fun y hy => hI y (by simp [Ann.names, hy]))
        (hfr.trans (List.prefix_append _ _)) (fun z hz => hμ z (by simp [Ann.freePars, hz]))
        hE hP.one
      simp only [Ann.slotOf, Ann.idOf]
      exact ⟨R₁ ++ R₂, .alt hk h₁ h₂, ResOK.two (by decide) hr₁ hr₂ (fun _ h => h) (fun _ h => h)
        (fun m hm => by simp [freeNames, hm]) (fun m hm => by simp [freeNames, hm])⟩
  | new ys b ih =>
      intro k env posS envI pv fr posI ν μ hwf hk hpat hν hI hfr hμ hE hP
      simp only [Ann.WF] at hwf
      cases ys with
      | nil =>
          obtain ⟨R, h, hr⟩ := ih (k := k) (posS := posS ++ [0]) (env := env) (envI := envI)
            (pv := pv) (fr := fr) (posI := posI) (ν := ν) (μ := μ) hwf hk
            (fun e => by have := hpat e; simpa [Ann.NewFree] using this)
            (fun y hy => hν y (by simpa [Ann.names] using hy))
            (fun y hy => hI y (by simpa [Ann.names] using hy)) hfr
            (fun z hz => hμ z (by simpa [Ann.freePars] using hz)) hE hP.zero
          simp only [Ann.slotOf, Ann.idOf, IEnv.set_nil]
          exact ⟨R, h, hr.nodup, fun m hm => hr.shape m hm, hr.free, hr.news⟩
      | cons y₀ ys =>
          have hkc : k = .code := by
            cases k with
            | val => exact absurd rfl hk
            | pat =>
                have := hpat rfl
                simp [Ann.NewFree] at this
            | code => rfl
          subst hkc
          have hν' : ∀ y ∈ b.names,
              bindν ν (posS ++ [0]) (y₀ :: ys) (fun y => ⟨y, fr, posI, .new⟩)
                (.src (env.update (y₀ :: ys) (posS ++ [0]) y, y)) =
              .src (.slot (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .new⟩) y)) := by
            intro y hy
            by_cases hyo : y ∈ y₀ :: ys
            · rw [Ann.update_of_mem hyo, bindν_on hyo, IEnv.set_of_mem hyo]
            · rw [Ann.update_of_not_mem hyo, bindν_not_mem hyo, IEnv.set_of_not_mem hyo]
              exact hν y (by simpa [Ann.names] using hy)
          have hI' : ∀ y ∈ b.names,
              (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .new⟩) y).spell = y ∧
              (envI.set (y₀ :: ys) (fun y => ⟨y, fr, posI, .new⟩) y).frame <+: fr := by
            intro y hy
            by_cases hyo : y ∈ y₀ :: ys
            · rw [IEnv.set_of_mem hyo]
              exact ⟨rfl, List.prefix_refl _⟩
            · rw [IEnv.set_of_not_mem hyo]
              exact hI y (by simpa [Ann.names] using hy)
          obtain ⟨Rb, hb, hrb⟩ := ih (k := .code) (posS := posS ++ [0])
            (env := env.update (y₀ :: ys) (posS ++ [0]))
            (envI := envI.set (y₀ :: ys) fun y => ⟨y, fr, posI, .new⟩) (pv := pv) (fr := fr)
            (posI := posI) (ν := bindν ν (posS ++ [0]) (y₀ :: ys) fun y => ⟨y, fr, posI, .new⟩)
            (μ := μ) hwf (by decide) (fun h => by cases h) hν' hI' hfr
            (fun z hz => hμ z (by simpa [Ann.freePars] using hz))
            (scopeOwner_update hE (headSafe.owner hP.1)) hP.zero
          simp only [Ann.slotOf, Ann.idOf, newBlock]
          exact rel_new_of (not_formRoot_append posS (by decide))
            (fun h => by
              obtain ⟨z, _, hz⟩ := Ann.freeParams_slotOf R b _ _ _ (Ann.Open.of_WF hwf) h
              simp [newParam] at hz)
            hb hrb (fun _ h => h)
            (fun n hn ho => by
              obtain ⟨y, _, rfl⟩ := Ann.freeNames_slotOf R b _ _ n (Ann.Open.of_WF hwf) hn
              by_cases hyo : y ∈ y₀ :: ys
              · rw [Ann.update_of_mem hyo, ownKey_map_src, decide_eq_false_iff_not] at ho
                exact absurd ⟨rfl, hyo⟩ ho
              · simpa [spellS] using hyo)

/-- **`rel_ann` needs a form root**: at the scope owner `[2]`, which is no form
root, the hole of a quotation is not a hole of the setting, so the two
elaborations of `(quote $y)` are not related.  The statement asked `scopeOwner R`
only; `[2]` is a scope owner. -/
theorem rel_ann_needs_formRoot (y : X) {ν μ : Nm (Slot X) → Nm (BId X)} {k : Kd}
    {Res : List (Nm (BId X))} {ok : Bool} {t₂ : Tm S (BId X)} :
    scopeOwner ([2] : Owner) ∧ ¬ Rel SC ν μ k Res ok (.quote (codeOf [2] (.sv y))) t₂ := by
  refine ⟨⟨rfl, by decide⟩, fun h => ?_⟩
  cases h with
  | quote hq =>
      have hh := hq.2.1.2.1 (.src ([2], y))
        (by simp [codeOf, codeAt, codeLookup, sealParams, paramOcc, codeVars])
      simp [holeName, SC, formRoot] at hh

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
