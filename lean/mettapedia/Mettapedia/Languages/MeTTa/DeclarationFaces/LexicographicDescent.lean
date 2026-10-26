import Mettapedia.Languages.MeTTa.DeclarationFaces.Termination

/-!
# Lexicographic descent: recursion on a list of positions

Structural descent recurses on one argument position. Ackermann's function

    (= (ack Z $n) (S $n))
    (= (ack (S $m) Z) (ack $m (S Z)))
    (= (ack (S $m) (S $n)) (ack $m (ack (S $m) $n)))

recurses on its first argument, or keeps it and recurses on its second. A **lexicographic
certificate** gives every symbol a rank and a list of positions. A call of `g` by an equation of `f` of
the same rank descends when, along their lists, it keeps the pattern argument at some first positions
syntactically and then takes a proper part of the pattern argument at the next one (`LexDesc`).
Symbols of one rank may call each other, so mutual recursion is covered:

    (= (even Z) True)   (= (even (S $n)) (odd $n))
    (= (odd Z) False)   (= (odd (S $n)) (even $n))

**Strong normalization** (`Program.LexDescends.stronglyNormalizing`): every term of a headed,
lexicographically descending program whose right sides use only their left side's variables starts
no infinite sequence of steps. The proof is the structural one with the single key replaced by the
list of keys, ordered lexicographically; that order is well founded on lists of strongly
normalizing terms (`acc_lexLt`).

Structural descent is the case of one position.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Relation Tm
open Mettapedia.Logic.Relation (IsNormal accessible_transitiveClosure)

universe u v

/-! ## The lexicographic order on lists of one length -/

/-- `LexLt R new old`: the lists agree up to a first position where `new` is `R`-below `old`; after it
they have the same length. -/
inductive LexLt {α : Type v} (R : α → α → Prop) : List α → List α → Prop where
  | head {a b : α} {l l' : List α} : R a b → l.length = l'.length → LexLt R (a :: l) (b :: l')
  | tail (a : α) {l l' : List α} : LexLt R l l' → LexLt R (a :: l) (a :: l')

theorem LexLt.length_eq {α : Type v} {R : α → α → Prop} {l l' : List α} (h : LexLt R l l') :
    l.length = l'.length := by
  induction h with
  | head _ len => simp [len]
  | tail _ _ ih => simp [ih]

/-- The lexicographic order restricted to lists of elements of a set. -/
def LexLtIn {α : Type v} (R : α → α → Prop) (D : α → Prop) (l l' : List α) : Prop :=
  LexLt R l l' ∧ ∀ a ∈ l, D a

/-- **The lexicographic order is well founded** on lists of elements on which `R` is. -/
theorem acc_lexLt {α : Type v} {R : α → α → Prop} {D : α → Prop}
    (accD : ∀ a, D a → Acc R a) : ∀ n (l : List α), l.length = n → (∀ a ∈ l, D a) →
      Acc (LexLtIn R D) l := by
  intro n
  induction n with
  | zero =>
      intro l len _
      rw [List.eq_nil_of_length_eq_zero len]
      constructor
      rintro l' ⟨lt, _⟩
      cases lt
  | succ n ihn =>
      have main : ∀ b, Acc R b → D b → ∀ l', l'.length = n → (∀ a ∈ l', D a) →
          Acc (LexLtIn R D) (b :: l') := by
        intro b accB
        induction accB with
        | intro b _ ihb =>
        intro hb l' len' hl'
        have accTail := ihn l' len' hl'
        induction accTail with
        | intro l' _ ihl =>
        constructor
        rintro k ⟨lt, hk⟩
        cases lt with
        | @head a _ l _ hR hlen =>
            exact ihb a hR (hk a List.mem_cons_self) l (by rw [hlen]; exact len')
              (fun x hx => hk x (List.mem_cons_of_mem a hx))
        | @tail _ l _ ltTail =>
            exact ihl l ⟨ltTail, fun x hx => hk x (List.mem_cons_of_mem b hx)⟩
              (by rw [ltTail.length_eq]; exact len')
              (fun x hx => hk x (List.mem_cons_of_mem b hx))
      intro l len hl
      cases l with
      | nil => simp at len
      | cons b l' =>
          exact main b (accD b (hl b List.mem_cons_self)) (hl b List.mem_cons_self) l'
            (by simpa using len) (fun a ha => hl a (List.mem_cons_of_mem b ha))

/-! ## Certificates and descent -/

variable {S : Type u}

/-- The argument at a position, or a variable when there is none. -/
def keyAt (args : List (Tm S)) (i : Nat) : Tm S := args[i]?.getD (.var "")

/-- **A lexicographic certificate**: a rank and a list of positions for every symbol. -/
structure LexCertificate (S : Type u) where
  rank : S → ℕ
  positions : S → List ℕ

/-- Lexicographic descent of the arguments `us` of a call along the positions `M` of the callee,
from the patterns `ps` along the positions `L` of the caller: some first keys are kept, the next is a
proper part, and the two lists have one length from there on. -/
inductive LexDesc (ps us : List (Tm S)) : List ℕ → List ℕ → Prop where
  | here {i j : Nat} {L M : List ℕ} : i < ps.length → j < us.length → L.length = M.length →
      ProperSub (keyAt ps i) (keyAt us j) → LexDesc ps us (i :: L) (j :: M)
  | next {i j : Nat} {L M : List ℕ} : i < ps.length → j < us.length → keyAt us j = keyAt ps i →
      LexDesc ps us L M → LexDesc ps us (i :: L) (j :: M)

/-- A call `(g us)` made by an equation of `f` with patterns `ps` descends lexicographically: `g` heads
no equation, or has a smaller rank, or has the same rank and its keys descend. Symbols of one rank may
call each other: mutual recursion. -/
def LexCallDescends (P : Program S) (c : LexCertificate S) (f : S) (ps : List (Tm S)) (g : S)
    (us : List (Tm S)) : Prop :=
  ¬ P.Defines g ∨ c.rank g < c.rank f ∨
    (c.rank g = c.rank f ∧ LexDesc ps us (c.positions f) (c.positions g))

/-- **A lexicographically descending program.** -/
def Program.LexDescends (P : Program S) (c : LexCertificate S) : Prop :=
  ∀ e ∈ P, ∃ f ps, e.lhs = .app f ps ∧ EveryCall (LexCallDescends P c f ps) e.rhs

/-- The keys of a call along a list of positions. -/
def lexKeys (L : List ℕ) (args : List (Tm S)) : List (Tm S) := L.map (keyAt args)

theorem keyAt_map_subst {σ : String → Tm S} {args : List (Tm S)} {i : Nat} (hi : i < args.length) :
    keyAt (args.map (subst σ)) i = (keyAt args i).subst σ := by
  simp [keyAt, hi]

theorem properSub_var_false {x : String} {t : Tm S} : ¬ ProperSub (.var x) t := by
  intro h
  induction h with
  | single sub => cases sub
  | tail _ sub ih => exact ih

/-- **Lexicographic descent is stable under instantiation**, as the lexicographic order on keys. -/
theorem LexDesc.instantiate {P : Program S} {ps us : List (Tm S)} (σ : String → Tm S) :
    ∀ {L M : List ℕ}, LexDesc ps us L M →
      LexLt (fun a b => TransGen (Below P) a b) (lexKeys M (us.map (subst σ))) (lexKeys L (ps.map (subst σ))) := by
  intro L M desc
  induction desc with
  | @here i j L M hp hu len part =>
      refine LexLt.head ?_ (by simp [len])
      rw [keyAt_map_subst hu, keyAt_map_subst hp]
      exact below_of_properSub (properSub_subst σ part)
  | @next i j L M hp hu same _ ih =>
      simp only [lexKeys, List.map_cons]
      rw [keyAt_map_subst hu, keyAt_map_subst hp, same]
      exact LexLt.tail _ ih

/-- Changing one argument by a step changes the keys downward, or not at all. -/
theorem keys_set {P : Program S} (args : List (Tm S)) (i : Nat) (lt : i < args.length) {b : Tm S}
    (step : Step P args[i] b) : ∀ L : List ℕ,
      (i ∈ L → LexLt (fun a b => TransGen (Below P) a b) (lexKeys L (args.set i b)) (lexKeys L args)) ∧
        (i ∉ L → lexKeys L (args.set i b) = lexKeys L args) := by
  intro L
  induction L with
  | nil => exact ⟨fun h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | cons j L ih =>
      constructor
      · intro hi
        by_cases same : j = i
        · subst same
          refine LexLt.head ?_ (by simp)
          simp only [keyAt, List.getElem?_set_self lt, Option.getD_some, lt, List.getElem?_eq_getElem]
          exact .single (Or.inl step)
        · have hL : i ∈ L := by
            rcases List.mem_cons.mp hi with h | h
            · exact absurd h.symm same
            · exact h
          simp only [lexKeys, List.map_cons]
          have hk : keyAt (args.set i b) j = keyAt args j := by
            simp [keyAt, List.getElem?_set_ne (Ne.symm same)]
          rw [hk]
          exact LexLt.tail _ (ih.1 hL)
      · intro hi
        have hj : j ≠ i := fun h => hi (h ▸ List.mem_cons_self)
        have hL : i ∉ L := fun h => hi (List.mem_cons_of_mem j h)
        simp only [lexKeys, List.map_cons]
        have hk : keyAt (args.set i b) j = keyAt args j := by
          simp [keyAt, List.getElem?_set_ne (Ne.symm hj)]
        rw [hk]
        exact congrArg _ (ih.2 hL)

theorem keyAt_sn {P : Program S} (headed : P.Headed) {args : List (Tm S)}
    (sn : ∀ a ∈ args, SN P a) (i : Nat) : SN P (keyAt args i) := by
  unfold keyAt
  cases h : args[i]? with
  | none => exact Acc.intro _ fun target step => absurd step (var_normal headed "" target)
  | some a => exact sn a (List.mem_of_getElem? h)

/-- **A call on strongly normalizing arguments is strongly normalizing**, under lexicographic descent. -/
theorem sn_call_lex {P : Program S} (headed : P.Headed) (bound : P.RightBound) {c : LexCertificate S}
    (descends : P.LexDescends c) :
    ∀ (f : S) (args : List (Tm S)), (∀ a ∈ args, SN P a) → SN P (.app f args) := by
  let R : Tm S → Tm S → Prop := fun a b => TransGen (Below P) a b
  let D : Tm S → Prop := fun a => SN P a
  have accD : ∀ a, D a → Acc R a := fun a h => accessible_transitiveClosure (acc_below h)
  have keysAcc : ∀ (g : S) (args : List (Tm S)), (∀ a ∈ args, SN P a) →
      Acc (LexLtIn R D) (lexKeys (c.positions g) args) := fun g args sn =>
    acc_lexLt accD _ _ rfl (by
      intro k hk
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
      exact keyAt_sn headed sn i)
  suffices ∀ n (ks : List (Tm S)), Acc (LexLtIn R D) ks → ∀ (f : S), c.rank f = n →
      ∀ args : List (Tm S), (∀ a ∈ args, SN P a) → lexKeys (c.positions f) args = ks →
        SN P (.app f args) from fun f args sn => this _ _ (keysAcc f args sn) f rfl args sn rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihRank =>
  intro ks acc
  induction acc with
  | intro ks _ ihKeys =>
  intro f hr args sn hk
  by_cases defined : P.Defines f
  swap
  · exact sn_constructor headed defined args sn
  have argsAcc := acc_listStep args sn
  induction argsAcc with
  | intro args _ ihArgs =>
  constructor
  intro target step
  cases step with
  | root root =>
      obtain ⟨e, he, σ, hs, rfl⟩ := root.exists_rule
      obtain ⟨f', ps, hlhs, every⟩ := descends e he
      rw [hlhs, subst_app] at hs
      obtain ⟨hf, hargs⟩ := Tm.app.inj hs
      subst hf
      subst hargs
      apply sn_instance σ _ every
      · intro x hx
        have hx' := bound e he x hx
        rw [hlhs, vars_app, List.mem_flatMap] at hx'
        obtain ⟨p, pMember, xMember⟩ := hx'
        exact SN.of_subStar (sn _ (List.mem_map_of_mem pMember)) (subStar_subst_var σ p xMember)
      · intro g us descent argsSN
        rcases descent with undefined | lower | ⟨sameRank, lexd⟩
        · exact sn_constructor headed undefined _ argsSN
        · exact ihRank (c.rank g) (hr ▸ lower) _ (keysAcc g _ argsSN) g rfl _ argsSN rfl
        · refine ihKeys (lexKeys (c.positions g) (us.map (subst σ))) ⟨?_, ?_⟩ g (sameRank.trans hr)
            (us.map (subst σ)) argsSN rfl
          · rw [← hk]; exact LexDesc.instantiate σ lexd
          · intro k hkm
            obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkm
            exact keyAt_sn headed argsSN j
  | @arg _ _ i lt b stepAt =>
      have listStep : ListStep P args (args.set i b) := ⟨i, lt, b, stepAt, rfl⟩
      obtain ⟨inL, notInL⟩ := keys_set args i lt stepAt (c.positions f)
      by_cases hi : i ∈ c.positions f
      · refine ihKeys (lexKeys (c.positions f) (args.set i b)) ⟨?_, ?_⟩ f hr (args.set i b)
          (listStep.sn sn) rfl
        · rw [← hk]; exact inL hi
        · intro k hkm
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkm
          exact keyAt_sn headed (listStep.sn sn) j
      · exact ihArgs _ listStep (listStep.sn sn) (by rw [notInL hi]; exact hk)

/-- **Strong normalization under lexicographic descent.** -/
theorem Program.LexDescends.stronglyNormalizing {P : Program S} {c : LexCertificate S}
    (descends : P.LexDescends c) (headed : P.Headed) (bound : P.RightBound) : ∀ t, SN P t := by
  intro t
  induction t using Tm.induction' with
  | var name => exact Acc.intro _ fun target step => absurd step (var_normal headed name target)
  | app head args ih => exact sn_call_lex headed bound descends head args ih

/-- **Structural descent is lexicographic descent along one position.** -/
theorem Program.Descends.lexDescends {P : Program S} {c : Certificate S} (descends : P.Descends c) :
    P.LexDescends ⟨c.rank, fun f => [c.position f]⟩ := by
  intro e he
  obtain ⟨f, ps, hl, every⟩ := descends e he
  refine ⟨f, ps, hl, ?_⟩
  clear hl
  generalize e.rhs = r at every ⊢
  induction every with
  | var x => exact .var x
  | app holds _ ih =>
      refine .app ?_ ih
      rcases holds with undefined | lower | ⟨rfl, hu, hp, part⟩
      · exact .inl undefined
      · exact .inr (.inl lower)
      · refine .inr (.inr ⟨rfl, LexDesc.here hp hu rfl ?_⟩)
        simpa [keyAt, hu, hp] using part

end Mettapedia.Languages.MeTTa.DeclarationFaces
