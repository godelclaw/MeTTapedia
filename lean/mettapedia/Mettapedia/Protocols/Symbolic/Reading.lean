import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Basic
import Mettapedia.Protocols.Symbolic.Message

/-!
# Reading strings as symbolic messages

Protocol models written over concrete data, such as Nostr events whose keys, identifiers,
signatures and contents are strings, meet the symbolic message algebra through a *reading*: a
bijection between strings and messages. Every string denotes one message and every message is
written by one string, so a string-level model can be interpreted symbolically and a symbolic
execution can be written out as strings. A protocol constrains its reading only where it writes
literal strings of its own (tag names, fixed values): those must denote public literals.

Readings exist. Messages over countably many names are countable (`Msg.code` is an injective
prefix code) and there are infinitely many of them (`Msg.pk` iterated), strings are countable
and infinite, so strings and messages are in bijection; any bijection can be adjusted to give
finitely many chosen strings chosen distinct meanings (`exists_equiv_extend`). Hence
`exists_reading`.

The reading is a modelling choice, not a parser: it fixes once and for all which symbolic message
each string stands for. Nothing about real encodings (hexadecimal keys, base64 ciphertexts) is
modelled.
-/

namespace Mettapedia.Protocols.Symbolic

namespace Msg

variable {N : Type}

/-- The prefix code of a message: a constructor tag followed by the codes of its arguments. -/
def code : Msg N → List (ℕ ⊕ (N ⊕ Sym2 N))
  | name n => [.inr (.inl n)]
  | pk x => .inl 0 :: code x
  | pair x y => .inl 1 :: (code x ++ code y)
  | hash x => .inl 2 :: code x
  | senc k m => .inl 3 :: (code k ++ code m)
  | sign k m => .inl 4 :: (code k ++ code m)
  | shared s => [.inr (.inr s)]
  | fail => [.inl 5]

/-- A prefix code determines the message and the rest of the list. -/
theorem code_append_inj :
    ∀ (x y : Msg N) (l l' : List (ℕ ⊕ (N ⊕ Sym2 N))), code x ++ l = code y ++ l' →
      x = y ∧ l = l' := by
  intro x
  induction x with
  | name n =>
      intro y l l' h
      cases y with
      | name m =>
          simp only [code, List.cons_append, List.nil_append, List.cons.injEq, Sum.inr.injEq,
            Sum.inl.injEq] at h
          exact ⟨by rw [h.1], h.2⟩
      | _ => simp [code] at h
  | pk x ih =>
      intro y l l' h
      cases y with
      | pk y =>
          simp only [code, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨rfl, rfl⟩ := ih y l l' h
          exact ⟨rfl, rfl⟩
      | _ => simp [code] at h
  | pair x₁ x₂ ih₁ ih₂ =>
      intro y l l' h
      cases y with
      | pair y₁ y₂ =>
          simp only [code, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
          obtain ⟨rfl, h'⟩ := ih₁ y₁ _ _ h
          obtain ⟨rfl, rfl⟩ := ih₂ y₂ l l' h'
          exact ⟨rfl, rfl⟩
      | _ => simp [code] at h
  | hash x ih =>
      intro y l l' h
      cases y with
      | hash y =>
          simp only [code, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨rfl, rfl⟩ := ih y l l' h
          exact ⟨rfl, rfl⟩
      | _ => simp [code] at h
  | senc k m ihk ihm =>
      intro y l l' h
      cases y with
      | senc k' m' =>
          simp only [code, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
          obtain ⟨rfl, h'⟩ := ihk k' _ _ h
          obtain ⟨rfl, rfl⟩ := ihm m' l l' h'
          exact ⟨rfl, rfl⟩
      | _ => simp [code] at h
  | sign k m ihk ihm =>
      intro y l l' h
      cases y with
      | sign k' m' =>
          simp only [code, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
          obtain ⟨rfl, h'⟩ := ihk k' _ _ h
          obtain ⟨rfl, rfl⟩ := ihm m' l l' h'
          exact ⟨rfl, rfl⟩
      | _ => simp [code] at h
  | shared s =>
      intro y l l' h
      cases y with
      | shared s' =>
          simp only [code, List.cons_append, List.nil_append, List.cons.injEq, Sum.inr.injEq] at h
          exact ⟨by rw [h.1], h.2⟩
      | _ => simp [code] at h
  | fail =>
      intro y l l' h
      cases y with
      | fail =>
          simp only [code, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
          exact ⟨rfl, h⟩
      | _ => simp [code] at h

theorem code_injective : Function.Injective (code (N := N)) := fun x y h =>
  (code_append_inj x y [] [] (by simpa using h)).1

instance [Countable N] : Countable (Msg N) := code_injective.countable

/-- Iterated public keys of the failure value: infinitely many distinct messages. -/
def pkIter : ℕ → Msg N
  | 0 => fail
  | n + 1 => pk (pkIter n)

theorem pkIter_injective : Function.Injective (pkIter (N := N)) := by
  intro m n h
  induction m generalizing n with
  | zero => cases n <;> simp_all [pkIter]
  | succ m ih =>
      cases n with
      | zero => simp [pkIter] at h
      | succ n =>
          simp only [pkIter, pk.injEq] at h
          exact congrArg (· + 1) (ih h)

instance : Infinite (Msg N) := Infinite.of_injective _ pkIter_injective

end Msg

/-- A bijection can be adjusted to agree with any assignment that is injective on a finite list
of distinct points. -/
theorem exists_equiv_extend {α β : Type} [DecidableEq β] (e : α ≃ β) (f : α → β) :
    ∀ (L : List α), L.Nodup → (∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) →
      ∃ e' : α ≃ β, ∀ a ∈ L, e' a = f a := by
  intro L
  induction L with
  | nil => exact fun _ _ => ⟨e, by simp⟩
  | cons a L ih =>
      intro hnd hf
      obtain ⟨ha, hnd⟩ := List.nodup_cons.mp hnd
      obtain ⟨e₁, he₁⟩ := ih hnd (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy]))
      refine ⟨e₁.trans (Equiv.swap (e₁ a) (f a)), ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · have hxa : x ≠ a := fun h => ha (h ▸ hx)
        have h₁ : f x ≠ f a := fun h => hxa (hf x (by simp [hx]) a (by simp) h)
        have h₂ : f x ≠ e₁ a := by
          rw [← he₁ x hx]
          exact fun h => hxa (e₁.injective h)
        simp only [Equiv.trans_apply, he₁ x hx]
        exact Equiv.swap_apply_of_ne_of_ne h₂ h₁

/-- Strings are countable. -/
theorem countable_string : Countable String := by
  have hinj : Function.Injective fun s : String => s.toList.map Char.toNat := fun a b hab =>
    String.toList_injective (List.map_injective_iff.mpr (fun _ _ h => Char.toNat_inj.mp h) hab)
  exact hinj.countable

/-- Readings exist: for countably many names, strings and messages are in bijection, and the
bijection can give finitely many chosen strings chosen distinct meanings. -/
theorem exists_reading {N : Type} [Countable N] [DecidableEq N] (L : List String) (hL : L.Nodup)
    (f : String → Msg N) (hf : ∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) :
    ∃ R : String ≃ Msg N, ∀ s ∈ L, R s = f s := by
  have := countable_string
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := String) (β := Msg N)
  exact exists_equiv_extend e f L hL hf

end Mettapedia.Protocols.Symbolic
