import Mettapedia.Protocols.Nostr.Archive
import Mettapedia.Protocols.Injection.Terminal

/-!
# The registry names the client accepts

The watcher takes the first word of `From:` as the sender, and a team's rules say
what that sender's typed mail may do: a parent's `reset` runs. `From:` carries the
name the registry gives the signing key. `watcher_control_sound` holds when every
name is clean (one word) and each name is given once; a JSON object gives the
second, but nothing gave the first.

The client now names a key only when the key has exactly one entry and that
entry's name is plain: letters, digits, `.`, `_` and `-`, starting with a letter or
a digit. It refuses mail from any other key. `checked` is the registry it then
reads by.

The theorems:
- `spaced_name_reads_as_another`: without the check, mail from the key of an entry
  named `lead x` is read by the watcher as from `lead`.
- `printable_merges_names`: removing control characters makes `lead` and a bell
  into `lead`, so a name cleaned for display is no identity.
- `nameOf_checked`: the checked registry names a key exactly as the client does.
- `checked_clean`, `checked_nodup`: its names are clean, and given once if the
  registry's are.
- `watcher_control_sound_checked`: control mail the watcher reads as from the
  parent was composed by the parent, on any registry that gives each name once.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.Names

open Mettapedia.Protocols.Nostr Mettapedia.Protocols.Nostr.Archive

/-- A character a plain name may hold. -/
def plainChar (c : Char) : Bool := c.isAlphanum || c == '.' || c == '_' || c == '-'

/-- A plain name: a letter or digit, then plain characters. -/
def plainName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => c.isAlphanum && cs.all plainChar

/-- The entries the client reads by: a plain name, and the only entry with its key. -/
def checked (reg : Registry) : Registry :=
  reg.filter fun m => plainName m.1 && reg.countP (·.2 == m.2) == 1

/-! ## Without the check -/

/-- An entry named `lead x`: the watcher reads its key's mail as from `lead`. -/
theorem spaced_name_reads_as_another {reg : Registry} {e : Event} {l : Letter}
    (hn : nameOf reg e.pubkey = some "lead x") :
    watcherFrom (archive reg e l) = some "lead".toList := by
  have horig : (render reg e l).originator = "lead x" := by simp [render, hn]
  apply watcherFrom_archive_word (tail := 'x' :: ' ' :: address e.pubkey)
  · rw [horig]; decide
  · rw [horig]; rfl
  · decide
  · decide

/-- Cleaning a name for display merges names: `lead` and a bell is shown `lead`. -/
theorem printable_merges_names :
    Injection.Terminal.printable ['l', 'e', 'a', 'd', Injection.Terminal.bel] = "lead".toList := by
  decide

/-! ## The check -/

theorem plainChar_word {c : Char} (h : plainChar c = true) : ¬ c.isWhitespace ∧ c ≠ ':' := by
  constructor
  · intro hw
    have : ((c = ' ' ∨ c = '\t') ∨ c = '\r') ∨ c = '\n' := by simpa [Char.isWhitespace] using hw
    rcases this with ((rfl | rfl) | rfl) | rfl <;> exact absurd h (by decide)
  · rintro rfl
    exact absurd h (by decide)

theorem plainName_clean {s : String} (h : plainName s = true) : CleanName s := by
  unfold plainName at h
  unfold CleanName
  cases hs : s.toList with
  | nil => simp [hs] at h
  | cons c cs =>
    rw [hs] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨by simp, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact plainChar_word (by simp [plainChar, h.1])
    · exact plainChar_word (h.2 x hx)

theorem checked_sublist (reg : Registry) : (checked reg).Sublist reg := List.filter_sublist

/-- Every name the checked registry gives is clean. -/
theorem checked_clean (reg : Registry) : ∀ m ∈ checked reg, CleanName m.1 := by
  intro m hm
  have := (List.mem_filter.mp hm).2
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact plainName_clean this.1

/-- It gives each name once if the registry does. -/
theorem checked_nodup {reg : Registry} (hu : (reg.map Prod.fst).Nodup) :
    ((checked reg).map Prod.fst).Nodup :=
  hu.sublist ((checked_sublist reg).map _)

/-- Two entries with the same key, in a registry where one entry has it, are one. -/
theorem eq_of_countP_one {reg : Registry} {k : PubKey} (h : reg.countP (·.2 == k) = 1)
    {a b : String × PubKey} (ha : a ∈ reg) (hak : a.2 = k) (hb : b ∈ reg) (hbk : b.2 = k) :
    a = b := by
  rw [List.countP_eq_length_filter] at h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h
  have ha' : a ∈ reg.filter (·.2 == k) := List.mem_filter.mpr ⟨ha, by simp [hak]⟩
  have hb' : b ∈ reg.filter (·.2 == k) := List.mem_filter.mpr ⟨hb, by simp [hbk]⟩
  rw [hx, List.mem_singleton] at ha' hb'
  rw [ha', hb']

/-- **The checked registry names a key as the client does**: by the one entry with
that key, when its name is plain. -/
theorem nameOf_checked (reg : Registry) (k : PubKey) (n : String) :
    nameOf (checked reg) k = some n ↔
      (n, k) ∈ reg ∧ plainName n = true ∧ reg.countP (·.2 == k) = 1 := by
  constructor
  · intro h
    have hm := nameOf_some h
    have hf := List.mem_filter.mp hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    exact ⟨hf.1, hf.2.1, hf.2.2⟩
  · rintro ⟨hm, hp, hc⟩
    have hmc : (n, k) ∈ checked reg := List.mem_filter.mpr ⟨hm, by simp [hp, hc]⟩
    unfold nameOf
    cases hf : (checked reg).find? (·.2 = k) with
    | none =>
      have := List.find?_eq_none.mp hf _ hmc
      simp at this
    | some p =>
      have hpk : p.2 = k := by simpa using List.find?_some hf
      have hp : p ∈ reg := (checked_sublist reg).subset (List.mem_of_find?_eq_some hf)
      have : p = (n, k) := eq_of_countP_one hc hp hpk hm rfl
      simp [this]

/-- **Control mail from the parent is the parent's**, on any registry that gives
each name once: the client reads by the checked registry, whose names are clean, so
`watcher_control_sound` needs no assumption about names. -/
theorem watcher_control_sound_checked {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    {opener : Opener} {reg : Registry} (hu : (reg.map Prod.fst).Nodup) {me : PubKey}
    {e : Event} {l : Letter} (ha : accept P opener (checked reg) me e = some l)
    {parent : String} {k : PubKey} (hk : (parent, k) ∈ reg) (hc : ¬ A.compromised k) {t : Text}
    (hfrom : watcherFrom (archive (checked reg) e l) = some parent.toList)
    (htype : watcherType (archive (checked reg) e l) = some t) :
    A.authored e.toUnsigned ∧
      ∃ s, l.type = some s ∧ t = (oneLine s.toList).dropWhile Char.isWhitespace := by
  obtain ⟨-, -, -, n, hn⟩ := accept_some ha
  have hmem : (n, e.pubkey) ∈ checked reg := nameOf_some hn
  have horig : (render (checked reg) e l).originator = n := by simp [render, hn]
  have ho : CleanName (render (checked reg) e l).originator := horig ▸ checked_clean reg _ hmem
  have hnp : n = parent := by
    rw [watcherFrom_archive ho, horig] at hfrom
    exact String.toList_inj.mp (Option.some.inj hfrom)
  subst hnp
  have hkk : e.pubkey = k := key_unique hu ((checked_sublist reg).subset hmem) hk
  exact watcher_control_sound A cf (checked_nodup hu) (checked_clean reg) ha (hkk ▸ hmem) hc
    hfrom htype

end Mettapedia.Protocols.Nostr.Names
