import Mettapedia.Protocols.Nostr.Archive
import Mettapedia.Protocols.Injection.Terminal

/-!
# Standing by key: names decide nothing

A team's rules say what a member's typed mail may do: a parent's `reset` runs.
`team.json` names the members, and `registry.json` gives each name its key. The
client once took the sender to be the first word of `From:`, the name the registry
gives the signing key, shown as text. An entry's name is whatever its author wrote,
so another entry could pass for a member. The client now takes a message's
standing from its signing key: a member's key is the one the registry gives the
name the team uses for it. Names stay as the registry has them.

The theorems:
- `spaced_name_reads_as_another`: by the first word of `From:`, mail from the key of
  an entry named `lead x` reads as from `lead`.
- `printable_merges_names`: a name shown cleaned is no identity: `lead` and a bell
  is shown `lead`.
- `control_from_parent`: control mail the client takes for the parent's is signed
  by the key the registry gives the parent's name, and, if that key is
  uncompromised, was composed by the parent. Nothing is assumed about names.
- `roleOfKey_other_entry`: an entry under a name the team does not use changes no
  one's standing, whatever its key.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.Names

open Mettapedia.Protocols.Nostr Mettapedia.Protocols.Nostr.Archive

/-! ## By name -/

/-- An entry named `lead x`: the watcher, reading the first word of `From:`, reads its
key's mail as from `lead`. -/
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

/-! ## By key -/

/-- A team as `team.json` gives it: its members' names. -/
structure Team where
  parent : Option String
  children : List String
  review : List String

/-- What a signer is to the avatar. -/
inductive Role where
  | parent
  | child
  | peer
  | none
  deriving DecidableEq, Repr

/-- The key the registry gives a name, as a lookup in a JSON object finds it. -/
def keyOf (reg : Registry) (n : String) : Option PubKey := (reg.find? (·.1 = n)).map (·.2)

/-- The client's `role_of_key`: the signer's standing, from its key alone. -/
def roleOfKey (reg : Registry) (team : Team) (k : PubKey) : Role :=
  if team.parent.bind (keyOf reg) = some k then .parent
  else if team.children.any (fun n => keyOf reg n == some k) then .child
  else if team.review.any (fun n => keyOf reg n == some k) then .peer
  else .none

theorem roleOfKey_parent {reg : Registry} {team : Team} {k : PubKey}
    (h : roleOfKey reg team k = .parent) : team.parent.bind (keyOf reg) = some k := by
  unfold roleOfKey at h
  by_contra hp
  rw [if_neg hp] at h
  split at h
  · cases h
  · split at h <;> cases h

/-- **Control mail taken for the parent's is the parent's.** A message the client
takes for the parent's is signed by the key the registry gives the parent's name;
if that key is uncompromised, the parent composed it. Nothing is assumed about the
registry's names. -/
theorem control_from_parent {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    {reg : Registry} {team : Team} {parent : String} (hp : team.parent = some parent)
    {e : Event} (hv : e.Valid P) (hrole : roleOfKey reg team e.pubkey = .parent)
    (hc : ∀ k, keyOf reg parent = some k → ¬ A.compromised k) :
    keyOf reg parent = some e.pubkey ∧ A.authored e.toUnsigned := by
  have hk : keyOf reg parent = some e.pubkey := by
    simpa [hp] using roleOfKey_parent hrole
  exact ⟨hk, authentic A cf hv (hc _ hk)⟩

/-- The names a team uses. -/
def Team.names (team : Team) : List String := team.parent.toList ++ team.children ++ team.review

theorem keyOf_cons_other {reg : Registry} {n m : String} {k : PubKey} (h : n ≠ m) :
    keyOf ((n, k) :: reg) m = keyOf reg m := by
  simp [keyOf, h]

theorem any_keyOf_cons {reg : Registry} {n : String} {k k' : PubKey} {l : List String}
    (hl : n ∉ l) :
    l.any (fun m => keyOf ((n, k) :: reg) m == some k') = l.any (fun m => keyOf reg m == some k') := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    have hm : n ≠ m := fun h => hl (by simp [h])
    have hl' : n ∉ l := fun h => hl (by simp [h])
    simp only [List.any_cons, keyOf_cons_other hm, ih hl']

/-- **Names decide nothing.** An entry under a name the team does not use changes no
one's standing, whatever key it carries: an entry named `lead x` beside the lead's
changes nothing. -/
theorem roleOfKey_other_entry (reg : Registry) (team : Team) {n : String} (k k' : PubKey)
    (hn : n ∉ team.names) :
    roleOfKey ((n, k) :: reg) team k' = roleOfKey reg team k' := by
  have hpar : team.parent.bind (keyOf ((n, k) :: reg)) = team.parent.bind (keyOf reg) := by
    cases hp : team.parent with
    | none => rfl
    | some p =>
      have : n ≠ p := fun h => hn (by simp [Team.names, hp, h])
      simp [keyOf_cons_other this]
  have hkids := any_keyOf_cons (reg := reg) (n := n) (k := k) (k' := k') (l := team.children)
    (fun h => hn (by simp [Team.names, h]))
  have hrev := any_keyOf_cons (reg := reg) (n := n) (k := k) (k' := k') (l := team.review)
    (fun h => hn (by simp [Team.names, h]))
  simp only [roleOfKey, hpar, hkids, hrev]

end Mettapedia.Protocols.Nostr.Names
