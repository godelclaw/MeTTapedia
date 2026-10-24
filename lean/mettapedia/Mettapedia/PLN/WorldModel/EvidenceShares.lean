import Mettapedia.GSLT.Causality.ResourceInteraction
import Mettapedia.PLN.WorldModel.EvidenceContracts

/-!
# Evidence as conserved shares: linear and fractional use prevent double counting

Revision adds evidence counts, and it is exact exactly when the two pieces of
evidence share no observation
(`Mettapedia.PLN.WorldModel.EvidenceContracts.additive_revision_exact_iff_disjoint`).
Double counting enters when one observation is credited to two conclusions that
are later revised together.  This module reads evidence as a **resource**: every
observation is issued a fixed supply of shares, a token of evidence holds some
shares (`Token`), and inference rules are resource interactions over a bag of
tokens (`Mettapedia.GSLT.Causality.ResourceInteraction.System`).

* **Conservation** (`content_reachable`): if every rule produces exactly the
  shares it consumes (`Conservative`), the shares held by the whole bag never
  change along any run.
* **Nobody holds more than the supply** (`shares_le_supply`,
  `pair_shares_le_supply`): every token, and every pair of tokens present
  together, holds at most the supply.
* **Linear evidence** (one share per observation): two tokens present together
  share no observation, so their additive revision is exact
  (`revision_exact_of_linear`).  No run of a conservative system can double count.
* **Fractional evidence** (several shares per observation): splitting a token
  between two uses (`Move.split`) conserves shares, and the credit of an
  observation in any token is bounded by its supply (`count_le_supply`): use is
  diluted, never multiplied.
* **Copying is what double counts** (`Controls.copying_double_counts`): a rule
  that reads its premise and gives the conclusion the premise's shares is not
  conservative (`Controls.deriveReading_not_conservative`); two such derivations
  from one premise reach a bag whose two conclusions overlap, and revising them
  counts the shared observation twice.

Linear and fractional use are two resource policies; tracking observation
identity and subtracting the overlap at revision is the third
(`Mettapedia.PLN.WorldModel.EvidenceContracts.ledgerOverlapModel`).  A shared
lazily computed value is the natural owner of the shares of what it computed:
its consumers either split them or carry the identity of the shared value.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.EvidenceShares

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.WorldModel.EvidenceSpaces

universe u v w

/-- A token of evidence: a claim and the observation shares credited to it. -/
structure Token (Claim : Type u) (Obs : Type v) where
  claim : Claim
  shares : Multiset Obs

instance {Claim : Type u} {Obs : Type v} [DecidableEq Claim] [DecidableEq Obs] :
    DecidableEq (Token Claim Obs) := fun first second =>
  if claim : first.claim = second.claim then
    if shares : first.shares = second.shares then
      isTrue (by cases first; cases second; simp_all)
    else isFalse fun same => shares (by rw [same])
  else isFalse fun same => claim (by rw [same])

variable {Claim : Type u} {Obs : Type v}

/-! ## The shares a bag holds -/

/-- The shares held by a bag of tokens. -/
def content (bag : Multiset (Token Claim Obs)) : Multiset Obs := (bag.map Token.shares).sum

@[simp] theorem content_zero : content (0 : Multiset (Token Claim Obs)) = 0 := by
  simp [content]

theorem content_add (first second : Multiset (Token Claim Obs)) :
    content (first + second) = content first + content second := by
  simp [content]

@[simp] theorem content_singleton (token : Token Claim Obs) : content {token} = token.shares := by
  simp [content]

theorem content_pair (first second : Token Claim Obs) :
    content {first, second} = first.shares + second.shares := by
  simp [content]

theorem content_mono {first second : Multiset (Token Claim Obs)} (le : first ≤ second) :
    content first ≤ content second := by
  obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp le
  rw [content_add]
  exact Multiset.le_add_right _ _

theorem shares_le_content {token : Token Claim Obs} {bag : Multiset (Token Claim Obs)}
    (member : token ∈ bag) : token.shares ≤ content bag := by
  have bound := content_mono (Multiset.singleton_le.mpr member)
  rwa [content_singleton] at bound

/-- A system conserves shares: every instance produces exactly the shares it
consumes. -/
def Conservative (S : System (Token Claim Obs)) : Prop :=
  ∀ {site : S.Site} (instance_ : S.Instance site), content (S.consume instance_) = content (S.produce instance_)

variable [DecidableEq Claim] [DecidableEq Obs]

/-- **A conservative firing keeps the shares of the bag.** -/
theorem content_fire {S : System (Token Claim Obs)} (conservative : Conservative S)
    {bag : Multiset (Token Claim Obs)} {site : S.Site} {instance_ : S.Instance site}
    (enabled : S.Enables bag instance_) : content (S.fire bag instance_) = content bag := by
  have consumed : S.consume instance_ ≤ bag := le_trans (Multiset.le_add_right _ _) enabled
  unfold System.fire
  rw [content_add, ← conservative instance_, ← content_add, Multiset.sub_add_cancel consumed]

/-- **Conservation along every run.** -/
theorem content_reachable {S : System (Token Claim Obs)} (conservative : Conservative S)
    {start finish : Multiset (Token Claim Obs)}
    (reach : Relation.ReflTransGen S.theory.rewrites start finish) : content finish = content start := by
  induction reach with
  | refl => rfl
  | tail _ step ih =>
      obtain ⟨site, instance_, enabled, rfl⟩ := step
      rw [content_fire conservative enabled, ih]

/-- **No reachable token holds more than the supply.** -/
theorem shares_le_supply {S : System (Token Claim Obs)} (conservative : Conservative S)
    {supply : Multiset Obs} {start finish : Multiset (Token Claim Obs)} (issued : content start ≤ supply)
    (reach : Relation.ReflTransGen S.theory.rewrites start finish) {token : Token Claim Obs}
    (member : token ∈ finish) : token.shares ≤ supply :=
  (shares_le_content member).trans ((content_reachable conservative reach).symm ▸ issued)

/-- The credit of an observation in any reachable token is bounded by its supply. -/
theorem count_le_supply {S : System (Token Claim Obs)} (conservative : Conservative S)
    {supply : Multiset Obs} {start finish : Multiset (Token Claim Obs)} (issued : content start ≤ supply)
    (reach : Relation.ReflTransGen S.theory.rewrites start finish) {token : Token Claim Obs}
    (member : token ∈ finish) (observation : Obs) :
    token.shares.count observation ≤ supply.count observation :=
  Multiset.count_le_of_le observation (shares_le_supply conservative issued reach member)

/-- **Two tokens present together hold at most the supply between them.** -/
theorem pair_shares_le_supply {S : System (Token Claim Obs)} (conservative : Conservative S)
    {supply : Multiset Obs} {start finish : Multiset (Token Claim Obs)} (issued : content start ≤ supply)
    (reach : Relation.ReflTransGen S.theory.rewrites start finish) {first second : Token Claim Obs}
    (both : ({first, second} : Multiset (Token Claim Obs)) ≤ finish) :
    first.shares + second.shares ≤ supply := by
  rw [← content_pair]
  exact (content_mono both).trans ((content_reachable conservative reach).symm ▸ issued)

/-! ## Linear evidence -/

/-- **Linear evidence cannot be double counted**: with one share per observation,
two tokens present together after any run have disjoint ledgers, and revising
them adds their evidence exactly. -/
theorem revision_exact_of_linear {W : Type w} {S : System (Token Claim Obs)}
    (conservative : Conservative S) {start finish : Multiset (Token Claim Obs)}
    (linear : (content start).Nodup) (reach : Relation.ReflTransGen S.theory.rewrites start finish)
    {first second : Token Claim Obs}
    (both : ({first, second} : Multiset (Token Claim Obs)) ≤ finish)
    (world : Obs → W) (φ : W → Bool) :
    ledgerEvidence world φ first.shares.toFinset + ledgerEvidence world φ second.shares.toFinset =
      ledgerEvidence world φ (first.shares.toFinset ∪ second.shares.toFinset) := by
  have bound := pair_shares_le_supply conservative le_rfl reach both
  have nodup : (first.shares + second.shares).Nodup := Multiset.nodup_of_le bound linear
  rw [additive_revision_exact_iff_disjoint]
  rw [Finset.disjoint_iff_ne]
  intro a inFirst b inSecond same
  subst same
  rw [Multiset.mem_toFinset] at inFirst inSecond
  have twice : 1 < (first.shares + second.shares).count a := by
    rw [Multiset.count_add]
    have := Multiset.count_pos.mpr inFirst
    have := Multiset.count_pos.mpr inSecond
    omega
  have once := (Multiset.nodup_iff_count_le_one.mp nodup) a
  omega

/-! ## Moves of evidence -/

/-- The moves of an evidence calculus that conserve shares. -/
inductive Move (Claim : Type u) (Obs : Type v) where
  /-- Revise two tokens into one, crediting it with both. -/
  | revise (first second : Token Claim Obs)
  /-- Split a token between two uses, possibly for different claims. -/
  | split (whole left right : Token Claim Obs) (partition : left.shares + right.shares = whole.shares)

/-- The calculus of revision and splitting. -/
def sharing : System.{max u v, max u v} (Token Claim Obs) where
  Site := PUnit
  Instance _ := Move Claim Obs
  consume
    | .revise first second => {first, second}
    | .split whole _ _ _ => {whole}
  read _ := 0
  produce
    | .revise first second => {⟨first.claim, first.shares + second.shares⟩}
    | .split _ left right _ => {left, right}

omit [DecidableEq Claim] [DecidableEq Obs] in
/-- **Revision and splitting conserve shares.** -/
theorem sharing_conservative : Conservative (sharing (Claim := Claim) (Obs := Obs)) := by
  intro _ move
  cases move with
  | revise first second =>
      change content {first, second} = content {⟨first.claim, first.shares + second.shares⟩}
      rw [content_pair, content_singleton]
  | split whole left right partition =>
      change content {whole} = content {left, right}
      rw [content_singleton, content_pair, partition]

/-! ## Controls -/

namespace Controls

/-- Tokens over observation identifiers. -/
abbrev Tok := Token ℕ ℕ

/-- Derive a conclusion by reading a premise and copying its shares. -/
abbrev copying : System Tok where
  Site := Unit
  Instance _ := Tok × ℕ
  consume _ := 0
  read derivation := {derivation.1}
  produce derivation := {⟨derivation.2, derivation.1.shares⟩}

/-- **Copying is not conservative.** -/
theorem deriveReading_not_conservative : ¬ Conservative copying := by
  intro conservative
  have := @conservative () (⟨0, {0}⟩, 1)
  simp at this

/-- The premise: claim `0`, credited with observation `0`. -/
def premise : Tok := ⟨0, {0}⟩

/-- A conclusion of claim `1` derived from the premise. -/
def conclusion : Tok := ⟨1, {0}⟩

/-- Deriving twice from the premise reaches a bag with two conclusions. -/
theorem derive_twice :
    Relation.ReflTransGen copying.theory.rewrites ({premise} : Multiset Tok)
      ({conclusion, conclusion, premise} : Multiset Tok) := by
  have first : copying.theory.rewrites ({premise} : Multiset Tok)
      ({conclusion, premise} : Multiset Tok) :=
    ⟨(), (premise, 1), by unfold System.Enables; decide, by decide⟩
  have second : copying.theory.rewrites ({conclusion, premise} : Multiset Tok)
      ({conclusion, conclusion, premise} : Multiset Tok) :=
    ⟨(), (premise, 1), by unfold System.Enables; decide, by decide⟩
  exact (Relation.ReflTransGen.single first).tail second

/-- **Copying double counts**: the two conclusions present together overlap, so
revising them adds the shared observation twice. -/
theorem copying_double_counts (world : ℕ → Bool) :
    ledgerEvidence world id conclusion.shares.toFinset +
        ledgerEvidence world id conclusion.shares.toFinset ≠
      ledgerEvidence world id (conclusion.shares.toFinset ∪ conclusion.shares.toFinset) := by
  rw [Ne, additive_revision_exact_iff_disjoint]
  simp [conclusion]

/-- The calculus of revision and splitting over these tokens. -/
abbrev natSharing : System.{0, 0} Tok := sharing

/-- **A linear token is revised once**: the bag holding one token cannot revise
it with itself. -/
theorem linear_revision_consumes :
    ¬ natSharing.Enables ({⟨0, {0}⟩} : Multiset Tok)
      (site := PUnit.unit) (Move.revise ⟨0, {0}⟩ ⟨0, {0}⟩) := by
  unfold System.Enables
  decide

/-- Splitting a two-share token between two conclusions credits each with one
share; revising them back gives the whole token's credit and no more. -/
theorem split_then_revise :
    Relation.ReflTransGen natSharing.theory.rewrites ({⟨0, {7, 7}⟩} : Multiset Tok)
      ({⟨1, {7, 7}⟩} : Multiset Tok) := by
  have first : natSharing.theory.rewrites ({⟨0, {7, 7}⟩} : Multiset Tok)
      ({⟨1, {7}⟩, ⟨1, {7}⟩} : Multiset Tok) :=
    ⟨PUnit.unit, Move.split ⟨0, {7, 7}⟩ ⟨1, {7}⟩ ⟨1, {7}⟩ rfl,
      by unfold System.Enables; decide, by decide⟩
  have second : natSharing.theory.rewrites ({⟨1, {7}⟩, ⟨1, {7}⟩} : Multiset Tok)
      ({⟨1, {7, 7}⟩} : Multiset Tok) :=
    ⟨PUnit.unit, Move.revise ⟨1, {7}⟩ ⟨1, {7}⟩, by unfold System.Enables; decide, by decide⟩
  exact (Relation.ReflTransGen.single first).tail second

/-- The credit of observation `7` in any token reached from a two-share supply is
at most two shares. -/
theorem split_credit_bounded {finish : Multiset Tok}
    (reach : Relation.ReflTransGen natSharing.theory.rewrites ({⟨0, {7, 7}⟩} : Multiset Tok) finish)
    {token : Tok} (member : token ∈ finish) : token.shares.count 7 ≤ 2 := by
  have bound := count_le_supply sharing_conservative (supply := {7, 7}) (by simp [content]) reach
    member 7
  simpa using bound

end Controls

end Mettapedia.PLN.WorldModel.EvidenceShares
