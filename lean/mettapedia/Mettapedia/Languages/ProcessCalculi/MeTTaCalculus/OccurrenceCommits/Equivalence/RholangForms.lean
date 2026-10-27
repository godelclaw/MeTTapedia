import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.AgentLaws

/-!
# Rholang's receive forms are exact definitions over `transform`

Rholang has three kinds of receipt and a choice among receives:

* linear `for (p₁ <- c₁ & … & pₙ <- cₙ) P`: consumes the receiver and one message on each channel;
* repeated `for (p₁ <= c₁ & …) P` (and `contract`): consumes the messages and stays;
* peek `for (p₁ <<- c₁ & …) P`: consumes the receiver and leaves the messages;
* `select { p₁ <- a & q₁ <- b => P ; r <- c => Q }`: consumes the select and, for one arm, one
  message on each channel of the arm's linear join.

Their reduction rules are given here as Rholang states them (`RhoRule`), over messages and receivers.
The language defines them over `transform` (`encode`):

* linear: `await (transform (, (take p₁ @ c₁) …) P)`;
* repeated: `whenever (transform (, (take p₁ @ c₁) …) P)`;
* peek: `await (transform (, (read p₁ @ c₁) …) P)`;
* select: `await (choose (transform (, (take p₁ @ a) (take q₁ @ b)) P) …)`, one transform per arm,
  taking every bind of the arm (`armTr`).

A select whose arms bind one channel each is the fragment of arms with no further bind
(`oneBind`, `select_oneBind`, `armTr_oneBind`). `Equivalence.RholangSelectJoins` has the controls
that tell a join arm from its first bind.

## The theorem

* **The rules correspond exactly** (`rholang_correspond`): every Rholang reduction rule is, label by
  label, a rule the transform definitions generate, and every generated rule whose labels are all
  encodings of Rholang processes is the encoding of a Rholang rule.
* **So bisimilarity is preserved and reflected** (`bisimilar_rholang_iff`): two Rholang soups are
  bisimilar over borrowed contexts exactly when their encodings are, relative to environments that
  are themselves Rholang soups. The transform language has more contexts (absence readers,
  predicate queries, mixed `read`/`take` receivers); relative to those, the encodings may be told apart where
  Rholang's own contexts cannot, so this is full abstraction for Rholang's environments, not for
  all of MeTTa's.

The general tool is a transport of bisimilarity along an injective relabelling between positive rule
sets that correspond (`Correspond`, `bisimilar_map_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence

universe u v w

/-! ## Transport along a relabelling -/

section Transport

variable {R : Type u} {R' : Type v} [DecidableEq R] [DecidableEq R'] (f : R → R')

/-- A positive rule, relabelled. -/
def Rule.mapPos (ρ : Rule R) : Rule R' := ⟨ρ.take.map f, ρ.keep.map f, ρ.make.map f, fun _ => false⟩

/-- Labels in the image of the relabelling. -/
def Image (y : R') : Prop := ∃ x, f x = y

/-- **Corresponding rule sets**: positive, every rule relabels to a rule, and every rule over
relabelled labels is a relabelled rule. -/
structure Correspond (Γ : Rule R → Prop) (Γ' : Rule R' → Prop) : Prop where
  positive : PositiveRules Γ
  forward : ∀ ρ, Γ ρ → Γ' (ρ.mapPos f)
  backward : ∀ ρ', Γ' ρ' → (∀ y ∈ ρ'.redex, Image f y) → ∃ ρ, Γ ρ ∧ ρ' = ρ.mapPos f

variable {f}

theorem map_sub_of_injective (hf : Function.Injective f) (A B : Multiset R) :
    (A - B).map f = A.map f - B.map f := by
  ext y
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := hy
    simp only [Multiset.count_sub, Multiset.count_map_eq_count' f _ hf]
  · have zero : ∀ M : Multiset R, Multiset.count y (M.map f) = 0 := fun M =>
      Multiset.count_eq_zero.mpr fun member => by
        obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp member
        exact hy ⟨x, rfl⟩
    rw [Multiset.count_sub, zero, zero, zero]

omit [DecidableEq R] [DecidableEq R'] in
theorem mapPos_redex (ρ : Rule R) : (ρ.mapPos f).redex = ρ.redex.map f := by
  simp [Rule.mapPos, Rule.redex, Multiset.map_add]

theorem mapPos_result (hf : Function.Injective f) (ρ : Rule R) (M : Multiset R) :
    (ρ.mapPos f).result (M.map f) = (ρ.result M).map f := by
  simp [Rule.mapPos, Rule.result, Multiset.map_add, map_sub_of_injective hf]

/-- A positive step, relabelled. -/
theorem Rule.Step.map (hf : Function.Injective f) {ρ : Rule R}
    {M M' J : Multiset R} {F : R → Bool} (step : ρ.Step M ⟨J, F⟩ M') :
    (ρ.mapPos f).Step (M.map f) ⟨J.map f, fun _ => false⟩ (M'.map f) := by
  obtain ⟨hJ, -, -, hM⟩ := step
  simp only at hJ hM
  subst hJ hM
  refine ⟨by rw [mapPos_redex, map_sub_of_injective hf], rfl, fun _ _ => rfl, ?_⟩
  simp only
  rw [← Multiset.map_add, mapPos_result hf]

/-- A relabelled step from a relabelled bag is the relabelling of a step. -/
theorem Rule.Step.unmap (hf : Function.Injective f) {ρ : Rule R} (positive : ρ.Positive)
    {M : Multiset R} {J' X' : Multiset R'} {G : R' → Bool}
    (step : (ρ.mapPos f).Step (M.map f) ⟨J', G⟩ X') :
    ∃ J X, J' = J.map f ∧ X' = X.map f ∧ ρ.Step M ⟨J, ρ.closed⟩ X := by
  obtain ⟨hJ, -, -, hX⟩ := step
  simp only at hJ hX
  refine ⟨ρ.redex - M, ρ.result (M + (ρ.redex - M)), ?_, ?_, ⟨rfl, rfl, fun x _ => positive x, rfl⟩⟩
  · rw [hJ, mapPos_redex, map_sub_of_injective hf]
  · rw [hX, hJ, mapPos_redex, ← map_sub_of_injective hf, ← Multiset.map_add, mapPos_result hf]

variable {Γ : Rule R → Prop} {Γ' : Rule R' → Prop} {ι : Type w} {obs : ι → R → Prop}

/-- Barbs read through the relabelling. -/
def mapObs (f : R → R') (obs : ι → R → Prop) : ι → R' → Prop := fun i y => ∃ x, f x = y ∧ obs i x

omit [DecidableEq R] [DecidableEq R'] in
theorem barb_map_iff (hf : Function.Injective f) {region : R → Prop} {M : Multiset R} :
    Barb (fun y => ∃ x, f x = y ∧ region x) (M.map f) ↔ Barb region M := by
  constructor
  · rintro ⟨y, member, x, rfl, h⟩
    obtain ⟨x', inM, eq⟩ := Multiset.mem_map.mp member
    exact ⟨x', inM, hf eq ▸ h⟩
  · rintro ⟨x, member, h⟩
    exact ⟨f x, Multiset.mem_map_of_mem f member, x, rfl, h⟩

omit [DecidableEq R] [DecidableEq R'] in
/-- A bag of image labels is the relabelling of a bag. -/
theorem exists_map_of_image {J' : Multiset R'} (image : ∀ y ∈ J', Image f y) :
    ∃ J : Multiset R, J' = J.map f := by
  classical
  by_cases hR : Nonempty R
  · refine ⟨J'.map (Function.invFun f), ?_⟩
    rw [Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id J']
    refine Multiset.map_congr rfl fun y member => ?_
    exact (Function.invFun_eq (image y member)).symm
  · refine ⟨0, ?_⟩
    rw [Multiset.map_zero, Multiset.eq_zero_iff_forall_notMem]
    intro y member
    obtain ⟨x, -⟩ := image y member
    exact hR ⟨x⟩

/-- A step of a relabelled bag with an image label is the relabelling of a step. -/
theorem BStep.unmap (corr : Correspond f Γ Γ') (hf : Function.Injective f) {M : Multiset R}
    {J' X' : Multiset R'} {G : R' → Bool} (image : ∀ y ∈ J', Image f y)
    (step : BStep Γ' (M.map f) ⟨J', G⟩ X') :
    ∃ J X F, J' = J.map f ∧ X' = X.map f ∧ BStep Γ M ⟨J, F⟩ X := by
  obtain ⟨ρ', member, stepρ⟩ := step
  have redexImage : ∀ y ∈ ρ'.redex, Image f y := by
    obtain ⟨hJ, -, -, -⟩ := stepρ
    simp only at hJ
    intro y inRedex
    have : ρ'.redex ≤ M.map f + J' := by rw [hJ]; exact le_add_label' _ _
    rcases Multiset.mem_add.mp (Multiset.mem_of_le this inRedex) with h | h
    · obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp h; exact ⟨x, rfl⟩
    · exact image y h
  obtain ⟨ρ, inΓ, rfl⟩ := corr.backward ρ' member redexImage
  obtain ⟨J, X, rfl, rfl, stepM⟩ := stepρ.unmap hf (corr.positive ρ inΓ)
  exact ⟨J, X, ρ.closed, rfl, rfl, ρ, inΓ, stepM⟩

/-- A step, relabelled. -/
theorem BStep.map (corr : Correspond f Γ Γ') (hf : Function.Injective f) {M M' J : Multiset R}
    {F : R → Bool} (step : BStep Γ M ⟨J, F⟩ M') :
    BStep Γ' (M.map f) ⟨J.map f, fun _ => false⟩ (M'.map f) := by
  obtain ⟨ρ, member, stepρ⟩ := step
  exact ⟨ρ.mapPos f, corr.forward ρ member, stepρ.map hf⟩

/-- **Bisimilarity transports along corresponding rule sets**: two bags are bisimilar (every label
admissible) exactly when their relabellings are bisimilar relative to relabelled environments. -/
theorem bisimilar_map_iff (corr : Correspond f Γ Γ') (hf : Function.Injective f) {M N : Multiset R} :
    Bisimilar Γ (fun _ => True) obs M N ↔ Bisimilar Γ' (Image f) (mapObs f obs) (M.map f) (N.map f) := by
  constructor
  · rintro ⟨B, bisim, related⟩
    refine ⟨fun X Y => ∃ M N, B M N ∧ X = M.map f ∧ Y = N.map f, ⟨?_, ?_, ?_⟩, ⟨M, N, related, rfl, rfl⟩⟩
    · rintro X Y ⟨M, N, rel, rfl, rfl⟩
      exact ⟨N, M, bisim.symm rel, rfl, rfl⟩
    · rintro X Y ⟨M, N, rel, rfl, rfl⟩ i shows
      exact (barb_map_iff hf).mpr (bisim.barb rel i ((barb_map_iff hf).mp shows))
    · rintro X Y ⟨M, N, rel, rfl, rfl⟩ J' F' X' adm step
      obtain ⟨J, X₀, F, rfl, rfl, stepM⟩ := step.unmap corr hf adm
      obtain ⟨G, N', -, answer, rel'⟩ := bisim.step rel (fun _ _ => trivial) stepM
      refine ⟨fun _ => false, N'.map f, weaker_none _ _, ?_, ⟨X₀, N', rel', rfl, rfl⟩⟩
      have := answer.map corr hf
      simpa [Multiset.map_add] using this
  · rintro ⟨B, bisim, related⟩
    refine ⟨fun M N => B (M.map f) (N.map f), ⟨fun _ _ h => bisim.symm h, ?_, ?_⟩, related⟩
    · intro M N rel i shows
      exact (barb_map_iff hf).mp (bisim.barb rel i ((barb_map_iff hf).mpr shows))
    · intro M N rel J F M' _ step
      obtain ⟨G', Y, -, answer, rel'⟩ := bisim.step rel
        (fun y member => by obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp member; exact ⟨x, rfl⟩)
        (step.map corr hf)
      rw [← Multiset.map_add] at answer
      obtain ⟨J₀, N', F', hJ₀, rfl, stepN⟩ := answer.unmap corr hf (by simp)
      have hJ0 : J₀ = 0 := by
        have := congrArg Multiset.card hJ₀
        simp at this
        exact Multiset.card_eq_zero.mp this.symm
      subst hJ0
      refine ⟨F', N', ?_, stepN, rel'⟩
      intro x _ h
      obtain ⟨ρ, member, ⟨-, hF, -, -⟩⟩ := stepN
      simp only at hF
      rw [hF, corr.positive ρ member x] at h
      exact absurd h (by decide)

end Transport

/-! ## Rholang's receive forms -/

namespace Rholang

open Agents

/-- The receipt kinds: linear `<-`, repeated `<=`, peek `<<-`. -/
inductive Kind where
  | linear
  | repeated
  | peek
  deriving DecidableEq, Repr

/-- An arm of a select: a linear receipt (first bind, further binds) and its continuation. -/
abbrev Arm (Ch : Type u) (Pat : Type v) (K : Type w) := (Ch × Pat) × List (Ch × Pat) × K

/-- Rholang's receivers: a receipt of one kind over at least one bind, or a select over arms that
are linear joins. Continuations are named process abstractions. -/
inductive Recv (Ch : Type u) (Pat : Type v) (K : Type w) where
  | receipt (kind : Kind) (first : Ch × Pat) (rest : List (Ch × Pat)) (k : K)
  | select (arms : List (Arm Ch Pat K))
  deriving DecidableEq

/-- Rholang's soup: messages and receivers. -/
inductive RhoLbl (Ch : Type u) (Val : Type u) (Pat : Type v) (K : Type w) where
  | msg (c : Ch) (x : Val)
  | recv (r : Recv Ch Pat K)
  deriving DecidableEq

variable {Ch Val : Type u} {Pat : Type v} {K : Type w}
variable (sat : Pat → Val → Prop)

/-- The messages a receive consumes or reads, bind by bind. -/
def msgs {L : Type*} (mk : Ch → Val → L) (binds : List (Ch × Pat)) (vals : List Val) : Multiset L :=
  ((binds.zip vals).map fun bv => mk bv.1.1 bv.2 : List L)

/-- Values that the binds' patterns accept, one per bind. -/
def Accepts (binds : List (Ch × Pat)) (vals : List Val) : Prop :=
  List.Forall₂ (fun b x => sat b.2 x) binds vals

variable (body : K → List Val → Multiset (RhoLbl Ch Val Pat K))

/-- **Rholang's reduction rules**, as Rholang states them. -/
inductive RhoRule : Rule (RhoLbl Ch Val Pat K) → Prop
  | linear {b : Ch × Pat} {bs : List (Ch × Pat)} {k : K} {vals : List Val} :
      Accepts sat (b :: bs) vals →
      RhoRule ⟨.recv (.receipt .linear b bs k) ::ₘ msgs .msg (b :: bs) vals, 0, body k vals, fun _ => false⟩
  | repeated {b : Ch × Pat} {bs : List (Ch × Pat)} {k : K} {vals : List Val} :
      Accepts sat (b :: bs) vals →
      RhoRule ⟨msgs .msg (b :: bs) vals, {.recv (.receipt .repeated b bs k)}, body k vals, fun _ => false⟩
  | peek {b : Ch × Pat} {bs : List (Ch × Pat)} {k : K} {vals : List Val} :
      Accepts sat (b :: bs) vals →
      RhoRule ⟨{.recv (.receipt .peek b bs k)}, msgs .msg (b :: bs) vals, body k vals, fun _ => false⟩
  | select {arms : List (Arm Ch Pat K)} {b : Ch × Pat} {bs : List (Ch × Pat)} {k : K} {vals : List Val} :
      (b, bs, k) ∈ arms → Accepts sat (b :: bs) vals →
      RhoRule ⟨.recv (.select arms) ::ₘ msgs .msg (b :: bs) vals, 0, body k vals, fun _ => false⟩

/-! ### The transform side -/

/-- How a source uses what it matches. -/
inductive Mode where
  | take
  | read
  deriving DecidableEq, Repr

/-- A source: a channel, a mode, a pattern. -/
structure Src (Ch : Type u) (Pat : Type v) where
  ch : Ch
  mode : Mode
  pat : Pat
  deriving DecidableEq

/-- A transform: its sources and the named template. -/
structure Tr (Ch : Type u) (Pat : Type v) (K : Type w) where
  sources : List (Src Ch Pat)
  k : K
  deriving DecidableEq

/-- Labels of the transform side: messages as data, and parked processes. -/
abbrev TLbl (Ch Val : Type u) (Pat : Type v) (K : Type w) := Agents.Lbl (Ch × Val) (Tr Ch Pat K)

/-- The messages of the sources of one mode. -/
def modeMsgs (mode : Mode) (sources : List (Src Ch Pat)) (vals : List Val) : Multiset (TLbl Ch Val Pat K) :=
  (((sources.zip vals).filter fun sv => sv.1.mode = mode).map fun sv => Lbl.data (sv.1.ch, sv.2) :
    List (TLbl Ch Val Pat K))

variable (tbody : K → List Val → Multiset (TLbl Ch Val Pat K))

/-- **The rows of a transform**: values accepted by its sources' patterns; the take sources' messages
are taken, the read sources' messages kept, the template made. -/
def trRows (t : Tr Ch Pat K) (r : Rule (TLbl Ch Val Pat K)) : Prop :=
  ∃ vals, List.Forall₂ (fun s x => sat s.pat x) t.sources vals ∧
    r = ⟨modeMsgs .take t.sources vals, modeMsgs .read t.sources vals, tbody t.k vals, fun _ => false⟩

/-- A list of binds as sources of one mode. -/
def asSources (mode : Mode) (binds : List (Ch × Pat)) : List (Src Ch Pat) :=
  binds.map fun cp => ⟨cp.1, mode, cp.2⟩

/-- The transform of an arm: every bind of its receipt taken, in one firing. -/
def armTr (a : Arm Ch Pat K) : Tr Ch Pat K := ⟨asSources .take (a.1 :: a.2.1), a.2.2⟩

/-- **The definitions**: each Rholang receiver as a parked transform; a select as one parked choice
over the transforms of its arms. -/
def encodeRecv : Recv Ch Pat K → Agent (Tr Ch Pat K)
  | .receipt .linear b bs k => .await ⟨asSources .take (b :: bs), k⟩
  | .receipt .repeated b bs k => .whenever ⟨asSources .take (b :: bs), k⟩
  | .receipt .peek b bs k => .await ⟨asSources .read (b :: bs), k⟩
  | .select arms => .choose (arms.map armTr)

/-- The encoding of the soup. -/
def encode : RhoLbl Ch Val Pat K → TLbl Ch Val Pat K
  | .msg c x => .data (c, x)
  | .recv r => .agent (encodeRecv r)

/-! ### One-bind arms -/

/-- An arm that binds one channel: a join arm with no further bind. -/
def oneBind (a : Ch × Pat × K) : Arm Ch Pat K := ((a.1, a.2.1), [], a.2.2)

/-- **A one-bind arm's transform takes its one bind.** -/
theorem armTr_oneBind (a : Ch × Pat × K) :
    armTr (oneBind a) = ⟨[⟨a.1, .take, a.2.1⟩], a.2.2⟩ := rfl

variable {sat body} in
/-- **A select over one-bind arms consumes the select and one message**, as Rholang's one-bind
`select` does. -/
theorem select_oneBind {arms : List (Ch × Pat × K)} {c : Ch} {p : Pat} {k : K} {x : Val}
    (member : (c, p, k) ∈ arms) (accepts : sat p x) :
    RhoRule sat body ⟨{.recv (.select (arms.map oneBind)), .msg c x}, 0, body k [x], fun _ => false⟩ := by
  have := RhoRule.select (sat := sat) (body := body) (arms := arms.map oneBind) (b := (c, p))
    (bs := []) (k := k) (vals := [x]) (List.mem_map_of_mem (f := oneBind) member)
    (List.Forall₂.cons accepts List.Forall₂.nil)
  simpa [msgs] using this

/-! ### The correspondence -/

section Correspondence

variable {sat} {body}

theorem asSources_injective (mode : Mode) : Function.Injective (asSources (Ch := Ch) (Pat := Pat) mode) := by
  intro a b h
  refine List.map_injective_iff.mpr ?_ h
  intro x y hxy
  simp only [Src.mk.injEq] at hxy
  exact Prod.ext hxy.1 hxy.2.2

theorem accepts_iff (mode : Mode) (binds : List (Ch × Pat)) (vals : List Val) :
    List.Forall₂ (fun s x => sat s.pat x) (asSources mode binds) vals ↔ Accepts sat binds vals := by
  unfold asSources Accepts
  rw [List.forall₂_map_left_iff]

theorem modeMsgs_same (mode : Mode) (binds : List (Ch × Pat)) (vals : List Val) :
    modeMsgs (K := K) mode (asSources mode binds) vals = (msgs RhoLbl.msg binds vals).map (encode (Pat := Pat) (K := K)) := by
  unfold modeMsgs msgs asSources
  rw [List.zip_map_left, List.filter_map]
  have : ((binds.zip vals).filter ((fun sv : Src Ch Pat × Val => decide (sv.1.mode = mode)) ∘
      Prod.map (fun cp : Ch × Pat => (⟨cp.1, mode, cp.2⟩ : Src Ch Pat)) id)) = binds.zip vals :=
    List.filter_eq_self.mpr fun _ _ => by simp
  rw [this, Multiset.map_coe, List.map_map, List.map_map]
  rfl

theorem modeMsgs_other {mode mode' : Mode} (ne : mode' ≠ mode) (binds : List (Ch × Pat)) (vals : List Val) :
    modeMsgs (Val := Val) (K := K) mode' (asSources mode binds) vals = 0 := by
  unfold modeMsgs asSources
  rw [List.zip_map_left, List.filter_map]
  have : ((binds.zip vals).filter ((fun sv : Src Ch Pat × Val => decide (sv.1.mode = mode')) ∘
      Prod.map (fun cp : Ch × Pat => (⟨cp.1, mode, cp.2⟩ : Src Ch Pat)) id)) = [] :=
    List.filter_eq_nil_iff.mpr fun _ _ => by simp [Ne.symm ne]
  rw [this]
  rfl

theorem armTr_injective : Function.Injective (armTr (Ch := Ch) (Pat := Pat) (K := K)) := by
  rintro ⟨b, bs, k⟩ ⟨b', bs', k'⟩ h
  simp only [armTr, Tr.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  have := asSources_injective .take hs
  simp only [List.cons.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  rfl

theorem encodeRecv_injective : Function.Injective (encodeRecv (Ch := Ch) (Pat := Pat) (K := K)) := by
  intro r r' h
  cases r with
  | receipt kind b bs k =>
      cases r' with
      | receipt kind' b' bs' k' =>
          cases kind <;> cases kind' <;> simp only [encodeRecv, Agent.await.injEq, Agent.whenever.injEq,
            reduceCtorEq, Tr.mk.injEq] at h <;>
            first
            | (obtain ⟨hs, rfl⟩ := h
               have := asSources_injective _ hs
               simp only [List.cons.injEq] at this
               obtain ⟨rfl, rfl⟩ := this
               rfl)
            | (obtain ⟨hs, -⟩ := h
               simp only [asSources, List.map_cons, List.cons.injEq, Src.mk.injEq] at hs
               exact absurd hs.1.2.1 (by decide))
      | select arms => cases kind <;> simp [encodeRecv] at h
  | select arms =>
      cases r' with
      | receipt kind' b' bs' k' => cases kind' <;> simp [encodeRecv] at h
      | select arms' =>
          simp only [encodeRecv, Agent.choose.injEq] at h
          rw [List.map_injective_iff.mpr armTr_injective h]

theorem encode_injective : Function.Injective (encode (Ch := Ch) (Val := Val) (Pat := Pat) (K := K)) := by
  intro x y h
  cases x with
  | msg c v =>
      cases y with
      | msg c' v' => simp only [encode, Lbl.data.injEq, Prod.mk.injEq] at h; rw [h.1, h.2]
      | recv r => simp [encode] at h
  | recv r =>
      cases y with
      | msg c' v' => simp [encode] at h
      | recv r' =>
          simp only [encode, Lbl.agent.injEq] at h
          rw [encodeRecv_injective h]

theorem rhoRule_positive : PositiveRules (RhoRule (Ch := Ch) (Val := Val) (Pat := Pat) (K := K) sat body) := by
  intro ρ h x
  cases h <;> rfl

/-- **Rholang's rules and the transform definitions correspond exactly.** -/
theorem rholang_correspond [DecidableEq Ch] [DecidableEq Val] [DecidableEq Pat] [DecidableEq K] :
    Correspond (encode (Ch := Ch) (Val := Val) (Pat := Pat) (K := K)) (RhoRule sat body)
      (Fires (trRows sat fun k vals => (body k vals).map encode)) := by
  refine ⟨rhoRule_positive, ?_, ?_⟩
  · intro ρ h
    cases h with
    | @linear b bs k vals acc =>
        have row : trRows sat (fun k vals => (body k vals).map encode)
            ⟨asSources .take (b :: bs), k⟩
            ⟨modeMsgs .take (asSources .take (b :: bs)) vals, modeMsgs .read (asSources .take (b :: bs)) vals,
              (body k vals).map encode, fun _ => false⟩ :=
          ⟨vals, (accepts_iff .take _ _).mpr acc, rfl⟩
        have := Fires.await row
        rw [modeMsgs_same, modeMsgs_other (by decide)] at this
        convert this using 1
        simp [Rule.mapPos, encode, encodeRecv]
    | @repeated b bs k vals acc =>
        have row : trRows sat (fun k vals => (body k vals).map encode)
            ⟨asSources .take (b :: bs), k⟩
            ⟨modeMsgs .take (asSources .take (b :: bs)) vals, modeMsgs .read (asSources .take (b :: bs)) vals,
              (body k vals).map encode, fun _ => false⟩ :=
          ⟨vals, (accepts_iff .take _ _).mpr acc, rfl⟩
        have := Fires.whenever row
        rw [modeMsgs_same, modeMsgs_other (by decide)] at this
        convert this using 1
        simp [Rule.mapPos, encode, encodeRecv]
    | @peek b bs k vals acc =>
        have row : trRows sat (fun k vals => (body k vals).map encode)
            ⟨asSources .read (b :: bs), k⟩
            ⟨modeMsgs .take (asSources .read (b :: bs)) vals, modeMsgs .read (asSources .read (b :: bs)) vals,
              (body k vals).map encode, fun _ => false⟩ :=
          ⟨vals, (accepts_iff .read _ _).mpr acc, rfl⟩
        have := Fires.await row
        rw [modeMsgs_same, modeMsgs_other (by decide)] at this
        convert this using 1
        simp [Rule.mapPos, encode, encodeRecv]
    | @select arms b bs k vals member acc =>
        have row : trRows sat (fun k vals => (body k vals).map encode) (armTr (b, bs, k))
            ⟨modeMsgs .take (asSources .take (b :: bs)) vals, modeMsgs .read (asSources .take (b :: bs)) vals,
              (body k vals).map encode, fun _ => false⟩ :=
          ⟨vals, (accepts_iff .take _ _).mpr acc, rfl⟩
        have := Fires.choose (ts := arms.map armTr) (List.mem_map_of_mem member) row
        rw [modeMsgs_same, modeMsgs_other (by decide)] at this
        convert this using 1
        simp [Rule.mapPos, encode, encodeRecv]
  · intro ρ' h image
    cases h with
    | @await t r row =>
        obtain ⟨vals, acc, rfl⟩ := row
        obtain ⟨x, hx⟩ := image (Lbl.agent (.await t)) (by simp [Rule.redex])
        cases x with
        | msg c v => simp [encode] at hx
        | recv rr =>
            cases rr with
            | select arms => simp [encode, encodeRecv] at hx
            | receipt kind b bs k =>
                cases kind with
                | repeated => simp [encode, encodeRecv] at hx
                | linear =>
                    simp only [encode, encodeRecv, Lbl.agent.injEq, Agent.await.injEq] at hx
                    subst hx
                    refine ⟨_, RhoRule.linear (b := b) (bs := bs) (k := k) ((accepts_iff .take _ _).mp acc), ?_⟩
                    simp only [Rule.mapPos]
                    rw [modeMsgs_same, modeMsgs_other (by decide)]
                    simp [encode, encodeRecv]
                | peek =>
                    simp only [encode, encodeRecv, Lbl.agent.injEq, Agent.await.injEq] at hx
                    subst hx
                    refine ⟨_, RhoRule.peek (b := b) (bs := bs) (k := k) ((accepts_iff .read _ _).mp acc), ?_⟩
                    simp only [Rule.mapPos]
                    rw [modeMsgs_same, modeMsgs_other (by decide)]
                    simp [encode, encodeRecv]
    | @whenever t r row =>
        obtain ⟨vals, acc, rfl⟩ := row
        obtain ⟨x, hx⟩ := image (Lbl.agent (.whenever t)) (by simp [Rule.redex])
        cases x with
        | msg c v => simp [encode] at hx
        | recv rr =>
            cases rr with
            | select arms => simp [encode, encodeRecv] at hx
            | receipt kind b bs k =>
                cases kind with
                | linear => simp [encode, encodeRecv] at hx
                | peek => simp [encode, encodeRecv] at hx
                | repeated =>
                    simp only [encode, encodeRecv, Lbl.agent.injEq, Agent.whenever.injEq] at hx
                    subst hx
                    refine ⟨_, RhoRule.repeated (b := b) (bs := bs) (k := k) ((accepts_iff .take _ _).mp acc), ?_⟩
                    simp only [Rule.mapPos]
                    rw [modeMsgs_same, modeMsgs_other (by decide)]
                    simp [encode, encodeRecv]
    | @choose ts t r tmem row =>
        obtain ⟨vals, acc, rfl⟩ := row
        obtain ⟨x, hx⟩ := image (Lbl.agent (.choose ts)) (by simp [Rule.redex])
        cases x with
        | msg c v => simp [encode] at hx
        | recv rr =>
            cases rr with
            | receipt kind b bs k => cases kind <;> simp [encode, encodeRecv] at hx
            | select arms =>
                simp only [encode, encodeRecv, Lbl.agent.injEq, Agent.choose.injEq] at hx
                subst hx
                obtain ⟨⟨b, bs, k⟩, armMem, rfl⟩ := List.mem_map.mp tmem
                refine ⟨_, RhoRule.select armMem ((accepts_iff .take _ _).mp acc), ?_⟩
                simp only [Rule.mapPos, armTr]
                rw [modeMsgs_same, modeMsgs_other (by decide)]
                simp [encode, encodeRecv]

/-- **Rholang soups are bisimilar exactly when their encodings are**, relative to environments that
are themselves Rholang soups. -/
theorem bisimilar_rholang_iff [DecidableEq Ch] [DecidableEq Val] [DecidableEq Pat] [DecidableEq K]
    {ι : Type*} {obs : ι → RhoLbl Ch Val Pat K → Prop}
    {M N : Multiset (RhoLbl Ch Val Pat K)} :
    Bisimilar (RhoRule sat body) (fun _ => True) obs M N ↔
      Bisimilar (Fires (trRows sat fun k vals => (body k vals).map encode)) (Image encode)
        (mapObs encode obs) (M.map encode) (N.map encode) :=
  bisimilar_map_iff rholang_correspond encode_injective

end Correspondence

end Rholang

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence
