(** ============================================================================
   Iter Native MeTTa Architecture Verification - Module 2
   Experience Hygiene, Windowing, Tool-Pairing Preservation, & Bucket-Skip Witness
   Target source: iter-native-release-20261028/iter.metta (lines 67-122, 223-245)
   Checked natively by CeTTa's Megalodon kernel against standard Egal preamble.mgs.
   Zero document axioms. Zero admitted. Zero aby.
   ============================================================================ *)

Section IterExperienceHygiene.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

(** ---- Part 1: Natural Arithmetic & Ordering Bridge on omega --------------- *)

Theorem nat_0_omega : 0 :e omega.
exact nat_p_omega 0 nat_0.
Qed.

Theorem nat_1_omega : 1 :e omega.
exact nat_p_omega 1 nat_1.
Qed.

Theorem nat_add_omega : forall n :e omega, forall m :e omega, n + m :e omega.
let n. assume Hn. let m. assume Hm.
rewrite <- add_nat_add_SNo n Hn m Hm.
exact nat_p_omega (add_nat n m) (add_nat_p n (omega_nat_p n Hn) m (omega_nat_p m Hm)).
Qed.

Theorem nat_mul_omega : forall n :e omega, forall m :e omega, n * m :e omega.
let n. assume Hn. let m. assume Hm.
rewrite <- mul_nat_mul_SNo n Hn m Hm.
exact nat_p_omega (mul_nat n m) (mul_nat_p n (omega_nat_p n Hn) m (omega_nat_p m Hm)).
Qed.

Theorem ordsucc_eq_add_1 : forall n :e omega, ordsucc n = n + 1.
let n. assume Hn.
rewrite <- add_nat_add_SNo n Hn 1 nat_1_omega.
prove ordsucc n = add_nat n (ordsucc 0).
rewrite add_nat_SR n 0 nat_0.
rewrite add_nat_0R n.
reflexivity.
Qed.

Theorem nat_In_SNoLt : forall n :e omega, forall m :e n, m < n.
let n. assume Hn. let m. assume Hm.
exact ordinal_In_SNoLt n (nat_p_ordinal n (omega_nat_p n Hn)) m Hm.
Qed.

Theorem nat_SNoLt_In : forall n :e omega, forall m :e omega, m < n -> m :e n.
let n. assume Hn. let m. assume Hm. assume Hlt.
apply ordinal_trichotomy_or_impred m n (nat_p_ordinal m (omega_nat_p m Hm)) (nat_p_ordinal n (omega_nat_p n Hn)).
- assume H : m :e n. exact H.
- assume Heq : m = n.
  apply FalseE. apply SNoLt_irref m.
  rewrite Heq at 2. exact Hlt.
- assume Hrev : n :e m.
  apply FalseE.
  claim Hgt : n < m. { exact nat_In_SNoLt m Hm n Hrev. }
  exact SNoLt_irref m (SNoLt_tra m n m (omega_SNo m Hm) (omega_SNo n Hn) (omega_SNo m Hm) Hlt Hgt).
Qed.

Theorem nat_SNoLe_cases : forall m :e omega, forall n :e omega, m <= n -> m :e n \/ m = n.
let m. assume Hm. let n. assume Hn. assume Hle.
apply ordinal_trichotomy_or_impred m n (nat_p_ordinal m (omega_nat_p m Hm)) (nat_p_ordinal n (omega_nat_p n Hn)).
- assume H : m :e n. exact orIL (m :e n) (m = n) H.
- assume H : m = n. exact orIR (m :e n) (m = n) H.
- assume Hrev : n :e m.
  apply FalseE.
  claim Hgt : n < m. { exact nat_In_SNoLt m Hm n Hrev. }
  exact SNoLt_irref n (SNoLtLe_tra n m n (omega_SNo n Hn) (omega_SNo m Hm) (omega_SNo n Hn) Hgt Hle).
Qed.

Theorem nat_0_Le : forall n :e omega, 0 <= n.
let n. assume Hn.
apply nat_ind (fun k => 0 <= k).
- exact SNoLe_ref 0.
- let k. assume Hk Hle.
  claim Hko : k :e omega. { exact nat_p_omega k Hk. }
  rewrite ordsucc_eq_add_1 k Hko.
  apply SNoLe_tra 0 k (k + 1) SNo_0 (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) Hle.
  rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
  exact add_SNo_Le2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
- exact omega_nat_p n Hn.
Qed.

Theorem nat_Le_In_ordsucc : forall m :e omega, forall n :e omega, m <= n -> m :e ordsucc n.
let m. assume Hm. let n. assume Hn. assume Hle.
apply nat_SNoLe_cases m Hm n Hn Hle.
- assume Hin : m :e n. exact ordsuccI1 n m Hin.
- assume Heq : m = n. rewrite Heq. exact ordsuccI2 n.
Qed.

Theorem nat_In_ordsucc_Le : forall n :e omega, forall m :e ordsucc n, m <= n.
let n. assume Hn. let m. assume Hm.
apply ordsuccE n m Hm.
- assume Hin : m :e n. exact SNoLtLe m n (nat_In_SNoLt n Hn m Hin).
- assume Heq : m = n. rewrite Heq. exact SNoLe_ref n.
Qed.

Theorem nat_In_omega : forall n :e omega, forall m :e n, m :e omega.
let n. assume Hn. let m. assume Hm.
exact nat_p_omega m (nat_p_trans n (omega_nat_p n Hn) m Hm).
Qed.

Theorem nat_pos_pred : forall n :e omega, 0 < n -> exists k :e omega, n = k + 1.
let n. assume Hn Hpos.
apply nat_inv n (omega_nat_p n Hn).
- assume H0 : n = 0.
  apply FalseE. apply SNoLt_irref 0.
  rewrite <- H0 at 2. exact Hpos.
- assume Hex. apply Hex. let k. assume Hk. apply Hk. assume Hkn Heq.
  claim Hko : k :e omega. { exact nat_p_omega k Hkn. }
  witness k. apply andI.
  + exact Hko.
  + rewrite Heq. exact ordsucc_eq_add_1 k Hko.
Qed.

Theorem nat_SNoLt_S_Le : forall m :e omega, forall n :e omega, m < n -> m + 1 <= n.
let m. assume Hm. let n. assume Hn Hlt.
claim Hin : m :e n. { exact nat_SNoLt_In n Hn m Hm Hlt. }
claim Hnpos : 0 < n. { exact SNoLeLt_tra 0 m n SNo_0 (omega_SNo m Hm) (omega_SNo n Hn) (nat_0_Le m Hm) Hlt. }
apply nat_pos_pred n Hn Hnpos. let k. assume Hk. apply Hk. assume Hko Heq.
claim Hmk : m :e ordsucc k.
{ rewrite ordsucc_eq_add_1 k Hko. rewrite <- Heq. exact Hin. }
claim Hle : m <= k. { exact nat_In_ordsucc_Le k Hko m Hmk. }
rewrite Heq.
exact add_SNo_Le1 m 1 k (omega_SNo m Hm) SNo_1 (omega_SNo k Hko) Hle.
Qed.

Theorem SNo_add_sub_cancel_1 : forall k m, SNo k -> SNo m -> (k + 1) + - (m + 1) = k + - m.
let k m. assume Hk Hm.
rewrite minus_add_SNo_distr m 1 Hm SNo_1.
rewrite add_SNo_com (- m) (- 1) (SNo_minus_SNo m Hm) (SNo_minus_SNo 1 SNo_1).
rewrite add_SNo_assoc (k + 1) (- 1) (- m) (SNo_add_SNo k 1 Hk SNo_1) (SNo_minus_SNo 1 SNo_1) (SNo_minus_SNo m Hm).
rewrite add_SNo_minus_R2 k 1 Hk SNo_1.
reflexivity.
Qed.

Theorem SNo_add_sub_L : forall a b, SNo a -> SNo b -> b + (a + - b) = a.
let a b. assume Ha Hb.
rewrite add_SNo_com a (- b) Ha (SNo_minus_SNo b Hb).
rewrite add_SNo_assoc b (- b) a Hb (SNo_minus_SNo b Hb) Ha.
rewrite add_SNo_minus_SNo_rinv b Hb.
exact add_SNo_0L a Ha.
Qed.

Theorem SNo_sub_add_R : forall a b, SNo a -> SNo b -> (a + b) + - b = a.
let a b. assume Ha Hb.
exact add_SNo_minus_R2 a b Ha Hb.
Qed.

Theorem SNo_add_cancel_R : forall a b c, SNo a -> SNo b -> SNo c -> a + c = b + c -> a = b.
let a b c. assume Ha Hb Hc Heq.
rewrite <- add_SNo_minus_R2 a c Ha Hc.
rewrite Heq.
exact add_SNo_minus_R2 b c Hb Hc.
Qed.

Theorem SNo_add_cancel_L : forall a b c, SNo a -> SNo b -> SNo c -> c + a = c + b -> a = b.
let a b c. assume Ha Hb Hc Heq.
apply SNo_add_cancel_R a b c Ha Hb Hc.
rewrite add_SNo_com a c Ha Hc.
rewrite add_SNo_com b c Hb Hc.
exact Heq.
Qed.

Theorem nat_sub_omega : forall m :e omega, forall n :e omega, m <= n -> n + - m :e omega.
let m. assume Hm.
apply nat_ind (fun k => forall n :e omega, k <= n -> n + - k :e omega).
- let n. assume Hn Hle.
  rewrite minus_SNo_0.
  rewrite add_SNo_0R n (omega_SNo n Hn).
  exact Hn.
- let k. assume Hk IH. let n. assume Hn Hle.
  claim Hko : k :e omega. { exact nat_p_omega k Hk. }
  claim Hk1 : ordsucc k = k + 1. { exact ordsucc_eq_add_1 k Hko. }
  claim Hnpos : 0 < n.
  { apply SNoLtLe_tra 0 (k + 1) n SNo_0 (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) (omega_SNo n Hn).
    - apply SNoLeLt_tra 0 k (k + 1) SNo_0 (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) (nat_0_Le k Hko).
      rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
      exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
    - rewrite <- Hk1. exact Hle. }
  apply nat_pos_pred n Hn Hnpos. let p. assume Hp. apply Hp. assume Hpo Hnp.
  claim Hkp : k <= p.
  { apply ordinal_trichotomy_or_impred k p (nat_p_ordinal k Hk) (nat_p_ordinal p (omega_nat_p p Hpo)).
    - assume H1 : k :e p. exact SNoLtLe k p (nat_In_SNoLt p Hpo k H1).
    - assume H1 : k = p. rewrite H1. exact SNoLe_ref p.
    - assume H1 : p :e k.
      apply FalseE.
      claim Hpk : p + 1 <= k. { exact nat_SNoLt_S_Le p Hpo k Hko (nat_In_SNoLt k Hko p H1). }
      claim Hnk : n < ordsucc k.
      { rewrite Hnp. rewrite Hk1.
        apply SNoLeLt_tra (p + 1) k (k + 1) (SNo_add_SNo p 1 (omega_SNo p Hpo) SNo_1) (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) Hpk.
        rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
        exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1. }
      exact SNoLt_irref n (SNoLtLe_tra n (ordsucc k) n (omega_SNo n Hn) (omega_SNo (ordsucc k) (omega_ordsucc k Hko)) (omega_SNo n Hn) Hnk Hle). }
  rewrite Hnp. rewrite Hk1.
  rewrite SNo_add_sub_cancel_1 p k (omega_SNo p Hpo) (omega_SNo k Hko).
  exact IH p Hpo Hkp.
- exact omega_nat_p m Hm.
Qed.

Theorem nat_In_sub_add : forall n :e omega, forall d :e omega, d <= n -> forall i :e n + - d, d + i :e n.
let n. assume Hn. let d. assume Hd Hle. let i. assume Hi.
claim Hsub : n + - d :e omega. { exact nat_sub_omega d Hd n Hn Hle. }
claim Hio : i :e omega. { exact nat_In_omega (n + - d) Hsub i Hi. }
claim Hilt : i < n + - d. { exact nat_In_SNoLt (n + - d) Hsub i Hi. }
apply nat_SNoLt_In n Hn (d + i) (nat_add_omega d Hd i Hio).
rewrite <- SNo_add_sub_L n d (omega_SNo n Hn) (omega_SNo d Hd).
exact add_SNo_Lt2 d i (n + - d) (omega_SNo d Hd) (omega_SNo i Hio) (omega_SNo (n + - d) Hsub) Hilt.
Qed.

Theorem nat_sub_Le : forall n :e omega, forall d :e omega, d <= n -> n + - d <= n.
let n. assume Hn. let d. assume Hd Hle.
claim Hsub : n + - d :e omega. { exact nat_sub_omega d Hd n Hn Hle. }
rewrite <- SNo_add_sub_L n d (omega_SNo n Hn) (omega_SNo d Hd) at 2.
rewrite <- add_SNo_0L (n + - d) (omega_SNo (n + - d) Hsub) at 1.
exact add_SNo_Le1 0 (n + - d) d SNo_0 (omega_SNo (n + - d) Hsub) (omega_SNo d Hd) (nat_0_Le d Hd).
Qed.

Theorem nat_least_witness : forall P:set -> prop, forall n :e omega,
  exists d :e ordsucc n, (forall j :e d, ~(P j)) /\ (d = n \/ P d).
let P. let n. assume Hn.
apply nat_ind (fun m => exists d :e ordsucc m, (forall j :e d, ~(P j)) /\ (d = m \/ P d)).
- prove exists d :e ordsucc 0, (forall j :e d, ~(P j)) /\ (d = 0 \/ P d).
  witness 0. apply andI.
  + exact ordsuccI2 0.
  + apply andI.
    * let j. assume Hj. apply FalseE. exact EmptyE j Hj.
    * apply orIL. reflexivity.
- let m. assume Hm IH.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  prove exists d :e ordsucc (ordsucc m), (forall j :e d, ~(P j)) /\ (d = ordsucc m \/ P d).
  apply IH. let d. assume Hd. apply Hd. assume Hdin Hspec. apply Hspec. assume Hall Hor.
  apply Hor.
  + assume Heq : d = m.
    apply xm (P m).
    * assume HPm : P m.
      witness m. apply andI.
      { exact ordsuccI1 (ordsucc m) m (ordsuccI2 m). }
      { apply andI.
        - rewrite <- Heq. exact Hall.
        - apply orIR. exact HPm. }
    * assume HnPm : ~(P m).
      witness (ordsucc m). apply andI.
      { exact ordsuccI2 (ordsucc m). }
      { apply andI.
        - let j. assume Hj.
          apply ordsuccE m j Hj.
          + assume Hjm : j :e m.
            claim Hjd : j :e d. { rewrite Heq. exact Hjm. }
            exact Hall j Hjd.
          + assume Hjeq : j = m. rewrite Hjeq. exact HnPm.
        - apply orIL. reflexivity. }
  + assume HPd : P d.
    witness d. apply andI.
    * exact ordsuccI1 (ordsucc m) d Hdin.
    * apply andI.
      { exact Hall. }
      { apply orIR. exact HPd. }
- exact omega_nat_p n Hn.
Qed.

Theorem nat_least_witness_unique : forall P:set -> prop, forall n :e omega,
  forall d1 :e ordsucc n, forall d2 :e ordsucc n,
  ((forall j :e d1, ~(P j)) /\ (d1 = n \/ P d1)) ->
  ((forall j :e d2, ~(P j)) /\ (d2 = n \/ P d2)) ->
  d1 = d2.
let P. let n. assume Hn. let d1. assume Hd1. let d2. assume Hd2.
assume Hs1 Hs2.
apply Hs1. assume Hall1 Hor1. apply Hs2. assume Hall2 Hor2.
claim Hd1o : d1 :e omega. { exact nat_In_omega (ordsucc n) (omega_ordsucc n Hn) d1 Hd1. }
claim Hd2o : d2 :e omega. { exact nat_In_omega (ordsucc n) (omega_ordsucc n Hn) d2 Hd2. }
apply ordinal_trichotomy_or_impred d1 d2 (nat_p_ordinal d1 (omega_nat_p d1 Hd1o)) (nat_p_ordinal d2 (omega_nat_p d2 Hd2o)).
- assume H12 : d1 :e d2.
  apply FalseE.
  apply Hor1.
  + assume Heq : d1 = n.
    claim Hn2 : n :e d2. { rewrite <- Heq. exact H12. }
    claim Hle2 : d2 <= n. { exact nat_In_ordsucc_Le n Hn d2 Hd2. }
    exact SNoLt_irref n (SNoLtLe_tra n d2 n (omega_SNo n Hn) (omega_SNo d2 Hd2o) (omega_SNo n Hn) (nat_In_SNoLt d2 Hd2o n Hn2) Hle2).
  + assume HP1 : P d1. exact Hall2 d1 H12 HP1.
- assume Heq : d1 = d2. exact Heq.
- assume H21 : d2 :e d1.
  apply FalseE.
  apply Hor2.
  + assume Heq : d2 = n.
    claim Hn1 : n :e d1. { rewrite <- Heq. exact H21. }
    claim Hle1 : d1 <= n. { exact nat_In_ordsucc_Le n Hn d1 Hd1. }
    exact SNoLt_irref n (SNoLtLe_tra n d1 n (omega_SNo n Hn) (omega_SNo d1 Hd1o) (omega_SNo n Hn) (nat_In_SNoLt d1 Hd1o n Hn1) Hle1).
  + assume HP2 : P d2. exact Hall1 d2 H21 HP2.
Qed.

(** ---- Part 2: Finite Message Sequences & Iter Roles ----------------------- *)

Definition RoleUser : set := 0.
Definition RoleSystem : set := 1.
Definition RoleAssistant : set := 2.
Definition RoleTool : set := 3.
Definition RoleRaw : set := 4.

Theorem RoleAssistant_neq_Tool : RoleAssistant <> RoleTool.
assume Heq : 2 = 3.
apply SNoLt_irref 2.
rewrite Heq at 2.
exact nat_In_SNoLt 3 (nat_p_omega 3 nat_3) 2 In_2_3.
Qed.

Theorem RoleUser_neq_Tool : RoleUser <> RoleTool.
assume Heq : 0 = 3.
apply SNoLt_irref 0.
rewrite Heq at 2.
exact nat_In_SNoLt 3 (nat_p_omega 3 nat_3) 0 In_0_3.
Qed.

Definition Msg : set -> set -> set := fun r c => setsum r c.
Definition msg_role : set -> set := fun m => proj0 m.
Definition msg_content : set -> set := fun m => proj1 m.

Theorem msg_role_pair : forall r c, msg_role (Msg r c) = r.
let r c. exact proj0_pair_eq r c.
Qed.

Theorem msg_content_pair : forall r c, msg_content (Msg r c) = c.
let r c. exact proj1_pair_eq r c.
Qed.

Definition Seq : set -> (set -> set) -> set := fun n f => setsum n (fun i :e n => f i).
Definition seq_len : set -> set := fun s => proj0 s.
Definition seq_at : set -> set -> set := fun s i => ap (proj1 s) i.
Definition ValidSeq : set -> prop := fun s => seq_len s :e omega.

Theorem seq_len_mk : forall n, forall f:set -> set, seq_len (Seq n f) = n.
let n f. exact proj0_pair_eq n (fun i :e n => f i).
Qed.

Theorem seq_at_mk : forall n, forall f:set -> set, forall i :e n, seq_at (Seq n f) i = f i.
let n f. let i. assume Hi.
prove ap (proj1 (setsum n (fun j :e n => f j))) i = f i.
rewrite proj1_pair_eq n (fun j :e n => f j).
exact beta n f i Hi.
Qed.

Theorem ValidSeq_mk : forall n :e omega, forall f:set -> set, ValidSeq (Seq n f).
let n. assume Hn. let f.
prove seq_len (Seq n f) :e omega.
rewrite seq_len_mk n f. exact Hn.
Qed.

Definition seq_take : set -> set -> set :=
  fun k s => Seq k (fun i => seq_at s i).

Definition seq_drop : set -> set -> set :=
  fun d s => Seq (seq_len s + - d) (fun i => seq_at s (d + i)).

(** Cleanup rule from iter.metta:67-79, parameterized by pure truncation/stripping *)
Variable trunc_tool : set -> set.
Variable strip_reasoning : set -> set.

Definition clean_msg : set -> set :=
  fun m =>
    if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
    else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
    else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
    else m.

Theorem clean_msg_preserves_role : forall m, msg_role (clean_msg m) = msg_role m.
let m.
apply xm (msg_role m = RoleTool).
- assume H : msg_role m = RoleTool.
  prove msg_role (if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
                  else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
                  else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
                  else m) = msg_role m.
  rewrite If_i_1 (msg_role m = RoleTool) (Msg RoleTool (trunc_tool (msg_content m)))
          (if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
           else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) H.
  rewrite msg_role_pair RoleTool (trunc_tool (msg_content m)).
  symmetry. exact H.
- assume Hnt : msg_role m <> RoleTool.
  prove msg_role (if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
                  else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
                  else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
                  else m) = msg_role m.
  rewrite If_i_0 (msg_role m = RoleTool) (Msg RoleTool (trunc_tool (msg_content m)))
          (if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
           else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hnt.
  apply xm (msg_role m = RoleAssistant).
  + assume Ha : msg_role m = RoleAssistant.
    rewrite If_i_1 (msg_role m = RoleAssistant) (Msg RoleAssistant (strip_reasoning (msg_content m)))
            (if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Ha.
    rewrite msg_role_pair RoleAssistant (strip_reasoning (msg_content m)).
    symmetry. exact Ha.
  + assume Hna : msg_role m <> RoleAssistant.
    rewrite If_i_0 (msg_role m = RoleAssistant) (Msg RoleAssistant (strip_reasoning (msg_content m)))
            (if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hna.
    apply xm (msg_role m = RoleRaw).
    * assume Hr : msg_role m = RoleRaw.
      rewrite If_i_1 (msg_role m = RoleRaw) (Msg RoleRaw (strip_reasoning (msg_content m))) m Hr.
      rewrite msg_role_pair RoleRaw (strip_reasoning (msg_content m)).
      symmetry. exact Hr.
    * assume Hnr : msg_role m <> RoleRaw.
      rewrite If_i_0 (msg_role m = RoleRaw) (Msg RoleRaw (strip_reasoning (msg_content m))) m Hnr.
      reflexivity.
Qed.

Definition cleanup_old_messages : set -> set -> set :=
  fun preserve s =>
    Seq (seq_len s) (fun i => if i + preserve < seq_len s then clean_msg (seq_at s i) else seq_at s i).

(** ToolPaired invariant: every Tool message has a positive index i = k + 1
    and its immediate predecessor at k is either Assistant or Tool.
    By induction this guarantees no leading Tool and every Tool belongs to a
    contiguous Assistant-then-Tool block with no intervening User/System/Raw. *)
Definition ToolPaired : set -> prop :=
  fun s =>
    forall i :e seq_len s, msg_role (seq_at s i) = RoleTool ->
      0 < i /\ (exists k :e omega, i = k + 1 /\
        (msg_role (seq_at s k) = RoleAssistant \/ msg_role (seq_at s k) = RoleTool)).

Definition NoLeadingTool : set -> prop :=
  fun s => seq_len s = 0 \/ msg_role (seq_at s 0) <> RoleTool.

Theorem ToolPaired_implies_NoLeadingTool : forall s, ValidSeq s -> ToolPaired s -> NoLeadingTool s.
let s. assume Hs Htp.
apply xm (seq_len s = 0).
- assume H0 : seq_len s = 0. exact orIL (seq_len s = 0) (msg_role (seq_at s 0) <> RoleTool) H0.
- assume Hne : seq_len s <> 0.
  prove seq_len s = 0 \/ msg_role (seq_at s 0) <> RoleTool.
  apply orIR.
  assume Htool : msg_role (seq_at s 0) = RoleTool.
  claim Hpos : 0 < seq_len s.
  { apply nat_SNoLe_cases 0 nat_0_omega (seq_len s) Hs (nat_0_Le (seq_len s) Hs).
    - assume H0in : 0 :e seq_len s. exact nat_In_SNoLt (seq_len s) Hs 0 H0in.
    - assume H0eq : 0 = seq_len s. apply FalseE. apply Hne. symmetry. exact H0eq. }
  claim H0in : 0 :e seq_len s. { exact nat_SNoLt_In (seq_len s) Hs 0 nat_0_omega Hpos. }
  claim H0lt0 : 0 < 0. { exact andEL (0 < 0) (exists k :e omega, 0 = k + 1 /\ (msg_role (seq_at s k) = RoleAssistant \/ msg_role (seq_at s k) = RoleTool)) (Htp 0 H0in Htool). }
  exact SNoLt_irref 0 H0lt0.
Qed.

(** ---- Theorem Group 1: cleanup_old_messages Guarantees -------------------- *)

Theorem cleanup_preserves_len : forall P s, seq_len (cleanup_old_messages P s) = seq_len s.
let P s. exact seq_len_mk (seq_len s) (fun i => if i + P < seq_len s then clean_msg (seq_at s i) else seq_at s i).
Qed.

Theorem cleanup_preserves_recent : forall P :e omega, forall s, ValidSeq s ->
  forall i :e seq_len s, seq_len s <= i + P ->
  seq_at (cleanup_old_messages P s) i = seq_at s i.
let P. assume HP. let s. assume Hs. let i. assume Hi Hge.
claim Hio : i :e omega. { exact nat_In_omega (seq_len s) Hs i Hi. }
claim Hnlt : ~(i + P < seq_len s).
{ assume Hlt : i + P < seq_len s.
  exact SNoLt_irref (seq_len s)
        (SNoLeLt_tra (seq_len s) (i + P) (seq_len s) (omega_SNo (seq_len s) Hs)
          (omega_SNo (i + P) (nat_add_omega i Hio P HP)) (omega_SNo (seq_len s) Hs) Hge Hlt). }
prove seq_at (Seq (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j)) i = seq_at s i.
rewrite seq_at_mk (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j) i Hi.
exact If_i_0 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hnlt.
Qed.

Theorem cleanup_preserves_roles : forall P s, forall i :e seq_len s,
  msg_role (seq_at (cleanup_old_messages P s) i) = msg_role (seq_at s i).
let P s. let i. assume Hi.
prove msg_role (seq_at (Seq (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j)) i) = msg_role (seq_at s i).
rewrite seq_at_mk (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j) i Hi.
apply xm (i + P < seq_len s).
- assume Hlt : i + P < seq_len s.
  rewrite If_i_1 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hlt.
  exact clean_msg_preserves_role (seq_at s i).
- assume Hnlt : ~(i + P < seq_len s).
  rewrite If_i_0 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hnlt.
  reflexivity.
Qed.

Theorem cleanup_preserves_ToolPaired : forall P s, ValidSeq s -> ToolPaired s -> ToolPaired (cleanup_old_messages P s).
let P s. assume Hs Htp.
let i. assume Hi Htool.
claim Hi' : i :e seq_len s. { rewrite <- cleanup_preserves_len P s. exact Hi. }
claim Htool' : msg_role (seq_at s i) = RoleTool.
{ rewrite <- cleanup_preserves_roles P s i Hi'. exact Htool. }
apply Htp i Hi' Htool'. assume Hpos Hex.
apply andI.
- exact Hpos.
- apply Hex. let k. assume Hk. apply Hk. assume Hko Hk2. apply Hk2. assume Hik Hor.
  claim Hkin : k :e seq_len s.
  { apply nat_SNoLt_In (seq_len s) Hs k Hko.
    apply SNoLt_tra k i (seq_len s) (omega_SNo k Hko) (omega_SNo i (nat_In_omega (seq_len s) Hs i Hi')) (omega_SNo (seq_len s) Hs).
    - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
      exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
    - exact nat_In_SNoLt (seq_len s) Hs i Hi'. }
  witness k. apply andI.
  + exact Hko.
  + apply andI.
    * exact Hik.
    * rewrite cleanup_preserves_roles P s k Hkin. exact Hor.
Qed.

(** ---- Theorem Group 2: drop_leading_tool_messages & ToolPaired Recovery --- *)

Definition lead_tool_cut : set -> set :=
  fun s => Eps_i (fun d => d :e ordsucc (seq_len s) /\
    (forall j :e d, msg_role (seq_at s j) = RoleTool) /\
    (d = seq_len s \/ msg_role (seq_at s d) <> RoleTool)).

Theorem lead_tool_cut_spec : forall s, ValidSeq s ->
  lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
let s. assume Hs.
claim Hex : exists d, d :e ordsucc (seq_len s) /\
  (forall j :e d, msg_role (seq_at s j) = RoleTool) /\
  (d = seq_len s \/ msg_role (seq_at s d) <> RoleTool).
{ apply nat_least_witness (fun j => msg_role (seq_at s j) <> RoleTool) (seq_len s) Hs.
  let d. assume Hd. apply Hd. assume Hdin Hrest. apply Hrest. assume Hall Hor.
  witness d. apply andI.
  - apply andI.
    + exact Hdin.
    + let j. assume Hj.
      apply xm (msg_role (seq_at s j) = RoleTool).
      * assume H : msg_role (seq_at s j) = RoleTool. exact H.
      * assume Hne : msg_role (seq_at s j) <> RoleTool. apply FalseE. exact Hall j Hj Hne.
  - exact Hor. }
exact Eps_i_ex (fun d => d :e ordsucc (seq_len s) /\
  (forall j :e d, msg_role (seq_at s j) = RoleTool) /\
  (d = seq_len s \/ msg_role (seq_at s d) <> RoleTool)) Hex.
Qed.

Theorem lead_tool_cut_eq : forall s, ValidSeq s -> forall d :e ordsucc (seq_len s),
  (forall j :e d, msg_role (seq_at s j) = RoleTool) ->
  (d = seq_len s \/ msg_role (seq_at s d) <> RoleTool) ->
  lead_tool_cut s = d.
let s. assume Hs. let d. assume Hdin Hall Hor.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 Hcor. apply Hc12. assume Hcin Hcall.
apply nat_least_witness_unique (fun j => msg_role (seq_at s j) <> RoleTool) (seq_len s) Hs (lead_tool_cut s) Hcin d Hdin.
- apply andI.
  + let j. assume Hj Hne. exact Hne (Hcall j Hj).
  + exact Hcor.
- apply andI.
  + let j. assume Hj Hne. exact Hne (Hall j Hj).
  + exact Hor.
Qed.

Definition drop_leading_tools : set -> set :=
  fun s => seq_drop (lead_tool_cut s) s.

Theorem drop_leading_tools_valid : forall s, ValidSeq s -> ValidSeq (drop_leading_tools s).
let s. assume Hs.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
claim Hco : lead_tool_cut s :e omega. { exact nat_In_omega (ordsucc (seq_len s)) (omega_ordsucc (seq_len s) Hs) (lead_tool_cut s) Hcin. }
claim Hcle : lead_tool_cut s <= seq_len s. { exact nat_In_ordsucc_Le (seq_len s) Hs (lead_tool_cut s) Hcin. }
exact ValidSeq_mk (seq_len s + - lead_tool_cut s) (nat_sub_omega (lead_tool_cut s) Hco (seq_len s) Hs Hcle)
      (fun i => seq_at s (lead_tool_cut s + i)).
Qed.

Theorem drop_leading_tools_len_le : forall s, ValidSeq s -> seq_len (drop_leading_tools s) <= seq_len s.
let s. assume Hs.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
claim Hco : lead_tool_cut s :e omega. { exact nat_In_omega (ordsucc (seq_len s)) (omega_ordsucc (seq_len s) Hs) (lead_tool_cut s) Hcin. }
claim Hcle : lead_tool_cut s <= seq_len s. { exact nat_In_ordsucc_Le (seq_len s) Hs (lead_tool_cut s) Hcin. }
prove seq_len (Seq (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i))) <= seq_len s.
rewrite seq_len_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)).
exact nat_sub_Le (seq_len s) Hs (lead_tool_cut s) Hco Hcle.
Qed.

Theorem drop_leading_tools_NoLeadingTool : forall s, ValidSeq s -> NoLeadingTool (drop_leading_tools s).
let s. assume Hs.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 Hcor. apply Hc12. assume Hcin Hcall.
claim Hco : lead_tool_cut s :e omega. { exact nat_In_omega (ordsucc (seq_len s)) (omega_ordsucc (seq_len s) Hs) (lead_tool_cut s) Hcin. }
claim Hcle : lead_tool_cut s <= seq_len s. { exact nat_In_ordsucc_Le (seq_len s) Hs (lead_tool_cut s) Hcin. }
claim Hlen : seq_len (drop_leading_tools s) = seq_len s + - lead_tool_cut s.
{ exact seq_len_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)). }
apply Hcor.
- assume Heq : lead_tool_cut s = seq_len s.
  prove seq_len (drop_leading_tools s) = 0 \/ msg_role (seq_at (drop_leading_tools s) 0) <> RoleTool.
  apply orIL.
  rewrite Hlen. rewrite Heq.
  exact add_SNo_minus_SNo_rinv (seq_len s) (omega_SNo (seq_len s) Hs).
- assume Hne : msg_role (seq_at s (lead_tool_cut s)) <> RoleTool.
  apply xm (seq_len (drop_leading_tools s) = 0).
  + assume H0 : seq_len (drop_leading_tools s) = 0.
    exact orIL (seq_len (drop_leading_tools s) = 0) (msg_role (seq_at (drop_leading_tools s) 0) <> RoleTool) H0.
  + assume Hne0 : seq_len (drop_leading_tools s) <> 0.
    prove seq_len (drop_leading_tools s) = 0 \/ msg_role (seq_at (drop_leading_tools s) 0) <> RoleTool.
    apply orIR.
    claim Hsub : seq_len s + - lead_tool_cut s :e omega. { exact nat_sub_omega (lead_tool_cut s) Hco (seq_len s) Hs Hcle. }
    claim H0in : 0 :e seq_len s + - lead_tool_cut s.
    { apply nat_SNoLe_cases 0 nat_0_omega (seq_len s + - lead_tool_cut s) Hsub (nat_0_Le (seq_len s + - lead_tool_cut s) Hsub).
      - assume H : 0 :e seq_len s + - lead_tool_cut s. exact H.
      - assume H0 : 0 = seq_len s + - lead_tool_cut s.
        apply FalseE. apply Hne0. rewrite Hlen. symmetry. exact H0. }
    prove msg_role (seq_at (Seq (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i))) 0) <> RoleTool.
    rewrite seq_at_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)) 0 H0in.
    rewrite add_SNo_0R (lead_tool_cut s) (omega_SNo (lead_tool_cut s) Hco).
    exact Hne.
Qed.

Theorem drop_leading_tools_idempotent : forall s, ValidSeq s ->
  drop_leading_tools (drop_leading_tools s) = drop_leading_tools s.
let s. assume Hs.
claim Ht : ValidSeq (drop_leading_tools s). { exact drop_leading_tools_valid s Hs. }
claim Hnlt : NoLeadingTool (drop_leading_tools s). { exact drop_leading_tools_NoLeadingTool s Hs. }
claim Hcut0 : lead_tool_cut (drop_leading_tools s) = 0.
{ apply lead_tool_cut_eq (drop_leading_tools s) Ht 0 (nat_Le_In_ordsucc 0 nat_0_omega (seq_len (drop_leading_tools s)) Ht (nat_0_Le (seq_len (drop_leading_tools s)) Ht)).
  - let j. assume Hj. apply FalseE. exact EmptyE j Hj.
  - apply Hnlt.
    + assume H0 : seq_len (drop_leading_tools s) = 0. apply orIL. symmetry. exact H0.
    + assume Hne : msg_role (seq_at (drop_leading_tools s) 0) <> RoleTool. apply orIR. exact Hne. }
claim Hlen : seq_len (drop_leading_tools s) + - 0 = seq_len (drop_leading_tools s).
{ rewrite minus_SNo_0. exact add_SNo_0R (seq_len (drop_leading_tools s)) (omega_SNo (seq_len (drop_leading_tools s)) Ht). }
prove setsum (seq_len (drop_leading_tools s) + - lead_tool_cut (drop_leading_tools s))
             (fun i :e seq_len (drop_leading_tools s) + - lead_tool_cut (drop_leading_tools s) =>
               seq_at (drop_leading_tools s) (lead_tool_cut (drop_leading_tools s) + i))
    = drop_leading_tools s.
rewrite Hcut0. rewrite Hlen.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
claim Hco : lead_tool_cut s :e omega. { exact nat_In_omega (ordsucc (seq_len s)) (omega_ordsucc (seq_len s) Hs) (lead_tool_cut s) Hcin. }
claim Hcle : lead_tool_cut s <= seq_len s. { exact nat_In_ordsucc_Le (seq_len s) Hs (lead_tool_cut s) Hcin. }
claim Hn' : seq_len (drop_leading_tools s) = seq_len s + - lead_tool_cut s.
{ exact seq_len_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)). }
claim Hlam : (fun i :e seq_len (drop_leading_tools s) => seq_at (drop_leading_tools s) (0 + i))
           = (fun i :e seq_len s + - lead_tool_cut s => seq_at s (lead_tool_cut s + i)).
{ rewrite Hn'.
  apply lam_ext (seq_len s + - lead_tool_cut s).
  let i. assume Hi.
  claim Hio : i :e omega. { exact nat_In_omega (seq_len s + - lead_tool_cut s) (nat_sub_omega (lead_tool_cut s) Hco (seq_len s) Hs Hcle) i Hi. }
  prove seq_at (drop_leading_tools s) (0 + i) = seq_at s (lead_tool_cut s + i).
  rewrite add_SNo_0L i (omega_SNo i Hio).
  exact seq_at_mk (seq_len s + - lead_tool_cut s) (fun j => seq_at s (lead_tool_cut s + j)) i Hi. }
rewrite Hlam. rewrite Hn'. reflexivity.
Qed.

(** Checkpoint prefix take preserves ToolPaired *)
Theorem seq_take_preserves_ToolPaired : forall s, ValidSeq s -> forall k :e omega, k <= seq_len s ->
  ToolPaired s -> ToolPaired (seq_take k s).
let s. assume Hs. let k. assume Hk Hkle Htp.
let i. assume Hi Htool.
claim Hik : i :e k. { rewrite <- seq_len_mk k (fun j => seq_at s j). exact Hi. }
claim Hio : i :e omega. { exact nat_In_omega k Hk i Hik. }
claim Hin : i :e seq_len s.
{ exact nat_SNoLt_In (seq_len s) Hs i Hio (SNoLtLe_tra i k (seq_len s) (omega_SNo i Hio) (omega_SNo k Hk) (omega_SNo (seq_len s) Hs) (nat_In_SNoLt k Hk i Hik) Hkle). }
claim Htool' : msg_role (seq_at s i) = RoleTool.
{ rewrite <- seq_at_mk k (fun j => seq_at s j) i Hik. exact Htool. }
apply Htp i Hin Htool'. assume Hpos Hex.
apply andI.
- exact Hpos.
- apply Hex. let p. assume Hp. apply Hp. assume Hpo Hp2. apply Hp2. assume Hip Hor.
  claim Hpk : p :e k.
  { apply nat_SNoLt_In k Hk p Hpo.
    apply SNoLt_tra p i k (omega_SNo p Hpo) (omega_SNo i Hio) (omega_SNo k Hk).
    - rewrite Hip. rewrite <- add_SNo_0R p (omega_SNo p Hpo) at 1.
      exact add_SNo_Lt2 p 0 1 (omega_SNo p Hpo) SNo_0 SNo_1 SNoLt_0_1.
    - exact nat_In_SNoLt k Hk i Hik. }
  witness p. apply andI.
  + exact Hpo.
  + apply andI.
    * exact Hip.
    * claim Hatp : seq_at (seq_take k s) p = seq_at s p. { exact seq_at_mk k (fun j => seq_at s j) p Hpk. }
      rewrite Hatp. exact Hor.
Qed.

(** MAIN THEOREM: Arbitrary prefix drop followed by drop_leading_tools ALWAYS restores ToolPaired! *)
Theorem drop_then_strip_preserves_ToolPaired : forall s, ValidSeq s -> forall d :e omega, d <= seq_len s ->
  ToolPaired s -> ToolPaired (drop_leading_tools (seq_drop d s)).
let s. assume Hs. let d. assume Hd Hdle Htp.
claim Hsub_o : seq_len s + - d :e omega. { exact nat_sub_omega d Hd (seq_len s) Hs Hdle. }
claim Hds : ValidSeq (seq_drop d s). { exact ValidSeq_mk (seq_len s + - d) Hsub_o (fun i => seq_at s (d + i)). }
claim Hnlt : NoLeadingTool (drop_leading_tools (seq_drop d s)). { exact drop_leading_tools_NoLeadingTool (seq_drop d s) Hds. }
claim Hspec : lead_tool_cut (seq_drop d s) :e ordsucc (seq_len (seq_drop d s)) /\
  (forall j :e lead_tool_cut (seq_drop d s), msg_role (seq_at (seq_drop d s) j) = RoleTool) /\
  (lead_tool_cut (seq_drop d s) = seq_len (seq_drop d s) \/ msg_role (seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s))) <> RoleTool).
{ exact lead_tool_cut_spec (seq_drop d s) Hds. }
apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
claim Hco : lead_tool_cut (seq_drop d s) :e omega.
{ exact nat_In_omega (ordsucc (seq_len (seq_drop d s))) (omega_ordsucc (seq_len (seq_drop d s)) Hds) (lead_tool_cut (seq_drop d s)) Hcin. }
claim Hcle : lead_tool_cut (seq_drop d s) <= seq_len (seq_drop d s).
{ exact nat_In_ordsucc_Le (seq_len (seq_drop d s)) Hds (lead_tool_cut (seq_drop d s)) Hcin. }
claim Hds_len : seq_len (seq_drop d s) = seq_len s + - d. { exact seq_len_mk (seq_len s + - d) (fun i => seq_at s (d + i)). }
claim Hfin_v : ValidSeq (drop_leading_tools (seq_drop d s)). { exact drop_leading_tools_valid (seq_drop d s) Hds. }
claim Hfin_len : seq_len (drop_leading_tools (seq_drop d s)) = seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s).
{ exact seq_len_mk (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun i => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + i)). }
let i. assume Hi Htool.
claim Hio : i :e omega. { exact nat_In_omega (seq_len (drop_leading_tools (seq_drop d s))) Hfin_v i Hi. }
claim Hipos : 0 < i.
{ apply nat_SNoLe_cases 0 nat_0_omega i Hio (nat_0_Le i Hio).
  - assume H0i : 0 :e i. exact nat_In_SNoLt i Hio 0 H0i.
  - assume H0eq : 0 = i.
    apply FalseE.
    apply Hnlt.
    + assume Hlen0 : seq_len (drop_leading_tools (seq_drop d s)) = 0.
      claim Hie : i :e 0. { rewrite <- Hlen0. exact Hi. }
      exact EmptyE i Hie.
    + assume Hne0 : msg_role (seq_at (drop_leading_tools (seq_drop d s)) 0) <> RoleTool.
      apply Hne0. rewrite H0eq. exact Htool. }
apply nat_pos_pred i Hio Hipos. let k. assume Hk. apply Hk. assume Hko Hik.
claim Hki_in : k :e seq_len (drop_leading_tools (seq_drop d s)).
{ apply nat_SNoLt_In (seq_len (drop_leading_tools (seq_drop d s))) Hfin_v k Hko.
  apply SNoLt_tra k i (seq_len (drop_leading_tools (seq_drop d s))) (omega_SNo k Hko) (omega_SNo i Hio) (omega_SNo (seq_len (drop_leading_tools (seq_drop d s))) Hfin_v).
  - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
    exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
  - exact nat_In_SNoLt (seq_len (drop_leading_tools (seq_drop d s))) Hfin_v i Hi. }
claim Hi_sub : i :e seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s).
{ rewrite <- Hfin_len. exact Hi. }
claim Hk_sub : k :e seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s).
{ rewrite <- Hfin_len. exact Hki_in. }
claim Hci_in : lead_tool_cut (seq_drop d s) + i :e seq_len (seq_drop d s).
{ exact nat_In_sub_add (seq_len (seq_drop d s)) Hds (lead_tool_cut (seq_drop d s)) Hco Hcle i Hi_sub. }
claim Hck_in : lead_tool_cut (seq_drop d s) + k :e seq_len (seq_drop d s).
{ exact nat_In_sub_add (seq_len (seq_drop d s)) Hds (lead_tool_cut (seq_drop d s)) Hco Hcle k Hk_sub. }
claim Hci_sub : lead_tool_cut (seq_drop d s) + i :e seq_len s + - d. { rewrite <- Hds_len. exact Hci_in. }
claim Hck_sub : lead_tool_cut (seq_drop d s) + k :e seq_len s + - d. { rewrite <- Hds_len. exact Hck_in. }
claim Hdci_in : d + (lead_tool_cut (seq_drop d s) + i) :e seq_len s.
{ exact nat_In_sub_add (seq_len s) Hs d Hd Hdle (lead_tool_cut (seq_drop d s) + i) Hci_sub. }
claim Hat_i : seq_at (drop_leading_tools (seq_drop d s)) i = seq_at s (d + (lead_tool_cut (seq_drop d s) + i)).
{ prove seq_at (Seq (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun j => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + j))) i
      = seq_at s (d + (lead_tool_cut (seq_drop d s) + i)).
  rewrite seq_at_mk (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun j => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + j)) i Hi_sub.
  exact seq_at_mk (seq_len s + - d) (fun j => seq_at s (d + j)) (lead_tool_cut (seq_drop d s) + i) Hci_sub. }
claim Hat_k : seq_at (drop_leading_tools (seq_drop d s)) k = seq_at s (d + (lead_tool_cut (seq_drop d s) + k)).
{ prove seq_at (Seq (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun j => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + j))) k
      = seq_at s (d + (lead_tool_cut (seq_drop d s) + k)).
  rewrite seq_at_mk (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun j => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + j)) k Hk_sub.
  exact seq_at_mk (seq_len s + - d) (fun j => seq_at s (d + j)) (lead_tool_cut (seq_drop d s) + k) Hck_sub. }
claim Htool_s : msg_role (seq_at s (d + (lead_tool_cut (seq_drop d s) + i))) = RoleTool.
{ rewrite <- Hat_i. exact Htool. }
apply Htp (d + (lead_tool_cut (seq_drop d s) + i)) Hdci_in Htool_s. assume Hpos_s Hex_s.
apply Hex_s. let p. assume Hp. apply Hp. assume Hpo Hp2. apply Hp2. assume Heqp Hor_s.
claim Hidx_eq : d + (lead_tool_cut (seq_drop d s) + i) = (d + (lead_tool_cut (seq_drop d s) + k)) + 1.
{ rewrite Hik.
  rewrite add_SNo_assoc (lead_tool_cut (seq_drop d s)) k 1 (omega_SNo (lead_tool_cut (seq_drop d s)) Hco) (omega_SNo k Hko) SNo_1.
  exact add_SNo_assoc d (lead_tool_cut (seq_drop d s) + k) 1 (omega_SNo d Hd) (omega_SNo (lead_tool_cut (seq_drop d s) + k) (nat_add_omega (lead_tool_cut (seq_drop d s)) Hco k Hko)) SNo_1. }
claim Hpeq : p = d + (lead_tool_cut (seq_drop d s) + k).
{ apply SNo_add_cancel_R p (d + (lead_tool_cut (seq_drop d s) + k)) 1
        (omega_SNo p Hpo) (omega_SNo (d + (lead_tool_cut (seq_drop d s) + k)) (nat_add_omega d Hd (lead_tool_cut (seq_drop d s) + k) (nat_add_omega (lead_tool_cut (seq_drop d s)) Hco k Hko))) SNo_1.
  rewrite <- Heqp. exact Hidx_eq. }
apply andI.
- exact Hipos.
- witness k. apply andI.
  + exact Hko.
  + apply andI.
    * exact Hik.
    * rewrite Hat_k. rewrite <- Hpeq. exact Hor_s.
Qed.

(** ---- Theorem Group 3: Iter Windowing Bound (MAX=100, RETAIN=80) ---------- *)

Definition window_trim : set -> set -> set -> set :=
  fun M R s => if M <= seq_len s then seq_drop (seq_len s + - R) s else s.

Definition hygiene_step : set -> set -> set -> set :=
  fun M R s => drop_leading_tools (window_trim M R s).

Theorem hygiene_step_bounded_and_paired : forall M :e omega, forall R :e omega, R < M ->
  forall s, ValidSeq s -> ToolPaired s ->
  ValidSeq (hygiene_step M R s) /\ seq_len (hygiene_step M R s) < M /\ ToolPaired (hygiene_step M R s).
let M. assume HM. let R. assume HR HRM. let s. assume Hs Htp.
apply xm (M <= seq_len s).
- assume Hge : M <= seq_len s.
  claim Htrim : window_trim M R s = seq_drop (seq_len s + - R) s.
  { exact If_i_1 (M <= seq_len s) (seq_drop (seq_len s + - R) s) s Hge. }
  claim HRle : R <= seq_len s.
  { exact SNoLtLe R (seq_len s) (SNoLtLe_tra R M (seq_len s) (omega_SNo R HR) (omega_SNo M HM) (omega_SNo (seq_len s) Hs) HRM Hge). }
  claim Hd_o : seq_len s + - R :e omega. { exact nat_sub_omega R HR (seq_len s) Hs HRle. }
  claim Hd_le : seq_len s + - R <= seq_len s. { exact nat_sub_Le (seq_len s) Hs R HR HRle. }
  claim Hw_len : seq_len (seq_drop (seq_len s + - R) s) = R.
  { prove seq_len (Seq (seq_len s + - (seq_len s + - R)) (fun i => seq_at s ((seq_len s + - R) + i))) = R.
    rewrite seq_len_mk (seq_len s + - (seq_len s + - R)) (fun i => seq_at s ((seq_len s + - R) + i)).
    rewrite minus_add_SNo_distr (seq_len s) (- R) (omega_SNo (seq_len s) Hs) (SNo_minus_SNo R (omega_SNo R HR)).
    rewrite minus_SNo_invol R (omega_SNo R HR).
    exact add_SNo_minus_L2' (seq_len s) R (omega_SNo (seq_len s) Hs) (omega_SNo R HR). }
  claim Hw_v : ValidSeq (seq_drop (seq_len s + - R) s).
  { prove seq_len (seq_drop (seq_len s + - R) s) :e omega. rewrite Hw_len. exact HR. }
  prove ValidSeq (drop_leading_tools (window_trim M R s)) /\
        seq_len (drop_leading_tools (window_trim M R s)) < M /\
        ToolPaired (drop_leading_tools (window_trim M R s)).
  rewrite Htrim.
  apply and3I.
  + exact drop_leading_tools_valid (seq_drop (seq_len s + - R) s) Hw_v.
  + apply SNoLeLt_tra (seq_len (drop_leading_tools (seq_drop (seq_len s + - R) s))) R M
          (omega_SNo (seq_len (drop_leading_tools (seq_drop (seq_len s + - R) s))) (drop_leading_tools_valid (seq_drop (seq_len s + - R) s) Hw_v))
          (omega_SNo R HR) (omega_SNo M HM).
    * rewrite <- Hw_len at 2. exact drop_leading_tools_len_le (seq_drop (seq_len s + - R) s) Hw_v.
    * exact HRM.
  + exact drop_then_strip_preserves_ToolPaired s Hs (seq_len s + - R) Hd_o Hd_le Htp.
- assume Hnge : ~(M <= seq_len s).
  claim HltM : seq_len s < M.
  { apply ordinal_trichotomy_or_impred (seq_len s) M (nat_p_ordinal (seq_len s) (omega_nat_p (seq_len s) Hs)) (nat_p_ordinal M (omega_nat_p M HM)).
    - assume H : seq_len s :e M. exact nat_In_SNoLt M HM (seq_len s) H.
    - assume H : seq_len s = M. apply FalseE. apply Hnge. rewrite H. exact SNoLe_ref M.
    - assume H : M :e seq_len s. apply FalseE. apply Hnge. exact SNoLtLe M (seq_len s) (nat_In_SNoLt (seq_len s) Hs M H). }
  claim Htrim : window_trim M R s = s.
  { exact If_i_0 (M <= seq_len s) (seq_drop (seq_len s + - R) s) s Hnge. }
  prove ValidSeq (drop_leading_tools (window_trim M R s)) /\
        seq_len (drop_leading_tools (window_trim M R s)) < M /\
        ToolPaired (drop_leading_tools (window_trim M R s)).
  rewrite Htrim.
  claim Hcut0 : lead_tool_cut s = 0.
  { apply lead_tool_cut_eq s Hs 0 (nat_Le_In_ordsucc 0 nat_0_omega (seq_len s) Hs (nat_0_Le (seq_len s) Hs)).
    - let j. assume Hj. apply FalseE. exact EmptyE j Hj.
    - apply ToolPaired_implies_NoLeadingTool s Hs Htp.
      + assume H0 : seq_len s = 0. apply orIL. symmetry. exact H0.
      + assume Hne : msg_role (seq_at s 0) <> RoleTool. apply orIR. exact Hne. }
  claim Hlen_eq : seq_len (drop_leading_tools s) = seq_len s.
  { prove seq_len (Seq (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i))) = seq_len s.
    rewrite seq_len_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)).
    rewrite Hcut0. rewrite minus_SNo_0. exact add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hs). }
  apply and3I.
  + exact drop_leading_tools_valid s Hs.
  + rewrite Hlen_eq. exact HltM.
  + let i. assume Hi Htool.
    claim Hi' : i :e seq_len s. { rewrite <- Hlen_eq. exact Hi. }
    claim Hat : forall j :e seq_len s, seq_at (drop_leading_tools s) j = seq_at s j.
    { let j. assume Hj.
      claim Hjo : j :e omega. { exact nat_In_omega (seq_len s) Hs j Hj. }
      claim Hj' : j :e seq_len s + - lead_tool_cut s.
      { rewrite Hcut0. rewrite minus_SNo_0. rewrite add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hs). exact Hj. }
      prove seq_at (Seq (seq_len s + - lead_tool_cut s) (fun u => seq_at s (lead_tool_cut s + u))) j = seq_at s j.
      rewrite seq_at_mk (seq_len s + - lead_tool_cut s) (fun u => seq_at s (lead_tool_cut s + u)) j Hj'.
      rewrite Hcut0. rewrite add_SNo_0L j (omega_SNo j Hjo). reflexivity. }
    claim Htool' : msg_role (seq_at s i) = RoleTool. { rewrite <- Hat i Hi'. exact Htool. }
    apply Htp i Hi' Htool'. assume Hpos Hex.
    apply andI.
    * exact Hpos.
    * apply Hex. let k. assume Hk. apply Hk. assume Hko Hk2. apply Hk2. assume Hik Hor.
      claim Hkin : k :e seq_len s.
      { apply nat_SNoLt_In (seq_len s) Hs k Hko.
        apply SNoLt_tra k i (seq_len s) (omega_SNo k Hko) (omega_SNo i (nat_In_omega (seq_len s) Hs i Hi')) (omega_SNo (seq_len s) Hs).
        - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
          exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
        - exact nat_In_SNoLt (seq_len s) Hs i Hi'. }
      witness k. apply andI.
      { exact Hko. }
      { apply andI.
        - exact Hik.
        - rewrite Hat k Hkin. exact Hor. }
Qed.

(** ---- Theorem Group 4: Constructive Bucket-Skip Witness (iter.metta:114-121) *)

Definition MAX_EXP : set := 5 * (10 + 10).
Definition RETAIN_EXP : set := 4 * (10 + 10).
Definition INTERVAL_EXP : set := 10 + 10.

Theorem n20_omega : INTERVAL_EXP :e omega.
exact nat_add_omega 10 (nat_p_omega 10 nat_10) 10 (nat_p_omega 10 nat_10).
Qed.

Theorem n80_omega : RETAIN_EXP :e omega.
exact nat_mul_omega 4 (nat_p_omega 4 nat_4) INTERVAL_EXP n20_omega.
Qed.

Theorem n100_omega : MAX_EXP :e omega.
exact nat_mul_omega 5 (nat_p_omega 5 nat_5) INTERVAL_EXP n20_omega.
Qed.

Theorem n100_eq_80_plus_20 : MAX_EXP = RETAIN_EXP + INTERVAL_EXP.
prove 5 * INTERVAL_EXP = 4 * INTERVAL_EXP + INTERVAL_EXP.
rewrite <- mul_nat_mul_SNo 5 (nat_p_omega 5 nat_5) INTERVAL_EXP n20_omega.
prove mul_nat (ordsucc 4) INTERVAL_EXP = 4 * INTERVAL_EXP + INTERVAL_EXP.
rewrite mul_nat_SL 4 nat_4 INTERVAL_EXP (omega_nat_p INTERVAL_EXP n20_omega).
rewrite add_nat_add_SNo (mul_nat 4 INTERVAL_EXP) (nat_p_omega (mul_nat 4 INTERVAL_EXP) (mul_nat_p 4 nat_4 INTERVAL_EXP (omega_nat_p INTERVAL_EXP n20_omega))) INTERVAL_EXP n20_omega.
rewrite mul_nat_mul_SNo 4 (nat_p_omega 4 nat_4) INTERVAL_EXP n20_omega.
reflexivity.
Qed.

Theorem n20_pos : 0 < INTERVAL_EXP.
claim H10o : 10 :e omega. { exact nat_p_omega 10 nat_10. }
claim H10p : 0 < 10.
{ exact nat_In_SNoLt 10 H10o 0 (nat_0_in_ordsucc 9 nat_9). }
prove 0 < 10 + 10.
apply SNoLt_tra 0 10 (10 + 10) SNo_0 (omega_SNo 10 H10o) (omega_SNo INTERVAL_EXP n20_omega) H10p.
rewrite <- add_SNo_0R 10 (omega_SNo 10 H10o) at 1.
exact add_SNo_Lt2 10 0 10 (omega_SNo 10 H10o) SNo_0 (omega_SNo 10 H10o) H10p.
Qed.

Theorem n80_lt_100 : RETAIN_EXP < MAX_EXP.
rewrite n100_eq_80_plus_20.
rewrite <- add_SNo_0R RETAIN_EXP (omega_SNo RETAIN_EXP n80_omega) at 1.
exact add_SNo_Lt2 RETAIN_EXP 0 INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) n20_pos.
Qed.

(** Floor bucket specification: b = floor(L / 20) iff 20b <= L < 20(b + 1) *)
Definition IsBucket20 : set -> set -> prop :=
  fun L b => b :e omega /\ b * INTERVAL_EXP <= L /\ L < (b + 1) * INTERVAL_EXP.

(** Constructive witness of the iter.metta:114-121 bucket-skip edge case:
    Build a ToolPaired history s of length 100 where index 19 is Assistant and
    index 20 is Tool (all other entries are User).
    1. window_trim 100 80 s drops 20 entries, yielding length 80 -> bucket 4 recorded.
    2. drop_leading_tools then sees Tool at new index 0 (old index 20), dropping it
       so final length is strictly < 80 (specifically 79).
    3. For EVERY subsequent length L < 100, its bucket b satisfies b <= 4, so
       cleanup_old_messages (guarded by b > 4 on line 115) CANNOT fire until L >= 100! *)
Definition witness_seq : set :=
  Seq MAX_EXP (fun i =>
    if i = INTERVAL_EXP then Msg RoleTool 0
    else Msg RoleAssistant 0).

Theorem witness_seq_valid : ValidSeq witness_seq.
exact ValidSeq_mk MAX_EXP n100_omega (fun i => if i = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0).
Qed.

Theorem witness_seq_ToolPaired : ToolPaired witness_seq.
let i. assume Hi Htool.
claim Hin : i :e MAX_EXP. { rewrite <- seq_len_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0). exact Hi. }
claim Hio : i :e omega. { exact nat_In_omega MAX_EXP n100_omega i Hin. }
claim Hi20 : i = INTERVAL_EXP.
{ apply xm (i = INTERVAL_EXP).
  - assume H : i = INTERVAL_EXP. exact H.
  - assume Hne : i <> INTERVAL_EXP.
    apply FalseE.
    claim Hat : seq_at witness_seq i = Msg RoleAssistant 0.
    { prove seq_at (Seq MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0)) i = Msg RoleAssistant 0.
      rewrite seq_at_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0) i Hin.
      exact If_i_0 (i = INTERVAL_EXP) (Msg RoleTool 0) (Msg RoleAssistant 0) Hne. }
    apply RoleAssistant_neq_Tool.
    rewrite <- msg_role_pair RoleAssistant 0.
    rewrite <- Hat. exact Htool. }
claim Hipos : 0 < i. { rewrite Hi20. exact n20_pos. }
apply nat_pos_pred i Hio Hipos. let k. assume Hk. apply Hk. assume Hko Hik.
claim Hkne : k <> INTERVAL_EXP.
{ assume Heq : k = INTERVAL_EXP.
  apply SNoLt_irref INTERVAL_EXP.
  rewrite <- Heq at 1. rewrite <- Hi20. rewrite Hik.
  rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
  exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1. }
claim Hkin : k :e MAX_EXP.
{ apply nat_SNoLt_In MAX_EXP n100_omega k Hko.
  apply SNoLt_tra k i MAX_EXP (omega_SNo k Hko) (omega_SNo i Hio) (omega_SNo MAX_EXP n100_omega).
  - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
    exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
  - exact nat_In_SNoLt MAX_EXP n100_omega i Hin. }
claim Hatk : seq_at witness_seq k = Msg RoleAssistant 0.
{ prove seq_at (Seq MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0)) k = Msg RoleAssistant 0.
  rewrite seq_at_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0) k Hkin.
  exact If_i_0 (k = INTERVAL_EXP) (Msg RoleTool 0) (Msg RoleAssistant 0) Hkne. }
apply andI.
- exact Hipos.
- witness k. apply andI.
  + exact Hko.
  + apply andI.
    * exact Hik.
    * apply orIL. rewrite Hatk. exact msg_role_pair RoleAssistant 0.
Qed.

Theorem bucket_skip_witness :
  ValidSeq witness_seq /\ ToolPaired witness_seq /\
  seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) = RETAIN_EXP /\
  IsBucket20 (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) 4 /\
  seq_len (hygiene_step MAX_EXP RETAIN_EXP witness_seq) < RETAIN_EXP /\
  (forall L :e omega, L < MAX_EXP -> forall b, IsBucket20 L b -> ~(4 < b)).
claim Hwlen : seq_len witness_seq = MAX_EXP.
{ exact seq_len_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0). }
claim Htrim : window_trim MAX_EXP RETAIN_EXP witness_seq = seq_drop INTERVAL_EXP witness_seq.
{ prove (if MAX_EXP <= seq_len witness_seq then seq_drop (seq_len witness_seq + - RETAIN_EXP) witness_seq else witness_seq)
      = seq_drop INTERVAL_EXP witness_seq.
  rewrite Hwlen.
  rewrite If_i_1 (MAX_EXP <= MAX_EXP) (seq_drop (MAX_EXP + - RETAIN_EXP) witness_seq) witness_seq (SNoLe_ref MAX_EXP).
  claim Hsub : MAX_EXP + - RETAIN_EXP = INTERVAL_EXP.
  { rewrite n100_eq_80_plus_20.
    rewrite add_SNo_com RETAIN_EXP INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) (omega_SNo INTERVAL_EXP n20_omega).
    exact add_SNo_minus_R2 INTERVAL_EXP RETAIN_EXP (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega). }
  rewrite Hsub. reflexivity. }
claim Htrim_len : seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) = RETAIN_EXP.
{ rewrite Htrim.
  prove seq_len (Seq (seq_len witness_seq + - INTERVAL_EXP) (fun i => seq_at witness_seq (INTERVAL_EXP + i))) = RETAIN_EXP.
  rewrite seq_len_mk (seq_len witness_seq + - INTERVAL_EXP) (fun i => seq_at witness_seq (INTERVAL_EXP + i)).
  rewrite Hwlen. rewrite n100_eq_80_plus_20.
  exact add_SNo_minus_R2 RETAIN_EXP INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) (omega_SNo INTERVAL_EXP n20_omega). }
claim Htrim_v : ValidSeq (window_trim MAX_EXP RETAIN_EXP witness_seq).
{ prove seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) :e omega. rewrite Htrim_len. exact n80_omega. }
claim H80_pos : 0 < RETAIN_EXP.
{ claim H4o : 4 :e omega. { exact nat_p_omega 4 nat_4. }
  claim H4p : 0 < 4. { exact nat_In_SNoLt 4 H4o 0 In_0_4. }
  exact mul_SNo_pos_pos 4 INTERVAL_EXP (omega_SNo 4 H4o) (omega_SNo INTERVAL_EXP n20_omega) H4p n20_pos. }
claim H0_in_80 : 0 :e RETAIN_EXP. { exact nat_SNoLt_In RETAIN_EXP n80_omega 0 nat_0_omega H80_pos. }
claim H20_in_100 : INTERVAL_EXP :e MAX_EXP.
{ apply nat_SNoLt_In MAX_EXP n100_omega INTERVAL_EXP n20_omega.
  rewrite n100_eq_80_plus_20.
  rewrite <- add_SNo_0L INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega) at 1.
  exact add_SNo_Lt1 0 INTERVAL_EXP RETAIN_EXP SNo_0 (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega) H80_pos. }
claim Hhead_tool : msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) 0) = RoleTool.
{ rewrite Htrim.
  claim H0_sub : 0 :e seq_len witness_seq + - INTERVAL_EXP.
  { rewrite Hwlen. rewrite n100_eq_80_plus_20.
    rewrite add_SNo_minus_R2 RETAIN_EXP INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) (omega_SNo INTERVAL_EXP n20_omega).
    exact H0_in_80. }
  prove msg_role (seq_at (Seq (seq_len witness_seq + - INTERVAL_EXP) (fun i => seq_at witness_seq (INTERVAL_EXP + i))) 0) = RoleTool.
  rewrite seq_at_mk (seq_len witness_seq + - INTERVAL_EXP) (fun i => seq_at witness_seq (INTERVAL_EXP + i)) 0 H0_sub.
  rewrite add_SNo_0R INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega).
  prove msg_role (seq_at (Seq MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0)) INTERVAL_EXP) = RoleTool.
  rewrite seq_at_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0) INTERVAL_EXP H20_in_100.
  claim Href20 : INTERVAL_EXP = INTERVAL_EXP. { reflexivity. }
  rewrite If_i_1 (INTERVAL_EXP = INTERVAL_EXP) (Msg RoleTool 0) (Msg RoleAssistant 0) Href20.
  exact msg_role_pair RoleTool 0. }
claim Hcut_pos : 0 < lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq).
{ claim Hspec : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) /\
    (forall j :e lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq), msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) j) = RoleTool) /\
    (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) = seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) \/
     msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))) <> RoleTool).
  { exact lead_tool_cut_spec (window_trim MAX_EXP RETAIN_EXP witness_seq) Htrim_v. }
  apply Hspec. assume Hc12 Hcor. apply Hc12. assume Hcin Hcall.
  claim Hco : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e omega.
  { exact nat_In_omega (ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq))) (omega_ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) Htrim_v) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hcin. }
  apply nat_SNoLe_cases 0 nat_0_omega (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco (nat_0_Le (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco).
  - assume H : 0 :e lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq).
    exact nat_In_SNoLt (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco 0 H.
  - assume H0 : 0 = lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq).
    apply FalseE.
    apply Hcor.
    + assume Heq : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) = seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq).
      apply SNoLt_irref 0.
      rewrite H0 at 2. rewrite Heq. rewrite Htrim_len. exact H80_pos.
    + assume Hne : msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))) <> RoleTool.
      apply Hne. rewrite <- H0. exact Hhead_tool. }
claim Hhyg_lt : seq_len (hygiene_step MAX_EXP RETAIN_EXP witness_seq) < RETAIN_EXP.
{ claim Hspec : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) /\
    (forall j :e lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq), msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) j) = RoleTool) /\
    (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) = seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) \/
     msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))) <> RoleTool).
  { exact lead_tool_cut_spec (window_trim MAX_EXP RETAIN_EXP witness_seq) Htrim_v. }
  apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
  claim Hco : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e omega.
  { exact nat_In_omega (ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq))) (omega_ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) Htrim_v) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hcin. }
  claim Hcle : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) <= RETAIN_EXP.
  { rewrite <- Htrim_len at 2. exact nat_In_ordsucc_Le (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) Htrim_v (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hcin. }
  claim Hsub_o : RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e omega.
  { exact nat_sub_omega (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco RETAIN_EXP n80_omega Hcle. }
  prove seq_len (Seq (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))
                     (fun i => seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) + i))) < RETAIN_EXP.
  rewrite seq_len_mk (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))
          (fun i => seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) + i)).
  rewrite Htrim_len.
  rewrite <- SNo_add_sub_L RETAIN_EXP (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) (omega_SNo RETAIN_EXP n80_omega) (omega_SNo (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco) at 3.
  rewrite <- add_SNo_0L (RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) (omega_SNo (RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hsub_o) at 1.
  exact add_SNo_Lt1 0 (RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))
        SNo_0 (omega_SNo (RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hsub_o)
        (omega_SNo (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco) Hcut_pos. }
claim H5_eq : 4 + 1 = 5.
{ symmetry. exact ordsucc_eq_add_1 4 (nat_p_omega 4 nat_4). }
apply andI.
- apply andI.
  + apply andI.
    * apply andI.
      { apply andI.
        - exact witness_seq_valid.
        - exact witness_seq_ToolPaired. }
      { exact Htrim_len. }
    * rewrite Htrim_len.
      prove 4 :e omega /\ 4 * INTERVAL_EXP <= RETAIN_EXP /\ RETAIN_EXP < (4 + 1) * INTERVAL_EXP.
      rewrite H5_eq.
      apply and3I.
      { exact nat_p_omega 4 nat_4. }
      { exact SNoLe_ref RETAIN_EXP. }
      { exact n80_lt_100. }
  + exact Hhyg_lt.
- let L. assume HL Hlt100. let b. assume Hb H4b.
  apply Hb. assume Hbo1 Hltb. apply Hbo1. assume Hbo Hble.
  claim H5le : 5 <= b. { rewrite <- H5_eq. exact nat_SNoLt_S_Le 4 (nat_p_omega 4 nat_4) b Hbo H4b. }
  claim H100le : MAX_EXP <= b * INTERVAL_EXP.
  { prove 5 * INTERVAL_EXP <= b * INTERVAL_EXP.
    claim Hd_o : b + - 5 :e omega. { exact nat_sub_omega 5 (nat_p_omega 5 nat_5) b Hbo H5le. }
    claim Hdeq : b = 5 + (b + - 5). { symmetry. exact SNo_add_sub_L b 5 (omega_SNo b Hbo) (omega_SNo 5 (nat_p_omega 5 nat_5)). }
    claim Hprod_nn : 0 <= (b + - 5) * INTERVAL_EXP.
    { exact nat_0_Le ((b + - 5) * INTERVAL_EXP) (nat_mul_omega (b + - 5) Hd_o INTERVAL_EXP n20_omega). }
    rewrite Hdeq.
    rewrite mul_SNo_distrR 5 (b + - 5) INTERVAL_EXP (omega_SNo 5 (nat_p_omega 5 nat_5)) (omega_SNo (b + - 5) Hd_o) (omega_SNo INTERVAL_EXP n20_omega).
    rewrite <- add_SNo_0R (5 * INTERVAL_EXP) (omega_SNo MAX_EXP n100_omega) at 1.
    exact add_SNo_Le2 (5 * INTERVAL_EXP) 0 ((b + - 5) * INTERVAL_EXP) (omega_SNo MAX_EXP n100_omega) SNo_0
          (omega_SNo ((b + - 5) * INTERVAL_EXP) (nat_mul_omega (b + - 5) Hd_o INTERVAL_EXP n20_omega)) Hprod_nn. }
  claim H100leL : MAX_EXP <= L.
  { exact SNoLe_tra MAX_EXP (b * INTERVAL_EXP) L (omega_SNo MAX_EXP n100_omega) (omega_SNo (b * INTERVAL_EXP) (nat_mul_omega b Hbo INTERVAL_EXP n20_omega)) (omega_SNo L HL) H100le Hble. }
  exact SNoLt_irref L (SNoLtLe_tra L MAX_EXP L (omega_SNo L HL) (omega_SNo MAX_EXP n100_omega) (omega_SNo L HL) Hlt100 H100leL).
Qed.

Theorem post_strip_bucket_fires_at_retain :
  forall L :e omega, L < RETAIN_EXP ->
  forall b, IsBucket20 L b -> b < 4 /\ IsBucket20 RETAIN_EXP 4.
let L. assume HL Hlt80. let b. assume Hb.
apply Hb. assume Hbo1 _. apply Hbo1. assume Hbo Hble.
claim H5_eq : 4 + 1 = 5.
{ symmetry. exact ordsucc_eq_add_1 4 (nat_p_omega 4 nat_4). }
apply andI.
- apply SNoLtLe_or b 4 (omega_SNo b Hbo) (omega_SNo 4 (nat_p_omega 4 nat_4)).
  + assume H : b < 4. exact H.
  + assume H4le : 4 <= b.
    apply FalseE.
    claim Hd_o : b + - 4 :e omega. { exact nat_sub_omega 4 (nat_p_omega 4 nat_4) b Hbo H4le. }
    claim Hdeq : b = 4 + (b + - 4). { symmetry. exact SNo_add_sub_L b 4 (omega_SNo b Hbo) (omega_SNo 4 (nat_p_omega 4 nat_4)). }
    claim Hprod_nn : 0 <= (b + - 4) * INTERVAL_EXP.
    { exact nat_0_Le ((b + - 4) * INTERVAL_EXP) (nat_mul_omega (b + - 4) Hd_o INTERVAL_EXP n20_omega). }
    claim H80le : RETAIN_EXP <= b * INTERVAL_EXP.
    { prove 4 * INTERVAL_EXP <= b * INTERVAL_EXP.
      rewrite Hdeq.
      rewrite mul_SNo_distrR 4 (b + - 4) INTERVAL_EXP (omega_SNo 4 (nat_p_omega 4 nat_4)) (omega_SNo (b + - 4) Hd_o) (omega_SNo INTERVAL_EXP n20_omega).
      rewrite <- add_SNo_0R (4 * INTERVAL_EXP) (omega_SNo RETAIN_EXP n80_omega) at 1.
      exact add_SNo_Le2 (4 * INTERVAL_EXP) 0 ((b + - 4) * INTERVAL_EXP) (omega_SNo RETAIN_EXP n80_omega) SNo_0
            (omega_SNo ((b + - 4) * INTERVAL_EXP) (nat_mul_omega (b + - 4) Hd_o INTERVAL_EXP n20_omega)) Hprod_nn. }
    claim H80leL : RETAIN_EXP <= L.
    { exact SNoLe_tra RETAIN_EXP (b * INTERVAL_EXP) L (omega_SNo RETAIN_EXP n80_omega) (omega_SNo (b * INTERVAL_EXP) (nat_mul_omega b Hbo INTERVAL_EXP n20_omega)) (omega_SNo L HL) H80le Hble. }
    exact SNoLt_irref L (SNoLtLe_tra L RETAIN_EXP L (omega_SNo L HL) (omega_SNo RETAIN_EXP n80_omega) (omega_SNo L HL) Hlt80 H80leL).
- prove 4 :e omega /\ 4 * INTERVAL_EXP <= RETAIN_EXP /\ RETAIN_EXP < (4 + 1) * INTERVAL_EXP.
  rewrite H5_eq.
  apply and3I.
  + exact nat_p_omega 4 nat_4.
  + exact SNoLe_ref RETAIN_EXP.
  + exact n80_lt_100.
Qed.

End IterExperienceHygiene.
