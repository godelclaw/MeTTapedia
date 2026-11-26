(** ============================================================================
   Mail waiter deadlines - Module 1
   A waiter with a finite deadline retries transient failures. Its clock and
   its sleeps have a resolution M (one millisecond), and a sleep may end up to
   E < M early. Quantities are surreal numbers, so the results hold for any
   units in which M and E are measured.

   The rule: a retry sleeps at least min(backoff, remaining) (rounded up to the
   resolution), and less than M left is the deadline. Then
     - a retry whose sleep was cut short to the deadline is the last one;
     - every other retry spends at least backoff - E;
     - no retry before the deadline sleeps less than M.
   The earlier rule slept min(backoff, remaining) rounded down and counted only
   nothing left as the deadline. With less than M left that sleep is zero while
   the waiter is not expired: retries without waiting, the burst it showed.

   Target: the claw-mail waiter's retry loop (cm:wait-loop, cm:expired?).
   Checked natively by CeTTa's Megalodon kernel against the standard Egal
   preamble. Zero document axioms. Zero admitted. Zero aby.
   ============================================================================ *)

Section MailWaitDeadline.

Infix + 360 right := add_SNo.

(** A sleep chosen by the rule: at least the remaining time when the backoff
    would overshoot the deadline, otherwise at least the backoff. *)
Definition NewDelay : set -> set -> set -> prop :=
  fun R B d => (R <= B -> R <= d) /\ (B < R -> B <= d).

(** A sleep of d that elapsed w, ending at most E early. *)
Definition EarlyWake : set -> set -> set -> prop := fun d w E => d <= w + E.

(** Less than one unit of resolution left is the deadline. *)
Definition Expired : set -> set -> prop := fun M R => R < M.

(** The earlier rule: a whole number of resolution units, rounded down. *)
Definition OldDelay : set -> set -> set -> set -> prop :=
  fun M R B d => (d <= R /\ d <= B) /\ (d = 0 \/ M <= d).

Theorem wait_clamped_retry_spends_the_rest :
  forall R B d w E M, SNo R -> SNo B -> SNo d -> SNo w -> SNo E -> SNo M ->
  R <= B -> NewDelay R B d -> EarlyWake d w E -> E < M -> R < w + M.
let R B d w E M. assume HR HB Hd Hw HE HM HRB HND Hwake HEM.
claim HRd : R <= d. { apply HND. assume H1 H2. exact H1 HRB. }
claim HwE : SNo (w + E). { exact SNo_add_SNo w E Hw HE. }
claim HwM : SNo (w + M). { exact SNo_add_SNo w M Hw HM. }
claim Hlt : w + E < w + M. { exact add_SNo_Lt2 w E M Hw HE HM HEM. }
claim HRwE : R <= w + E. { exact SNoLe_tra R d (w + E) HR Hd HwE HRd Hwake. }
exact SNoLeLt_tra R (w + E) (w + M) HR HwE HwM HRwE Hlt.
Qed.

(** After a sleep cut short to the deadline, what is left is under one unit:
    the waiter stops instead of retrying again. *)
Theorem wait_clamped_retry_is_the_last :
  forall R R2 B d w E M, SNo R -> SNo R2 -> SNo B -> SNo d -> SNo w -> SNo E -> SNo M ->
  R <= B -> NewDelay R B d -> EarlyWake d w E -> E < M -> R = R2 + w -> Expired M R2.
let R R2 B d w E M. assume HR HR2 HB Hd Hw HE HM HRB HND Hwake HEM Hsplit.
claim Hspent : R < w + M. { exact wait_clamped_retry_spends_the_rest R B d w E M HR HB Hd Hw HE HM HRB HND Hwake HEM. }
claim Hcom : R2 + w = w + R2. { exact add_SNo_com R2 w HR2 Hw. }
claim Hlt : w + R2 < w + M.
{ rewrite <- Hcom. rewrite <- Hsplit. exact Hspent. }
exact add_SNo_Lt2_cancel w R2 M Hw HR2 HM Hlt.
Qed.

Theorem wait_unclamped_retry_spends_the_backoff :
  forall R B d w E, SNo R -> SNo B -> SNo d -> SNo w -> SNo E ->
  B < R -> NewDelay R B d -> EarlyWake d w E -> B <= w + E.
let R B d w E. assume HR HB Hd Hw HE HBR HND Hwake.
claim HBd : B <= d. { apply HND. assume H1 H2. exact H2 HBR. }
exact SNoLe_tra B d (w + E) HB Hd (SNo_add_SNo w E Hw HE) HBd Hwake.
Qed.

(** Before the deadline, with a backoff of at least one unit, no retry sleeps
    less than one unit. *)
Theorem wait_never_sleeps_less_than_a_unit :
  forall R B d M, SNo R -> SNo B -> SNo d -> SNo M ->
  ~ Expired M R -> M <= B -> NewDelay R B d -> M <= d.
let R B d M. assume HR HB Hd HM Hlive HMB HND.
claim HMR : M <= R.
{ apply SNoLtLe_or R M HR HM.
  - assume H : R < M. apply FalseE. exact Hlive H.
  - assume H : M <= R. exact H. }
apply HND. assume H1 H2.
apply SNoLtLe_or B R HB HR.
- assume HBR : B < R. exact SNoLe_tra M B d HM HB Hd HMB (H2 HBR).
- assume HRB : R <= B. exact SNoLe_tra M R d HM HR Hd HMR (H1 HRB).
Qed.

(** The earlier rule: with less than one unit left, the only sleep it allows is
    zero. *)
Theorem wait_old_rule_forces_a_zero_sleep :
  forall M R B d, SNo M -> SNo R -> SNo d -> R < M -> OldDelay M R B d -> d = 0.
let M R B d. assume HM HR Hd HRM HOD.
apply HOD. assume H12 H3. apply H12. assume HdR HdB.
apply H3.
- assume Hz : d = 0. exact Hz.
- assume HMd : M <= d. apply FalseE.
  claim HdM : d < M. { exact SNoLeLt_tra d R M Hd HR HM HdR HRM. }
  exact SNoLt_irref M (SNoLeLt_tra M d M HM Hd HM HMd HdM).
Qed.

(** ... and that zero sleep happens while the earlier rule's waiter is not
    expired (only nothing left counted as the deadline): it retries again at
    once, the burst the earlier rule showed. *)
Theorem wait_old_rule_retries_without_waiting :
  forall M R B, SNo M -> SNo R -> SNo B -> 0 <= B -> 0 < R -> R < M ->
  OldDelay M R B 0 /\ ~ (R <= 0).
let M R B. assume HM HR HB HB0 HR0 HRM.
apply andI.
- prove (0 <= R /\ 0 <= B) /\ (0 = 0 \/ M <= 0).
  apply andI.
  + apply andI.
    * exact SNoLtLe 0 R HR0.
    * exact HB0.
  + apply orIL. reflexivity.
- assume HRle : R <= 0.
  exact SNoLt_irref 0 (SNoLtLe_tra 0 R 0 SNo_0 HR SNo_0 HR0 HRle).
Qed.

End MailWaitDeadline.
