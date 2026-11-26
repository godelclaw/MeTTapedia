(** Negative control for Module 1: claims the earlier waiter rule never sleeps
    zero with less than one unit left. The earlier rule allows exactly that, so
    this document must not verify. *)

Section MailWaitOldRuleControl.

Definition OldDelay : set -> set -> set -> set -> prop :=
  fun M R B d => (d <= R /\ d <= B) /\ (d = 0 \/ M <= d).

Theorem old_rule_never_sleeps_zero :
  forall M R B d, SNo M -> SNo R -> SNo d -> 0 < R -> R < M -> OldDelay M R B d -> 0 < d.
let M R B d. assume HM HR Hd HR0 HRM HOD.
apply HOD. assume H12 H3. apply H12. assume HdR HdB.
exact SNoLtLe_tra 0 R d SNo_0 HR Hd HR0 HdR.
Qed.

End MailWaitOldRuleControl.
