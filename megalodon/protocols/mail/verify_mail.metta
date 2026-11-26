;; ============================================================================
;; Mail protocol Megalodon modules: verification runner
;;
;; Run from the MeTTapedia repository root:
;;   cetta --lang petta megalodon/protocols/mail/verify_mail.metta
;;
;; Checks each module against the standard Egal preamble with CeTTa's native
;; Megalodon kernel and audits every verdict: all theorems verified, zero
;; document axioms, zero admitted, zero aby, zero dependent, zero unfinished,
;; zero out of budget. A negative control states the earlier waiter rule as if
;; it had no zero-sleep retry and must be rejected.
;; ============================================================================

!(import! &self (library megalodon))
!(import! &self (library system))

(= (mail-verify:preamble) ("megalodon/ramsey36/preamble.mgs"))

(= (mail-verify:fail $msg)
   (let $_ (println! (MailVerifyFailed $msg)) (system:exit 1)))

(= (mail-verify:check-mg $path $expected_count)
   (let $doc (mg:check-document (mail-verify:preamble) $path ())
     (case $doc
       (((Megalodon.document $theory $authority verified
            (summary (theorems $nt) (checked $nc) (verified $nv)
                     (admitted 0) (aby 0) (dependent 0)
                     (unfinished 0) (out-of-budget 0)
                     (document-axioms 0) (aby-steps-tried 0) (aby-steps-proved 0))
            $entries)
         (if (and (== $nt $nc) (and (== $nt $nv) (== $nt $expected_count)))
             (let $_ (println! (MegalodonVerified $path (theorems $nv) (document-axioms 0) (admitted 0) (aby 0)))
               $nv)
             (mail-verify:fail (CountMismatch $path $expected_count $nt $nc $nv))))
        ($other (mail-verify:fail (DocumentNotVerified $path $other)))))))

;; A document that must not verify.
(= (mail-verify:rejected $path)
   (case (mg:check-document (mail-verify:preamble) $path ())
     (((Megalodon.document $theory $authority verified $summary $entries)
       (mail-verify:fail (NegativeControlVerified $path)))
      ($other (let $_ (println! (NegativeControlRejected $path)) True)))))

!(let* (($n1 (mail-verify:check-mg "megalodon/protocols/mail/01_wait_deadline.mg" 6))
        ($_ (mail-verify:rejected "megalodon/protocols/mail/controls/01_old_rule_never_bursts.mg")))
   (println! (MailVerificationSuitePass (modules 1) (theorems $n1) (document-axioms 0) (admitted 0) (aby 0))))
