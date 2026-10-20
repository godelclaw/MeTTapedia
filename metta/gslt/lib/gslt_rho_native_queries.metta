(: rho:native:hit (-> Atom Atom Atom %Undefined%))
(= (rho:native:hit $standard $target $receipts)
  (case $receipts
    ((LNil False)
     ((LCons $receipt $rest)
       (let $next (gslt:runner:target $standard $receipt)
         (if (== $next $target) True (rho:native:hit $standard $target $rest)))))))
(: rho:native:verdict (-> Atom Atom Atom %Undefined%))
(= (rho:native:verdict $standard $target $readout)
  (case $readout
    (((ClassReadout $members $receipts $complete)
      (if (rho:native:hit $standard $target $receipts) RhoProved
        (if $complete RhoRefuted RhoUnknown))))))
