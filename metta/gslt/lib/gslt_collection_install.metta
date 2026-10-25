; Install freshly prepared frames while retaining existing work and history.
(: gslt:occurrence-install:append (-> Atom Atom %Undefined%))
(= (gslt:occurrence-install:append $fresh $state)
  (case $state
    (((RecursiveOccurrenceBatch $frames $log)
      (let $extended (gslt:automata:append $frames $fresh)
        (RecursiveOccurrenceBatch $extended $log))))))
