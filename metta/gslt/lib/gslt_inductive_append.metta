; Retained expression arrays. Arguments are captured values; sequence producers
; explicitly with let before passing their results to these operations.
(: gslt:inductive:append (-> Atom Atom Expression))
(= (gslt:inductive:append $left $right) (union-atom $left $right))

(: gslt:inductive:length (-> Atom Number))
(= (gslt:inductive:length $values) (size-atom $values))

(: gslt:inductive:add (-> Atom Atom Number))
(= (gslt:inductive:add $left $right) (+ $left $right))
