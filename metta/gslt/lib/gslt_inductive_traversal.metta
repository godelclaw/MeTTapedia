; Traverse captured positions in their declared order, retaining duplicates.
(: gslt:inductive:visit-positions (-> Atom %Undefined%))
(= (gslt:inductive:visit-positions $positions)
  (case $positions
    ((LNil LNil)
     ((LCons $position $rest)
      (let $visited (gslt:inductive:visit-positions $rest)
        (LCons (Visited $position) $visited))))))
