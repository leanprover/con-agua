example (l : List Nat) : l.headD 0 = l.head?.getD 0 := by simp
#check @List.headD_eq_head?_getD
