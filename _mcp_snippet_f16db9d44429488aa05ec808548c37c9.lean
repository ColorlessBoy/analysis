import Mathlib
#check (Equiv.piFinFin (m := 3) (n := 4) : (Fin 4 → Fin 3) ≃ Fin (3 ^ 4))
#check (Equiv.piFinFin (n := 3) (m := 2) : (Fin 3 → Fin 2) ≃ Fin (2 ^ 3))