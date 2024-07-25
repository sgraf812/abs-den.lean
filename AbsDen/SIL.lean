
def downClosed (p : Nat → Prop) := ∀ n₁ n₂ (_ : n₁ ≤ n₂) (_ : p n₂) , p n₁

structure IxType : Type where
  fam : Nat → Prop
  down : downClosed fam
  tz : fam 0                -- tz short for true at zero
open IxType

def IxFalse : IxType := ⟨ fun | .zero => True | _ => False , by sorry , by exact trivial⟩
