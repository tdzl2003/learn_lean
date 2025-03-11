namespace Exercise1
  def pred : Nat → Nat
    | 0 => 0
    | Nat.succ n => n

  def mul: (n m: Nat) → Nat
    | 0, _ => 0
    | n, 0 => 0
    | n, Nat.succ m => mul n m + n

  def sub: (n m : Nat) → Nat
    | 0, _ => 0
    | n, 0 => n
    | Nat.succ n, Nat.succ m => sub n m
end Exercise1

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    rfl
    rw [Nat.mul_comm]
