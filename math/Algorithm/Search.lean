
def find(nums: Array Nat)(target: Nat) : Option (Fin nums.size) := Id.run do
  for a in Array.finRange nums.size do
    if nums[a] = target then
      return a
  none

theorem find_result_is_answer (nums: Array Nat)(target: Nat) :
   ∀ a: Fin nums.size, find nums target = some a → nums[a] = target :=
  by
    intro a
    simp [find, ←Array.forIn_toList, List.forIn_cons]







example (nums: Array Nat)(target: Nat) : find nums target = none ↔ ∀ a: Fin nums.size, nums[a] ≠ target :=
  by
    simp [find]
    apply Iff.intro
    focus
      sorry
    focus
      intro h
      -- 忽略simp带来的无用变量
      intro
      sorry
