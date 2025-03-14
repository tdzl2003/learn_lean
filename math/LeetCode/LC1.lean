/-
https://leetcode.cn/problems/two-sum/description/
给定一个整数数组 nums 和一个整数目标值 target，请你在该数组中找出 和为目标值 target  的那 两个 整数，并返回它们的数组下标。
你可以假设每种输入只会对应一个答案，并且你不能使用两次相同的元素。
你可以按任意顺序返回答案。
-/

variables (nums: Array<Nat>)
variables (target: Nat)

def IsAnswer := (ans: Nat × Nat) →
  let ⟨a, b⟩  = ans
  a≠b ∧ nums[a]+nums[b] = target


-- 已知存在答案
-- 题目中提到的已知只存在一个有效答案只影响判定，不影响解的正确性
def HasAnswer := ∃ ans, IsAnswer ans
variables [HasAnswer nums target]

-- 解法1：暴力枚举a和b，直到找到满足条件的答案
def Solution1: Nat × Nat :=
  for a in [:nums.size] do
    for b in [a+1:num.size] do
      if nums[a]+nums[b] = target then return ⟨a, b⟩
  failure

-- 解法1的正确性证明
theorem solution1_is_answer : IsAnswer nums target <| Solution1 nums target := by
  sorry

-- 解法1的复杂度证明
-- TODO
