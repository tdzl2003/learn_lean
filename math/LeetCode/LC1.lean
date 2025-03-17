/-
https://leetcode.cn/problems/two-sum/description/
给定一个整数数组 nums 和一个整数目标值 target，请你在该数组中找出 和为目标值 target  的那 两个 整数，并返回它们的数组下标。
你可以假设每种输入只会对应一个答案，并且你不能使用两次相同的元素。
你可以按任意顺序返回答案。
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Classical

-- 给定的参数
variable (nums: Array Nat)
variable (target: Nat)

-- 定义答案满足要求的条件
def IsAnswer(ans: Nat × Nat) :=
  let ⟨a, b⟩  := ans
  if h : a < nums.size ∧ b < nums.size then
    a<b ∧ nums[a]'h.left+nums[b]'h.right = target
  else
    False

-- 已知存在答案
-- 题目中提到的已知只存在一个有效答案只影响判定，不影响解的正确性
def HasAnswer := ∃ ans, IsAnswer nums target ans

-- 解法1：暴力枚举a和b，直到找到满足条件的答案
def Solution1: Nat × Nat := Id.run do
  for a in Array.finRange nums.size do
    for b in Array.finRange nums.size do
      if a<b ∧ nums[a]+nums[b] = target then
        return (a.val, b.val)
  return (0,0)

-- 样例数据
#eval Solution1 [2,7,11,15].toArray 9
#eval Solution1 [3,2,4].toArray 6
#eval Solution1 [3,3].toArray 6

-- 解法1的正确性证明
theorem solution1_is_right(hHasAnswer: HasAnswer nums target) : IsAnswer nums target <| Solution1 nums target := by
  conv =>
    arg 3
    simp [Solution1, Id.run]
  split
  {
    -- 无解分支，通过和有解推出矛盾证明
    rename_i x heq
    sorry
  }
  {
    -- 有解分支，证明解的正确性
    rename_i x ans heq
    sorry
  }

structure AnswerWithProof where
  ans: Nat × Nat
  proof: HasAnswer nums target -> IsAnswer nums target ans


-- 带有证明逻辑的Solution1，很难证明其和Solution1的等价性，但可以直接使用它得到一个带证明的实现
def Solution1_1_with_proof: AnswerWithProof nums target := Id.run do
  for a in Array.finRange nums.size do
    for b in Array.finRange nums.size do
      if h: a<b ∧ nums[a.val]+nums[b.val] = target then
        return AnswerWithProof.mk (a.val, b.val) (by
          {
            intro hHasAnswer
            simp [IsAnswer]
            simp [h.left]
            have x: a.val < nums.size∧b.val < nums.size := ⟨a.isLt, b.isLt⟩
            exact h.right
          })
  -- 无解情形的证明：需证明和有解矛盾，这个证明仍然涉及对for的拆解，比较困难
  return AnswerWithProof.mk (0,0) (by sorry)

def Solution1_1: ℕ×ℕ :=
    (Solution1_1_with_proof nums target).ans


theorem Solution1_1_is_right(hHasAnswer: HasAnswer nums target) : IsAnswer nums target <| Solution1_1 nums target := by
  exact (Solution1_1_with_proof nums target).proof hHasAnswer
