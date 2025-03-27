-- 参考 https://github.com/Qiu233/MergeSort/blob/master/MergeSort/Basic.lean
-- 尝试以另一种结构给出相同的实现和证明

import Mathlib.Data.List.Permutation
import Mathlib.Tactic.Linarith

variable {α : Type}

variable [LinearOrder α]

def Merge : List α → List α → List α
  | [], y => y
  | x, [] => x
  | a :: x, b :: y =>
    if a ≤ b
      then a :: Merge x (b :: y)
      else b :: Merge (a :: x) y
termination_by x y => x.length + y.length
