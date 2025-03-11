-- 1.0 预备知识
import Mathlib.Tactic

open Function
open Set

variable {α β : Type*}

-- 习题1：设X和Y是两个集合
variable {X: Set α}
variable {Y: Set β}

-- f: X→Y 和　g: Y→X 是两个映射。
variable (f: α → β)
variable (g: β → α)

-- f是X上的单射
#check X.InjOn

-- g是f的左逆
#check X.LeftInvOn g f

-- f存在左逆 ↔ f是单射
theorem injective_of_left_inv: ((∃ g, X.LeftInvOn g f) ↔ X.InjOn f) := by
  apply Iff.intro
  {
    -- 证明f存在左逆 表示f是单射
    intro h
    let ⟨g, hg⟩ := h
    intro x hx y hy h2
    have h3: g (f x) = g (f y) := by
      simp [h2]
    simp [hg hx, hg hy] at h3
    exact h3
  }
  {
    -- 证明f是单射 表示f存在左逆
    intro h
    let Y' := f '' X
    sorry
  }
