-- 1.0 预备知识
import Mathlib.Tactic


open Classical
open Function

variable {α β : Type*} [Nonempty α]

-- 习题1：设X和Y是两个集合
-- 然而后续证明其实不必讨论X，和Y，只需要设α'=↑X β'=↑Y即可
variable {X: Set α}
variable {Y: Set β}

-- f: X→Y 和　g: Y→X 是两个映射。
variable (f: α → β)
variable (g: β → α)

-- 参考这个实现：
#check Function.HasLeftInverse.injective
#check Function.Injective.hasLeftInverse

noncomputable def inv_fun (f : α → β) : β → α :=
  fun y ↦ if h: ∃ x, f x = y then h.choose else Classical.arbitrary α

-- 习题1.1 证明 f存在左逆 ↔ f是单射
theorem injective_of_left_inv: (HasLeftInverse f ↔ Injective f) := by
  apply Iff.intro
  {
    -- 证明f存在左逆 表示f是单射
    intro h
    let ⟨g, hg⟩ := h
    intro x y h2
    have h3: g (f x) = g (f y) := by
      simp [h2]
    simp [hg x, hg y] at h3
    exact h3
  }
  {
    -- 证明f是单射 表示f存在左逆
    intro h
    let g := inv_fun f
    have h2: LeftInverse g f := by
      intro x
      let y := f x
      have h3: ∃ a, f a = y := by
        exact Exists.intro x rfl
      have h4: f (inv_fun f y) = y := by
        simp [inv_fun, dif_pos h3, h3.choose_spec]
      exact h h4
    exact Exists.intro g h2
  }

theorem surjective_of_right_inv: (HasRightInverse f ↔ Surjective f) := by
  apply Iff.intro
  sorry
  sorry
