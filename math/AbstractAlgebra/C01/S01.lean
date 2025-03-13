-- 1.0 预备知识
import Mathlib.Tactic


open Classical
open Function

variable {α β : Type*}

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

-- 为所有非空函数定义反函数。注意这个定义不一定是函数的左逆或右逆，这需要单独的证明
noncomputable def inv_fun [Nonempty α](f : α → β) : β → α :=
  -- 如果存在至少一个x满足 f(x)= y ，则任取一个定义 g(y)= x
  -- 如果不存在 f(x)=y，则任意定义 g(y)
  fun y ↦ if h: ∃ x, f x = y then h.choose else Classical.arbitrary α

-- 左逆存在性的定义：存在函数g: β→α，使得g(f(x)) = x
#check HasLeftInverse
-- 单射的定义：对于任意x y，f(x) = f(y) => x = y （课本上采用的是逆否命题定义，但显然二个定义等价）
#check Injective

-- 习题1.1 证明 f存在左逆 ↔ f是单射
-- 我发现书上的定理表述不完全，实际上逆命题仅当α非空时成立
-- 参考 @[Function.HasLeftInverse.injective] 和 @[Function.Injective.hasLeftInverse]
theorem injective_of_left_inv [Nonempty α]: (HasLeftInverse f ↔ Injective f) := by
  apply Iff.intro
  -- 证明f存在左逆 表示f是单射
  {
    -- 已知f存在左逆
    intro h
    -- 设 g 是 f 的左逆
    let ⟨g, hg⟩ := h
    -- 尝试证明f是单射，即对于任意x y，f(x) = f(y) => x = y
    {
      intro x y
      -- 已知f(x) = f(y)
      intro h2
      -- 所以根据f(x) = f(y)可得 g(f(x)) = g(f(y))
      have h3: g (f x) = g (f y) := by
        simp [h2]
      -- 由于g是f的左逆，所以g(f(x)) = x, g(f(y)) = y
      simp [hg x, hg y] at h3
      -- 所以可得 x = y，因此f是单射
      exact h3
    }
  }
  -- 证明f是单射 表示f存在左逆
  {
    -- 已知f是单射
    intro h
    -- 我们构造g为f的反函数
    let g := inv_fun f
    -- 证明当f是单射时，g是f的左逆，即证明 对任意的x 有 g(f(x)) = x
    have h2: LeftInverse g f := by
      -- 对任意的x
      intro x
      -- 设 y = f(x)
      let y := f x
      -- 显然根据y的定义，至少存在一个a满足 f(a) = y （x是一个例子）
      have h3: ∃ a, f a = y := by
        exact Exists.intro x rfl
      -- 然后我们要证明 f(g(y))=y
      have h4: f (inv_fun f y) = y := by
        -- 根据反函数的定义，因为g(y)是一个满足f(a)=y的a，所以f(g(y)) = y
        simp [inv_fun, h3, h3.choose_spec]
      -- 注意到f是单射，所以f(g(f(x))) = f(x) => g(f(x)) = x
      exact h h4
    -- 我们已经成功构造左逆，所以可以当做存在性的证明
    exact Exists.intro g h2
  }

-- 习题1.2 证明 f存在右逆 ↔ f是满射
-- 和上题一样，必须假设α非空，否则无法定义反函数
theorem surjective_of_right_inv[Nonempty α]: (HasRightInverse f ↔ Surjective f) := by
  apply Iff.intro
  -- 证明f存在右逆 表示f是满射
  {
    -- 已知f存在右逆
    intro h
    -- 设 g 是 f 的右逆
    let ⟨g, hg⟩ := h
    -- 证明f是满射，即对于任意y，存在x使得f(x) = y
    {
      -- 对任意y
      intro y
      -- 由于g是f的右逆，所以f(g(y)) = y
      have h2: f (g y) = y := by
        simp [hg y]
      -- 所以我们找到了一个x=g(y)满足f(x) = y
      exact Exists.intro (g y) h2
    }
  }
  -- 证明f是满射 表示f存在右逆
  {
    -- 已知f是满射
    intro h
    -- 构造g为f的反函数
    let g := inv_fun f
    have : g = inv_fun f := rfl
    -- 证明g是f的右逆，即证明 对任意的y 有 f(g(y)) = y
    have h2: RightInverse g f := by
      -- 对任意的y
      intro y
      -- 设 x = g(y)
      let x := g y
      have : x = g y := rfl
      -- 我们要证明 f(x) = y
      have h3: f x = y := by
        -- 因为f是满射，所以对任意的y都存在a满足f(a) = y，
        have : ∃ a, f a = y := by
          simp [h y]
        -- 因此根据反函数的定义，x满足f(x)=y
        simp [*, inv_fun, (h y).choose_spec]
      -- 因此得证
      exact h3
    -- 我们已经成功构造右逆，所以可以当做存在性的证明
    exact Exists.intro g h2
  }
