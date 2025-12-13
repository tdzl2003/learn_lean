import Mathlib

open Complex Real


-- 实数
#check ℝ

-- 复数
#check ℂ

-- 复数的加法
#check Complex.instAdd

-- 复数的乘法
#check Complex.instMul

-- i^2=-1
#check Complex.I_mul_I


-- （2+3i)(4+5i)
example : (2+3*I)*(4+5*I) = -7+22*I := by
  ring_nf
  rw [pow_two, I_mul_I]
  ring_nf

-- 复数的运算性质
-- 加法交换律
#check Complex.addCommGroup.add_comm
-- 乘法交换律
#check Complex.commRing.mul_comm
-- 加法结合律
#check Complex.addCommGroup.add_assoc
-- 乘法结合律
#check Complex.commRing.mul_assoc
-- 加法恒等元
#check Complex.addCommGroup.add_zero
-- 乘法恒等元
#check Complex.commRing.mul_one
-- 加法逆元
#check Complex.instNeg
#check Complex.addCommGroup.neg_add_cancel
-- 乘法逆元
#check Complex.instInv
#check Complex.instField.mul_inv_cancel
-- 分配性质
#check Complex.commRing.right_distrib


variable (𝔽: Type)[Field 𝔽](n: ℕ)

abbrev Vec := (Fin n)→ 𝔽

-- R³
#check Vec ℝ 3
-- ℂ^4
#check Vec ℂ 4

variable (α β :Vec 𝔽 n)

-- 加法定义
#check α+β
-- 实际定义来自：Pi空间：(v + w) i = v i + w i
#check Pi.instAdd

-- Pi空间自动带有其实例的加法交换群性质，所以向量加法满足交换律、结合律等
#check Pi.addCommGroup.add_comm

-- 记号0
example : Vec ℝ 3 := 0

-- 直接书写一个向量的表示
noncomputable example : Vec ℝ 5 := ![2, -3, 17, π, √2]

-- 逆元定义
#check -α
-- 同样来自Pi空间
#check Pi.instNeg

-- 无法在Lean里使用λ符号，用相反的γ替代
variable (γ: 𝔽)

-- 标量乘法
#check γ • α

-- 习题1A.1
example :∀ (α β : ℂ), α + β = β + α := by
   intros; apply Complex.ext <;> simp <;> ring

-- 习题1A.2
example : ∀ (α β γ : ℂ), (α + β) + γ = α + (β + γ) := by
  intros; apply Complex.ext <;> simp <;> ring

-- 习题1A.3
example :  ∀ (α β γ : ℂ), (α * β) * γ = α * (β * γ) := by
  intros; apply Complex.ext <;> simp <;> ring

-- 习题1A.4
example :  ∀ (α β γ : ℂ), γ * (α + β) = γ * α + γ * β := by
  intros; apply Complex.ext <;> simp <;> ring

-- 上述四道题全部都是直接展开定义就完成了证明

-- 习题1A.5
example : ∀ α: ℂ, ∃ β: ℂ, α + β = 0 := by
  intro α
  use ⟨-α.re, -α.im⟩
  apply Complex.ext <;> simp

-- 习题1A.6
example : ∀ α: ℂ, α ≠ 0 → ∃ β: ℂ, α * β = 1 := by
  intro α h1
  use ((⟨α.re, -α.im⟩: ℂ) * ((α.normSq)⁻¹))
  -- 展开并依次计算实部和虚部
  apply Complex.ext <;> simp [normSq] <;> ring_nf
  -- 实部合并后还原回normSq形式并得到1
  simp [← add_mul, pow_two,  ← normSq_apply]
  apply mul_inv_cancel₀
  -- 需要补充证明 α.normSq ≠ 0，根据α ≠ 0 得到
  intro he
  apply h1
  rw [normSq_eq_zero] at he
  exact he

-- 习题1A.7 也就是展开再展开，计算题
example : ((-1 + √3 * I)/ 2)^3 = 1 := by
  apply Complex.ext <;> simp [pow_three] <;> ring_nf <;> simp [pow_three] <;> ring_nf

-- 习题1A.8
example : ∀ α: ℂ, α = (√2 + √2 * I )/2 ∨ α = -(√2 + √2 * I )/2 ↔ α ^ 2 = I := by
  intro α
  constructor
  . intro h
    rcases h with h | h
    all_goals rw [h] ; apply Complex.ext <;> simp [I, pow_two] ; ring_nf
    all_goals norm_num
  . -- 尝试附加难度，证明只有这两个解
    intro h

    -- a^2-b^2 = 0
    have t1: (α^2).re = 0 := by rw [h]; simp
    -- 2ab = 1
    have t2: (α^2).im = 1 := by rw [h]; simp

    simp [pow_two] at t1 t2

    generalize hre: α.re = a, him: α.im = b at t1 t2

    -- t1: a^2 = b^2
    rw [sub_eq_zero, ← pow_two, ← pow_two] at t1

    -- t1: a = b ∨ a = -b
    rw [sq_eq_sq_iff_eq_or_eq_neg] at t1

    rcases t1 with t1 | t1
    . -- case a = b
      rw [← t1,← mul_two, ← pow_two] at t2

      have t2 : a^2 = 1/2 := by nlinarith [t2]
      have hs: (√2/2)^2 = 1/2 := by
        rw [pow_two]
        field_simp
        simp

      have t2 : a = √2/2 ∨ a = -(√2/2) := by
        apply sq_eq_sq_iff_eq_or_eq_neg.mp
        rw [hs, t2]

      rcases t2 with t2 | t2
      . apply Or.inl
        apply Complex.ext
        . rw [hre, t2]
          simp
        . rw [him, ← t1, t2]
          simp
      . apply Or.inr
        apply Complex.ext
        . rw [hre, t2]
          simp
          linarith
        . rw [him, ← t1, t2]
          simp
          linarith
    . -- case a = -b
      have t2: b^2 = -1/2 := by
        simp [t1] at t2
        rw [← neg_add, neg_eq_iff_eq_neg, ← mul_two, ← pow_two] at t2
        rw [← t2]
        norm_num

      have t3: b^2 >= 0 := by
        apply sq_nonneg

      rw [t2] at t3
      linarith

-- 习题1A.9
example : ∀ x: Vec ℝ 4, ![4,-3,1,7] + (2: ℝ) • x= ![5,9,-6,8] ↔ x = ![1/2,6,-7/2,1/2] := by
  intro x
  constructor
  . -- 逐维求解
    intro h
    funext i
    have h := congrArg (fun v : Fin 4 → _ => v i) h
    fin_cases i
    all_goals {
      simp
      simp at h
      linarith
    }
  . -- 代入验算
    intro h
    rw [h]
    simp
    norm_num

-- 习题1A.10
example : ∀ γ: ℂ, γ • ![2-3*I, 5+4*I, -6+7*I] ≠  ![12-5*I, 7+22*I, -32-9*I] := by
  intro γ h

  have hne : (2 - 3 * I : ℂ) ≠ 0 := by
    intro h
    -- 取虚部：im(2 - 3i) = -3，不可能等于 0
    have : ((2 - 3 * I : ℂ).im) = 0 := by simp [h]
    -- simp 会把它化成 (-3:ℝ)=0
    norm_num at this

  -- 选择两个矛盾的维度
  have h1 := congrArg (fun v : Fin 3 → _ => v 0) h
  have h2 := congrArg (fun v : Fin 3 → _ => v 2) h
  simp at h1 h2
  rw [← eq_div_iff hne] at h1
  rw [h1] at h2

  have hcalc : ((12 - 5 * I) / (2 - 3 * I) * (-6 + 7 * I)) = -32 + 9* I := by
    field_simp [hne]
    ring_nf
    have : (2 - I * 3)⁻¹ = 2/13+3/13*I:= by
      rw [Complex.inv_def]
      simp [normSq]
      simp [starRingEnd_apply]
      ring_nf

    rw [this]
    ring_nf
    rw [I_sq, I_pow_three]
    ring

  rw [hcalc] at h2
  rw [Complex.mk.injEq] at h2
  norm_num at h2

-- 习题1A.11
example : ∀ x y z : Vec 𝔽 n, (x+y)+z=x+(y+z) := by
  intro x y z
  funext i
  simp [add_assoc]

-- 习题1A.12
example : ∀ x : Vec 𝔽 n, ∀ a b : 𝔽, (a*b) • x = a • (b • x) := by
  intro x a b
  funext i
  simp [mul_assoc]

-- 习题1A.13
example : ∀ x : Vec 𝔽 n, 1 • x = x := by
  intro x
  funext i
  simp

-- 习题1A.14
example : ∀ γ : 𝔽, ∀ x y : Vec 𝔽 n, γ • (x+y) = γ • x + γ • y := by
  intro x a b
  funext i
  simp [left_distrib]

-- 习题1A.15
example : ∀ a b : 𝔽 , ∀ x : Vec 𝔽 n, (a + b) • x = a • x + b • x := by
  intro a b x
  funext i
  simp [right_distrib]
