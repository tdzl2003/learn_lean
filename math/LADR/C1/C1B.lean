import Mathlib

-- 向量空间的定义，这里并没有要求Field，只要求Semiring
class MyVectorSpace (𝔽: Type)(V: Type)[Semiring 𝔽] extends AddCommGroup V, Module 𝔽 V

section

  variable (𝔽: Type)[Ring 𝔽]

  -- 𝔽^n 是向量空间
  abbrev FinVec(n: ℕ) := (Fin n) → 𝔽

  namespace FinVec
    variable {𝔽: Type}[Ring 𝔽]{n: ℕ}
    instance instVectorSpace: MyVectorSpace 𝔽 (FinVec 𝔽 n) :=
      {
        toAddCommGroup := (inferInstance : AddCommGroup _),
        toModule     := (inferInstance : Module 𝔽 _)
      }
  end FinVec

  -- 𝔽^∞ 也是向量空间
  abbrev InfVec := ℕ → 𝔽

  namespace InfVec
    variable {𝔽 : Type}[Ring 𝔽]
    instance instVectorSpace: MyVectorSpace 𝔽 (InfVec 𝔽) :=
      {
        toAddCommGroup := (inferInstance : AddCommGroup _),
        toModule     := (inferInstance : Module 𝔽 _)
      }
  end InfVec

  -- F^S 是向量空间，这里用Type而不是Set表示集合
  abbrev SetVec(S: Type) := S → 𝔽

  namespace SetVec
    variable {𝔽 : Type}[Ring 𝔽]{S: Type}
    instance instVectorSpace: MyVectorSpace 𝔽 (SetVec 𝔽 S) :=
      {
        toAddCommGroup := (inferInstance : AddCommGroup _),
        toModule     := (inferInstance : Module 𝔽 _)
      }
  end SetVec

  -- 我们从一开始就把 𝔽^n 定义为 (Fin n) → 𝔽 正好符合这一节的描述。

  -- 下面开始我们针对抽象的向量空间进行证明，不再针对𝔽^n空间了。
  variable (V: Type)[MyVectorSpace 𝔽 V]

  -- 向量空间有唯一的加法恒等元 0。
  example : ∃! zero : V, ∀ v : V , v+zero = v := by
    use 0
    constructor
    . -- 0 是加法恒等元
      simp
    . -- 如果hy: y是恒等元
      intro y hy
      -- 代入0，则有0 + y = 0
      have hy := hy 0
      -- 化简得 y = 0
      simp at hy ; exact hy

  -- 加法逆元的定义，-v实际上在这里定义：
  -- 原书在向量空间定义中给出了逆元的存在性，这里直接用构造性定义取代存在性。
  #check Pi.instNeg

  -- 加法逆元唯一
  example : ∀ v : V, ∃! v': V, v+v' = 0 := by
    intro v
    use -v
    constructor
    . -- -v 是 v 的加法逆元
      simp
    . -- 如果 w 也是 v 的加法逆元，那么 w = -v
      intro w hw
      calc w = w + 0 := by simp
        _ = w + (v + -v) := by simp
        _ = (w+v)+-v := by simp
        _ = 0 + -v := by rw [add_comm w, hw]
        _ = _ := by simp

  -- 向量与数0相乘
  example : ∀ v : V, 0 • v = 0 := by
    simp

  -- 数与向量0相乘
  example : ∀ a : 𝔽, a • (0: V) = 0 := by
    simp

  -- 向量与数-1相乘
  example : ∀ v : V, (-1) • v = -v := by
    simp

end section

section
  -- 许多习题中要求𝔽是数域才能证明，所以重新定义并加强
  variable (𝔽: Type)[Field 𝔽](V: Type)[MyVectorSpace 𝔽 V]

  -- 习题1B.1
  example: ∀ v : V, -(-v) = v := by
    simp

  -- 习题1B.2
  -- 隐含假设：𝔽 是域
  example  : ∀ (a : 𝔽)(v : V), a • v = 0 → a = 0 ∨ v = 0 := by
    intro a v h1
    by_cases h2: a = 0
    . -- a = 0
      exact Or.inl h2
    . -- a ≠ 0
      apply Or.inr
      have : a⁻¹ • (a • v) = 0 := by simp [h1]
      simp [← mul_smul, inv_mul_cancel₀ h2] at this
      exact this

  -- 习题1B.3
  -- 隐含假设：𝔽 是域，且3≠0 （如𝔽是数域）
  example [CharZero 𝔽]: ∀ v w : V, ∃! x: V, v + (3: 𝔽) • x = w := by
    intro v w
    let x := ((3: 𝔽)⁻¹) • (w - v)
    use x
    and_intros
    . simp [x]
    . intro y hy
      unfold x
      calc
        y = ((3: 𝔽)⁻¹) • (v + (3: 𝔽) • y - v) := by
            simp
        _ = _ := by
            rw [hy]

  -- 习题1B.4
  -- 显然空集不满足存在性加法恒等元的要求。其余要求都是满足的。

  -- 习题1B.5
  section
    -- 重新定义类型以引入不同的假设
    -- DistribMulAction中包含了 乘法恒等元 和 分配性质
    variable (𝔽: Type)[Field 𝔽](V: Type)[AddMonoid V][DistribMulAction 𝔽 V]
    variable (zero: V)

    -- 利用引入的新假设、乘法恒等元、分配性质 可以证出加法恒等元。
    -- 因为新假设已经引入了zero的定义，所以这里略过存在性的证明。
    example
      (h: ∀ v : V, 0 • v = zero)
      : ∀ v: V, v + zero = v := by
      intro v
      calc _ = v + 0 • v := by simp [← h v]
        _ = 1 • v + 0 • v := by simp
        _ = 1 • v := by simp
        _ = v := by simp
  end

  -- 习题1B.6
  -- 显然这样的运算规则不满足加法结合律，因此不满足向量空间的可结合性要求
  -- 如 ∞ + (-∞) + 1 = 0 + 1 = 1
  -- 而 ∞ + ((-∞) + 1) = ∞ + (-∞) = 0

  -- 习题1B.7
  -- 实际上可以看出这个V^S 就是广义的矩阵
  -- 但是我们这里没法直接使用Pi，也没法直接得到V是一个Ring，所以对成员依次完成证明
  section
    variable (S: Type)
    abbrev VV := S → V

    instance instVectorSpace: MyVectorSpace 𝔽 (VV V S) :=
      {
        add (a b: VV V S)(i:S) := a i + b i
        add_assoc := by simp [add_assoc]
        add_comm := by simp [add_comm]
        zero (i:S) := 0
        zero_add := by simp
        add_zero := by simp

        neg (v: VV V S)(i: S):= - v i
        neg_add_cancel := by
          intro a
          funext i
          simp

        smul (a: 𝔽)(v: VV V S)(i: S) := a • v i
        one_smul := by simp
        mul_smul := by simp [mul_smul]

        smul_zero := by simp [smul_zero]
        smul_add := by simp [smul_add]
        add_smul := by simp [add_smul]
        zero_smul := by simp [zero_smul]
        sub_eq_add_neg := by
          intro a b
          funext i
          simp [sub_eq_add_neg]

        -- 下面这些不属于书本内容，但是是Lean中的定义包含的，也一并定义
        nsmul (n: ℕ)(v: VV V S)(i:S):= n • v i
        zsmul (z: ℤ)(v: VV V S)(i:S):= z • v i
        nsmul_zero := by
          intro x
          funext i
          simp
        nsmul_succ := by
          intro n x
          funext i
          simp [add_smul]
        zsmul_zero' := by
          intro x
          funext i
          simp
        zsmul_succ' := by
          intro z x
          funext i
          simp [add_smul]
        zsmul_neg' := by
          intro z x
          funext i
          simp [add_smul]
      }
  end

  -- 习题1B.8
  -- 证明 V × V 是 ℂ 的向量空间
  section
    variable (V: Type)[MyVectorSpace ℝ V]
    abbrev VC := V × V

    def csmul(z: ℂ)(p: VC V) :=
        ( (z.re : ℝ) • p.1 - (z.im : ℝ) • p.2
        , (z.im : ℝ) • p.1 + (z.re : ℝ) • p.2 )

    instance : SMul ℂ (VC V) where
      smul := csmul V

    instance : Module ℂ (VC (V := V)) where
        smul := (· • ·)
        one_smul p := by
          ext
          all_goals simp [HSMul.hSMul, SMul.smul, csmul]
          . change ( (1 : ℝ) • p.1 - (0 : ℝ) • p.2 = p.1 )
            simp
          . change ( (0 : ℝ) • p.1 + (1 : ℝ) • p.2 = p.2 )
            simp
        mul_smul z w p := by
          ext
          all_goals simp [HSMul.hSMul, SMul.smul, csmul]
          . change ((z.re * w.re - z.im * w.im) • p.1 - (z.re * w.im + z.im * w.re) • p.2 =
              z.re • (w.re • p.1 - w.im • p.2) - z.im • (w.im • p.1 + w.re • p.2))
            simp [smul_sub, smul_smul, sub_smul, add_smul, sub_sub, add_comm, add_assoc]
          . change ((z.re * w.im + z.im * w.re) •  p.1 + (z.re * w.re - z.im * w.im)• p.2 =
              z.im • (w.re • p.1- w.im • p.2) + z.re • (w.im • p.1 + w.re • p.2))
            simp [smul_smul, add_smul, sub_eq_add_neg, ← add_comm, ← add_assoc]
        smul_add z p q := by
          ext
          all_goals simp [HSMul.hSMul, SMul.smul, csmul]
          . change (z.re • (p.1 + q.1) - z.im • (p.2 + q.2)=
              z.re • p.1 - z.im • p.2 + (z.re • q.1 - z.im • q.2))
            simp [smul_add, ← sub_sub, add_sub]
            simp [sub_eq_add_neg, add_comm, ← add_assoc]
          .
            change (z.im • (p.1 + q.1) + z.re • (p.2 + q.2) =
              z.im • p.1 + z.re • p.2 + (z.im • q.1 + z.re • q.2))
            simp [add_comm, ← add_assoc]
        smul_zero z := by
          ext
          all_goals {
            simp [HSMul.hSMul, SMul.smul, csmul]
            repeat rw [show ∀ r: ℝ, SMul.smul r (0: V) = r • 0 by intro r ; simp [HSMul.hSMul]]
            simp [smul_zero]
          }
        add_smul z w p := by
          ext
          all_goals {
            simp [HSMul.hSMul, SMul.smul, csmul]
            repeat rw [show ∀ (r: ℝ)(v: V), SMul.smul r v = r • v by intro r ; simp [HSMul.hSMul]]
            simp [add_smul, ← sub_sub, add_sub]
            simp [sub_eq_add_neg, add_comm, ← add_assoc]
          }
        zero_smul p := by
          ext
          all_goals {
            simp [HSMul.hSMul, SMul.smul, csmul]
            repeat rw [show ∀ (r: ℝ)(v: V), SMul.smul r v = r • v by intro r ; simp [HSMul.hSMul]]
            simp [zero_smul]
          }

      instance instVectorSpaceVC: MyVectorSpace ℝ (VC V) :=
        {
          toAddCommGroup := (inferInstance : AddCommGroup _),
          toModule     := (inferInstance : Module ℝ _)
        }
  end

end section
