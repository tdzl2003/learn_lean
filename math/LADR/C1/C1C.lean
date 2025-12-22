import Mathlib

-- Lean中线性子空间的定义
-- 它使用carrier: Set M来表示“子集”，不去单独定义类型和运算
#check Subspace

-- 加法恒等元的存在性
#check AddSubmonoid.zero_mem'

-- 对于加法封闭
#check AddSubsemigroup.add_mem'

-- 对于标量乘法封闭
#check SubMulAction.smul_mem'


-- 例1.35.a
namespace _1_35_a
  variable (𝔽: Type)[Field 𝔽]
  variable (b: 𝔽)
  abbrev V := (Fin 4) → 𝔽

  def SV := { v : V 𝔽 | v 2 = 5 * v 3 + b }

  example: (∃ W : Subspace 𝔽 (V 𝔽), W.carrier = SV 𝔽 b) ↔ b = 0 :=
    by
      constructor
      . -- 已知是子空间，证明b=0
        intro ⟨W, hW⟩
        have h1 := W.zero_mem'
        rw [hW] at h1
        unfold SV at h1
        simp only [Set.mem_setOf_eq, Pi.zero_apply] at h1
        simp only [mul_zero, zero_add] at h1
        rw [h1]
      . -- 已知b=0，证明是子空间
        intro hb
        use {
          carrier := SV 𝔽 b,
          zero_mem' := by
            simp [hb, SV]
          add_mem' := by
            intros x y hx hy
            simp [SV, hb] at hx hy ⊢
            rw [hx, hy, mul_add]
          smul_mem' := by
            intros a x hx
            simp [SV, hb] at hx ⊢
            rw [hx, ← mul_assoc, ← mul_assoc, mul_comm a 5]
        }
end _1_35_a

-- 例1.35.b
namespace _1_35_b
  abbrev I01 := Set.Icc (0: ℝ) 1
  -- 定义在[0,1]上的全体实值函数
  abbrev V := I01 → ℝ
  -- 定义在[0,1]上的全体连续函数
  abbrev SV := {f: V | Continuous f}

  example: Subspace ℝ V := {
    carrier := SV
    zero_mem' := by
      simp only [Set.mem_setOf_eq]
      apply continuous_const
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq]
      apply ha.add hb
    smul_mem' := by
      intro c f hf
      simp only [Set.mem_setOf_eq] at ⊢
      apply hf.const_smul c
  }

end _1_35_b

-- 例1.35.c
namespace _1_35_c
  abbrev V := ℝ → ℝ
  abbrev SV := {f : V | Differentiable ℝ f}

  example: Subspace ℝ V := {
    carrier := SV
    zero_mem' := by
      simp only [Set.mem_setOf_eq]
      apply differentiable_const
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq]
      apply ha.add hb
    smul_mem' := by
      intro c f hf
      simp only [Set.mem_setOf_eq] at ⊢
      apply hf.const_smul c
  }

end _1_35_c


-- 例1.35.d
namespace _1_35_d
  abbrev I03 := Set.Ioo (0: ℝ) 3
  abbrev V := I03 → ℝ
  variable (b: ℝ)
  abbrev SV: Set V := {
    f : V |
      ∃ g : ℝ → ℝ,
        (∀ x : I03, g x.1 = f x) ∧                 -- g 在区间内等于 f
        (∀ x ∈ I03, DifferentiableAt ℝ g x) ∧      -- g 在 (0,3) 内处处可微
        deriv g 2 = b
  }

  example: (∃ W: Subspace ℝ V, W.carrier = SV b) ↔ b = 0 := by
    constructor
    . intro ⟨W, hW⟩
      have h := W.zero_mem'
      rw [hW] at h
      simp at h
      let ⟨g, hg⟩ := h
      have hEq : g =ᶠ[nhds 2] (fun _ => (0 : ℝ)) := by
        have hnhds : Set.Ioo (1 : ℝ) 3 ∈ nhds (2 : ℝ) := by
          -- 1 < 2 < 3，所以 (1,3) 是 2 的邻域
          apply IsOpen.mem_nhds
          . apply isOpen_Ioo
          . simp
            linarith
        filter_upwards [hnhds] with x hx
        -- hx : x ∈ (1,3)
        have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < 1) hx.1
        have : g x = 0 := hg.1 x hx0 hx.2
        simpa using this

      have hHas : HasDerivAt g 0 (2 : ℝ) := by
        have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 (2 : ℝ) := by
          apply hasDerivAt_const
        apply hconst.congr_of_eventuallyEq
        exact hEq
      rw [← hg.2.2]
      exact hHas.deriv
    . intro h1
      use {
        carrier := SV b,
        zero_mem' := by
          simp [h1]
          use fun v => 0
          simp
        add_mem' := by
          intro a b ⟨ga, ha⟩ ⟨gb, hb⟩
          use ga + gb
          and_intros
          . simp [ha, hb]
          . intro x hx
            apply DifferentiableAt.add
            exact ha.2.1 x hx
            exact hb.2.1 x hx
          . rw [h1] at ⊢ ha hb
            rw [deriv_add, ha.2.2, hb.2.2]
            simp
            . apply ha.2.1
              simp
              linarith
            . apply hb.2.1
              simp
              linarith
        smul_mem' := by
          intro c f ⟨g, hg⟩
          use c • g
          and_intros
          . simp [hg]
          . intro x hx
            apply DifferentiableAt.const_smul
            exact hg.2.1 x hx
          . rw [h1] at ⊢ hg
            rw [deriv_const_smul, hg.2.2, smul_zero]
            apply hg.2.1
            simp
            linarith
      }


end _1_35_d
