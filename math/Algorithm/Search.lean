
open Classical

def find(nums: Array Nat)(target: Nat) : Option (Fin nums.size) := Id.run do
  for a in Array.finRange nums.size do
    if nums[a] = target then
      return a
  none

structure FindResult (nums: Array Nat)(target: Nat) where
  index : Fin nums.size
  proof : nums[index] = target

def findWithProof(nums: Array Nat)(target: Nat) : Option (FindResult nums target) := Id.run do
  for a in Array.finRange nums.size do
    if h: nums[a] = target then
      return some ⟨a, h⟩
  none

theorem find_result_is_answer (nums: Array Nat)(target: Nat) :
   ∀ a, find nums target = some a → nums[a] = target := by
    intro a
    intro h1
    let f := fun x: FindResult nums target => Option.some x.index
    have h: find nums target = (findWithProof nums target).bind f := by
      simp [find, findWithProof, Id.run, Option.bind, f]
      repeat rw [← Array.forIn_toList]
      simp only [forIn, forIn', List.forIn', List.forIn'.loop]
      generalize (Array.finRange nums.size).toList = list
      induction list with
      | nil =>
        simp [List.forIn'.loop]
      | cons a as ih =>
        simp [List.forIn'.loop]
        by_cases h3: nums[↑a] = target
        . simp_all only [Fin.getElem_fin, ite_true, dite_true, f]
        . sorry -- don't know how to do this yet
    rw [h] at h1
    simp [Option.bind]
    cases ih: findWithProof nums target with
    | none =>
      have h2: (match findWithProof nums target, f with
        | none, x => none
        | some a, f => f a) = none := by
        simp [ih]
      simp_all
    | some x =>
      have h3: f x = some a := by
        simp_all
      have h4: x.index = a := by
        rw [ih] at h1
        simp [f] at h1
        exact h1
      have h5 := x.proof
      simp [h4] at h5
      exact h5



-- 值得参考的实现：
#check List.find?_eq_some_iff_append
#check List.forIn'_cons


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
