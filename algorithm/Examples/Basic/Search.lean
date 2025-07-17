
import Mathlib

def findIndex(nums: Array Nat)(target: Nat) : Option (Fin nums.size) := Id.run do
  for a in Array.finRange nums.size do
    if nums[a] = target then
      return a
  none

theorem forIn_eq_find?
  {α β} {as: List α } {p: α → Prop} {hp: (a: α) → Decidable (p a)} {init: β} {res: α → β } :
  (forIn as init fun a _ =>
    if p a then Id.instMonad.pure (ForInStep.done (res a))
    else Id.instMonad.pure (ForInStep.yield init)
  ) = (
    match List.find? (fun a => Decidable.decide (p a)) as with
    | none => init
    | some a => Id.instMonad.pure (res a)
  ):= by
  induction as with
  | nil =>
      simp
      rfl
  | cons a as prev =>
      by_cases h: p a
      . simp [h]
      . simp [h, prev]

theorem target_not_exists_of_findIndex_returns_none
  (nums: Array Nat)(target: Nat) :
  findIndex nums target = none → ¬ ∃ a: Fin nums.size, nums[a] = target := by
  intro h
  simp [findIndex, Id] at h
  rw [← Array.forIn_toList] at h
  rw [forIn_eq_find?] at h
  by_contra h'
  have ⟨i, hi ⟩ := h'
  have hi': i ∈ (Array.finRange nums.size).toList := by
    apply Array.mem_def.mp
    apply Array.mem_iff_getElem.mpr
    use i
    simp
  have h' : ∃ i ∈ (Array.finRange nums.size).toList, Decidable.decide (nums[i] = target) = true := by
    use i
    constructor
    . exact hi'
    . simp [hi]
  have h1 := List.find?_isSome.mpr h'
  split at h
  next x heq =>
    split at heq
    next x_1 heq_1 =>
      simp [heq_1] at h1
    next x_1 heq_1 =>
      simp at heq
  next x a heq =>
    split at heq
    next x_1 heq_1 =>
      simp [Id.run] at heq
    next x_1 a_1 heq_1 =>
      simp at heq
      simp [← heq] at h

theorem findIndex_returns_none_of_target_not_exists
  (nums: Array Nat)(target: Nat) :
   (¬ ∃ a: Fin nums.size, nums[a] = target) → findIndex nums target = none  := by
  intro h
  simp [findIndex]
  rw [← Array.forIn_toList, forIn_eq_find?]
  simp at h
  rw [List.find?_eq_none.mpr]
  simp [Id.run]
  simp [h]

theorem findIndex_returns_none_iff_target_not_exists
 (nums: Array Nat)(target: Nat) :
 findIndex nums target = none ↔ ¬ ∃ a: Fin nums.size, nums[a] = target :=
  by
    constructor
    . apply target_not_exists_of_findIndex_returns_none
    . apply findIndex_returns_none_of_target_not_exists
