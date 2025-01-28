-- 使用tactics重写前两章练习题

-- 引入 & 方便后续书写更少的 And.intro
-- 它用来连接两个假设，类型分别为 p 和 q，返回 p ∧ q 的假设
notation:65 lhs:65 " & " rhs:66 => And.intro lhs rhs

-- 引入 : 方便后续书写更少的 Or.inl Or.inr
notation:30 lhs:30 ":" => Or.inl lhs
notation:30 ":" rhs:30 => Or.inr rhs

namespace Exercise3_1
  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := by
    have swapAnd{p}{q}: p∧q→q∧p := (by
      intro ⟨hp,hq⟩
      exact hq & hp
    )
    apply Iff.intro <;> apply swapAnd

  example : p ∧ q ↔ q ∧ p := by
    have swapAnd{p}{q}: p∧q→q∧p := (by
      intro ⟨hp,hq⟩
      constructor <;> assumption
    )
    apply Iff.intro <;> apply swapAnd

  example : p ∧ q ↔ q ∧ p := by
    constructor <;>
    . intro ⟨_, _⟩
      constructor <;> assumption

  example : p ∧ q ↔ q ∧ p := by
    simp [And.comm]

  example : p ∨ q ↔ q ∨ p := by
    have swapOr{p}{q}: p∨q→q∨p := (by
      intro hp
      apply Or.elim hp Or.inr Or.inl
    )
    apply Iff.intro <;> apply swapOr

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
    apply Iff.intro
    . intro ⟨⟨hp,hq⟩,hr⟩
      exact hp  & (hq & hr)
    . intro ⟨ hp, ⟨ hq, hr ⟩ ⟩
      exact (hp & hq ) & hr

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
    apply Iff.intro
    . intro
      | (p:): => exact p:
      | (:q): => exact :(q:)
      | :r => exact :(:r)
    . intro
      | p: => exact (p:):
      | :(q:) => exact (:q):
      | :(:r) => exact :r

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    apply Iff.intro
    . intro ⟨hp, h1r⟩
      match h1r with
      | hq: => exact (hp & hq):
      | :hr => exact :(hp&hr)
    . intro
      | (hp&hq): => exact hp & (hq:)
      | :(hp&hr) => exact hp & (:hr)

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
    apply Iff.intro
    . intro
      | hp: => exact (hp:)&(hp:)
      | :(hq&hr) => exact (:hq)&(:hr)
    . intro ⟨ h2l, h2r ⟩
      match h2l with
      | hp: => exact hp:
      | :hq => match h2r with
        | hp: => exact hp:
        | :hr => exact :(hq&hr)

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := by
    apply Iff.intro
    . intro h
      intro ⟨pq, pr⟩
      exact h pq pr
    . intro h
      intro hq
      intro hr
      exact h (hq&hr)

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
    apply Iff.intro
    . intro h
      apply And.intro
      . intro hp
        exact h (hp:)
      . intro hq
        exact h (:hq)
    . intro ⟨hpr, hqr⟩
      intro
      | hp: => exact hpr hp
      | :hq => exact hqr hq

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
    apply Iff.intro
    . intro h1
      apply And.intro
      . intro hp
        exact h1 (hp:)
      . intro hq
        exact h1 (:hq)
    . intro ⟨hnp,hnq⟩
      intro
      | hp: => exact absurd hp hnp
      | :hq => exact absurd hq hnq

  example : ¬p ∨ ¬q → ¬(p ∧ q) := by
    intro h
    intro ⟨hp,hq⟩
    match h with
    | hnp: =>
      exact absurd hp hnp
    | :hnq =>
      exact absurd hq hnq

  example : ¬(p ∧ ¬p) := by
    intro ⟨hp,hnp⟩
    exact absurd hp hnp

  example : p ∧ ¬q → ¬(p → q) := by
    intro ⟨hp,hnq⟩
    intro hpq
    have hq := hpq hp
    exact absurd hq hnq

  example : ¬p → (p → q) := by
    intro hnp
    intro hp
    exact absurd hp hnp

  example : (¬p ∨ q) → (p → q) := by
    intro hnporq
    intro hp
    match hnporq with
    | hnp: => exact absurd hp hnp
    | :hq => exact hq

  example : p ∨ False ↔ p := by
    apply Iff.intro
    . intro
      | hp: => exact hp
      | :f => apply f.elim
    . intro hp
      exact hp:

  example : p ∧ False ↔ False := by
    apply Iff.intro
    . intro ⟨hp,hf⟩
      exact hf
    . intro hf
      apply hf.elim

  example : (p → q) → (¬q → ¬p) := by
    intro hp2q
    intro hnq
    apply Not.imp hnq hp2q

end Exercise3_1


namespace Exercise3_2
  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
    intro h1
    match em p with
    | hp: => match h1 hp with
      | hq: => exact Or.inl fun hp => hq
      | :hr => exact Or.inr fun hp => hr
    | :nhp => exact Or.inl fun hp => absurd hp nhp

  example : ¬(p ∧ q) → ¬p ∨ ¬q := by
    intro h1
    match em p with
    | hp: => match em q with
      | hq: => exact absurd (hp&hq) h1
      | :nhq => apply Or.inr; assumption
    | :nhp => apply Or.inl; assumption

  example : ¬(p ∧ q) → ¬p ∨ ¬q := by
    intro h1
    apply not_and_iff_or_not_not.mp
    assumption

  example : ¬(p → q) → p ∧ ¬q := by
    intro h1
    apply And.intro
    . apply Classical.byContradiction
      intro hnp
      apply h1
      intro p
      apply Not.elim
      repeat assumption
    . intro hq
      apply h1
      intro p
      assumption

  example : (p → q) → (¬p ∨ q) := by
    intro h1
    match em p with
    | hp: =>
        apply Or.inr
        apply h1
        assumption
    | :nhp =>
        apply Or.inl
        assumption

  example : (¬q → ¬p) → (p → q) := by
    intro h1
    intro hp
    apply byContradiction
    intro hnq
    apply Not.elim
    apply h1
    repeat assumption

  example : p ∨ ¬p := by
    apply em

  example : (((p → q) → p) → p) := by
    intro h1
    match em p with
    | hp:  => assumption
    | :hnp =>
      apply Not.elim hnp
      apply h1
      intro hp
      exact absurd hp hnp

end Exercise3_2

namespace Exercise4_1
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
    constructor
    . intro h1
      constructor
      . intro x
        exact (h1 x).left
      . intro x
        exact (h1 x).right
    . intro ⟨h2l,h2r⟩
      intro x
      constructor
      apply h2l
      apply h2r
      repeat assumption

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
    intro h1
    intro h2
    intro x
    exact h1 x (h2 x)

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
    intro h1
    intro hx
    apply h1.elim
    intro h1l
    apply (h1l hx):
    intro h1r
    apply :(h1r hx)
end Exercise4_1

namespace Exercise4_2
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ x : α, r) ↔ r) := by
    intro x0
    apply Iff.intro
    . intro h1
      exact h1 x0
    . intro hr
      intro x
      assumption

  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
    apply Iff.intro
    . intro h1
      match Classical.em r with
      | hr: => apply Or.inr; assumption
      | :hnr =>
        apply Or.inl
        intro x
        match h1 x with
        | hpx: => assumption
        | :hr => exact absurd hr hnr
    . intro
      | h2l: =>
        intro x
        have px := h2l x
        apply Or.inl
        assumption
      | :h2r =>
        intro x
        apply Or.inr
        assumption

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
    apply Iff.intro
    . intro h1
      intro r
      intro x
      exact h1 x r
    . intro h2
      intro x
      intro r
      exact h2 r x

end Exercise4_2

namespace Exercise4_3
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
    match Classical.em (shaves barber barber) with
    | hp: =>
      have h1 := (h barber).mp
      exact absurd hp (h1 hp)
    | :hnp =>
      have h1 := (h barber).mpr
      exact absurd (h1 hnp) hnp
end Exercise4_3

namespace Exercise4_5
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ x : α, r) → r := by
    intro ⟨_,hr⟩
    assumption

  example (a : α) : r → (∃ x : α, r) := by
    intro hr
    apply Exists.intro
    repeat assumption

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
    apply Iff.intro
    . intro ⟨x,hpx&hr⟩
      apply And.intro
      exact Exists.intro x hpx
      assumption
    . intro ⟨⟨x,hpx⟩,hr⟩
      apply Exists.intro x
      exact hpx&hr

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
    apply Iff.intro
    . intro
      | ⟨x,hpx:⟩ => apply Or.inl; apply Exists.intro; repeat assumption;
      | ⟨x,:hqx⟩ => apply Or.inr; apply Exists.intro; repeat assumption;
    . intro
      | ⟨x,hpx⟩: => apply Exists.intro; apply Or.inl; repeat assumption;
      | :⟨x,hqx⟩ => apply Exists.intro; apply Or.inr; repeat assumption;

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
    apply Iff.intro
    . intro h1
      intro ⟨x,hpx⟩
      exact absurd (h1 x) hpx
    . intro nh2
      intro x
      apply byContradiction
      intro h1
      exact absurd (Exists.intro x h1) nh2

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
    apply Iff.intro
    . intro ⟨x,hpx⟩
      intro h2
      exact absurd hpx (h2 x)
    . intro hn2
      apply byContradiction
      intro hn1
      apply Not.elim hn2
      intro x
      intro hpx
      have h1 := Exists.intro x hpx
      exact absurd h1 hn1

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
    apply Iff.intro
    . intro hn1
      intro x
      apply Not.imp hn1
      intro hp1
      apply Exists.intro x hp1
    . intro h2
      apply Not.intro
      intro ⟨x,hpx⟩
      exact absurd hpx (h2 x)

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
    apply Iff.intro
    . intro hn1
      apply byContradiction
      intro hn2
      apply hn1.elim
      intro x
      match em (p x) with
      | hpx: => assumption
      | :hnpx =>
        apply Not.elim hn2
        exact Exists.intro x hnpx
    . intro ⟨x,hnpx⟩
      intro h1
      apply Not.elim
      . assumption
      . exact h1 x

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
    exact not_forall

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
    apply Iff.intro
    . intro h1
      intro ⟨x, hpx⟩
      have r := h1 x hpx
      assumption
    . intro h2r
      intro x
      intro hpx
      have r := h2r (Exists.intro x hpx)
      assumption

  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
    apply Iff.intro
    . intro ⟨x, px2r⟩
      intro h2l
      exact px2r (h2l x)
    . intro h2
      match em (∀ x, p x) with
      | h2l: =>
        apply Exists.intro a
        intro hpx
        have r := h2 h2l
        assumption
      | :hn2l =>
        match em (∃ x, ¬ p x) with
        | ⟨x,hnpx⟩: =>
          apply Exists.intro x
          intro hpx
          exact absurd hpx hnpx
        | :ne =>
          apply hn2l.elim
          intro x
          apply byContradiction
          intro hnpx
          apply ne.elim
          apply Exists.intro
          repeat assumption



  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
    apply Iff.intro
    . intro ⟨x,hr2px⟩
      intro r
      apply Exists.intro x
      apply hr2px
      assumption
    . intro h1
      match em r with
      | hr: =>
        have ⟨x, hpx⟩ := h1 hr
        apply Exists.intro x
        intro hr
        assumption
      | :hnr =>
        apply Exists.intro a
        intro hr
        exact absurd hr hnr

end Exercise4_5
