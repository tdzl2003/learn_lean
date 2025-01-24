namespace Question1
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    ⟨
      fun h => And.intro
        (fun x => (h x).left)
        (fun x => (h x).right),
      fun h => fun x => And.intro (h.left x) (h.right x)
    ⟩

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    fun h1 => fun h2 => fun x => (h1 x) (h2 x)

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    fun h1 => fun x => Or.elim h1
      (fun hpx => Or.inl (hpx x))
      (fun hpx => Or.inr (hpx x))
end Question1

namespace Question2
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ _ : α, r) ↔ r) :=
    fun a => ⟨
      (fun h => h a),
      (fun hr => fun _ => hr)
      ⟩

  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    ⟨
      fun h =>
        Or.elim
          (Classical.em r)
          (fun hr => Or.inr hr)
          (fun hnr => Or.inl (fun x => Or.elim (h x) (id) (fun hr => absurd hr hnr))),
      fun h => Or.elim h
        (fun h1 => fun x => Or.inl (h1 x))
        (fun hr => fun _ => Or.inr hr)
    ⟩

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    ⟨
      fun h1 => fun hr => fun x => h1 x hr,
      fun h1 => fun x => fun hr => h1 hr x
    ⟩
end Question2

namespace Question3
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    Or.elim (Classical.em (shaves barber barber))
      (fun h1 => absurd h1 ((h barber).mp h1))
      (fun nh1 => absurd ((h barber).mpr nh1) nh1)
end Question3


namespace Question4
  def even (n : Nat) : Prop := ∃x, x * 2 = n
  def prime (n : Nat) : Prop := ¬(∃x y, x>1∧y>1∧x*y=n)
  def infinitely_many_primes : Prop := ∀n, ∃p, p>n ∧ prime p
  def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃x, 2^2^x+1 = n
  def infinitely_many_Fermat_primes : Prop := ∀n, ∃p, p>n ∧ Fermat_prime p
  def goldbach_conjecture : Prop := ∀n, n>2∧even n → ∃ p q, prime p ∧ prime q ∧ p+q=n
  def Goldbach's_weak_conjecture : Prop := ∀n, n>5∧¬ even n → ∃ p q r, prime p ∧ prime q ∧ prime r ∧ p+q+r=n
  def Fermat's_last_theorem : Prop := ∀ n, n>3 -> ¬ ∃ x y z, x>0 ∧ y>0 ∧ z>0 ∧ x^n+y^n=z^n
end Question4

namespace Question5
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ x : α, r) → r :=
    fun h => h.elim (fun _ => fun hr => hr)

  example (a : α) : r → (∃ x : α, r) :=
    fun hr => Exists.intro a hr

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    ⟨
      fun h1 =>
        And.intro (h1.elim (fun a => fun hx => Exists.intro a hx.left)) (h1.choose_spec.right),
      fun h1 => h1.left.elim (fun a => fun hx => Exists.intro a (And.intro hx h1.right))
    ⟩

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    ⟨
      fun h1 =>
        Or.elim (em (∃ x, p x))
          Or.inl
          (fun hn1 => Or.inr (h1.elim
            (fun x => fun h2 => h2.elim
              (fun h3 => absurd (Exists.intro x h3) hn1)
              (fun h3 => Exists.intro x h3)
            )
          )
          )
        ,
      fun h1 => h1.elim
        (fun h1l => h1l.elim (
          fun x => fun h2 => Exists.intro x (Or.inl h2)
        ))
        (fun h1l => h1l.elim (
          fun x => fun h2 => Exists.intro x (Or.inr h2)
        ))
    ⟩

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    ⟨
      fun h1 => byContradiction (
        fun hnn2 =>
          have h2 := (not_not.mp) hnn2
          h2.elim (
            fun x => fun hpx => absurd (h1 x) hpx
          )
      ),
      fun hn2 => fun x => Or.elim (em (p x))
        id
        (fun hnp => absurd (Exists.intro x hnp) hn2)
    ⟩

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    ⟨
      fun h1 => byContradiction (
        fun hnn2 =>
          have h2 := not_not.mp hnn2
          h1.elim (
            fun x => fun hpx => absurd hpx (h2 x)
          )
      ),
      fun hn2 => not_not.mp (Not.imp hn2 (
        fun hn1 => fun x => Or.elim (em (p x))
          (fun hp => absurd (Exists.intro x hp) hn1)
          id
      ))
    ⟩

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    ⟨ not_forall_not.mpr, not_forall_not.mp ⟩ -- 从decidable_of_iff 和 上一个定理 推导出来

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨
    fun hn1 => fun x => Or.elim (em (p x))
      (fun hpx => absurd (Exists.intro x hpx) hn1)
      id,
    fun h2 => Or.elim (em (∃ x, p x))
      (fun hx => absurd hx.choose_spec (h2 hx.choose))
      id
  ⟩

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    ⟨forall_not_of_not_exists, not_exists_of_forall_not ⟩

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    ⟨
      fun hn1 =>  not_not.mp (Not.imp hn1 (
        fun h2 => fun x => Or.elim (em (p x))
          id
          (fun npx => absurd (Exists.intro x npx) h2)
      )),
      fun h2 => Not.intro (
        fun h1 => absurd (h1 h2.choose) h2.choose_spec
      )
    ⟩

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    ⟨
      fun h1 => fun h2 => h1 h2.choose h2.choose_spec,
      fun h2 => fun x => fun hpx => Or.elim (em (∃ x, p x))
        (fun h1 => h2 h1)
        (fun hn3 => absurd (Exists.intro x hpx) hn3)
    ⟩

  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    ⟨
      fun h1 => fun h2 => h1.choose_spec (h2 h1.choose),
      fun h2 => Or.elim (em (∀ x, p x))
        (fun h3 => Exists.intro a (fun _ => h2 h3))
        (fun nh3 => not_not.mp (Not.imp nh3 (
          fun nh1 =>
            absurd
            (
              fun x => Or.elim (em (p x))
              id
              (fun nhpx => absurd (Exists.intro x (fun hpx => absurd hpx nhpx )) nh1)
            )
            nh3
        )))
    ⟩

  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    ⟨
      fun h1 => fun r => Exists.intro h1.choose (h1.choose_spec r),
      fun h2 => Or.elim (em r)
        (
          fun hr => (
            have h3 := h2 hr
            Exists.intro h3.choose (fun _ => h3.choose_spec)
          )
        )
        (fun hnr => Exists.intro a (fun hr => absurd hr hnr))
    ⟩
end Question5
