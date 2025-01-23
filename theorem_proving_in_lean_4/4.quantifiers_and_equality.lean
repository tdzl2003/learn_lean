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
      fun h1 => And.intro (sorry) (sorry),
      sorry
    ⟩

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
end namespace
