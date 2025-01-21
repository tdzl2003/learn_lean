
namespace Learn

  def Implies (p q : Prop) : Prop := p → q
  structure Proof (p : Prop) : Type where
    proof : p
  #check Proof   -- Proof : Prop → Type

  axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

  variable (p q : Prop)
  #check and_comm p q     -- Proof (Implies (And p q) (And q p))


  variable {p : Prop}
  variable {q : Prop}
  theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

  #print t1

end Learn
