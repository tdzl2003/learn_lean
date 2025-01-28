section define
variable {k: Nat}
variable {hk: k > 0}

structure ModK {hk: k > 0} where
  val: Nat
  {ok: val < k}

instance : ToString (ModK (k:=k) (hk:=hk)) where
  toString p := (toString p.val) ++ "(mod " ++ (toString k)++")"

def ModK.add (a: ModK (k:=k) (hk:=hk)) (b:ModK (k:=k) (hk:=hk)): ModK (k:=k) (hk:=hk) :=
  ModK.mk (k:=k) (hk:=hk) ((a.val+b.val)%k) (ok:=by simp [Nat.mod_lt, hk])

instance : HAdd (ModK (k:=k) (hk:=hk)) (ModK (k:=k) (hk:=hk)) (ModK (k:=k) (hk:=hk)) where
  hAdd x y := x.add y

-- 根据add的定义可以自然说明，无需证明
axiom ModK.mod_add_equal_add_mod: ∀(n m: ModK (k:=k) (hk:=hk)), (n+m).val = (n.val+m.val)%k

-- 定义modK的相等，即为值相等
axiom ModK.val_equal_imp_equal: ∀(n m: ModK (k:=k) (hk:=hk)), (n.val = m.val) → n = m
axiom ModK.equal_imp_val_equal: ∀(n m: ModK (k:=k) (hk:=hk)), n = m → (n.val = m.val)

theorem ModK.equal_iff_val_equal: ∀(n m: ModK (k:=k) (hk:=hk)), n = m ↔ (n.val = m.val) := by
  intro n
  intro m
  apply Iff.intro
  . apply ModK.equal_imp_val_equal n m
  . apply ModK.val_equal_imp_equal n m

theorem ModK.add_comm: ∀(n m: ModK (k:=k) (hk:=hk)), n+m=m+n := by
  intros
  apply ModK.val_equal_imp_equal
  simp [ModK.mod_add_equal_add_mod, Nat.add_comm]

theorem ModK.add_assoc: ∀(a b c: ModK (k:=k) (hk:=hk)), a+b+c=a+(b+c) := by
  intros
  apply ModK.val_equal_imp_equal
  simp [ModK.mod_add_equal_add_mod, Nat.add_assoc]

end define


section test
  def Mod6 := ModK (k:=6) (hk:=by simp)
  def mk := ModK.mk (k:=6) (hk:=by simp)

  def _0 := mk 0 (ok:=by simp)
  def _1 := mk 1 (ok:=by simp)
  def _2 := mk 2 (ok:=by simp)
  def _3 := mk 3 (ok:=by simp)
  def _4 := mk 4 (ok:=by simp)
  def _5 := mk 5 (ok:=by simp)

  #eval _3 + _5

  example : _3+_5 = _5+_3 := by simp [ModK.add_comm (k:=6)]

  example : ∀(a b: ModK (k:=6) (hk:=gt)), a+b=b+a := by simp [ModK.add_comm (k:=6)]

end test



-- theorem

#check Nat.add_comm
#check Nat.add_assoc
